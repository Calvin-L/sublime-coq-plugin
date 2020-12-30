"""
Sublime Text 3 plugin for Coq.
"""

# builtin modules
import contextlib
import os.path
import threading
import time

# sublime
import sublime
import sublime_plugin

# local modules
from . import coq

# relevant
# https://sympa.inria.fr/sympa/arc/coqdev/2013-11/msg00084.html
# https://github.com/the-lambda-church/coquille
# https://github.com/the-lambda-church/coquille/issues/18
# http://www.vim.org/scripts/script.php?script_id=4388
# http://code.tutsplus.com/tutorials/how-to-create-a-sublime-text-2-plugin--net-22685
# http://www.sublimetext.com/docs/3/api_reference.html
# https://github.com/wuub/SublimeREPL/blob/master/sublimerepl.py

# relevant to Coq 8.5
# http://coq-club.inria.narkive.com/aGFS1KGj/printing-a-structured-representation-of-a-prop
# https://github.com/coq/coq/blob/trunk/stm/stm.mli
# https://github.com/coq/coq/blob/trunk/lib/feedback.ml

# relevant to future versions?
# https://github.com/coq/coq/blob/master/dev/doc/xml-protocol.md

# Regarding translucent colors in Sublime:
# A region with the name "region.[color]ish" preserves foreground syntax
# highlighting [1,2], as of build 3148.
# [1]: https://forum.sublimetext.com/t/dev-build-3153/33014/25
# [2]: https://www.sublimetext.com/3dev

# --------------------------------------------------------- Constants

# COQ_MAJOR_VERSION = (8,5)
COQ_MAJOR_VERSION = (8,9)

TODO_SCOPE_NAME = "region.yellowish"
TODO_FLAGS = sublime.DRAW_NO_OUTLINE # sublime.DRAW_NO_FILL | sublime.DRAW_NO_OUTLINE | sublime.DRAW_SOLID_UNDERLINE
DONE_SCOPE_NAME = "region.greenish"
DONE_FLAGS = sublime.DRAW_NO_OUTLINE # sublime.DRAW_SQUIGGLY_UNDERLINE | sublime.DRAW_NO_FILL | sublime.DRAW_NO_OUTLINE

# Which display style to use if the user's settings specify an unrecognized
# view style.
FALLBACK_DISPLAY_STYLE = "inline"

# --------------------------------------------------------- Feedback Display

""" !!! IMPORTANT NOTE !!!

    In general, interaction with Sublime Text should be done only on the main
    thread.  This is true even though the ST plugin manual [1] claims that "All
    API functions are thread-safe".  Here are some good reasons why you should
    not assume that "thread-safe" means "always safe to call from a secondary
    thread":

      - Even if each call to an ST plugin procedure is atomic, we need to
        string multiple calls together.  Those calls will not be atomic, so if
        multiple threads are modifying the same view, the view can get into an
        unexpected state.  It is much simpler to assume that every procedure we
        write will be run atomically, with no interleaving from other threads.

      - Deadlock is possible.  ST's thread safety involves some internal hidden
        locks, and I have seen a lot of deadlocks of the form:
          1. The main thread acquires some internal lock.
          2. A secondary thread acquires some plugin-specific lock.
          3. The secondary thread tries to call a ST function that acquires the
             same internal lock, and blocks.
          4. An EventListener tries to acquire the same plugin-specific lock
             to safely interact with the secondary thread, and blocks, causing
             deadlock.
"""

class CoqDisplay(object):
    """A thread-safe display handle.

    Instances of this class interact with Sublime Text to provide feedback to
    the user.  They have the following convenient attributes:

     - Thread-safe.  Any thread may use most methods of this class without fear
       of deadlock or concurrency issues.  (There are some exceptions, noted in
       the docstrings.  Private methods start with underscores and should not
       be called externally.)
     - Batching.  Frequent changes to the display will be accumulated into a
       single batch and applied all at once.

    Lifecycle:

        +--- Synchronized -----------+
        | (initial state;            |
        | update_scheduled=False and |
        | flush() is not running)    |
        +----------------------------+
                |  ^
         update |  | flush
                v  |
        +--- Update Scheduled ----+
        +-------------------------+
                |
                | if should_close=True
                v
        +--- Closed -----+
        | is_closed=True |
        +----------------+

    """

    def __init__(self, view):
        """This method may only be called from the main thread.

        Subclasses may initialize the view when this is called."""

        self.view = view

        self.high_water_mark = 0
        self.todo_mark = 0
        self.goal = ""
        self.should_close = False
        self.is_closed = False
        self.update_scheduled = False

        self.lock = threading.Lock()

    def set_marks(self, high_water_mark, todo_mark):
        with self._update():
            self.high_water_mark = high_water_mark
            self.todo_mark = todo_mark

    def show_goal(self, goal):
        with self._update():
            self.goal = goal

    def was_closed_by_user(self):
        """This method may only be called from the main thread."""
        raise NotImplementedError()

    def close(self):
        with self._update():
            self.should_close = True

    @contextlib.contextmanager
    def _update(self):
        need_schedule = False
        with self.lock:
            yield

            # With the lock held, try to become the one thread responsible for
            # scheduling the update.
            if not self.update_scheduled:
                need_schedule = True
                self.update_scheduled = True

        if need_schedule:
            # Delay to increase odds of successful batching, and to give
            # Sublime Text some time to accept user input.
            delay_milliseconds = 10
            sublime.set_timeout(self.flush, delay_milliseconds)

    def flush(self):
        """This method may only be called from the main thread."""

        # take a snapshot of the state
        with self.lock:
            should_close = self.should_close
            high_water_mark = self.high_water_mark
            todo_mark = self.todo_mark
            goal = self.goal

            # No future update is scheduled.  If the state changes after this
            # snapshot, another update will be scheduled to handle it later.
            self.update_scheduled = False

        # update the display
        if should_close:
            if not self.is_closed:
                self._cleanup()
                self.is_closed = True
        else:
            self._apply(high_water_mark, todo_mark, goal)

    def _cleanup(self):
        """Subclasses must implement this."""
        raise NotImplementedError()

    def _apply(self, high_water_mark, todo_mark, goal):
        """Subclasses must implement this."""
        raise NotImplementedError()

class SplitPaneDisplay(CoqDisplay):
    def __init__(self, view):
        super().__init__(view)
        self.response_view = view.window().new_file()
        self.response_view.set_syntax_file("Packages/sublime-coq-plugin/Coq.tmLanguage")
        self.response_view.set_scratch(True)
        self.response_view.set_read_only(True)
        name = view.name() or os.path.basename(view.file_name() or "")
        title = "*** Coq for {} ***".format(name) if name else "*** Coq ***"
        self.response_view.set_name(title)

        window = view.window()
        ngroups = window.num_groups()
        if ngroups == 1:
            window.run_command("new_pane")
        else:
            group = window.num_groups() - 1
            if window.get_view_index(view)[1] == group:
                group -= 1
            window.set_view_index(self.response_view, group, 0)
        window.focus_view(view)

    def was_closed_by_user(self):
        return self.view.window() is None or self.response_view.window() is None

    def _cleanup(self):
        self.view.erase_regions("Coq")
        self.view.erase_regions("CoqTODO")

        # clean up the response view if it still exists
        response_view = self.response_view
        window = response_view.window()
        if window is not None:
            window.focus_view(response_view)
            window.run_command("close")
            window.focus_view(self.view)

    def _apply(self, high_water_mark, todo_mark, goal):
        self.view.add_regions("Coq", [sublime.Region(0, high_water_mark)], scope=DONE_SCOPE_NAME, flags=DONE_FLAGS)
        if todo_mark > high_water_mark:
            self.view.add_regions("CoqTODO", [sublime.Region(high_water_mark, todo_mark)], scope=TODO_SCOPE_NAME, flags=TODO_FLAGS)
        else:
            self.view.erase_regions("CoqTODO")
        self.response_view.run_command("coq_update_output_buffer", {"text": goal})

class InlinePhantomDisplay(CoqDisplay):
    def __init__(self, view):
        super().__init__(view)
        self.phantoms = sublime.PhantomSet(view, "CoqPhantoms")
        self.region = sublime.Region(0, 0)

    def format_goal(self, goal):
        goal = (goal
            .strip()
            .replace("&", "&amp;")
            .replace(" ", "&nbsp;")
            .replace("<", "&lt;")
            .replace(">", "&gt;")
            .replace("\n", "<br>"))
        return """
        <body id="coq-goal-phantom">
            <style>
                html {{ background-color: color(black alpha(0.25)); }}
                div.coq-goal {{ padding: 0.5rem; }}
            </style>
            <div class="coq-goal">{goal}</div>
        </body>
        """.format(goal=goal)

    def inline_marker(self):
        return """
        <body id="coq-highwater-phantom">
            <style>
                span.coq-highwater { color: red; }
            </style>
            <span class="coq-highwater">#</span>
        </body>
        """

    def was_closed_by_user(self):
        return self.view.window() is None

    def _cleanup(self):
        self.view.erase_regions("Coq")
        self.view.erase_regions("CoqTODO")
        self.phantoms.update([])

    def _apply(self, high_water_mark, todo_mark, goal):
        self.region = region = sublime.Region(0, high_water_mark)
        self.view.add_regions("Coq", [region], scope=DONE_SCOPE_NAME, flags=DONE_FLAGS)
        if todo_mark > high_water_mark:
            self.view.add_regions("CoqTODO", [sublime.Region(high_water_mark, todo_mark)], scope=TODO_SCOPE_NAME, flags=TODO_FLAGS)
        else:
            self.view.erase_regions("CoqTODO")

        marker_pos = self.region.end()
        marker_region = sublime.Region(marker_pos, marker_pos)
        goal_pos = self.view.line(marker_region).begin()
        self.phantoms.update([
            sublime.Phantom(
                region=marker_region,
                content=self.inline_marker(),
                layout=sublime.LAYOUT_INLINE),
            sublime.Phantom(
                region=sublime.Region(goal_pos, goal_pos),
                content=self.format_goal(goal),
                layout=sublime.LAYOUT_BELOW)])

# A "registry" of CoqDisplay subclasses for the "view_style" setting.  Each
# constructor should take a single `view` argument (in addition to `self`).
DISPLAY_CLASSES_BY_NAME = {
    "split": SplitPaneDisplay,
    "inline": InlinePhantomDisplay,
}

# --------------------------------------------------------- Logging

class Log(object):
    def __init__(self):
        pass
    def write(self, value):
        pass

## Uncomment this definition to use a real log file.
#
# class Log(object):
#     def __init__(self):
#         self.f = open("/tmp/sublime-coq-plugin.log", "a")
#     def write(self, value):
#         now = time.asctime(time.localtime())
#         self.f.write("[{}, {}]: {}\n".format(
#             now,
#             threading.get_ident(),
#             value))
#         self.f.flush()

log = Log()

# --------------------------------------------------------- Coq Worker

class CoqWorker(threading.Thread):
    """Asynchronous worker thread for the Sublime-Coq plugin.

    Lifecycle:
                  +-------+      +----------+      +------+
        Init ---> | ALIVE | ---> | STOPPING | ---> | DEAD |
                  +-------+      +----------+      +------+

    Note that the "ALIVE" state includes both forward evaluation (sending
    new commands to Coq) and backward evaluation (rewinding to an earlier
    state).

    Commands that can be called from other threads:
      - seek(text, pos)  --> start evaluating or change evaluation target
      - mark_dirty(text) --> seek backwards if changes have been made in the proven region
      - stop()           --> enter the STOPPING state to shut down Coq

    Note the "text" parameter: the worker needs to be given the current view
    contents.  A value of `None` indicates that the text has not changed.

    The worker updates the Sublime Text view as it changes state and as Coq
    sends responses.
    """

    def __init__(self, display, coq_install_dir, file_path=None):
        super().__init__(daemon=True)
        self.display = display

        working_dir = None
        if file_path is not None:
            working_dir = os.path.dirname(file_path)

        while coq_install_dir.endswith("/"):
            coq_install_dir = coq_install_dir[:-1]
        while coq_install_dir.endswith("bin"):
            coq_install_dir = coq_install_dir[:-3]
        while coq_install_dir.endswith("/"):
            coq_install_dir = coq_install_dir[:-1]

        self.coq = coq.CoqBot(
            coq_install_dir=coq_install_dir,
            coq_version=COQ_MAJOR_VERSION,
            working_dir=working_dir)

        self.text = ""
        self.state = "ALIVE"
        self.dirty = False
        self.desired_high_water_mark = 0
        self.high_water_mark = 0
        self.monitor = threading.Condition()

    def run(self):
        while True:
            do_step = None
            log.write("Waiting on monitor [run]...")
            with self.monitor:
                log.write("Acquired monitor! [run]")
                log.write("Worker state is: {} ({} --> {})".format(self.state, self.high_water_mark, self.desired_high_water_mark))
                if self.state == "ALIVE":
                    if self.dirty:
                        self.check_for_modifications()
                    elif self.desired_high_water_mark != self.high_water_mark:
                        do_step = (self.high_water_mark, self.desired_high_water_mark)
                    else:
                        log.write("Releasing monitor [idle]")
                        self.monitor.wait()
                        log.write("Acquired monitor [not-idle]")
                elif self.state == "STOPPING":
                    self.coq.stop()
                    self.display.close()
                    self.state = "DEAD"
                else:
                    return

            self.display.set_marks(self.high_water_mark, self.desired_high_water_mark)
            if do_step:
                try:
                    self.step(*do_step)
                except Exception as e:
                    log.write("uncaught exception: {}".format(e))
                    self.stop()

    def seek(self, text, pos):
        log.write("Waiting on monitor [seek]...")
        with self.monitor:
            log.write("Acquired monitor! [seek]")
            if self.state == "ALIVE" and pos != self.desired_high_water_mark:
                if text is not None:
                    self.text = text
                self.desired_high_water_mark = pos
                self.display.show_goal("Working...")
                self.display.set_marks(min(pos, self.high_water_mark), pos)
                log.write("Notifying all [seek]")
                self.monitor.notify_all()
            log.write("Releasing monitor [seek]")

    def stop(self):
        log.write("Waiting on monitor [stop]...")
        with self.monitor:
            log.write("Acquired monitor! [step]")
            if self.state == "ALIVE":
                self.state = "STOPPING"
                self.display.show_goal("Stopping...")
                log.write("Notifying all [stop]")
                self.monitor.notify_all()
            log.write("Releasing monitor [stop]")

    def mark_dirty(self, text=None, dirty=True):
        log.write("Waiting on monitor [mark_dirty]...")
        with self.monitor:
            log.write("Acquired monitor! [mark_dirty]")
            if text is not None:
                self.text = text
            self.dirty = dirty
            log.write("Notifying all [mark_dirty]")
            self.monitor.notify_all()
            log.write("Releasing monitor [mark_dirty]")

    def is_alive(self):
        return self.state != "DEAD"

    def check_for_modifications(self):
        """
        Called when the user altered the underlying buffer. We might need to
        rewind if they changed something in the proven region.
        """
        log.write("Checking for modifications...")
        index = 0
        self.mark_dirty(dirty=False)
        buffer = self.text[0 : self.high_water_mark]
        for cmd in self.coq.sent_buffer():
            log.write("Checking command {!r}".format(cmd))
            new_index = coq.find_first_coq_command(buffer, start=index)
            if new_index is None or cmd != buffer[index:new_index]:
                self.seek(text=None, pos=index)
                return
            assert new_index > index
            index = new_index
        log.write("Check for modifications finished")

    def change_desired_high_water_mark(self, expected_value, new_value):
        """Set self.desired_high_water_mark via compare-and-swap.

        This helper method can be used to safely write to
        self.desired_high_water_mark.  Normally it is unsafe to do so directly
        since other threads may write to it via self.seek().

        This method returns True if the value was equal to expected_value and
        was updated.  Otherwise it returns False and has no effect.  The return
        value can be used to detect whether self.seek() was called between when
        expected_value was read and when this method was called.
        """
        log.write("Waiting on monitor [change_desired_high_water_mark]...")
        with self.monitor:
            log.write("Acquired monitor! [change_desired_high_water_mark]")
            if self.desired_high_water_mark == expected_value:
                self.desired_high_water_mark = new_value
                log.write("Releasing monitor [OK]")
                return True
            else:
                log.write("Releasing monitor [FAILED]")
                return False

    def step(self, from_idx, to_idx):
        log.write("step called: {} --> {}".format(from_idx, to_idx))

        if from_idx < to_idx:
            text = self.text[from_idx:to_idx]
            log.write("unsent: {!r}".format(text))
            try:
                cmd_len = self.coq.append(text)
            except Exception as e:
                self.display.show_goal("Error: {}".format(e))
                self.change_desired_high_water_mark(to_idx, from_idx)
                return

            if cmd_len == 0:
                self.change_desired_high_water_mark(to_idx, from_idx)
            else:
                self.high_water_mark += cmd_len

        else:

            try:
                rewind_point = self.coq.rewind_to(to_idx)
            except coq.CoqException as e:
                # The exception will be caught and displayed when we try to
                # show the current goal later.
                pass
            self.high_water_mark = rewind_point
            self.change_desired_high_water_mark(to_idx, rewind_point)

        # This read ought to be safe even without lock acquisition.
        ultimate_target = self.desired_high_water_mark

        if self.high_water_mark == ultimate_target:

            try:
                goal = self.coq.current_goal()
            except coq.CoqException as e:
                goal = "Error: {}".format(str(e))
                self.change_desired_high_water_mark(to_idx, self.high_water_mark)

            self.display.set_marks(self.high_water_mark, ultimate_target)
            self.display.show_goal(goal)

# --------------------------------------------------------- Worker table

# A map from view IDs to worker threads.  This structure may only be read
# or written from the Sublime Text main thread.
coq_threads = dict()

def stop_worker(view_id, worker, reason):
    log.write("stopping {} ({})...".format(worker, reason))
    worker.stop()
    worker.join(1)
    if not worker.is_alive():
        del coq_threads[view_id]
        log.write("killed {}".format(worker))
    else:
        log.write("worker didn't die!")

# --------------------------------------------------------- Sublime Commands

class CoqCommand(sublime_plugin.TextCommand):
    def run(self, edit):
        log.write(self.view.style_for_scope(DONE_SCOPE_NAME))
        # return

        if "coq" not in self.view.scope_name(0):
            log.write("not inside a coq buffer")
            return
        worker_key = self.view.id()
        worker = coq_threads.get(worker_key, None)
        if not worker:
            settings = sublime.load_settings("CoqInteractive.sublime-settings")

            view_style = settings.get("view_style", FALLBACK_DISPLAY_STYLE)
            if view_style not in DISPLAY_CLASSES_BY_NAME:
                sublime.error_message('Your "view_style" setting specifies an '
                    + "unknown view style ({!r}). ".format(view_style)
                    + "Please use one of the official view styles: "
                    + ", ".join(DISPLAY_CLASSES_BY_NAME.keys())
                    + ". The plugin will now proceed using the "
                    + FALLBACK_DISPLAY_STYLE + " style.")
                view_style = FALLBACK_DISPLAY_STYLE

            DisplayClass = DISPLAY_CLASSES_BY_NAME[view_style]
            worker = CoqWorker(
                display         = DisplayClass(self.view),
                coq_install_dir = settings.get("coq_install_dir"),
                file_path       = self.view.file_name())
            coq_threads[worker_key] = worker
            worker.start()
            log.write("spawned worker {} for view {}".format(worker, worker_key))

        pos = self.view.sel()[0].a
        text = self.view.substr(sublime.Region(0, pos))
        worker.seek(text=text, pos=pos)

class CoqKillCommand(sublime_plugin.TextCommand):
    def run(self, edit):
        worker_key = self.view.id()
        worker = coq_threads.get(worker_key, None)
        if worker:
            stop_worker(worker_key, worker, "user-issued kill command")
        else:
            log.write("no worker to kill")

class CoqUpdateOutputBufferCommand(sublime_plugin.TextCommand):
    def run(self, edit, text=""):
        self.view.set_read_only(False)
        self.view.erase(edit, sublime.Region(0, self.view.size()))
        self.view.insert(edit, 0, text)
        self.view.show(0)
        self.view.set_read_only(True)

# --------------------------------------------------------- Event Management

class CoqViewEventListener(sublime_plugin.EventListener):

    def on_clone(self, view):
        pass # TODO: what happens when coq response views are duplicated?

    def on_modified(self, view):
        worker_key = view.id()
        worker = coq_threads.get(worker_key, None)
        if worker:
            # NOTE: While not immediately obvious, I think that reading the
            # `desired_high_water_mark` proprty is safe here, since only the
            # main thread changes that property via `seek`.
            text = view.substr(sublime.Region(0, worker.desired_high_water_mark))
            worker.mark_dirty(text=text)

    def on_close(self, view):
        for worker_key, worker in list(coq_threads.items()):
            if worker.display.was_closed_by_user():
                log.write("worker {} was closed??".format(worker))
                stop_worker(worker_key, worker, "view closed by user")
