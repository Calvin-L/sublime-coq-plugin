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
# https://github.com/coq/coq/blob/master/dev/doc/changes.md

# Regarding translucent colors in Sublime:
# A region with the name "region.[color]ish" preserves foreground syntax
# highlighting [1,2], as of build 3148.
# [1]: https://forum.sublimetext.com/t/dev-build-3153/33014/25
# [2]: https://www.sublimetext.com/3dev

# --------------------------------------------------------- Constants

TODO_SCOPE_NAME = "region.yellowish"
TODO_FLAGS = sublime.DRAW_NO_OUTLINE # sublime.DRAW_NO_FILL | sublime.DRAW_NO_OUTLINE | sublime.DRAW_SOLID_UNDERLINE
DONE_SCOPE_NAME = "region.greenish"
DONE_FLAGS = sublime.DRAW_NO_OUTLINE # sublime.DRAW_SQUIGGLY_UNDERLINE | sublime.DRAW_NO_FILL | sublime.DRAW_NO_OUTLINE
ERROR_SCOPE_NAME = "region.error.coq"
ERROR_FLAGS = sublime.DRAW_NO_OUTLINE | sublime.DRAW_SQUIGGLY_UNDERLINE

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
        self.bad_ranges = []
        self.should_close = False
        self.is_closed = False
        self.update_scheduled = False

        self.lock = threading.Lock()

    def set_marks(self, high_water_mark, todo_mark):
        with self._update():
            self.high_water_mark = high_water_mark
            self.todo_mark = todo_mark

    def show_goal(self, text="", goal=None):
        goal = format_goal_response(goal) if goal else ""

        with self._update():
            self.goal = (text + "\n\n" + goal).strip("\n")

    def set_bad_ranges(self, bad_ranges):
        with self._update():
            self.bad_ranges = bad_ranges

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
            bad_ranges = self.bad_ranges

            # No future update is scheduled.  If the state changes after this
            # snapshot, another update will be scheduled to handle it later.
            self.update_scheduled = False

        # update the display
        if should_close:
            if not self.is_closed:
                self._cleanup()
                self.is_closed = True
        else:
            self._apply(high_water_mark, todo_mark, goal, bad_ranges)

    def _cleanup(self):
        """Subclasses must implement this."""
        raise NotImplementedError()

    def _apply(self, high_water_mark, todo_mark, goal):
        """Subclasses must implement this."""
        raise NotImplementedError()

    def owns_view(self, view):
        """This method may only be called from the main thread.

        Returns True iff the argument is a subordinate view owned by this
        display (and therefore not a view into a normal Coq file)."""
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
            # At this point self.response_view has focus, so it will be moved
            # to the new pane automagically.
            window.run_command("new_pane")
        else:
            view_group, _ = window.get_view_index(view)
            group = (view_group + 1) % ngroups
            window.set_view_index(self.response_view, group, 0)
        window.focus_view(view)

    def was_closed_by_user(self):
        return self.view.window() is None or self.response_view.window() is None

    def _cleanup(self):
        self.view.erase_regions("Coq")
        self.view.erase_regions("CoqTODO")
        self.view.erase_regions("CoqError")

        # clean up the response view if it still exists
        response_view = self.response_view
        window = response_view.window()
        if window is not None:
            window.focus_view(response_view)
            window.run_command("close")
            window.focus_view(self.view)

    def _apply(self, high_water_mark, todo_mark, goal, bad_ranges):
        self.view.add_regions("Coq", [sublime.Region(0, high_water_mark)], scope=DONE_SCOPE_NAME,
            flags=DONE_FLAGS | sublime.NO_UNDO)
        if todo_mark > high_water_mark:
            self.view.add_regions("CoqTODO", [sublime.Region(high_water_mark, todo_mark)], scope=TODO_SCOPE_NAME,
                flags=TODO_FLAGS | sublime.NO_UNDO)
        else:
            self.view.erase_regions("CoqTODO")

        bad_ranges = [sublime.Region(start, end) for (start, end) in bad_ranges]
        self.view.add_regions("CoqError", bad_ranges, scope=ERROR_SCOPE_NAME, flags=ERROR_FLAGS | sublime.NO_UNDO)

        self.response_view.run_command("coq_update_output_buffer", {"text": goal})

    def owns_view(self, view):
        return self.response_view.id() == view.id()

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
        self.view.erase_regions("CoqError")
        self.phantoms.update([])

    def _apply(self, high_water_mark, todo_mark, goal, bad_ranges):
        self.region = region = sublime.Region(0, high_water_mark)
        self.view.add_regions("Coq", [region], scope=DONE_SCOPE_NAME, flags=DONE_FLAGS | sublime.NO_UNDO)
        if todo_mark > high_water_mark:
            self.view.add_regions("CoqTODO", [sublime.Region(high_water_mark, todo_mark)], scope=TODO_SCOPE_NAME,
                flags=TODO_FLAGS | sublime.NO_UNDO)
        else:
            self.view.erase_regions("CoqTODO")

        bad_ranges = [sublime.Region(start, end) for (start, end) in bad_ranges]
        self.view.add_regions("CoqError", bad_ranges, scope=ERROR_SCOPE_NAME, flags=ERROR_FLAGS | sublime.NO_UNDO)

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

    def owns_view(self, view):
        return False

# A "registry" of CoqDisplay subclasses for the "view_style" setting.  Each
# constructor should take a single `view` argument (in addition to `self`).
DISPLAY_CLASSES_BY_NAME = {
    "split": SplitPaneDisplay,
    "inline": InlinePhantomDisplay,
}

# --------------------------------------------------------- Display formatting

def format_goal_response(rp):
    """Format a CoqGoalResponse into a readable form."""

    settings = sublime.load_settings("CoqInteractive.sublime-settings")
    feedback = "\n".join(rp.feedback())

    if not rp.is_in_proof():
        return feedback

    other_counts = []
    primary_goal = None
    output = ""

    focused_goals = rp.goals("focused")
    finished = (len(focused_goals) == 0)
    summary = "Goals: {}".format(len(focused_goals))
    if focused_goals:
        primary_goal = focused_goals[0]

    # Flatten the background goal stack
    bg_goals = []
    for before, after in rp.bg_goals():
        bg_goals += before + after
    if bg_goals:
        other_counts.append("{} background".format(len(bg_goals)))

    shelved_goals = rp.goals("shelved")
    if shelved_goals:
        other_counts.append("{} background".format(len(shelved_goals)))

    admitted_goals = rp.goals("admitted")
    if admitted_goals:
        other_counts.append("{} admitted".format(len(admitted_goals)))

    if other_counts:
       summary += " (" + ", ".join(other_counts) + ")"
    summary += "\n\n"

    if finished:
        if bg_goals:
            goals = "\n\n".join(coq.text_of(goal) for hyps, goal in bg_goals)
            return feedback + "This subproof is complete, but there are some unfocused goals:\n\n" + goals
        elif admitted_goals:
            goals = "\n\n".join(coq.text_of(goal) for hyps, goal in admitted_goals)
            return feedback + "No more goals, but there are some goals you gave up:\n\n" + goals
        else:
            return feedback + "No more goals."

    if settings.get("show_goals", "focused") == "primary":
        goals_to_show = [primary_goal] if primary_goal else []
    else:
        goals_to_show = focused_goals

    for i, (hyps, goal) in enumerate(goals_to_show):
        if i == 0:
            output += "".join("  {}\n".format(coq.text_of(h)) for h in hyps)
        output += "  " + ("─" * 40) + " ({}/{})\n".format(i+1, len(goals_to_show))
        output += "  {}\n".format(coq.text_of(goal))

    return feedback + summary + output

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
#         msg = "[{}, {}]: {}".format(
#             now,
#             threading.get_ident(),
#             value)
#         print(msg)
#         self.f.write(msg)
#         self.f.write("\n")
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
            need_check_for_modifications = False
            log.write("Waiting on monitor [run]...")
            with self.monitor:
                log.write("Acquired monitor! [run]")
                log.write("Worker state is: {} ({} --> {})".format(self.state, self.high_water_mark, self.desired_high_water_mark))
                text = self.text
                if self.state == "ALIVE":
                    if self.dirty:
                        self.dirty = False
                        need_check_for_modifications = True
                    elif self.desired_high_water_mark != self.high_water_mark:
                        do_step = (self.high_water_mark, self.desired_high_water_mark)
                    else:
                        log.write("Releasing monitor [idle]")
                        self.monitor.wait()
                        log.write("Acquired monitor [not-idle]")
                elif self.state == "STOPPING":
                    # NOTE: self.coq.stop() is not necessary here; that is done
                    # in `self.stop()` after entering the "STOPPING" state.
                    self.display.close()
                    self.state = "DEAD"
                else:
                    return

            self.display.set_marks(self.high_water_mark, self.desired_high_water_mark)

            try:
                if need_check_for_modifications:
                    self._check_for_modifications(text)
                elif do_step:
                    self.step(text, *do_step)
            except coq.StoppedException:
                log.write("Worker is aborting due to StoppedException")
                assert self.state in ("STOPPING", "DEAD")
                continue # next loop iteration will take appropate action
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
                self.display.show_goal(text="Working...")
                self.display.set_marks(min(pos, self.high_water_mark), pos)
                log.write("Notifying all [seek]")
                self.monitor.notify_all()
            log.write("Releasing monitor [seek]")

    def stop(self):
        log.write("Waiting on monitor [stop]...")
        with self.monitor:
            log.write("Acquired monitor! [stop]")
            if self.state == "ALIVE":
                self.state = "STOPPING"
                self.display.show_goal(text="Stopping...")
                log.write("Notifying all [stop]")
                self.monitor.notify_all()
            log.write("Releasing monitor [stop]")

        # Stop the coqtop process.  If the worker thread is stuck waiting on a
        # response that will never come, this should free it up.
        self.coq.stop()

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

    def _check_for_modifications(self, text):
        """
        Called when the user altered the underlying buffer. We might need to
        rewind if they changed something in the proven region.
        """
        log.write("Checking for modifications...")
        index = 0
        for cmd in self.coq.sent_buffer():
            log.write("Checking command {!r}".format(cmd))
            new_index = coq.find_first_coq_command(text, start=index)
            if new_index is None or cmd != text[index:new_index]:

                # It's possible that the user did a seek while we were checking
                # for modifications.  If they did a seek forward, we want to
                # overwrite their intention---a change in the proven region
                # requires a rewind.  If they did a seek far enough backwards
                # though, then there is no need to destroy their intention.
                #
                # Nontrivial interaction with self.desired_high_water_mark
                # requires a lock acquisition---although since we are running
                # in the worker thread, there is no need to notify anyone (we'd
                # only be notifying ourselves).
                log.write("Waiting on monitor [_check_for_modifications]...")
                with self.monitor:
                    log.write("Acquired monitor! [_check_for_modifications]")
                    self.desired_high_water_mark = min(self.desired_high_water_mark, index)
                    log.write("Releasing monitor [_check_for_modifications]")

                # Regardless of what the user wants, we need to rewind back to
                # the now-unproven position.
                while self.high_water_mark > index:
                    self.step(text, from_idx=self.high_water_mark, to_idx=index)

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

    def step(self, text, from_idx, to_idx):
        log.write("step called: {} --> {}".format(from_idx, to_idx))

        self.display.set_bad_ranges([])

        if from_idx < to_idx:
            log.write("unsent: {!r}".format(text[from_idx:to_idx]))
            try:
                cmd_end = self.coq.append(text, start=from_idx, end=to_idx, verbose=True)
            except coq.CoqException as e:
                log.write("send was rejected ({})".format(e))
                self._stop_and_show_error(to_idx, e)
                return

            if cmd_end == 0:
                if not self.change_desired_high_water_mark(to_idx, from_idx):
                    print("WARNING: mark update {}-->{} failed".format(to_idx, from_idx))
                    return
            else:
                self.high_water_mark = cmd_end

        elif from_idx > to_idx:
            rewind_point = self.coq.rewind_to(to_idx)
            self.high_water_mark = rewind_point
            if not self.change_desired_high_water_mark(to_idx, rewind_point):
                print("WARNING: mark update {}-->{} failed".format(to_idx, rewind_point))
                return

        # This read ought to be safe even without lock acquisition.
        ultimate_target = self.desired_high_water_mark

        self.display.set_marks(self.high_water_mark, ultimate_target)
        if self.high_water_mark == ultimate_target:
            self._show_goal(ultimate_target)

    def _show_goal(self, desired_high_water_mark):
        log.write("checking goal [target={}]".format(desired_high_water_mark))

        try:
            feedback_text, goal = self.coq.current_goal()
        except coq.CoqException as e:
            self._stop_and_show_error(desired_high_water_mark, e)
            return

        self.display.show_goal(text=feedback_text, goal=goal)
        self.display.set_marks(self.high_water_mark, desired_high_water_mark)

    def _stop_and_show_error(self, desired_high_water_mark, error):
        tip = self.high_water_mark
        goal = "Error: {}".format(error)
        if self.change_desired_high_water_mark(desired_high_water_mark, tip):
            self.display.set_bad_ranges([(start + tip, end + tip) for (start, end) in error.bad_ranges])
            self.display.show_goal(text=goal)
            self.display.set_marks(tip, tip)
        else:
            print("WARNING: mark update {}-->{} failed".format(desired_high_water_mark, tip))

# --------------------------------------------------------- Worker table

# A map from view IDs to worker threads.  This structure may only be read
# or written from the Sublime Text main thread.
coq_threads = dict()

def spawn_worker(settings: sublime.Settings, view: sublime.View) -> CoqWorker:
    """Spawn a worker using the given `settings` on the given `view`.

    In addition to allocating a new `CoqWorker` object, this method:
      - creates a `CoqDisplay`
      - registers the worker in the `coq_threads` table
      - starts the `CoqWorker`
      - reports any errors encountered during spawning to the display
    """

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
    display = DisplayClass(view)

    try:
        worker_key = view.id()
        worker = CoqWorker(
            display         = display,
            coq_install_dir = settings.get("coq_install_dir"),
            file_path       = view.file_name())
        coq_threads[worker_key] = worker
        worker.start()
        log.write("spawned worker {} for view {}".format(worker, worker_key))
    except Exception as e:
        display.show_goal("Something went wrong: {}".format(e))
        raise

    return worker

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
        for worker in coq_threads.values():
            if worker.display.owns_view(self.view):
                log.write("inside a split view display")
                return
        worker_key = self.view.id()
        worker = coq_threads.get(worker_key, None)

        if worker and not worker.is_alive():
            stop_worker(worker_key, worker, "worker has crashed")
            worker = None

        settings = sublime.load_settings("CoqInteractive.sublime-settings")
        for k in ("coq_install_dir", "view_style", "move_cursor_after_command", "show_goals"):
            if self.view.settings().has("coq."+k):
                settings.set(k, self.view.settings()["coq."+k])

        if not worker:
            worker = spawn_worker(settings, self.view)

        pos = self.seek_pos(worker)
        if pos is not None:
            text = self.view.substr(sublime.Region(0, pos + 1))
            worker.seek(text=text, pos=pos)

            if settings.get("move_cursor_after_command", True):
                # In inline mode, move after the phantom block
                is_inline = isinstance(worker.display, DISPLAY_CLASSES_BY_NAME["inline"])
                if is_inline and self.view.substr(pos) == "\n":
                    pos += 1
                self.view.sel().clear()
                self.view.sel().add(sublime.Region(pos, pos))
                self.view.show(pos)

    def seek_pos(self, worker):
        return self.view.sel()[0].a

class CoqSeekStartCommand(CoqCommand):
    def seek_pos(self, worker):
        return 0

class CoqSeekEndCommand(CoqCommand):
    def seek_pos(self, worker):
        return self.view.size()

class CoqSeekNextCommand(CoqCommand):
    def seek_pos(self, worker):
        pos = worker.high_water_mark
        buffer = self.view.substr(sublime.Region(pos, self.view.size()))
        cmdpos = coq.find_first_coq_command(buffer)
        return cmdpos + pos if cmdpos is not None else None

class CoqSeekPrevCommand(CoqCommand):
    def seek_pos(self, worker):
        pos = worker.high_water_mark
        buffer = self.view.substr(sublime.Region(0, pos))
        return coq.find_last_coq_command(buffer)

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
        if self.view.substr(sublime.Region(0, self.view.size())) != text:
            self.view.set_read_only(False)
            self.view.erase(edit, sublime.Region(0, self.view.size()))
            self.view.insert(edit, 0, text)
            self.view.show(0)
            self.view.set_read_only(True)

# --------------------------------------------------------- Event Management

def handle_view_modification(view, modification_start_index):
    """Called when the user modifies the text in a view.

    This is a helper procedure for both CoqViewEventListener and
    CoqTextChangeListener.

    Parameters:
        - view (the modified view)
        - modification_start_index (a lower-bound on the set of text positions
          that were modified)
    """
    worker_key = view.id()
    worker = coq_threads.get(worker_key, None)
    if worker:
        # NOTE: While not immediately obvious, I think that reading the
        # `desired_high_water_mark` proprty is safe here, since only the
        # main thread changes that property via `seek`.
        worker_watermark = worker.desired_high_water_mark

        # NOTE: tricky off-by-one prevention here.  Normally we could use `<`
        # in this check since positions are indexed from 0.  However, positions
        # up to `worker_watermark+1` matter (see the Region selected below), so
        # we use `<=` to catch that +1.
        if modification_start_index <= worker_watermark:
            log.write("worker {} might be dirty [desired_high_water_mark={}, modification_start_index={}]".format(
                worker,
                worker_watermark,
                modification_start_index))
            text = view.substr(sublime.Region(0, worker_watermark + 1))
            worker.mark_dirty(text=text)
            worker.display.set_bad_ranges([])

def check_for_terminated_views():
    for worker_key, worker in list(coq_threads.items()):
        if worker.display.was_closed_by_user():
            log.write("worker {} was closed??".format(worker))
            stop_worker(worker_key, worker, "view closed by user")

# NOTE 2022/1/22: Sublime Text docs erroneously state that TextChangeListener
# lives in the `sublime` module [1]; in fact, it lives in `sublime_plugin`.
# [1]: https://www.sublimetext.com/docs/api_reference.html#sublime.TextChangeListener
HAVE_ON_TEXT_CHANGED_SUPPORT = hasattr(sublime_plugin, "TextChangeListener")

if HAVE_ON_TEXT_CHANGED_SUPPORT:

    class CoqTextChangeListener(sublime_plugin.TextChangeListener):

        def on_text_changed(self, changes):
            modification_start_index = min(change.a.pt for change in changes)
            for view in self.buffer.views():
                handle_view_modification(view, modification_start_index)

        @classmethod
        def is_applicable(cls, buffer):
            # While deeply unsatisfying, we have to listen to every change on
            # every buffer or risk missing some events.  See a description of
            # the issue here:
            #     https://github.com/Calvin-L/sublime-coq-plugin/issues/9
            # We should be able to fix this obvious performance penalty if the
            # Sublime Text devs have time to act on an issue I filed upstream:
            #     https://github.com/sublimehq/sublime_text/issues/6117
            # If we discover this really does incur a meaningful performance
            # penalty and the ST devs are unable (or unwilling) to fix the
            # upstream issue, then we will have to switch to manually
            # attach()-ing and detach()-ing instances of this listener as
            # workers are spawned and stopped.
            return True

class CoqViewEventListener(sublime_plugin.ViewEventListener):

    @classmethod
    def is_applicable(cls, settings):
        return settings.get("syntax", "").endswith("/Coq.tmLanguage")

    def on_clone(self):
        pass # TODO: what happens when coq response views are duplicated?

    def on_modified(self):
        if not HAVE_ON_TEXT_CHANGED_SUPPORT:
            # No information about what changed, so we have to be very
            # pessimistic.
            handle_view_modification(self.view, 0)

    def on_close(self):
        # NOTE 2021/11/29: There seems to be a bug in Sublime 4 (build 4121)
        # where some views have .window() == None even when they are not being
        # closed---but only during event callbacks like this one.  (Maybe
        # related: https://github.com/sublimehq/sublime_text/issues/4444 .)
        #
        # Approximate steps to reproduce:
        #   1. Use split Coq display
        #   2. Start the plugin
        #   3. Drag the response view to a different tab group
        #   4. Drag the response view back to its original tab group
        #   5. During this callback, the response view has window == None, even
        #      though it is not being closed (some anonymous view is being
        #      closed).
        #
        # The fix is easy enough: take this event callback as a "hint" that
        # some views have been closed.  At the next opportunity, check for
        # any views that have been closed.
        sublime.set_timeout(check_for_terminated_views, 1)

def plugin_unloaded():
    """Hook called by Sublime just before the plugin is unloaded.

    See: https://www.sublimetext.com/docs/3/api_reference.html#plugin_lifecycle

    This hook is mostly useful for development.  When the plugin is reloaded
    because the source code changed, it is helpful to have it cleanly shut down
    active Coq sessions.

    The docs are incredibly vague about what this hook is allowed to do and
    what it can rely on from Sublime.  I think we can trust that:
     - This hook is called on the main thread.
     - This hook can do the same things as a normal callback.

    But:
     - Sublime will not always wait for this hook to finish; we can only do a
       best-effort cleanup.
    """

    for worker_key, worker in list(coq_threads.items()):
        stop_worker(worker_key, worker, "plugin unloaded")
