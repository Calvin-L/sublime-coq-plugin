"""
Sublime Text 3 plugin for Coq.
"""

# builtin modules
import collections
import os.path
import queue
import re
import shlex
import string
import subprocess
import threading
import time
import xml.etree.ElementTree as ET

# sublime
import sublime
import sublime_plugin

# local modules
from . import util
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

# --------------------------------------------------------- Constants

# COQ_MAJOR_VERSION = (8,5)
COQ_MAJOR_VERSION = (8,9)
COQTOP_PATH = "/usr/local/bin/"

TODO_SCOPE_NAME = "meta.coq.todo"
TODO_FLAGS = 0 # sublime.DRAW_NO_FILL | sublime.DRAW_NO_OUTLINE | sublime.DRAW_SOLID_UNDERLINE
DONE_SCOPE_NAME = "meta.coq.proven"
DONE_FLAGS = 0 # sublime.DRAW_SQUIGGLY_UNDERLINE | sublime.DRAW_NO_FILL | sublime.DRAW_NO_OUTLINE

# --------------------------------------------------------- Feedback Display

class CoqDisplay(object):
    def __init__(self, view):
        self.view = view
    def set_marks(self, high_water_mark, todo_mark):
        raise NotImplementedError()
    def show_goal(self, goal):
        raise NotImplementedError()
    def was_closed_by_user(self):
        raise NotImplementedError()
    def close(self):
        raise NotImplementedError()

class SplitPaneDisplay(CoqDisplay):
    def __init__(self, view):
        super().__init__(view)
        self.response_view = view.window().new_file()
        self.response_view.set_syntax_file("Packages/sublime-coq/Coq.tmLanguage")
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

    def set_marks(self, high_water_mark, todo_mark):
        self.view.add_regions("Coq", [sublime.Region(0, high_water_mark)], scope=DONE_SCOPE_NAME, flags=DONE_FLAGS)
        if todo_mark > high_water_mark:
            self.view.add_regions("CoqTODO", [sublime.Region(high_water_mark, todo_mark)], scope=TODO_SCOPE_NAME, flags=TODO_FLAGS)
        else:
            self.view.erase_regions("CoqTODO")

    def show_goal(self, goal):
        self.response_view.run_command("coq_update_output_buffer", {"text": goal})

    def was_closed_by_user(self):
        return self.view.window() is None or self.response_view.window() is None

    def close(self):
        sublime.set_timeout(self._cleanup, 0)

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

class InlinePhantomDisplay(CoqDisplay):
    def __init__(self, view):
        super().__init__(view)
        self.phantoms = sublime.PhantomSet(view, "CoqPhantoms")
        self.region = sublime.Region(0, 0)

    def set_marks(self, high_water_mark, todo_mark):
        self.region = region = sublime.Region(0, high_water_mark)
        self.view.add_regions("Coq", [region], scope=DONE_SCOPE_NAME, flags=DONE_FLAGS)
        if todo_mark > high_water_mark:
            self.view.add_regions("CoqTODO", [sublime.Region(high_water_mark, todo_mark)], scope=TODO_SCOPE_NAME, flags=TODO_FLAGS)
        else:
            self.view.erase_regions("CoqTODO")

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

    def show_goal(self, goal):
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

    def was_closed_by_user(self):
        return self.view.window() is None

    def close(self):
        sublime.set_timeout(self._cleanup, 0)

    def _cleanup(self):
        self.view.erase_regions("Coq")
        self.view.erase_regions("CoqTODO")
        self.phantoms.update([])

# --------------------------------------------------------- Coq Worker

# maps view IDs to worker threads
coq_threads = dict()

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
      - seek(pos) --> start evaluating or change evaluation target
      - mark_dirty() --> seek backwards if changes have been made in the proven region
      - stop()    --> enter the STOPPING state to shut down Coq

    The worker updates the Sublime Text view as it changes state and as Coq
    sends responses.
    """

    def __init__(self, view):
        super().__init__(daemon=True)
        self.view = view
        self.display = InlinePhantomDisplay(view)

        working_dir = None
        f = view.file_name()
        if f is not None:
            working_dir = os.path.dirname(f)

        coqtop_path = COQTOP_PATH
        while coqtop_path.endswith("/"):
            coqtop_path = coqtop_path[:-1]
        while coqtop_path.endswith("bin"):
            coqtop_path = coqtop_path[:-3]
        while coqtop_path.endswith("/"):
            coqtop_path = coqtop_path[:-1]

        self.coq = coq.CoqBot(
            coq_install_dir=coqtop_path,
            coq_version=COQ_MAJOR_VERSION,
            working_dir=working_dir)

        self.state = "ALIVE"
        self.dirty = False
        self.desired_high_water_mark = 0
        self.high_water_mark = 0
        self.monitor = threading.Condition()

    def run(self):
        while True:
            do_step = None
            with self.monitor:
                print("Worker state is: {} ({} --> {})".format(self.state, self.high_water_mark, self.desired_high_water_mark))
                if self.state == "ALIVE":
                    if self.dirty:
                        self.check_for_modifications()
                    elif self.desired_high_water_mark != self.high_water_mark:
                        do_step = (self.high_water_mark, self.desired_high_water_mark)
                    else:
                        self.monitor.wait()
                elif self.state == "STOPPING":
                    self.coq.stop()
                    self.display.close()
                    self.state = "DEAD"
                else:
                    return

            if do_step:
                try:
                    self.step(*do_step)
                except Exception as e:
                    print("uncaught exception: {}".format(e))
                    self.stop()

    def seek(self, pos):
        with self.monitor:
            if self.state == "ALIVE":
                self.desired_high_water_mark = pos
                self.display.show_goal("Working...")
                self.display.set_marks(min(pos, self.high_water_mark), pos)
                self.monitor.notify_all()

    def stop(self):
        with self.monitor:
            if self.state == "ALIVE":
                self.state = "STOPPING"
                self.display.show_goal("Stopping...")
                self.monitor.notify_all()

    def mark_dirty(self, dirty=True):
        with self.monitor:
            self.dirty = dirty
            self.monitor.notify_all()

    def is_alive(self):
        return self.state != "DEAD"

    def check_for_modifications(self):
        """
        Called when the user altered the underlying buffer. We might need to
        rewind if they changed something in the proven region.
        """
        index = 0
        self.mark_dirty(False)
        buffer = self.view.substr(sublime.Region(0, self.high_water_mark))
        for cmd in self.coq.sent_buffer():
            new_index = coq.find_first_coq_command(buffer, start=index)
            if new_index is None or cmd != buffer[index:new_index]:
                self.seek(index)
                return
            index = new_index

    def step(self, from_idx, to_idx):
        if self.display.was_closed_by_user():
            print("worker {}'s display was closed; stopping")
            self.stop()
            return

        view = self.view

        print("step called: {} --> {}".format(from_idx, to_idx))

        if from_idx < to_idx:
            text = view.substr(sublime.Region(from_idx, to_idx))
            print("unsent: {!r}".format(text))
            try:
                cmd_len = self.coq.append(text)
            except Exception as e:
                self.display.show_goal("Error: {}".format(e))
                self.desired_high_water_mark = from_idx
                return

            if cmd_len == 0:
                self.desired_high_water_mark = from_idx
            else:
                self.high_water_mark += cmd_len

        else:

            try:
                self.high_water_mark = self.desired_high_water_mark = self.coq.rewind_to(to_idx)
            except coq.CoqException as e:
                # The exception will be caught and displayed when we try to
                # show the current goal later.
                pass

        try:
            goal = self.coq.current_goal()
        except coq.CoqException as e:
            goal = "Error: {}".format(str(e))
            self.desired_high_water_mark = self.high_water_mark

        self.display.set_marks(self.high_water_mark, self.desired_high_water_mark)
        self.display.show_goal(goal)

# --------------------------------------------------------- Sublime Commands

class CoqCommand(sublime_plugin.TextCommand):
    def run(self, edit):
        print(self.view.style_for_scope(DONE_SCOPE_NAME))
        # return

        if "coq" not in self.view.scope_name(0):
            print("not inside a coq buffer")
            return
        worker_key = self.view.id()
        worker = coq_threads.get(worker_key, None)
        if not worker:
            worker = CoqWorker(self.view)
            coq_threads[worker_key] = worker
            worker.start()
            print("spawned worker {} for view {}".format(worker, worker_key))
        worker.seek(pos=self.view.sel()[0].a)

class CoqKillCommand(sublime_plugin.TextCommand):
    def run(self, edit):
        worker_key = self.view.id()
        worker = coq_threads.get(worker_key, None)
        if worker:
            print("stopping {}...".format(worker))
            worker.stop()
            worker.join(1)
            if not worker.is_alive():
                del coq_threads[worker_key]
                print("killed {}".format(worker))
            else:
                print("worker didn't die!")
        else:
            print("no worker to kill")

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
            worker.mark_dirty()

    def on_close(self, view):
        for view_id, worker in list(coq_threads.items()):
            if worker.display.was_closed_by_user():
                print("worker {} was closed??".format(worker))
                worker.view.run_command("coq_kill")
