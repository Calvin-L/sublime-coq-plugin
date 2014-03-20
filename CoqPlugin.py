"""
Sublime Text 3 plugin for Coq.
"""

# builtin modules
import collections
import threading
import time

# sublime
import sublime
import sublime_plugin

# relevant
# https://sympa.inria.fr/sympa/arc/coqdev/2013-11/msg00084.html
# https://github.com/the-lambda-church/coquille
# https://github.com/the-lambda-church/coquille/issues/18
# http://www.vim.org/scripts/script.php?script_id=4388
# http://code.tutsplus.com/tutorials/how-to-create-a-sublime-text-2-plugin--net-22685
# http://www.sublimetext.com/docs/3/api_reference.html

# --------------------------------------------------------- Parsing

def find_index(haystack, needle, predicate, forward=True):
    def f(limit):
        start, end = (limit, len(haystack)) if forward else (0, limit)
        return (haystack.find(needle, start, end)
                if forward else haystack.rfind(needle, start, end))

    idx = f(0 if forward else len(haystack))
    while idx >= 0 and not predicate(idx):
        idx = f(idx + (1 if forward else 0))
    return idx if idx >= 0 else None

def coq_command_end_filter(view, start=0):
    def filt(i):
        scope_name = view.scope_name(i + start)
        return "coq" in scope_name and not ("comment" in scope_name or "string" in scope_name)
    return filt

def next_command(view, start=0):
    """
    Returns the index of the final "." of the next complete Coq command in the
    given view after the given offset (start). May return None if there are no
    more commands.
    """
    s = view.substr(sublime.Region(start, view.size()))
    idx = find_index(s, ".", coq_command_end_filter(view, start))
    return idx + start if idx is not None else None

def prev_command(view, end=0):
    """
    Returns the index of the final "." of the last complete Coq command in the
    given view that comes before the given end point. May return None if
    there are no such commands.
    """
    s = view.substr(sublime.Region(0, end))
    return find_index(s, ".", coq_command_end_filter(view), forward=False)

# --------------------------------------------------------- Coqtop Interaction

class CoqtopProc(object):
    def __init__(self):
        """
        Spawns a new coqtop process and creates pipes for interaction.
        """
        pass

    def send(self, text):
        """
        Send the given text to coqtop and wait for a full response. Returns
        the response text.
        """
        pass

    def stop(self):
        """
        Stop the underlying coqtop process.
        """
        pass

# --------------------------------------------------------- Coq Worker

# maps view IDs to worker threads
coq_threads = dict()

# messages
StopMessage = object()
EvalMessage = collections.namedtuple("EvalMessage", ["pos"])

class CoqWorker(threading.Thread):

    def __init__(self, view):
        super().__init__(daemon=True)
        self.lock = threading.Lock()
        self.lock.acquire()
        self.request = None
        self.view = view

    def send_req(self, req):
        self.request = req
        self.lock.release()

    def get_req(self):
        self.lock.acquire()
        return self.request

    def run(self):
        while True:
            req = self.get_req()
            print("worker {} got message: {}".format(self, req))
            if req is StopMessage:
                print("worker {} got stop message".format(self))
                self.view.erase_regions("Coq")
                self.view.erase_regions("CoqTODO")
                return
            elif isinstance(req, EvalMessage):
                self.do_coq_thing(req.pos)
            else:
                print("unknown message: {}".format(req))

    def do_coq_thing(self, idx):
        """
        Set coq evaluation to idx in the given buffer.
        """
        idx = prev_command(self.view, idx)
        if idx:
            scope_name = "comment"
            todo_flags = sublime.DRAW_NO_FILL | sublime.DRAW_NO_OUTLINE | sublime.DRAW_SOLID_UNDERLINE
            done_flags = 0
            self.view.add_regions("CoqTODO", [sublime.Region(0, idx + 1)], scope=scope_name, flags=todo_flags)
            time.sleep(1)
            self.view.add_regions("Coq", [sublime.Region(0, idx + 1)], scope=scope_name, flags=done_flags)
            self.view.erase_regions("CoqTODO")
        else:
            print("ugh")

# --------------------------------------------------------- Sublime Commands

class CoqCommand(sublime_plugin.TextCommand):

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    def run(self, edit):
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
        worker.send_req(EvalMessage(pos=self.view.sel()[0].a))

class CoqKillCommand(sublime_plugin.TextCommand):
    def run(self, edit):
        worker_key = self.view.id()
        worker = coq_threads.get(worker_key, None)
        if worker:
            worker.send_req(StopMessage)
            worker.join(1)
            if not worker.is_alive():
                del coq_threads[worker_key]
                print("killed {}".format(worker))
            else:
                print("worker didn't die!")
        else:
            print("no worker to kill")
