"""
Sublime Text 3 plugin for Coq.
"""

# builtin modules
import collections
import os.path
import re
import subprocess
import threading
import time
import xml.etree.ElementTree as ET

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
# https://github.com/wuub/SublimeREPL/blob/master/sublimerepl.py

# --------------------------------------------------------- Constants
BULLET_CHARS = { '-', '+', '*', '{', '}' }

# --------------------------------------------------------- Helpers

def xml_encode(s):
    return (s
        .replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace("'", "&apos;")
        .replace('"', "&quot;"))

def count(seq):
    i = 0
    for x in seq:
        i += 1
    return i

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
    Returns (index, cmd) where
     - index is the index of the final char of the next complete Coq command in
       the given view after the given offset (start)
     - cmd is the command itself

    Returns (None, None) if there are no more commands or if parsing fails.
    """
    s = view.substr(sublime.Region(start, view.size()))
    idx = find_index(s, ".", coq_command_end_filter(view, start))
    if not idx:
        return (None, None)
    idx += start
    cmd = view.substr(sublime.Region(start, idx + 1))
    first_non_whitespace_match = re.search(r'\S', cmd)
    if first_non_whitespace_match:
        first_char_start = first_non_whitespace_match.start()
        char = first_non_whitespace_match.group()
        if char in BULLET_CHARS:
            idx = idx - len(cmd) + first_char_start + 1
            cmd = cmd[:first_non_whitespace_match.end()]
    return (idx, cmd)

def prev_command(view, end=0):
    """
    Returns the index of the final "." of the last complete Coq command in the
    given view that comes before the given end point. May return None if
    there are no such commands.
    """
    s = view.substr(sublime.Region(0, end))
    return find_index(s, ".", coq_command_end_filter(view), forward=False)

def split_commands(view, start, end):
    """
    Generates all complete coq commands in view between start and end. If it is
    not on a command boundary, then the first yielded command will be partial.
    """
    while start < end:
        idx, cmd = next_command(view, start)
        if idx < start:
            print("Warning: next_command returned idx < start")
            break
        if idx is None:
            break # normal termination condition
        print("==> {:5} {}".format(view.rowcol(idx), cmd))
        yield cmd
        start = idx + 1

def format_response(text, error=None):
    """
    Takes XML output from coqtop and makes it clean and pretty. Sample input:
    <value val="good"><option val="some"><goals><list><goal><string>14</string><list><string>n : nat</string></list><string>{rs : list record_name |
    forall r : record_name, In r rs &lt;-&gt; refers_to (EConst n) r}</string></goal><goal><string>15</string><list><string>r : record_name</string></list><string>{rs : list record_name |
    forall r0 : record_name, In r0 rs &lt;-&gt; refers_to (EVar r) r0}</string></goal><goal><string>20</string><list><string>e1 : expr</string><string>e2 : expr</string><string>IHe1 : {rs : list record_name |
    forall r : record_name, In r rs &lt;-&gt; refers_to e1 r}</string><string>IHe2 : {rs : list record_name |
    forall r : record_name, In r rs &lt;-&gt; refers_to e2 r}</string></list><string>{rs : list record_name |
    forall r : record_name, In r rs &lt;-&gt; refers_to (EPlus e1 e2) r}</string></goal></list><list/></goals></option></value>

    Error parameter is an optional string describing any error that took place.
    """
    root = ET.fromstring(text)
    if not root:
        return "Parse failed: {}".format(text)
    if root.attrib.get("val") != "good":
        return "Error: {}".format(text)
    goals = list(root.iter("goal"))
    output = "Goals: {}\n\n".format(len(goals))
    if goals:
        primary_goal = goals[0]
        strs = list(primary_goal.iter("string"))[1:]
        hyps = strs[:-1]
        goal = strs[-1]
        for h in hyps:
            output += "  {}\n".format(h.text)
        output += "  " + ("-" * 40) + "\n"
        output += "  {}\n".format(goal.text)
    if error:
        output += "\nError: {}".format(error)
    return output

# --------------------------------------------------------- Coqtop Interaction

class CoqtopProc(object):
    def __init__(self, working_dir=None):
        """
        Spawns a new coqtop process and creates pipes for interaction.
        """
        self.proc = subprocess.Popen(
            ["/usr/local/bin/coqtop", "-ideslave"],
            cwd=working_dir,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE)

    def send(self, text):
        """
        Send the given text to coqtop and wait for a full response. Returns
        the response text.
        """

        # Send
        self.proc.stdin.write(text.encode('ascii'))
        self.proc.stdin.flush()

        # Recieve until we find </value>
        s = ""
        while "</value>" not in s:
            response = self.proc.stdout.read(1024).decode('ascii')
            print("got partial response: {}".format(response))
            s += response
        return s


    def stop(self):
        """
        Stop the underlying coqtop process.
        """
        self.proc.terminate()
        self.proc = None

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
        self.coq_eval_point = 0
        working_dir = None
        f = self.view.file_name()
        if f is not None:
            working_dir = os.path.dirname(f)
        self.coqtop = CoqtopProc(working_dir=working_dir)
        self.response_view = self.view.window().new_file()
        self._on_start()

    def _on_start(self):
        self.response_view.set_syntax_file("Packages/sublime-coq/Coq.tmLanguage")
        self.response_view.set_scratch(True)
        self.response_view.set_read_only(True)
        name = self.view.name() or os.path.basename(self.view.file_name() or "")
        title = "*** Coq for {} ***".format(name) if name else "*** Coq ***"
        self.response_view.set_name(title)

        window = self.view.window()
        ngroups = window.num_groups()
        if ngroups == 1:
            window.run_command("new_pane")
        else:
            group = window.num_groups() - 1
            if window.get_view_index(self.view)[1] == group:
                group -= 1
            window.set_view_index(self.response_view, group, 0)
        window.focus_view(self.view)

    def _on_stop(self):
        self.coqtop.stop()
        self.view.erase_regions("Coq")
        self.view.erase_regions("CoqTODO")

    def send_req(self, req):
        self.request = req
        if not self.lock.acquire(blocking=False):
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
                self._on_stop()
                return
            elif isinstance(req, EvalMessage):
                self.do_coq_thing(req.pos)
            else:
                print("unknown message: {}".format(req))

    def do_coq_thing(self, idx):
        """
        Set coq evaluation to idx in the given buffer.
        """
        if not self.response_view.window():
            print("worker {} has no more response buffer; stopping")
            self._on_stop()
            return

        idx = prev_command(self.view, idx)
        if idx is None:
            print("no more commands in file?")
            return

        idx += 1

        if idx == self.coq_eval_point:
            print("no need to go anywhere")
            return

        todo_scope_name = "meta.coq.todo"
        todo_flags = 0 # sublime.DRAW_NO_FILL | sublime.DRAW_NO_OUTLINE | sublime.DRAW_SOLID_UNDERLINE
        done_scope_name = "meta.coq.proven"
        done_flags = 0

        self.view.add_regions("CoqTODO", [sublime.Region(self.coq_eval_point, idx)], scope=todo_scope_name, flags=todo_flags)
        self.response_view.run_command("coq_update_output_buffer", {"text": "Working..."})

        cmds = []

        if idx > self.coq_eval_point:
            i = self.coq_eval_point
            for cmd in split_commands(self.view, self.coq_eval_point, idx):
                to_send = '<call val="interp" id="0">{}</call>'.format(xml_encode(cmd.strip()))
                i += len(cmd)
                cmds.append((to_send, i))
        else:
            steps_back = count(split_commands(self.view, idx, self.coq_eval_point))
            to_send = '<call val="rewind" steps="{}"></call>'.format(steps_back)
            cmds.append((to_send, idx))

        error = None

        for cmd, end_idx in cmds:
            print("sending: {}".format(cmd))
            response = self.coqtop.send(cmd)
            print("got full response: {}".format(response))
            parsed = ET.fromstring(response)
            if parsed is None or parsed.attrib.get("val") != "good":
                print("Error!")
                error = parsed.text
                idx = end_idx + 1
                break
            self.view.add_regions("Coq", [sublime.Region(0, end_idx)], scope=done_scope_name, flags=done_flags)

        print("asking for goal")
        response = self.coqtop.send('<call val="goal"></call>')
        response = format_response(response, error)
        self.response_view.run_command("coq_update_output_buffer", {"text": response})
        self.view.window().focus_view(self.view)
        self.view.erase_regions("CoqTODO")
        self.coq_eval_point = idx

# --------------------------------------------------------- Sublime Commands

class CoqCommand(sublime_plugin.TextCommand):
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

            # clean up the response view if it still exists
            response_view = worker.response_view
            window = response_view.window()
            if window is not None:
                window.focus_view(response_view)
                window.run_command("close")

        else:
            print("no worker to kill")
            self.view.erase_regions("Coq")
            self.view.erase_regions("CoqTODO")

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
            # UGH
            pass

    def on_close(self, view):
        for view_id, worker in coq_threads.items():
            if worker.response_view.id() == view.id():
                worker.view.run_command("coq_kill")
