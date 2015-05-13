"""
Sublime Text 3 plugin for Coq.
"""

# builtin modules
import collections
import os.path
import re
import string
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

COQTOP_CMD = "/usr/local/bin/coqtop.opt"
BULLET_CHARS = { "-", "+", "*", "{", "}" }
LTAC_START_COMMANDS = { "Definition", "Lemma", "Theorem" }
LTAC_END_COMMANDS = { "Admitted", "Qed", "Defined" }
PUNCTUATION_REGEX = re.compile(r"[{}]".format(re.escape(string.punctuation)))
REWIND_CMD = '<call val="rewind" steps="1"></call>' # multiple steps only works for ltac, so we just do one each time to be safe

# --------------------------------------------------------- Helpers

def xml_encode(s):
    return (s
        .replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace("'", "&apos;")
        .replace('"', "&quot;"))

def count(seq):
    return sum(1 for _ in seq)

def find_index(haystack, needle, predicate, forward=True):
    """
    Find the index of needle in haystack where predicate(index) is true.
    If forward=True, it searches forward from the beginning, otherwise it
    searches backward from the end.
    """
    def f(limit):
        start, end = (limit, len(haystack)) if forward else (0, limit)
        return (haystack.find(needle, start, end)
                if forward else haystack.rfind(needle, start, end))
    idx = f(0 if forward else len(haystack))
    while idx >= 0 and not predicate(idx):
        idx = f(idx + (1 if forward else 0))
    return idx if idx >= 0 else None

# --------------------------------------------------------- Parsing

# Various commands. We need to differentiate these because when you finish a
# block of Ltac (e.g. Qed) the whole block of Ltac becomes ONE command. That
# is, while in Ltac mode, "Undo" undoes one Ltac statement, but outside of Ltac
# mode, "Undo" undoes entire proofs.
COMMAND_FIELDS = ["start", "end", "text"]

# start of Ltac, e.g. Definition [...]. or Theorem [...].
LtacStartCommand = collections.namedtuple("LtacStartCommand", COMMAND_FIELDS)

# end of Ltac, e.g. Admitted, Qed, Defined.
LtacEndCommand = collections.namedtuple("LtacEndCommand", COMMAND_FIELDS)

# everything else: vernacular, ltac, etc.
NormalCommand = collections.namedtuple("NormalCommand", COMMAND_FIELDS)

def coq_command_end_filter(view, start=0):
    def filt(i):
        scope_name = view.scope_name(i + start)
        return "coq" in scope_name and not ("comment" in scope_name or "string" in scope_name)
    return filt

def prev_command(view, end=0):
    """
    Returns the index of the final "." of the last complete Coq command in the
    given view that comes before the given end point. May return None if
    there are no such commands. Note that this is not a perfect mirror of
    next_command; it is only used to find command boundaries and I'm pretty
    sure we only have to worry about command boundaries at fullstops.
    """
    s = view.substr(sublime.Region(0, end))
    return find_index(s, ".", coq_command_end_filter(view), forward=False)

def parse_command(index, text):
    """
    Given some text and a start index, returns one of NormalCommand,
    LtacStartCommand, or LtacEndCommand.
    """
    token = text.split()[0] # first word of the command
    token = PUNCTUATION_REGEX.sub("", token) # remove punctuation
    ty = NormalCommand
    if token in LTAC_START_COMMANDS and ":=" not in text:
        ty = LtacStartCommand
    elif token in LTAC_END_COMMANDS:
        ty = LtacEndCommand
    return ty(text=text, start=index, end=index+len(text))

def next_command_text(view, start=0):
    """
    Returns (index, cmd) where
     - index is the index of the final char of the next complete Coq command in
       the given view after the given offset (start)
     - cmd is the command itself
     - index + len(cmd) gives the ending index of the command

    Returns (None, None) if there are no more commands or if parsing fails.
    """
    s = view.substr(sublime.Region(start, view.size()))
    idx = find_index(s, ".", coq_command_end_filter(view, start))
    if not idx:
        return (None, None)
    idx += start
    cmd = view.substr(sublime.Region(start, idx + 1))

    # Bullet characters in Ltac require some care; each is its own command
    first_non_whitespace_match = re.search(r'\S', cmd)
    if first_non_whitespace_match:
        first_char_start = first_non_whitespace_match.start()
        char = first_non_whitespace_match.group()
        if char in BULLET_CHARS:
            idx = idx - len(cmd) + first_char_start + 1
            cmd = cmd[:first_non_whitespace_match.end()]
    return (idx, cmd)

def next_command(view, start=0):
    """
    Returns one of NormalCommand, LtacStartCommand, or LtacEndCommand
    according to the contract of next_command_text. May return None if there
    are no more commands.
    """
    idx, cmd = next_command_text(view, start)
    if idx is None or cmd is None:
        return None
    return parse_command(idx - len(cmd) + 1, cmd)

def split_commands(view, start, end):
    """
    Generates all complete coq commands in view between start and end. If it is
    not on a command boundary, then the first yielded command will be partial.
    """
    while start < end:
        cmd = next_command(view, start)
        if cmd is None:
            # normal termination condition: no more commands in file
            break
        if cmd.start < start:
            # super safety code to prevent infinite loops
            print("Insanity: next_command starts before start!?")
            break
        print("==> {}-{} {:5} {} [len={}]".format(cmd.start, cmd.end, view.rowcol(cmd.start), cmd.text.strip(), len(cmd.text)))
        yield cmd
        start = cmd.end + 1

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
        output += "\n{}".format(error.strip())
    return output

# --------------------------------------------------------- Coqtop Interaction

class CoqtopProc(object):

    def __init__(self, working_dir=None):
        """
        Spawns a new coqtop process and creates pipes for interaction.
        """
        print("Starting {} in {}".format(COQTOP_CMD, working_dir))
        self.proc = subprocess.Popen(
            [COQTOP_CMD, "-ideslave"],
            bufsize=0,
            cwd=working_dir,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE)

    def send(self, text):
        """
        Send the given text to coqtop and wait for a full response. Returns
        the response text.
        """

        if text[-1] != "\n":
            text += "\n"
        print("sending: {}".format(text.encode("unicode-escape")))

        # Send
        self.proc.stdin.write(text.encode('ascii'))
        self.proc.stdin.flush()

        # Recieve until we find </value>
        s = ""
        while "</value>" not in s:
            response = self.proc.stdout.read(1024).decode('ascii')
            print("got partial response: {}".format(response))
            if not response:
                break
            s += response

        print("got full response: {}".format(s))
        return s

    def stop(self):
        """
        Stop the underlying coqtop process.
        """
        self.proc.terminate()
        self.proc = None

# --------------------------------------------------------- Undo Stack

class UndoStack(object):
    """
    Keeps a record of commands we sent to coqtop. This helps us do two things:
     1. We can properly collapse definitions into a single "Undo-able" op
     2. We can stay in sync with coqtop when the user has modified the file
        in unexpected ways.
    """

    def __init__(self):
        self.stack = []

    def most_recent(self, ty):
        """
        Returns index in self.stack of the most recent command of the given
        type. May return None if no such command exists.
        """
        i = 1
        for cmd in self.stack.__reversed__():
            if isinstance(cmd, ty):
                return len(self.stack) - i
            i += 1
        return None

    def push(self, cmd):
        if isinstance(cmd, LtacEndCommand):
            # search backwards for the LtacStartCommand
            idx = self.most_recent(LtacStartCommand)
            if idx:
                # collapse this ltac stuff and change it to a single vernac command
                start_cmd = self.stack[idx]
                cmd = NormalCommand(
                    start=start_cmd.start,
                    end=cmd.end,
                    text=''.join(x.text for x in self.stack[idx:]) + cmd.text)
                print("Collapsed {} commands into one: {}".format(len(self.stack) - idx + 1, cmd.text))
                self.stack = self.stack[:idx]
            else:
                print("Insanity: got an Ltac end command with no start!?")
        self.stack.append(cmd)

    def rewind_to(self, index):
        """
        Returns the commands that come after index. The length of the returned
        list indicates how many undos must be performed to rewind to the given
        index. The "start" location of the first command in the list indicates
        the new high-water mark for what has been proven so far.

        The returned commands are removed from this UndoStack.
        """
        to_undo = []
        for cmd in self.stack.__reversed__():
            if cmd.end > index:
                to_undo.append(cmd)
            else:
                break
        self.stack = self.stack[:(len(self.stack) - len(to_undo))]
        to_undo.reverse()
        return to_undo

# --------------------------------------------------------- Coq Worker

# maps view IDs to worker threads
coq_threads = dict()

# messages
StopMessage = object()
EvalMessage = collections.namedtuple("EvalMessage", ["pos"])
CheckForModificationMessage = object()

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
        self.undo_stack = UndoStack()
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
            elif req is CheckForModificationMessage:
                print("worker {} is checking for modifications...")
                self.check_for_modifications()
            else:
                print("unknown message: {}".format(req))

    def check_for_modifications(self):
        """
        Called when the user altered the underlying buffer. We might need to
        rewind if they changed something in the proven region.
        """
        comparison = UndoStack()
        cmds = split_commands(self.view, 0, self.coq_eval_point)
        for cmd in cmds:
            comparison.push(cmd)
        for expected, actual in zip(self.undo_stack.stack, comparison.stack):
            if expected.text.strip() != actual.text.strip():
                self.do_coq_thing(expected.start)
                return

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

        forward = idx > self.coq_eval_point
        if forward:
            for cmd in split_commands(self.view, self.coq_eval_point, idx):
                to_send = '<call val="interp" id="0">{}</call>'.format(xml_encode(cmd.text.strip()))
                cmds.append((to_send, cmd))
        else:
            cmds_to_undo = self.undo_stack.rewind_to(idx)
            print("Undoing {} things...".format(len(cmds_to_undo)))
            for cmd in cmds_to_undo:
                print("Undoing {}".format(cmd.text.strip()))
                cmds.append((REWIND_CMD, None))
            if cmds_to_undo:
                idx = cmds_to_undo[0].start
                self.view.erase_regions("Coq")
                self.view.add_regions("Coq", [sublime.Region(0, idx)], scope=done_scope_name, flags=done_flags)

        error = None

        for coq_cmd, cmd in cmds:
            response = self.coqtop.send(coq_cmd)
            parsed = ET.fromstring(response)
            if parsed is None or parsed.attrib.get("val") != "good":
                print("Error!")
                error = parsed.text
                if cmd:
                    idx = cmd.start
                break
            if forward:
                self.undo_stack.push(cmd)
                self.view.add_regions("Coq", [sublime.Region(0, cmd.end)], scope=done_scope_name, flags=done_flags)

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
            worker.send_req(CheckForModificationMessage)

    def on_close(self, view):
        for view_id, worker in list(coq_threads.items()):
            if worker.response_view.id() == view.id():
                worker.view.run_command("coq_kill")
