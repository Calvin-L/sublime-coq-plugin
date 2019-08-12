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
# COQTOP_CMD = [
#     "/Users/loncaric/sources/epics/neutrons/coq/build/bin/coqtop",
#     "-main-channel", "stdfds", "-ideslave",
#     ]
COQ_MAJOR_VERSION = (8,7)
COQTOP_PATH = "/usr/local/bin/"
COQTOP_CMD = [COQTOP_PATH + "coqtop.opt", "-ideslave"]
if COQ_MAJOR_VERSION >= (8,5):
    COQTOP_CMD = [
        # "/Users/loncaric/sources/epics/neutrons/coq/build/bin/coqtop",
        COQTOP_PATH + "coqtop.opt",
        "-main-channel", "stdfds", "-ideslave",
        # "-R", "/Users/loncaric/sources/epics/neutrons/python", "",
        # "-R", "/Users/loncaric/sources/vhttp/src", "",
        # "-R", "/Users/loncaric/sources/epics/neutrons/semantics", "",
        # "-R", "/Users/loncaric/sources/epics/neutrons/python/flocq-2.5.1/src", "Flocq",
        ]
if COQ_MAJOR_VERSION >= (8,9):
    COQTOP_CMD = [
        COQTOP_PATH + "coqidetop.opt",
        "-main-channel", "stdfds"]
BULLET_CHARS = { "-", "+", "*", "{", "}" }
LTAC_START_COMMANDS = { "Definition", "Lemma", "Theorem" }
LTAC_END_COMMANDS = { "Admitted", "Qed", "Defined" }
PUNCTUATION_REGEX = re.compile(r"[{}]".format(re.escape(string.punctuation)))
REWIND_CMD = '<call val="rewind" steps="1"></call>' # multiple steps only works for ltac, so we just do one each time to be safe
TODO_SCOPE_NAME = "meta.coq.todo"
TODO_FLAGS = 0 # sublime.DRAW_NO_FILL | sublime.DRAW_NO_OUTLINE | sublime.DRAW_SOLID_UNDERLINE
DONE_SCOPE_NAME = "meta.coq.proven"
DONE_FLAGS = 0 # sublime.DRAW_SQUIGGLY_UNDERLINE | sublime.DRAW_NO_FILL | sublime.DRAW_NO_OUTLINE
RICHPP = (COQ_MAJOR_VERSION >= (8,6)) # newer versions of Coq (8.6+?) need this

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

def coq_command_end_filter(s, view, start=0):
    def filt(i):
        scope_name = view.scope_name(i + start)
        return (
            "coq" in scope_name
            and not ("comment" in scope_name or "string" in scope_name)
            and (i + 1 >= len(s) or s[i + 1] in string.whitespace))
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
    return find_index(s, ".", coq_command_end_filter(s, view), forward=False)

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
    idx = find_index(s, ".", coq_command_end_filter(s, view, start))
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

# def parse_coqtop_xml(text):
#     text = """<?xml version="1.1" ?>
#         <!DOCTYPE naughtyxml [
#             <!ENTITY nbsp "&#0160;">
#             <!ENTITY copy "&#0169;">
#         ]>
#         <root>""" + text + "</root>"
#     return ET.fromstring(text)

def text_of(xml):
    return "".join(xml.itertext())

def format_response(xml, error=None):
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

    for x in xml:
        if x.tag == "value":
            if x.attrib.get("val") != "good":
                return "Error: {}".format(text_of(x))
            goals = list(x.iter("goal"))
            output = "Goals: {}\n\n".format(len(goals))
            if goals:
                # from xml import etree
                # print("\n".join(ET.tostring(g).decode("UTF-8") for g in goals))
                primary_goal = goals[0]
                if RICHPP:
                    strs = list(primary_goal.iter("richpp"))
                else:
                    strs = list(primary_goal.iter("string"))[1:]
                hyps = strs[:-1]
                goal = strs[-1]
                for h in hyps:
                    output += "  {}\n".format(text_of(h))
                output += "  " + ("-" * 40) + "\n"
                output += "  {}\n".format(text_of(goal))
            if error:
                output += "\n{}".format(error.strip())
            return output
        else:
            print("got tag '{}'".format(x))

# --------------------------------------------------------- Coqtop Process

class CoqtopProc(object):

    def __init__(self, working_dir=None):
        """
        Spawns a new coqtop process and creates pipes for interaction.
        """

        cmd = list(COQTOP_CMD)

        if working_dir is not None:
            project_file = self.find_coqproject_file(working_dir)
            if project_file is not None:
                working_dir = os.path.dirname(project_file)
                with open(project_file, "r") as f:
                    cmd.extend(shlex.split(f.read()))

        print("Starting `{}` in {}".format(" ".join(cmd), working_dir))
        self.proc = subprocess.Popen(
            cmd,
            bufsize=0,
            cwd=working_dir,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE)

    def find_coqproject_file(self, dir):
        if dir.endswith("/"):
            dir = dir[:-1]
        if not dir:
            return None
        project_file = os.path.join(dir, "_CoqProject")
        if os.path.isfile(project_file):
            return project_file
        if dir != "/":
            return self.find_coqproject_file(os.path.dirname(dir))
        return None

    def send(self, text):
        """
        Send the given text to coqtop. Yields XML tags found in the response.
        For proper operation, clients must always exhaust this generator.
        """

        if text[-1] != "\n":
            text += "\n"
        print("sending: {}".format(text.encode("unicode-escape")))

        # Send
        self.proc.stdin.write(text.encode('ascii'))
        self.proc.stdin.flush()
        # print("sent")

        # Recieve until we find <value>...</value>
        xm = util.XMLMuncher()
        done = False
        while not done:
            buf = self.proc.stdout.read(1024)
            try:
                response = buf.decode('ascii')
            except UnicodeDecodeError as e:
                print("{}".format(list("{:x}".format(b) for b in buf)))
                raise e
            # print("got partial response: {}".format(response))
            if not response:
                raise Exception("coqtop died!")
            for tag in xm.process(response):
                xml = ET.fromstring(tag)
                yield xml
                if xml.tag == "value":
                    done = True
                    # print("--- DONE ---")

    def stop(self):
        """
        Stop the underlying coqtop process.
        """
        self.proc.terminate()
        ret = self.proc.wait()
        print("coqtop exited with status {}".format(ret))
        self.proc = None

# --------------------------------------------------------- Undo Stack

class UndoStack(object):
    """
    Keeps a record of commands we sent to coqtop. This helps us do two things:
     1. We can properly collapse definitions into a single "Undo-able" op
     2. We can stay in sync with coqtop when the user has modified the file
        in unexpected ways.
    """

    def __init__(self, init_state_id=1):
        self.stack = []
        self.state_ids = []
        self.init_state_id = init_state_id

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

    def push(self, cmd, state_id=None):
        if isinstance(cmd, LtacEndCommand) and COQ_MAJOR_VERSION < (8,5):
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
        if state_id is not None:
            self.state_ids.append(state_id)

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
        new_end_idx = len(self.stack) - len(to_undo)
        self.stack = self.stack[:new_end_idx]
        self.state_ids = self.state_ids[:new_end_idx]
        to_undo.reverse()
        return (to_undo, self.state_ids[-1] if self.state_ids else self.init_state_id)

    def state_id_of_tip(self):
        """
        Returns the most recent state id.
        """
        return self.state_ids[-1] if self.state_ids else self.init_state_id

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

# messages
StopMessage = object()
EvalMessage = collections.namedtuple("EvalMessage", ["pos"])
CheckForModificationMessage = object()

class CoqWorker(threading.Thread):

    def __init__(self, view):
        super().__init__(daemon=True)
        self.request_queue = queue.Queue()
        self.view = view
        self.coq_eval_point = 0
        working_dir = None
        f = view.file_name()
        if f is not None:
            working_dir = os.path.dirname(f)
        self.coqtop = CoqtopProc(working_dir=working_dir)

        state_id = 1
        if COQ_MAJOR_VERSION >= (8,9):
            for parsed in self.coqtop.send('<call val="Init"><option val="none"/></call>'):
                if parsed.tag == "value":
                    state_id = int(parsed.find(".//state_id").attrib.get("val"))

        self.undo_stack = UndoStack(state_id)
        self.display = InlinePhantomDisplay(view)

    def _on_stop(self):
        self.coqtop.stop()
        self.display.close()

    def send_req(self, req):
        self.request_queue.put_nowait(req)

    def get_req(self):
        """Get the most recent request (skipping all others)"""
        res = self.request_queue.get(block=True)
        while True:
            try:
                res = self.request_queue.get_nowait()
            except queue.Empty:
                break
        return res

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
        if self.display.was_closed_by_user():
            print("worker {}'s display was closed; stopping")
            self._on_stop()
            return

        idx = prev_command(self.view, idx)
        if idx is None:
            idx = 0
        else:
            idx += 1

        if idx == self.coq_eval_point:
            print("no need to go anywhere")
            return

        self.display.show_goal("Working...")
        self.display.set_marks(min(idx, self.coq_eval_point), idx)

        cmds = []
        state_id = self.undo_stack.state_id_of_tip()

        forward = idx > self.coq_eval_point
        if forward:
            for cmd in split_commands(self.view, self.coq_eval_point, idx):
                if COQ_MAJOR_VERSION >= (8,7):
                    to_send = '<call val="Add"><pair><pair><string>{cmd}</string><int>1</int></pair><pair><state_id val="{state_id}"/><bool val="false"/></pair></pair></call>'.format(
                        cmd=xml_encode(cmd.text.strip()),
                        state_id=state_id)
                elif COQ_MAJOR_VERSION >= (8,5):
                    to_send = '<call val="Interp"><pair><pair><bool val="false"/><bool val="false"/></pair><string>{}</string></pair></call>'.format(xml_encode(cmd.text.strip()))
                else:
                    to_send = '<call val="interp" id="0">{}</call>'.format(xml_encode(cmd.text.strip()))
                cmds.append((to_send, cmd))
                state_id += 1
        else:
            (cmds_to_undo, state_to_rewind_to) = self.undo_stack.rewind_to(idx)
            if COQ_MAJOR_VERSION >= (8,5):
                if cmds_to_undo:
                    cmd = cmds_to_undo[0]
                    print("Rewinding to state {}...".format(state_to_rewind_to))
                    cmds.append(('<call val="Edit_at"><state_id val="{}"/></call>'.format(state_to_rewind_to), None))
                    idx = cmd.start
            else:
                print("Undoing {} things...".format(len(cmds_to_undo)))
                for cmd in cmds_to_undo:
                    print("Undoing {}".format(cmd.text.strip()))
                    cmds.append((REWIND_CMD, None))
                if cmds_to_undo:
                    idx = cmds_to_undo[0].start
            self.display.set_marks(idx, idx)

        error = None

        def pr(e, depth=0):
            print("{}{} [text={}]".format(" " * depth, e, e.text))
            if e:
                for x in e:
                    pr(x, depth + 2)

        stop = False
        for coq_cmd, cmd in cmds:
            if stop:
                break
            for parsed in self.coqtop.send(coq_cmd):
                if parsed.tag != "value":
                    continue
                if parsed.attrib.get("val") != "good":
                    print("Error!")
                    pr(parsed)
                    error = "".join(parsed.itertext()).strip() # WTF ETree API?!?
                    if not error:
                        error = "(unknown error)"
                    if cmd:
                        idx = cmd.start
                    stop = True
                    break
                if forward:
                    state_id = None
                    if COQ_MAJOR_VERSION >= (8,5):
                        # pr(parsed)
                        # pr(parsed.find(".//state_id"))
                        # print(repr(parsed.find(".//state_id").attrib))
                        # print(repr(parsed.find(".//state_id").attrib.get("val")))
                        state_id = int(parsed.find(".//state_id").attrib.get("val"))
                        # print("GOT STATE ID: {}".format(state_id))
                    self.undo_stack.push(cmd, state_id=state_id)
                    self.display.set_marks(cmd.end, cmd.end)

        print("asking for goal")
        if COQ_MAJOR_VERSION >= (8,5):
            response = self.coqtop.send('<call val="Goal"><unit/></call>')
        else:
            response = self.coqtop.send('<call val="goal"></call>')
        response = format_response(response, error)
        self.display.show_goal(response)
        # self.response_view.run_command("coq_update_output_buffer", {"text": response})
        # self.view.window().focus_view(self.view)
        # self.view.erase_regions("CoqTODO")
        self.coq_eval_point = idx

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
        worker.send_req(EvalMessage(pos=self.view.sel()[0].a))

class CoqKillCommand(sublime_plugin.TextCommand):
    def run(self, edit):
        worker_key = self.view.id()
        worker = coq_threads.get(worker_key, None)
        if worker:
            print("stopping {}...".format(worker))
            worker.send_req(StopMessage)
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
            worker.send_req(CheckForModificationMessage)

    def on_close(self, view):
        for view_id, worker in list(coq_threads.items()):
            if worker.display.was_closed_by_user():
                print("worker {} was closed??".format(worker))
                worker.view.run_command("coq_kill")
