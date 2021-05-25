"""Reusable tooling for interacting with Coq.

Key contents:
  - CoqtopProc: thin wrapper for the `coqtop` process (via XML API)
  - CoqBot: high-level wrapper
"""

import os.path
import re
import subprocess
import shlex
import codecs

from . import util


CHARSET = "utf-8"

class CoqtopProc(object):

    def __init__(self, coq_install_dir, coq_version, extra_args=(), working_dir=None, verbose=False):
        """
        Spawns a new coqtop process and creates pipes for interaction.
        """

        if coq_version >= (8,9):
            cmd = [
                os.path.join(coq_install_dir, "bin", "coqidetop"),
                "-main-channel", "stdfds"]
        elif coq_version >= (8,5):
            cmd = [
                os.path.join(coq_install_dir, "bin", "coqtop"),
                "-main-channel", "stdfds", "-ideslave"]
        elif coq_version >= (8,4):
            cmd = [
                os.path.join(coq_install_dir, "bin", "coqtop"),
                "-ideslave"]
        else:
            raise Exception("specified version of coqtop is too old!")

        cmd.extend(extra_args)

        if working_dir is not None:
            project_file = self.find_coqproject_file(working_dir)
            if project_file is not None:
                working_dir = os.path.dirname(project_file)
                with open(project_file, "r") as f:
                    cmd.extend(shlex.split(f.read()))

        self.verbose = verbose

        print("Starting `{}` in {}".format(" ".join(cmd), working_dir))
        self.proc = subprocess.Popen(
            cmd,
            bufsize=0,
            cwd=working_dir,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE)

        self.decoder = codecs.getincrementaldecoder(CHARSET)()

    def print(self, value):
        if self.verbose:
            print(value)

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
        self.print("sending: {}".format(text.encode("unicode-escape")))

        # Send
        self.proc.stdin.write(text.encode(CHARSET))
        self.proc.stdin.flush()
        self.print("sent")

        # Recieve until we find <value>...</value>
        xm = util.XMLMuncher()
        done = False
        while not done:
            buf = self.proc.stdout.read(1024)
            try:
                response = self.decoder.decode(buf)
            except UnicodeDecodeError as e:
                self.print("{}".format(list("{:x}".format(b) for b in buf)))
                raise e
            self.print("got partial response: {}".format(response))
            if not response:
                raise Exception("coqtop died!")
            for xml in xm.process(response):
                yield xml
                if isinstance(xml, util.XMLTag) and xml.tag == "value":
                    done = True
                    self.print("--- DONE ---")

    def stop(self):
        """
        Stop the underlying coqtop process.
        """
        p = self.proc
        if p is not None:
            p.terminate()
            ret = p.wait()
            print("coqtop exited with status {}".format(ret))
            self.proc = None

TOKENS = (
    ("open_comment",  re.compile(r'\(\*')),
    ("close_comment", re.compile(r'\*\)')),
    ("string",        re.compile(r'"[^"]*"')),
    ("whitespace",    re.compile(r'\s+')),
    ("word",          re.compile(r'\w+')),
    ("fullstop",      re.compile(r'\.(?:\s+|$)')),
)

def tokens(text, start=0):
    i = start
    comment_depth = 0
    while i < len(text):
        name = "other"
        match = text[i]
        for n, regex in TOKENS:
            m = regex.match(text, pos=i)
            if m and n == "symbol" and ("(*" in m.group(0) or "*)" in m.group(0)):
                m = None
            if m:
                name = n
                match = m.group(0)
                break
        if name == "open_comment":
            comment_depth += 1
        elif name == "close_comment":
            comment_depth -= 1
        elif name == "whitespace":
            pass
        elif comment_depth == 0:
            yield (i, name, len(match), match)
        i += len(match)


BULLET_CHARS = { "-", "+", "*", "{", "}" }
BULLET_CHARS_REGEX = re.compile(r"\s*[" + re.escape("".join(BULLET_CHARS)) + r"]")
def find_first_coq_command(text, start=0):
    """Find the first Coq command in `text[start:]`.

    The return value is the index one past the end of the command, such that
    `text[start:RETURN_VALUE]` gives the text of the command.

    If no command is present, this function returns None.
    """

    is_first = True
    for token_pos, token_type, token_len, token_text in tokens(text, start):

        # Bullet characters in Ltac require some care; each is its own command
        if is_first:
            match = BULLET_CHARS_REGEX.match(token_text)
            if match:
                return token_pos + match.end()

        # Otherwise, commands end in fullstops
        if token_type == "fullstop":
            return token_pos + 1

        is_first = False

    return None


def pr(e, depth=0):
    print("{}{}".format(" " * depth, e))
    if e:
        for x in e:
            pr(x, depth + 2)


def text_of(xml):
    return "".join(xml.itertext())


def find_child(xml, tag_name):
    for res in xml.iter(tag_name):
        return res
    raise ValueError("{} has no {} child".format(xml, tag_name))


def get_state_id(xml):
    assert xml.tag == "value"
    return int(find_child(xml, "state_id").attrib.get("val"))


def format_response(xml, coq_version):
    """Takes XML output from coqtop and makes it clean and pretty.

    Sample input:
        <value val="good"><option val="some"><goals><list><goal><string>14</string><list><string>n : nat</string></list><string>{rs : list record_name |
        forall r : record_name, In r rs &lt;-&gt; refers_to (EConst n) r}</string></goal><goal><string>15</string><list><string>r : record_name</string></list><string>{rs : list record_name |
        forall r0 : record_name, In r0 rs &lt;-&gt; refers_to (EVar r) r0}</string></goal><goal><string>20</string><list><string>e1 : expr</string><string>e2 : expr</string><string>IHe1 : {rs : list record_name |
        forall r : record_name, In r rs &lt;-&gt; refers_to e1 r}</string><string>IHe2 : {rs : list record_name |
        forall r : record_name, In r rs &lt;-&gt; refers_to e2 r}</string></list><string>{rs : list record_name |
        forall r : record_name, In r rs &lt;-&gt; refers_to (EPlus e1 e2) r}</string></goal></list><list/></goals></option></value>
    """

    messages = []
    for x in xml:
        if x.tag == "feedback":
            for msg in x.iter("message"):
                messages.append(text_of(msg))
        if x.tag == "value":
            if x.attrib.get("val") != "good":
                state_id = get_state_id(x)
                raise _CoqExceptionAtState(text_of(x), state_id)
            goals = list(x.iter("goal"))
            output = "Goals: {}\n\n".format(len(goals))
            output += "\n".join(messages)
            if goals:
                # from xml import etree
                # print("\n".join(ET.tostring(g).decode("UTF-8") for g in goals))
                primary_goal = goals[0]
                if coq_version >= (8,6):
                    strs = list(primary_goal.iter("richpp"))
                else:
                    strs = list(primary_goal.iter("string"))[1:]
                hyps = strs[:-1]
                goal = strs[-1]
                for h in hyps:
                    output += "  {}\n".format(text_of(h))
                output += "  " + ("-" * 40) + "\n"
                output += "  {}\n".format(text_of(goal))
            return output
        # else:
        #     print("got tag '{}'".format(x))


class CoqException(Exception):
    def __init__(self, message, bad_ranges=()):
        super().__init__(message)
        self.bad_ranges = bad_ranges


class _CoqExceptionAtState(CoqException):
    def __init__(self, message, state_id):
        super().__init__(message)
        self.state_id = state_id


class CoqBot(object):

    def __init__(self, coq_install_dir, coq_version, extra_args=(), working_dir=None, verbose=False):
        self.verbose = verbose
        self.coqtop = CoqtopProc(
            coq_install_dir=coq_install_dir,
            coq_version=coq_version,
            extra_args=extra_args,
            working_dir=working_dir,
            verbose=verbose)
        self.coq_version = coq_version
        self.cmds_sent = [] # list of (command, state_id_before_command)

        self.state_id = None
        for parsed in self.coqtop.send('<call val="Init"><option val="none"/></call>'):
            if parsed.tag == "value":
                self.state_id = get_state_id(parsed)
        if self.state_id is None:
            raise Exception("did not get an initial state ID from coqtop")

    def print(self, value):
        if self.verbose:
            print(value)

    def _append_and_check_response(self, xml_command):
        value_tag = None
        for parsed in self.coqtop.send(xml_command):
            if parsed.tag == "value":
                if parsed.attrib.get("val") == "good":
                    value_tag = parsed
                else:
                    print("Error!")
                    pr(parsed)
                    error = text_of(parsed).strip()
                    if not error:
                        error = "(unknown error)"

                    bad_ranges = []

                    start = parsed.attrib.get("loc_s")
                    end = parsed.attrib.get("loc_e")
                    if start and end:
                        bad_ranges.append((int(start), int(end)))

                    raise CoqException(error, bad_ranges=bad_ranges)

        assert value_tag is not None
        return value_tag

    def append(self, text, start=0):
        """Send the first command in `text[start:]` to Coq.

        Returns the new offset after processing the first command in
        text[start:], such that `text[start:RETURN_VALUE]` is what was sent.

        Appends the sent command to this object's "sent buffer" (see
        `rewind_to(...)`).

        Returns 0 if there is no command in the given text.

        Throws CoqException if Coq reports an error.  Throws other kinds of
        exceptions if there is some problem communicating with the CoqTop
        process.

        NOTE: To send multiple commands, use a loop.  For instance:

            idx = 0
            while True:
                n = bot.append(text, start=idx)
                if n == 0:
                    break
                else:
                    # Optional: update display
                    idx = n
        """

        index_of_end_of_command = find_first_coq_command(text, start)

        if index_of_end_of_command:
            coq_cmd = text[start:index_of_end_of_command]

            if self.coq_version >= (8,7):
                to_send = '<call val="Add"><pair><pair><string>{cmd}</string><int>1</int></pair><pair><state_id val="{state_id}"/><bool val="false"/></pair></pair></call>'.format(
                    cmd=util.xml_encode(coq_cmd),
                    state_id=self.state_id)
            elif self.coq_version >= (8,5):
                to_send = '<call val="Interp"><pair><pair><bool val="false"/><bool val="false"/></pair><string>{}</string></pair></call>'.format(util.xml_encode(coq_cmd))
            else:
                to_send = '<call val="interp" id="0">{}</call>'.format(util.xml_encode(coq_cmd))

            state_id = get_state_id(self._append_and_check_response(to_send))
            self.cmds_sent.append((coq_cmd, self.state_id))
            self.state_id = state_id

            self.print("sending status query")
            try:
                self._append_and_check_response('<call val="Status"><bool val="{force}"/></call>'.format(force="true"))
            except CoqException:
                # If coq accepts the Add command, then it has moved us to a new
                # state id.  We really do have to tell it we want to go back to
                # an earlier state if the command fails.
                self._rewind_to(len(self.cmds_sent) - 1)
                raise

        return index_of_end_of_command or 0

    def current_goal(self):
        """Read the current goal.

        Returns text indicating how many unproven goals remain and showing the
        focused goal.
        """

        self.print("asking for goal")
        if self.coq_version >= (8,5):
            response = self.coqtop.send('<call val="Goal"><unit/></call>')
        else:
            response = self.coqtop.send('<call val="goal"></call>')
        return format_response(response, coq_version=self.coq_version)

    def _rewind_to(self, index_of_earliest_undone_command):
        if index_of_earliest_undone_command == len(self.cmds_sent):
            return
        _, state_to_rewind_to = self.cmds_sent[index_of_earliest_undone_command]
        to_send = '<call val="Edit_at"><state_id val="{}"/></call>'.format(state_to_rewind_to)
        for parsed in self.coqtop.send(to_send):
            pass
        self.cmds_sent = self.cmds_sent[0:index_of_earliest_undone_command]
        self.state_id = state_to_rewind_to

    def rewind_to(self, idx):
        """Rewind to an earlier state.

        This procedure rewinds to the end of the last command which ends before
        `idx` in this object's "sent buffer".  The `append(...)` call adds
        commands to the sent buffer.

        Returns the resulting index.
        """

        index_of_earliest_undone_command = None
        count = 0
        for i, (cmd, state_id) in enumerate(self.cmds_sent):
            new_count = count + len(cmd)
            if new_count > idx:
                index_of_earliest_undone_command = i
                break
            count = new_count

        if index_of_earliest_undone_command is not None:
            self._rewind_to(index_of_earliest_undone_command)
        else:
            print("WARNING: cannot rewind to {} (too large)".format(idx))

        return count

    def sent_buffer(self):
        for cmd_text, _ in self.cmds_sent:
            yield cmd_text

    def stop(self):
        self.coqtop.stop()
