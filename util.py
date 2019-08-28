import io
import re

def xml_encode(s):
    return (s
        .replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace("'", "&apos;")
        .replace('"', "&quot;"))

class XMLMuncher(object):
    """
    Splits a series of XML tags (e.g. <a><c/></a><b/>) into a stream
    (e.g. '<a><c/></a>', '<b/>'). This class is intended to be used
    to process streams of data. For instance:

    xm = XMLMuncher()
    xm.process("<b")           # no yields
    xm.process(">hello</b>")   # yields "<b>hello</b>"
    """

    # states
    START     = 0
    START_TAG = 1
    IN_TAG    = 2
    IN_STR1   = 3
    IN_STR2   = 4
    DEFAULT   = 5

    TRANSITIONS = {
        (START,   '<'):   (START_TAG,  1),
        (DEFAULT, '<'):   (START_TAG,  1),
        (IN_TAG,  "'"):   (IN_STR1, 0),
        (IN_TAG,  '"'):   (IN_STR2, 0),
        (IN_TAG,  '/'):   (IN_TAG, -1),
        (IN_TAG,  '>'):   (DEFAULT, 0),
        (IN_STR1, "'"):   (IN_TAG,  0),
        (IN_STR2, '"'):   (IN_TAG,  0),
    }

    WHITESPACE = re.compile(r"\s")

    def __init__(self):
        self.buf = io.StringIO()
        self.state = XMLMuncher.START
        self.open_tag_count = 0

    def reset(self):
        self.buf.close()
        self.__init__()

    def process(self, buf):
        """
        Append buf, yield any completed XML tags. This is a stateful API, so
        callers MUST exhaust the generator before making another call to any
        methods on this class.
        """

        for char in buf:
            self.buf.write(char)

            # special case 1: ignore all whitespace
            if XMLMuncher.WHITESPACE.match(char):
                continue

            # special case 2: START_TAG immediately transitions to IN_TAG
            if self.state == XMLMuncher.START_TAG:
                if char == '/':
                    self.open_tag_count -= 2
                self.state = XMLMuncher.IN_TAG
                continue

            # consult transition table
            (new_state, inc) = XMLMuncher.TRANSITIONS.get((self.state, char), (self.state, 0))
            self.state = new_state
            # print("{} --> {},{}".format(char, self.state, self.open_tag_count))
            self.open_tag_count += inc
            if self.state == XMLMuncher.DEFAULT and self.open_tag_count == 0:
                xml_str = self.buf.getvalue()
                # print("--> munched {}".format(xml_str))
                yield xml_str.replace("&nbsp;", " ") # HACK
                self.reset()
