import io
import re
from xml.sax import make_parser
from xml.sax.handler import ContentHandler

def xml_encode(s):
    return (s
        .replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace("'", "&apos;")
        .replace('"', "&quot;"))

class XMLNode(object):

    def __iter__(self):
        return iter(())

    def flatten(self):
        q = [self]
        while q:
            x = q.pop()
            yield x
            q.extend(reversed(list(x)))

    def iter(self, tag_name):
        for x in self.flatten():
            if isinstance(x, XMLTag) and x.tag == tag_name:
                yield x

    def itertext(self):
        for x in self.flatten():
            if isinstance(x, XMLText):
                yield x.string

class XMLTag(XMLNode):
    __slots__ = ("tag", "attrib", "contents")

    def __init__(self, tag, attrib, contents):
        self.tag = tag
        self.attrib = attrib
        self.contents = contents

    def __iter__(self):
        return iter(self.contents)

class XMLText(XMLNode):
    __slots__ = ("string",)

    def __init__(self, string):
        self.string = string

class _Handler(ContentHandler):
    __slots__ = ("finished_tags", "stack")

    def __init__(self):
        self.finished_tags = []
        self.stack = [] # stack of XMLTag

    def reset(self):
        self.finished_tags.clear()
        self.stack.clear()

    # def startDocument(self):
    #     print("startDocument()")

    # def endDocument(self):
    #     print("endDocument()")

    def startElement(self, name, attrs):
        # print("startElement({!r}, {!r})".format(name, attrs))
        self.stack.append(XMLTag(name, attrs, []))

    def endElement(self, name):
        # print("endElement({!r})".format(name))
        tag = self.stack.pop()
        if self.stack:
            self.stack[-1].contents.append(tag)
        else:
            self.finished_tags.append(tag)
            # print(" --> DONE: {}".format(self.finished_tags[-1]))

    def characters(self, text):
        # print("characters({!r})".format(text))
        if len(self.stack) > 0:
            self.stack[-1].contents.append(XMLText(text))

class XMLMuncher(object):
    __slots__ = ("parser", "handler")

    def __init__(self):
        self.reset()

    def reset(self):
        self.parser = make_parser()
        self.handler = _Handler()
        self.parser.setContentHandler(self.handler)
        self.parser.feed("""
            <?xml version="1.0"?>
            <!DOCTYPE coq [
            <!ENTITY nbsp " ">
            ]>
            <coq>
        """.strip())
        self.handler.reset()

    def process(self, buf):
        self.parser.feed(buf)
        yield from self.handler.finished_tags
        self.handler.finished_tags.clear()


def byte_to_character_offset(text, byte_offset, charset):
    """Convert a byte offset to a character offset.

    Generally, this function obeys the law:

        text[:_byte_to_character_offset(text, byte_offset)] ==
        text.encode(charset)[:byte_offset].decode(charset)

    Note that if byte_offset falls in the middle of a character, this function
    silently rounds up to the next character.
    """
    position = 0
    bytes_spanned = 0

    while bytes_spanned < byte_offset:
        bytes_spanned += len(text[position].encode(charset))
        position += 1

    return position
