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

class _Handler(ContentHandler):
    __slots__ = ("finished_tags", "buffer", "depth")

    def __init__(self):
        self.finished_tags = []
        self.buffer = io.StringIO()
        self.depth = 0

    def clear_buffer(self):
        self.buffer.close()
        self.buffer = io.StringIO()

    def reset(self):
        self.clear_buffer()
        self.finished_tags.clear()
        self.depth = 0

    # def startDocument(self):
    #     print("startDocument()")

    # def endDocument(self):
    #     print("endDocument()")

    def startElement(self, name, attrs):
        # print("startElement({!r}, {!r})".format(name, attrs))
        wr = self.buffer.write
        wr('<')
        wr(name)
        for attr_name, attr_value in attrs.items():
            wr(' ')
            wr(attr_name)
            wr('="')
            wr(xml_encode(attr_value))
            wr('"')
        wr('>')
        self.depth += 1

    def endElement(self, name):
        # print("endElement({!r})".format(name))
        wr = self.buffer.write
        wr('</')
        wr(name)
        wr('>')
        self.depth -= 1
        if self.depth == 0:
            self.finished_tags.append(self.buffer.getvalue())
            # print(" --> DONE: {}".format(self.finished_tags[-1]))
            self.clear_buffer()

    def characters(self, text):
        # print("characters({!r})".format(text))
        if self.depth > 0:
            self.buffer.write(xml_encode(text))

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
