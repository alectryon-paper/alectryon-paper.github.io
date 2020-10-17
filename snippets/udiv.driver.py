#!/usr/bin/env python3

"""
An alternative Alectryon driver that uses pygments and objdump too
pretty-print listings.
"""

import re
import subprocess
from tempfile import NamedTemporaryFile

from dominate import tags
from dominate.util import raw as dom_raw
from pygments.lexers.c_cpp import CLexer
from pygments.lexers.asm import CObjdumpLexer

from alectryon.pygments import _highlight, HTML_FORMATTER
import alectryon.cli, alectryon.transforms

def hl(m, filter, lexer):
    code = filter(m.string[m.start(1):m.end(1)])
    before, highlighted, after = _highlight(code, lexer(), HTML_FORMATTER)
    return tags.span(
        m.string[:m.start()],
        tags.span(before, dom_raw(highlighted), after, cls="highlight"),
        m.string[m.end():],
        cls="udiv-listing")

def bytes_of_response(s):
    for d in ("[", "]", "Byte.x"):
        s = s.replace(d, "")
    return bytes(int(b.strip(), 16) for b in s.split(";"))

RE_DUMP_REMOVE = re.compile(r".*Disassembly of section [.]text:\s*", re.DOTALL)
RE_DUMP_FMT = re.compile(r"(\t)({h}{h})({h}{h})({h}{h})({h}{h})(\s*\t)".format(h="[0-9A-Za-z]"), re.DOTALL)

def cleanup_objdump(dump):
    dump = RE_DUMP_REMOVE.sub("", dump)
    # Work around a limitation of Pygments objdump highlighter
    dump = RE_DUMP_FMT.sub(r"\1\2 \3 \4 \5\6", dump)
    return dump

def objdump(bs):
    with NamedTemporaryFile() as f:
        f.write(bs)
        f.flush()
        cmd = ["riscv-none-embed-objdump", "--disassemble", f.name]
        dump = subprocess.check_output(cmd, stderr=subprocess.STDOUT).decode("utf-8")
        return cleanup_objdump(dump)

def objdump_filter(s):
    bs = bytes_of_response(s)
    dump = objdump(bs)
    return dump

def str_filter(s):
    return s.replace('""', '"')

RE_C = re.compile(r'[{]c\s*"\s*(.*?)\s*"\s*c[}]\s*', re.DOTALL)
RE_MC = re.compile(r'[{]mc\s*(.*?)\s*mc[}]\s*', re.DOTALL)
RE_COMPUTE = re.compile(r'\A\s*=', re.DOTALL) # Multiline strings break the dedent pass

def custom_transform(fragments):
    for fr in fragments:
        for msgs in alectryon.transforms.fragment_message_sets(fr):
            for idx, r in enumerate(msgs):
                r = r._replace(contents=RE_COMPUTE.sub("=", r.contents))
                if (m := RE_C.search(r.contents)):
                    msgs[idx] = r._replace(contents=hl(m, str_filter, CLexer))
                elif (m := RE_MC.search(r.contents)):
                    msgs[idx] = r._replace(contents=hl(m, objdump_filter, CObjdumpLexer))
        yield fr

old_highlight = alectryon.pygments.highlight_html
def highlight_html(s):
    if isinstance(s, str):
        return old_highlight(s)
    return s

alectryon.pygments.highlight_html = highlight_html
alectryon.transforms.DEFAULT_TRANSFORMS.append(custom_transform)

import alectryon.core, alectryon.docutils
alectryon.core.SerAPI.DEFAULT_PP_ARGS['pp_margin'] = 50
alectryon.docutils.LONG_LINE_THRESHOLD = 90

if __name__ == '__main__':
    alectryon.cli.main()
