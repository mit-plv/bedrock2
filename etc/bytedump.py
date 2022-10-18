#!/usr/bin/env python3
import os, sys, shlex, subprocess
try:
    from resource import RLIMIT_STACK, RLIM_INFINITY, setrlimit
    # tuple is (soft, hard)
    setrlimit(RLIMIT_STACK, (RLIM_INFINITY, RLIM_INFINITY))
except Exception as e:
    print(e, file=sys.stderr)

if len(sys.argv) != 2 or sys.argv[1] in ("-h", "--help"):
    print(f"Usage: COQFLAGS=... {sys.argv[0]} GALLINA_CONSTANT", file=sys.stderr)
    sys.exit(1)

constant = sys.argv[1]
modpath, _ = constant.rsplit(".", 1)
COQFLAGS = shlex.split(os.getenv("COQFLAGS", default=""))
# we need stdin to be bytes in order to get stdout as bytes
# use os.fsencode to get bytes, as per https://stackoverflow.com/a/27185688/377022
p = subprocess.run(["coqtop", "-q", "-quiet"] + COQFLAGS, capture_output=True, input=os.fsencode(f"""
Require bedrock2.PrintListByte {modpath}.
Local Set Printing Width 2147483647.
Goal True.
  idtac "COQBUG(15373)".
  idtac "LINE_SEPARATOR_LOTTERY".
  PrintListByte.print_list_byte {constant}.
Abort.
"""))
# coqtop only exits with nonzero on the case of segfaults, etc.
# Normal coq errors do not interrupt coqtop (unlike coqc), so all we
# can go on is the error message
if p.returncode != 0 or b"\nError:" in p.stderr:
    sys.stderr.buffer.write(p.stderr)
    sys.exit(p.returncode or 2)

# strip header, detect \r\n or \n, convert to \n, strip last \n
# os.linesep is \n on cygwin but \r\n in cygwin coq on github ci
output = p.stdout
try:
    _header, output = output.split(b"COQBUG(15373)", 1)
    linesep, output = output.split(b"LINE_SEPARATOR_LOTTERY", 1)
    empty  , output = output.split(linesep, 1)
    if empty != b"": print(f"Non-empty after LINE_SEPARATOR_LOTTERY: {empty!r}", file=sys.stderr); sys.exit(3)
    output , end = output[:-len(linesep)], output[-len(linesep):]
    sys.stdout.buffer.write(output)
    if end != linesep: print(f"Non-linesep at end: {end!r}", file=sys.stderr); sys.exit(4)
except ValueError as e:
    print(f"Failure to split: {output!r}\n{e}", file=sys.stderr); sys.exit(5)
