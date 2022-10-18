#!/usr/bin/env python3
import os, sys, shlex, subprocess
try:
    from resource import RLIMIT_STACK, RLIM_INFINITY, setrlimit
    # tuple is (soft, hard)
    setrlimit(RLIMIT_STACK, (RLIM_INFINITY, RLIM_INFINITY))
except Exception as e:
    print(e, file=sys.stderr)

is_help = any(f in sys.argv[1:] for f in ('-h', '--help'))
CONSTANT_NAME = "GALLINA_CONSTANT"
USAGE = f"Usage: COQFLAGS=... {sys.argv[0]} {CONSTANT_NAME}"
if len(sys.argv) < 2 or is_help:
    print(USAGE, file=sys.stderr)
    sys.exit(0 if is_help else 1)

# we need stdin to be bytes in order to get stdout as bytes
# use os.fsencode to get bytes, as per https://stackoverflow.com/a/27185688/377022
constant = os.fsencode(sys.argv[1])
modpath = b".".join(constant.split(b".")[:-1])
COQFLAGS = shlex.split(os.getenv("COQFLAGS", default=""))
p = subprocess.run(["coqtop", "-q", "-quiet"] + COQFLAGS, capture_output=True, input=b"""
Require bedrock2.PrintListByte """ + modpath + b""".
Local Set Printing Width 2147483647.
Goal True.
  idtac "COQBUG(15373)".
  idtac "LINE_SEPARATOR_LOTTERY".
  PrintListByte.print_list_byte """ + constant + b""".
Abort.
""")
if p.returncode != 0 or b"\nError:" in p.stderr:
    sys.stderr.buffer.write(p.stderr)
    sys.exit(p.returncode or 5)

#  strip header, detect \r\n or \n, convert to \n, strip last \n
# os.linesep is \n on cygwin but \r\n in cygwin coq on github ci
stdout = p.stdout
def read(n):
    global stdout
    r, stdout = stdout[:n], stdout[n:]
    return r

b = b""
while not b.endswith(b"COQBUG(15373)"):
	r = read(1); b += r
	if not r: print(f"{b!r}"); sys.exit(4)
b = b""
while not b.endswith(b"LINE_SEPARATOR_LOTTERY"):
	r = read(1); b += r
	if not r: print(f"{b!r}"); sys.exit(3)
linesep = b[:-len(b"LINE_SEPARATOR_LOTTERY")]
read(len(linesep)) == linesep or sys.exit(2)
b = b""
while True:
	r = read(1); b += r
	if not r: sys.exit(not b.endswith(b"\n"))
	if b == linesep: b = b"\n"
	os.write(1, b[-2:-1])
	b = b[-1:]
