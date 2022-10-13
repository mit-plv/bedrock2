#/bin/sh
set -eu
ulimit -s unlimited || true

{
coqtop -q -quiet $COQFLAGS 2>/dev/null << EOF
Require bedrock2.PrintListByte ${1%.*}.
Local Set Printing Width 2147483647.
Goal True.
  idtac "COQBUG(15373)".
  idtac "LINE_SEPARATOR_LOTTERY".
  PrintListByte.print_list_byte ${1}.
Abort.
EOF

} | python3 -c '#  strip header, detect \r\n or \n, convert to \n, strip last \n
import os, sys # os.linesep is \n on cygwin but \r\n in cygwin coq on github ci
b = b""
while not b.endswith(b"COQBUG(15373)"):
	r = os.read(0, 1); b += r
	if not r: print(f"{b!r}"); sys.exit(4)
b = b""
while not b.endswith(b"LINE_SEPARATOR_LOTTERY"):
	r = os.read(0, 1); b += r
	if not r: print(f"{b!r}"); sys.exit(3)
linesep = b[:-len(b"LINE_SEPARATOR_LOTTERY")]
os.read(0, len(linesep)) == linesep or sys.exit(2)
b = b""
while True:
	r = os.read(0, 1); b += r
	if not r: sys.exit(not b.endswith(b"\n"))
	if b == linesep: b = b"\n"
	os.write(1, b[-2:-1])
	b = b[-1:]
'
