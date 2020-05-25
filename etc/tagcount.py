import sys, re
counts = dict()
current = 'UNTAGGED'

invalidUtf8 = 0
if hasattr(sys.stdin, 'buffer'):
    lines = sys.stdin.buffer.readlines()
else:
    lines = sys.stdin.readlines()

for line in lines:
    try:
        line = line.decode('utf-8')
    except UnicodeDecodeError: #
        line = 'a line containing invalid utf-8'
        invalidUtf8 += 1
    line = line.strip()
    if not line:
        continue
    m = re.match(r'\(\*tag:(\w+)\*\)', line)
    if m:
        current = m[1]
    else:
        counts[current] = counts.get(current, 0) + 1
s = sum(counts.values())
u = counts.get('UNTAGGED', 0)
if u:
    print(f'{u} untagged lines')
s -= u
counts.pop('UNTAGGED', None)
#print ('\n'.join(reversed(sorted(('%2d%% %5d %s'%(100*v/s, v, k)) for (k, v) in counts.items()))))
print ('\n'.join(reversed(sorted(('%5d %s'%(v, k)) for (k, v) in counts.items()))))
#print(counts)
if invalidUtf8:
    print(f'{invalidUtf8} lines contained invalid utf-8 and were still counted, but not regex-matched')
