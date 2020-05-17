import sys, re
counts = dict()
current = 'UNTAGGED'
for line in sys.stdin:
    line = line.strip()
    if not line:
        continue
    m = re.match(r'\(\*tag:(\w+)\*\)', line)
    if m:
        current = m[1]
    else:
        counts[current] = counts.get(current, 0) + 1
s = sum(counts.values())
print ('\n'.join(reversed(sorted(('%02d%% %s'%(100*v/s, k)) for (k, v) in counts.items()))))
