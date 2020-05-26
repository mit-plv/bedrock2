import sys, re, traceback, collections

def maplabel(l):
    return l

def count_lines_in_file(filepath):
  counts = dict()
  current = 'UNTAGGED'
  
  invalidUtf8 = 0
  lines=[]
  try:
      with open(filepath, 'rb') as f:
          lines = f.read().splitlines()
  except Exception as e:
      traceback.print_exc(file=sys.stderr)
  
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
          current = maplabel(m[1])
      else:
          counts[current] = counts.get(current, 0) + 1
  return counts

row = 'NOCATEGORY'
table = collections.Counter()
for line in sys.stdin.read().splitlines():
    line = line.strip()
    if line.startswith('#='):
        row = line[2:].strip()
        continue
    if line.startswith('#'):
        continue
    cts = count_lines_in_file(line)
    table += collections.Counter((row+':'+k, v) for (k,v) in cts.items())
print (table)
