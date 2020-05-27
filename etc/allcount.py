import sys, re, traceback, collections

tag2col = {
    # tags to recategorize:
    'lemma': 'TODO',
    'notations': 'TODO',
    'automation': 'TODO',

    # tags mapped to rows in "Excluded" mini-table:
    'unrelated': 'unrelated',
    'test': 'unrelated',
    'library': 'library',
    'importboilerplate': 'imports',
    'administrativia': 'imports',
    'administrivia': 'imports',
    'doc': 'doc',

    # tags mapped to columns in main table:
    'code': 'implementation',
    'compiletimecode': 'implementation',
    'spec': 'interface',
    'proof': 'interesting proof',
    'loopinv': 'interesting proof',
    'workaround': 'low-insight proof',
    'bitvector': 'low-insight proof',
    'symex': 'low-insight proof',
    'obvious': 'low-insight proof',
    'lists': 'low-insight proof',
    'maps': 'low-insight proof'
}

def maplabel(l):
    return tag2col[l]

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
    table += collections.Counter(dict((row+':'+k, v) for (k,v) in cts.items()))

def countBy(p):
    items = [(k,v) for (k, v) in table.items() if p(k)]
    for k,v in items:
        del table[k]
    return sum(v for (k,v) in items)

with open('loc_excluded.tex', 'w') as f1:
    def line(what, v):
        f1.write(f'  {what:10s} & {v:5d} \\\\ \\hline \n')
    line('unrelated', countBy(lambda s: s.startswith('unrelated:') or s.endswith(':unrelated')))
    line('library', countBy(lambda s: s.startswith('coqutil:') or s.endswith(':library')))
    line('imports', countBy(lambda s: s.endswith(':imports')))
    line('doc', countBy(lambda s: s.endswith(':doc')))
    line('Kami', countBy(lambda s: s.startswith('kami:')))

with open('loc.tex', 'w') as f2:
    for (row, rowname) in list(dict(programlogic='program logic', lightbulb='lightbulb app', compiler='compiler', hwsw='SW/HW interface').items())+[('end-to-end','end-to-end')]:
        print(f'{rowname:20s} & ', end='', file=f2)
        r = dict()
        for column in ['interface', 'implementation', 'interesting proof', 'low-insight proof']:
            r[column] = countBy(lambda s: s == row+':'+column)
            print(f'{r[column]:4d} & ', end='', file=f2)
        if r['implementation']:
            overh =      (r['implementation'] + r['interface'] + r['interesting proof'] + r['low-insight proof'] + 0.0) / r['implementation']
            idealOverh = (r['implementation'] + r['interface'] + r['interesting proof']                          + 0.0) / r['implementation']
            f2.write(f'   {overh:6.1f} &   {idealOverh:6.1f}')
        else:
            f2.write('      \\NA &      \\NA')
        f2.write(' \\\\ \\hline\n')

print('code unaccounted for:')
for k,v in table.items():
    print (k, v)
