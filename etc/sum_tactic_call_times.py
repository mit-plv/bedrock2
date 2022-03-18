import sys
import os
import re

class Stats:
   def __init__(self):
      self.nCalls = 0
      self.longestCall = 0
      self.totalTime = 0

   def add_call(self, t):
      self.nCalls += 1
      self.longestCall = max(self.longestCall, t)
      self.totalTime += t


filepath = sys.argv[1]

if not os.path.isfile(filepath):
   print(f"File path {filepath} does not exist. Exiting...")
   sys.exit(1)

stats = dict()

with open(filepath) as fp:
   for line in fp:
      tacMatch = re.search('Tactic call (.*) ran for ([0-9.]+) secs.*\((success|failure).*\)', line)
      if tacMatch:
         tacName = tacMatch.group(1)
         tacTime = tacMatch.group(2)
         tacOutcome = tacMatch.group(3)
         if not stats.get(tacName):
            stats[tacName] = Stats()
         stats[tacName].add_call(float(tacTime))
         if float(tacTime) > 100:
            print(line)

print(f'{"Tactic name":<25}{"Calls":>7}{"Max time":>9}{"Total time":>12}')

for tacName, s in stats.items():
   print(f'{tacName:<25}{s.nCalls:>7}{s.longestCall:9.3f}{s.totalTime:12.3f}')
