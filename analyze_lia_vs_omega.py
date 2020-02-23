# Compare lia vs omega performance
# Usage:
# In deps/coqutil/src/coqutil/Z/Lia.v, replace the line
# Ltac blia := lia.
# by
# Ltac blia := compare_omega_lia_timed.
# and replace the line
# Ltac bomega := omega.
# by
# Ltac bomega := compare_omega_lia_timed.
# Then run
# make clean_all
# and
# time make 2>&1 | tee log1.txt
# and
# python3 analyze_lia_vs_omega.py log1.txt

import sys
import os
import re

filepath = sys.argv[1]

if not os.path.isfile(filepath):
   print("File path {} does not exist. Exiting...".format(filepath))
   sys.exit()

# (omegaTime, liaTime) tuples
tuples = []

with open(filepath) as fp:
   lastWasOmega = False
   omegaTime = "N/A"
   lineNo = 1
   for line in fp:
      omegaMatch = re.search('Tactic call omega ran for ([0-9.]*) secs.*\((success|failure)\)', line)
      if omegaMatch:
         omegaTime = omegaMatch.group(1)
         lastWasOmega = True
      elif line.strip() == "Did not dare to run omega":
         omegaTime = -10000000
         lastWasOmega = True
      else:
         liaMatch = re.search('Tactic call lia ran for ([0-9.]*) secs.*\((success|failure)\)', line)
         if liaMatch:
            liaTime = liaMatch.group(1)
            if lastWasOmega:
               tuples.append((float(omegaTime), float(liaTime)))
            else:
               print("weird: lia time without preceding omega time at line {}".format(lineNo))
         else:
            if lastWasOmega:
               print("weird: omega time without following lia time {}".format(lineNo))
            else:
               pass
         lastWasOmega = False
      lineNo += 1

tuples.sort()

totalOmega = 0.0
totalLia = 0.0
omegaNA = 0

slowTuples = []

for omegaTime, liaTime in tuples:
   if omegaTime < 0:
      omegaNA += 1
   elif omegaTime > 1 or liaTime > 1:
      slowTuples.append((omegaTime, liaTime))
   else:
      totalOmega += omegaTime
      totalLia += liaTime
      print("{:.3f};{:.3f}".format(omegaTime, liaTime))

print("Ignored {:d} cases where we did not dare to run omega".format(omegaNA))

print("Ignored {:d} cases where omega or lia took more than a second, here they are:".format(len(slowTuples)))
for omegaTime, liaTime in slowTuples:
   print("{:.3f};{:.3f}".format(omegaTime, liaTime))

print("Total omega time: {:.1f}s".format(totalOmega))
print("Total lia time: {:.1f}s".format(totalLia))

print("Omega is {:.2f} times faster than lia".format(totalLia/totalOmega))
