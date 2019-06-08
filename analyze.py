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

for omegaTime, liaTime in tuples:
   totalOmega += omegaTime
   totalLia += liaTime
   print("{:.3f};{:.3f}".format(omegaTime, liaTime))

print("Total omega time: {:.1f}s".format(totalOmega))
print("Total lia time: {:.1f}s".format(totalLia))

print("Omega is {:.2f} times faster than lia".format(totalLia/totalOmega))
