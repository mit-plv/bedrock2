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
   print(f"File path {filepath} does not exist. Exiting...")
   sys.exit(1)

# (tacATime, tacBTime) tuples
tuples = []

tacAName = "original_lia"
tacBName = "enhanced_lia"

tacBTimeThresh = 1.0

with open(filepath) as fp:
   lastWasTacA = False
   tacATime = "N/A"
   lineNo = 1
   currentFile = "N/A"
   currentFileWasPrinted = False
   for line in fp:
      fileMatch = re.search('COQC (.*)', line)
      if fileMatch:
         currentFile = fileMatch.group(1)
         currentFileWasPrinted = False
      tacAMatch = re.search(f'{tacAName} ran for ([0-9.]*) secs.*\((success|failure)\)', line)
      if tacAMatch:
         tacATime = tacAMatch.group(1)
         lastWasTacA = True
      elif line.strip() == f"Did not dare to run {tacAName}":
         tacATime = -10000000
         lastWasTacA = True
      else:
         tacBMatch = re.search(f'{tacBName} ran for ([0-9.]*) secs.*\((success|failure)\)', line)
         if tacBMatch:
            tacBTime = tacBMatch.group(1)
            if lastWasTacA:
               tuples.append((float(tacATime), float(tacBTime)))
               if float(tacBTime) >= tacBTimeThresh:
                  if not currentFileWasPrinted:
                     print(f'Cases where {tacBName} takes more than {tacBTimeThresh:.3f}s in {currentFile}:')
                     currentFileWasPrinted = True
                  print(f"{float(tacATime):.3f};{float(tacBTime):.3f}")
            else:
               print(f"weird: {tacBName} time without preceding {tacAName} time at line {lineNo}")
         else:
            if lastWasTacA:
               print(f"weird: {tacAName} time without following {tacBName} time at line {lineNo}")
            else:
               pass
         lastWasTacA = False
      lineNo += 1

tuples.sort()

totalTacA = 0.0
totalTacB = 0.0
tacANA = 0
tacBNA = 0
tacAFaster = 0
tacBFaster = 0
sameTime = 0

slowTuples = []

thresh = 100000.0

for tacATime, tacBTime in tuples:
   if tacATime < 0:
      tacANA += 1
   elif tacBTime < 0:
      tacBNA += 1
   elif tacATime > thresh or tacBTime > thresh:
      slowTuples.append((tacATime, tacBTime))
   else:
      totalTacA += tacATime
      totalTacB += tacBTime
      if tacATime < tacBTime:
         tacAFaster += 1
      elif tacBTime < tacATime:
         tacBFaster += 1
      elif tacATime == tacBTime:
         sameTime += 1

print(f"Ignored {tacANA:d} cases where we did not dare to run {tacAName}")
print(f"Ignored {tacBNA:d} cases where we did not dare to run {tacBName}")

print(f"Ignored {len(slowTuples):d} cases where {tacAName} or {tacBName} took more than {thresh:.1f}s, here they are:")
for tacATime, tacBTime in slowTuples:
   print(f"{tacATime:.3f};{tacBTime:.3f}")

print(f"# of cases where {tacAName} is faster: {tacAFaster}")
print(f"# of cases where {tacBName} is faster: {tacBFaster}")
print(f"# of cases where both have the same running time: {sameTime}")
print(f"Sum of these three numbers: {tacAFaster+tacBFaster+sameTime}")
print(f"Total number of measurements: {len(tuples)}")

print(f"Total {tacAName} time: {totalTacA:.1f}s")
print(f"Total {tacBName} time: {totalTacB:.1f}s")

print(f"{tacAName} is {totalTacB/totalTacA:.2f} times faster than {tacBName}")

try:
   import matplotlib.pyplot as plt
except ImportError:
   print("Not creating graphics because matplotlib not installed")
   sys.exit(0)

if filepath[-4:] != ".txt":
   print(f"{filepath} does not end in '.txt'")
   sys.exit(1)

noext = filepath[:-4]

def sorted_prefix_sums(l):
   l.sort()
   sum = 0.0
   for i in range(len(l)):
      sum += l[i]
      l[i] = sum
   return l

# sorted running time plot

plt.figure()

plt.plot(sorted([tA for tA, tB in tuples]), color='gray', label=tacAName)
plt.plot(sorted([tB for tA, tB in tuples]), color='red', label=tacBName)
plt.ylim(0.0, 0.05)
plt.xlabel("instances sorted by time")
plt.ylabel("time [s]")
plt.legend()
plt.savefig(f"{noext}_ranked_times_linearscale.png", dpi=200)
plt.ylim(0.0001, 1500)
plt.yscale("log")
plt.savefig(f"{noext}_ranked_times_logscale.png", dpi=200)


# sorted cumulative running time plot
plt.figure()
plt.plot(sorted_prefix_sums([tA for tA, tB in tuples]), color='gray', label=tacAName)
plt.plot(sorted_prefix_sums([tB for tA, tB in tuples]), color='red', label=tacBName)
plt.xlabel("instances sorted by time")
plt.ylabel("cumulative time [s]")
plt.legend()
plt.ylim(0, 500)
plt.savefig(f"{noext}_ranked_times_cumulative_linearscale.png", dpi=200)
plt.yscale("log")
plt.ylim(0.0001, 2000)
plt.savefig(f"{noext}_ranked_times_cumulative_logscale.png", dpi=200)

# tacA time vs tacB time scatter plot
plt.figure()

X = [0.001 if x == 0 else x for x, y in tuples]
Y = [0.001 if y == 0 else y for x, y in tuples]

plt.xlabel(f"running time of {tacAName}[s]")
plt.ylabel(f"running time of {tacBName}[s]")
plt.plot([0.0001, 10000], [0.0001, 10000], color='red', label='same running time')
plt.scatter(X, Y, marker='.', color='blue', label='measurement point')
plt.legend()
plt.xlim(0, 15)
plt.ylim(0, 15)
plt.savefig(f"{noext}_scatter_linearscale.png", dpi=200)
plt.xlim(0.0005, 1500)
plt.ylim(0.0005, 1500)
plt.xscale("log")
plt.yscale("log")
plt.savefig(f"{noext}_scatter_logscale.png", dpi=200)
