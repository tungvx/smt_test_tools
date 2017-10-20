import csv
import sys
import os

UNSOUND="unsound"
NUMBER="Number"
CPU="CPU time"
WALL="Wall"
TIME="time"
TIMEOUT="Timed out"

RESULT = "veriT result"
STATUS="status"
PROBLEM="Problem"

def comp_criteria(result1, result2):
	return result1 != result2 and (result1 in ["sat", "unsat"] or result2 in ["sat", "unsat"])

data1={}
with open(sys.argv[1]) as fin:
	reader=csv.DictReader(fin, skipinitialspace=True, quotechar="'")
	for row in reader:
		data1[row[PROBLEM]]=row

data2={}
with open(sys.argv[2]) as fin:
	reader=csv.DictReader(fin, skipinitialspace=True, quotechar="'")
	for row in reader:
		data2[row[PROBLEM]]=row

differences = []
x = []
y = []
for problem, results_1 in data1.items():
	results_2 = data2[problem]
	# if results_1[RESULT] == results_2[RESULT]:
	
	x.append(results_1[CPU])
	y.append(results_2[CPU])

	if comp_criteria(results_1[RESULT], results_2[RESULT]):
		same = False
		differences.append((problem, results_1, results_2))

if differences:
	for difference in differences:
		print (difference)
	print "There are", len(differences), "different results"
else:
	print "Same results"

import matplotlib.pyplot as plt
import pylab
from matplotlib import rc
rc('font',**{'family':'sans-serif','sans-serif':['Helvetica']})
rc('text', usetex=True)

fig = plt.figure()
ax = plt.gca()
ax.plot(x ,y, 'o', c='blue', markeredgecolor='none', ms=2)
ax.set_yscale('log')
ax.set_xscale('log')
ax.set_aspect('equal', adjustable='box')
plt.ylim(ymin=0.05)
plt.xlim(xmin=0.05)
plt.grid()
ax.plot([0, 1], [0, 1], transform=ax.transAxes)
plt.xlabel(os.path.splitext(sys.argv[1])[0], fontsize=18)
plt.ylabel(os.path.splitext(sys.argv[2])[0], fontsize=18)
# plt.show()
outfile=os.path.splitext(sys.argv[1])[0] + "vs"+os.path.splitext(sys.argv[2])[0] +".pdf"
fig.savefig(outfile, bbox_inches='tight')
import webbrowser
webbrowser.open_new(outfile)