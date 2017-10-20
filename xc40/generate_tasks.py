import os
import sys

SMT2 = ".smt2"

smt2Files = []
for root, dirnames, filenames in os.walk(sys.argv[1]):
	for filename in filenames:
		if filename.endswith(SMT2):
			smt2Files.append(os.path.abspath(os.path.join(root, filename)))

with open("tasks.dict", "w+") as tasks:
	tasks.write("{\n")
	for idx, smt2File in enumerate(smt2Files):
		tasks.write(str(idx) + "\t: " + repr(smt2File) + ",\n")
	tasks.write("}")