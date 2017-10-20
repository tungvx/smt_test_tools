from constants import *
from configure import *
import sys
import os

with open(config[RESULT_FILE], "w+", 1) as outfile:
	outfile.write(",".join(HEADERS)+"\n")

	for idx in range(int(sys.argv[1])):
		current_out_path = str(idx)+".csv"
		outfile.write(open(current_out_path, "r").read())
		os.remove(current_out_path)
