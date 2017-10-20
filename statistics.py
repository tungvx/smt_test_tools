import csv
import sys
import os
import ntpath
import itertools
import re
import math

UNSOUND="unsound"
NUMBER="Number"
CPU="CPU time"
CPUS="CPUs"
WALL="Wall"
TIME="time"
TIMEOUT="Timed out"
PROBLEM="Problem"
RAW="RAW"
ALL = ["sat", "unsat", "unknown"]
ALLTEXT = "-".join(ALL)

RESULT = "veriT result"
STATUS="status"

def to_tex(text):
	return text.replace("_", "\_").replace("\n", "\n\n")


def gen_report(files, shortfiles, gen_bar_charts):
	results = {}

	outputs = [UNSOUND]

	for file in files:
		results[file] = {UNSOUND:{NUMBER:0,CPU:0,WALL:0, CPUS:[]}, RAW:{}, ALLTEXT:{}}
		with open(file) as fin:
			reader=csv.DictReader(fin, skipinitialspace=True, quotechar="\"")
			for row in reader:
				# print row
				if not row[RESULT]:
					row[RESULT] = TIMEOUT

				results[file][RAW][row[PROBLEM]]=row

				if (row[STATUS]=="sat" and row[RESULT]=="unsat") or (row[STATUS]=="unsat" and row[RESULT]=="sat"):
					results[file][UNSOUND][NUMBER] += 1
					results[file][UNSOUND][CPU] += float(row[CPU])
					results[file][UNSOUND][WALL] += float(row[TIME])

				if row[RESULT] not in results[file]:
					results[file][row[RESULT]] = {}

				if row[RESULT] not in outputs:
					outputs.append(row[RESULT])

				try:
					results[file][row[RESULT]][NUMBER]+=1
				except Exception:
					results[file][row[RESULT]][NUMBER] = 1

				try:
					results[file][row[RESULT]][CPU]+=float(row[CPU])
				except Exception:
					results[file][row[RESULT]][CPU] = float(row[CPU])

				try:
					results[file][row[RESULT]][CPUS].append(float(row[CPU]))
				except Exception:
					results[file][row[RESULT]][CPUS] = [float(row[CPU])]


				if row[RESULT] in ALL:
					try:
						results[file][ALLTEXT][CPUS].append(float(row[CPU]))
					except Exception:
						results[file][ALLTEXT][CPUS] = [float(row[CPU])]					

					try:
						results[file][ALLTEXT][CPU]+=float(row[CPU])
					except Exception:
						results[file][ALLTEXT][CPU] = float(row[CPU])


				try:
					results[file][row[RESULT]][WALL]+=float(row[TIME])
				except Exception:
					results[file][row[RESULT]][WALL] = float(row[TIME])

	for file in files:
		for output in outputs:
			if output not in results[file]:
				results[file][output] = {NUMBER: 0, CPU: 0, CPUS:[],WALL:0}

	differences = {}
	differences_keys = []
	def gen_differences(file1, file2, key):
		for problem, result1 in results[file1][RAW].iteritems():
			result2 = results[file2][RAW][problem]
			subkey = result1[RESULT]+" - "+result2[RESULT]
			if subkey not in differences_keys:
				differences_keys.append(subkey)

			try:
				differences[key][subkey] += 1
			except Exception:
				differences[key][subkey] = 1
				
	for file1, file2 in itertools.combinations(files, 2):
		key = shortfiles[file1]+" - " + shortfiles[file2]
		differences[key] = {}
		gen_differences(file1, file2, key)


	# for output in outputs:
	# 	print "\t",output, "\tCPU", "\tWall",

	# print ("")
	# for file in files:
	# 	# print (ntpath.basename(file)), ":"
	# 	print ((file), ":")
	# 	for output in results[file]:
	# 		if output in outputs:
	# 			print ("\t", output, ":", \
	# 							 "\t%s:" % NUMBER, results[file][output][NUMBER], \
	# 							"\t%s:" % CPU, results[file][output][CPU], \
	# 							"\t%s:" % WALL, results[file][output][WALL])

	# plot average of times:
	import matplotlib.pyplot as plt

	newoutputs = [output for output in outputs if output != TIMEOUT]

	newoutputs.append(ALLTEXT)


	pos = list(range(len(newoutputs)))
	width = 0.25


	# Create a bar with pre_score data,
	# in position pos,
	def gen_charts(data, label, outfile):
		fig, ax = plt.subplots(figsize=(10,5))
		for i, file in enumerate(files):
			# print i, file, [results[file][output][CPU] for output in newoutputs]
			plt.bar([p + width*i for p in pos],
			        #using df['pre_score'] data,
			        data[file],
			        # of width
			        width,
			        # with alpha 0.5
			        alpha=0.5,
			        # with label the first value in first_name
			        label=file)

		ax.set_xticks([p + 1 * width for p in pos])
		ax.set_xticklabels(newoutputs)
		ax.set_ylabel(label)
		plt.legend([os.path.splitext(ntpath.basename(file))[0] for file in files], loc='upper left')

		plt.grid()
		fig.savefig(outfile, bbox_inches='tight')
		plt.clf()
		# import webbrowser
		# webbrowser.open_new(outfile)

	if gen_bar_charts:
		import numpy as np

		chart_datas = [({file: [results[file][output][CPU] for output in newoutputs] for file in files}, "CPU time", "CPU.pdf"),
				 ({file: [np.mean(np.array(results[file][output][CPUS])) for output in newoutputs] for file in files}, "Average CPU time", "A-CPU.pdf"),
				 ({file: [np.median(np.array(results[file][output][CPUS])) for output in newoutputs] for file in files}, "Median CPU time", "M-CPU.pdf"),
				 ({file: [np.std(np.array(results[file][output][CPUS])) for output in newoutputs] for file in files}, "Standard Deviation CPU time", "STD-CPU.pdf")]

		for (data, label, outfile) in chart_datas:
			gen_charts(data, label, outfile)
	# exit(1)

	def gen_scatter(x, y, xlabel, ylabel, outfile):
		fig = plt.figure()
		ax = plt.gca()
		ax.set_aspect('equal', adjustable='box')
		ax.plot(x ,y, 'o', c='blue', markeredgecolor='none', ms=2)
		ax.set_yscale('log')
		ax.set_xscale('log')
		plt.xlabel(xlabel, fontsize=18)
		plt.ylabel(ylabel, fontsize=18)
		plt.grid()
		# axes_min = min([min(x), min(y)])
		# print axes_min
		axes_min = pow(10, math.floor(math.log10(min([min(x), min(y)]))))
		axes_max = pow(10, math.ceil(math.log10(max([max(x), max(y)]))))
		# print axes_min
		# exit()
		# axes_min = 0.001
		plt.ylim(ymin=axes_min, ymax=axes_max)
		plt.xlim(xmin=axes_min, xmax=axes_max)
		ax.plot([0, 1], [0, 1], transform=ax.transAxes, ls='--', lw=0.5)

		fig.savefig(outfile, bbox_inches='tight')
		plt.clf()
		# import webbrowser
		# webbrowser.open_new(outfile)

	def gen_scatters(file1, file2, label1, label2, outfile):
		x = [] 
		y = []
		for problem, result1 in results[file1][RAW].iteritems():
			result2 = results[file2][RAW][problem]
			x.append(float(result1[CPU]))		
			y.append(float(result2[CPU]))		

		gen_scatter(x, y, label1, label2, outfile)

	# gen_scatters(files[0], files[1])
	scatters_figs=[]
	for file1, file2 in itertools.combinations(files, 2):
		label1 = shortfiles[file1]
		label2 = shortfiles[file2]
		outfile=label1 + "vs"+label2 +".pdf"
		gen_scatters(file1, file2, label1,label2, outfile)
		scatters_figs.append(outfile)


	# output latex table:


	# table of summary
	f.write("\\begin{table}[H]\n")
	f.write("\centering\n")
	f.write("\\resizebox{\columnwidth}{!}{\n")
	f.write("\\begin{tabular}{@{}"+"|".join(["r"]*(len(outputs)*3+1))+"@{}}\n")
	f.write("\\hline\n")
	# titles of tabular
	header = ["\multirow{2}{*}{Tool}"]
	for output in outputs:
		header.append("\multicolumn{3}{|c}{"+output+"}")
	f.write("&".join(header));
	f.write("\\\\\\cline{2-"+str(len(outputs)*3+1)+"}\n")

	subheader = [""]
	for output in outputs:
		subheader.append("No.")
		subheader.append("CPU")
		subheader.append("Wall")
	f.write("&".join(subheader));
	f.write("\\\\\\hline\n")

	# print outputs
	for file in files:
		file_results = [to_tex(shortfiles[file])]
		for output in outputs:
			try:
				file_results.append(str(results[file][output][NUMBER]))
				file_results.append(str(round(results[file][output][CPU], 2)))
				file_results.append(str(round(results[file][output][WALL], 2)))
			except:
				file_results.append("0") 
				file_results.append("0.00") 
				file_results.append("0.00") 
		f.write("&".join(file_results))
		f.write("\\\\\\hline\n");

	f.write("\end{tabular}\n")
	f.write("}\n" )
	f.write("\caption{Comparisons between tools}\n")
	f.write("\\end{table}\n")


	# table of difference
	f.write("\\begin{table}[H]\n")
	f.write("\centering\n")
	f.write("\\resizebox{\columnwidth}{!}{\n")
	f.write("\\begin{tabular}{@{}"+"|".join(["r"]*(len(differences)+1))+"@{}}\n")
	f.write("\\hline\n")
	# titles of tabular
	header = ["Results"]
	for pair in differences:
		header.append(to_tex(pair))
	f.write("&".join(header));
	f.write("\\\\\\hline\n")

	# print outputs
	for differences_key in differences_keys:
		difference = [differences_key]
		for pair, difference_val in differences.iteritems():
			try:
				difference.append(str(difference_val[differences_key]))
			except:
				difference.append("0")  
		f.write("&".join(difference))
		f.write("\\\\\\hline\n");

	f.write("\end{tabular}\n")
	f.write("}\n" )
	f.write("\caption{Differences between tools}\n")
	f.write("\\end{table}\n")


	if gen_bar_charts:
		for (data, label, outfile) in chart_datas:
			f.write("\\begin{figure}[H]\n")
			f.write("\includegraphics[width=\columnwidth]{"+outfile+"}\n")
			f.write("\\end{figure}\n")

	for outfile in scatters_figs:
		f.write("\\begin{figure}[H]\n")
		f.write("\includegraphics[width=\columnwidth]{"+outfile+"}\n")
		# f.write("\\caption{"+os.path.splitext(outfile)[0]+"}\n")
		f.write("\\end{figure}\n")

def readme(path):
	try:
		return to_tex(open(path, "r").read())
	except Exception:
		return ""	

need_proccess = []

if len(sys.argv)==3 and os.path.isdir(sys.argv[1]) and os.path.isdir(sys.argv[2]):
	readme1 = readme(os.path.join(sys.argv[1], "README"))
	readme2 = readme(os.path.join(sys.argv[2], "README"))
	readme = sys.argv[1]+":\n\n"+readme1+"\n\n"+sys.argv[2]+":\n\n"+readme2
	for filename in os.listdir(sys.argv[1]):
		if filename.endswith("csv"):
			files = []
			shortfiles = {}
			file1=os.path.join(sys.argv[1], filename)
			file2=os.path.join(sys.argv[2], filename)
			files.append(file1)
			files.append(file2)
			try:
				shortfiles[file1]= re.search("\{\{(.*)\}\}", readme1).group(1) + "-" + os.path.splitext(ntpath.basename(file1))[0]
			except Exception:				
				shortfiles[file1]= os.path.splitext(ntpath.basename(file1))[0]

			try:
				shortfiles[file2]=re.search("\{\{(.*)\}\}", readme2).group(1) + "-" + os.path.splitext(ntpath.basename(file2))[0]
			except Exception:
				shortfiles[file2]=os.path.splitext(ntpath.basename(file2))[0]

			need_proccess.append((files, shortfiles))
else:
	files = []
	shortfiles = {}
	for argv in sys.argv[1:]:
		if os.path.isfile(argv):
			files.append(argv)
			shortfiles[argv]=os.path.splitext(ntpath.basename(argv))[0]
		elif os.path.isdir(argv):
			for filename in os.listdir(argv):
				if filename.endswith("csv"):
					file=os.path.join(argv, filename)
					files.append(file);
					shortfiles[file]=os.path.splitext(ntpath.basename(file))[0]

	readme = readme("README")

	need_proccess.append((files, shortfiles))

# print need_proccess
# exit()

if not need_proccess:
	print ("Provide input csv files or folders containing csv files")
	exit()

f = open("report.tex", "w+")
f.write("\\documentclass{article}\n")
f.write("\\usepackage{graphicx}\n")
f.write("\\usepackage{multirow}\n")
f.write("\usepackage{hyperref}\n\hypersetup{\ncolorlinks,\ncitecolor=black,\nfilecolor=black,\nlinkcolor=black,\nurlcolor=black\n}\n")
f.write("\\begin{document}\n")
f.write("\\title{Report on Experiments}\n")
f.write("\\maketitle\n")


f.write(readme)

f.write("\\tableofcontents\n");

for files, shortfiles in need_proccess:
	f.write("\clearpage\n")
	f.write("\section{Comparing "+" ".join([to_tex(file) for file in files])+"}\n")
	gen_report(files, shortfiles, len(need_proccess)==1)

f.write("\end{document}\n" )

f.close()

# compile report.tex and open it
os.system("pdflatex report.tex")
import webbrowser
webbrowser.open_new("report.pdf")