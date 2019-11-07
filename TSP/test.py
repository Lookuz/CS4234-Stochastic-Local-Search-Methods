#!/usr/bin/env python3

'''
Run command '/test.py' to run this script
Please make sure you have "progress" package installed

'''

from progress.bar import Bar
from subprocess import Popen, PIPE, call, run
from os import listdir
from os.path import isfile, join
import math

def avg(lst):
	return sum(lst)/len(lst)

def bold(string):
	return '\033[1m' + string + '\033[0m'

# 𝑥=(Val−Opt)/(Naive−Opt). 
#(In the special case that Naive=Opt, define 𝑥=0 if Val=Opt, and 𝑥=∞ if Val>Opt.)
def kattisScore(val, opt, naive):
	if naive == opt:
		if val == opt:
			x = 0
		elif val > opt:
			x = float('inf')
	else:
		x = (val-opt)/(naive-opt)
	return 0.02 ** x

def percentAboveOpt(val, opt):
	if opt == 0:
		if val == 0:
			return 100
		else:
			return float('-inf')
	else:
		return val*100/opt

def printResults(scores, averagePercents):
	i = 0
	kattisScores = []
	for scoreDict in scores:
		scoreList = []
		print(bold(f"Iteration {i}: "))
		for file, score in scoreDict.items():
			print(file, ": ", round(score, 4))
			scoreList.append(score)
		print("")
		kattisScore = round(avg(scoreList)*50, 4)
		kattisScores.append(kattisScore)
		print("Kattis score: ", kattisScore)
		print("Average percent above OPT: ", averagePercents[i])
		print("\n")
		i += 1

	print(bold("Summary of All Iterations"))
	print("Average of all Kattis Scores: ", avg(kattisScores))
	print("Average of all percent above OPT: ", avg(averagePercents))

sourceFile = input("Please enter source filename (Just press enter for tsp0.cpp): ")
if sourceFile == "":
	sourceFile = "tsp0.cpp"
naiveSourceFile = "naive_tsp.cpp"

files = listdir("tsptests/")

# Do compilation
print("Compiling...")
call(["g++", "-O2", "-std=gnu++17", "-o", "tsp0.out", sourceFile])
call(["g++", "-O2", "-std=gnu++17", "-o", "naive_tsp", naiveSourceFile])
print("Compiled ", sourceFile)
print("Compiled ", naiveSourceFile)
try:
	f = open("tsp0.out", 'r')
	f = open("naive_tsp", 'r')
	print("Found: tsp0.out")
	print("Found: naive_tsp")
except FileNotFoundError:
	print("Error: Cannot find executable tsp0.out or naive_tsp")

n = int(input("How many test iterations? "))

skippedTestFiles = set()

naiveLengths = dict()
bar = Bar('Testing naive tsp', max=len(files))
for file in files:
		# Run naive tsp
		p = Popen(["./naive_tsp"], stdin=PIPE, stdout=PIPE)
		f = open("tsptests/" + file, "rb").read()
		out, err = p.communicate(input=f)
		naiveLength = int(out.decode('utf-8'))
		naiveLengths[file] = naiveLength
		bar.next()
bar.finish()
# print(naiveLengths)

scores = []
averagePercents = []
#run tsp0
for i in range(n):
	lengths = []
	percents = []
	score = {}

	bar = Bar(f'Testing iteration {i}', max=len(files))

	# Run all test files
	for file in files:
		p = Popen(["./tsp0.out"], stdin=PIPE, stdout=PIPE)
		f = open("tsptests/" + file, "rb").read()
		out, err = p.communicate(input=f)
		result = out.decode('utf-8').split(' ')
		# if result[1] == 'nan':
		# 	bar.next()
		# 	continue
		length = int(result[0])
		optLength = int(result[1])

		try:
			lengths.append(length)
			percents.append(percentAboveOpt(length, optLength))
			score[file] = kattisScore(length, optLength, naiveLengths[file])
		except ValueError:
			skippedTestFiles.add(file)
		bar.next()


	scores.append(score)
	# Show results
	bar.finish()
	if len(percents) == 0:
		print(f"Test iteration {i} score: No valid files")
	else:
		averagePercent = sum(percents)/len(percents)
		# print(f"Test iteration {i} average percent above OPT: ", averagePercent)
		averagePercents.append(averagePercent)

print("\n\nReport: \n\n")
printResults(scores, averagePercents)
# if len(averagePercents) == 0:
# 	print("Final Average Percent Above OPT: Can't be calculated - no valid iterations")
# else:
# 	print("Final Average Percent Above OPT: ", sum(averagePercents)/len(averagePercents))





