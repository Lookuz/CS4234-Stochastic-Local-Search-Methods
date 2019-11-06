from subprocess import Popen, PIPE, call, run
from os import listdir
from os.path import isfile, join

files = listdir("tsptests/")

# Do compilation
call(["g++", "-O2", "-std=gnu++17", "-o", "tsp0.out", "tsp0.cpp"])
try:
	f = open("tsp0.out", 'r')
	print("Found: tsp0.out")
except FileNotFoundError:
	print("Error: Cannot find executable tsp0.out")


# Run all test files
for file in files:
	p = Popen(["./tsp0.out"], stdin=PIPE)
	print("Running with input: ", file)
	f = open("tsptests/" + file, "rb").read()
	p.communicate(input=f)

