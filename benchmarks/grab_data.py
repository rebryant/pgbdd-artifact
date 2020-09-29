#!/usr/bin/python

#####################################################################################
# Copyright (c) 2020 Marijn Heule, Randal E. Bryant, Carnegie Mellon University
# Last edit: Sept. 29, 2020
# 
# Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
# associated documentation files (the "Software"), to deal in the Software without restriction,
# including without limitation the rights to use, copy, modify, merge, publish, distribute,
# sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
# 
# The above copyright notice and this permission notice shall be included in all copies or
# substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
# NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
# DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
# OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
########################################################################################


import sys
import re

# Generate tabbed data of numbers specified on target lines
# Extracts problem size from file name

triggers = [
    # Phrase in data file, Title
    ("Total Clauses", "Clauses"),
    ("Elapsed time for SAT", "Seconds")
]

headers = ["Problem"] + [header for (phrase, header) in triggers]

def trim(s):
    while len(s) > 0 and s[-1] == '\n':
        s = s[:-1]
    return s

dashOrDot = re.compile('[.-]')
def ddSplit(s):
    return dashOrDot.split(s)

colonOrSpace = re.compile('[\s:]+')
def lineSplit(s):
    return colonOrSpace.split(s)

# Look for first field that can be parsed as number
# Return field
def firstNumberAsString(fields):
    for field in fields:
        try:
            val = float(field)
            return field
        except:
            try:
                val = int(field)
                return field
            except:
                continue
    return ""


# Extract clause data from log.  Turn into something useable for other tools
def extract(fname):
    # Try to find size from file name:
    fields = ddSplit(fname)
    prob = firstNumberAsString(fields)
    if prob == "":
        print("Couldn't extract problem size from file name '%s'" % fname)
        return None
    try:
        f = open(fname, 'r')
    except:
        print("Couldn't open file '%s'" % fname)
        return None
    strDict = { header : "" for header in headers }
    strDict["Problem"] = prob
    for line in f:
        line = trim(line)
        for (phrase, header) in triggers:
            if phrase in line:
                fields = lineSplit(line)
                strDict[header] = firstNumberAsString(fields)
    f.close()
    return strDict

def usage(name):
    print("Usage: %s file1 file2 ..." % name)
    sys.exit(0)

def showList(ls):
    print "\t".join(ls)

def run(name, args):
    if len(args) < 1:
        usage(name)
    showList(headers)
    for fname in args:
        strDict = extract(fname)
        strList = [strDict[header] for header in headers]
        showList(strList)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

            
        
                
