#!/usr/bin/env python3

import csv
import sys
import unicodedata

# This script takes as argument a CSV file, a student name, a grade,
# and a column number. It then tries to match the name to an actual id
# and outputs the corresponding line in the CSV

if len(sys.argv) <= 4:
    print("gradeCSV expect 4 arguments, a csv file to complete, a\
 student name, a grade, and column number")
    exit(1)

filename = sys.argv[1]
studentname = sys.argv[2]
grade = sys.argv[3]
col = sys.argv[4]

def normalize(str):
    # Translation map for corrupted characters
    translation_map = {
        "├л" : "ë",
        "├о" : "î",
        "├з" : "ç",
        "├и" : "è",
        "├й" : "é",
        "├д" : "ä",
        "├п" : "ï",
        "├в" : "â",
        "├е" : "å"
    }
    for corrupted, correct in translation_map.items():
        str = str.replace(corrupted, correct)
    return str.replace("\"","").replace(" ","_").replace("'","")

with open(filename, newline='') as csvfile:
    form = csv.reader(csvfile, delimiter=',', quotechar='|')
    found=False
    for row in form:
        fstname=normalize(row[1])
        lastname=normalize(row[2])
        dirname=fstname+"_"+lastname
        if (dirname == normalize(studentname)):
            found=True
            row[int(col)-1]=grade
            print(', '.join(row))
            exit(0)
    if not found:
        print ("could not found id for: "+sys.argv[2])
        exit(1)
