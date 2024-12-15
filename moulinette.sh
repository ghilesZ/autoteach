#!/bin/bash

# Check if usage is valid
if [ $# -lt 3 ]; then
    echo "Usage: $0 <file1> <file2> <command to execute> [ command options ]"
    echo "I need a submission directory (.zip) and a csv file to complete (.csv) and a command to launch on all directories"
    exit 1
fi

zip_file=""
csv_file=""
command="${@:3}"

# Check the file extensions of the provided arguments
for file in "${@:1:3}"; do
    if [[ "$file" == *.zip ]]; then
        zip_file="$file"
    elif [[ "$file" == *.csv ]]; then
        csv_file="$file"
    fi
done

# Check if both variables were assigned
if [ -z "$zip_file" ] || [ -z "$csv_file" ]; then
    echo "Error: Please provide one .zip file and one .csv file."
    exit 1
fi

# Check if both actually exist
[ ! -f "$zip_file" ] && { echo "zip file $zip_file not found!"; exit 1; }
[ ! -f "$csv_file" ] && { echo "csv file $csp_file not found!"; exit 1; }

# Create a directory to store the results of the autograding
printf -v date '%(%Y-%m)T'
destination=submissions_"$date"
mkdir -p "$destination"
# when things go bad, faulty submissions are copied here
mkdir -p "$destination"/manual_grading
#graded
mkdir -p "$destination"/done
# yet to grade
unzip -o -q -d "$destination"/to_process "$zip_file"

# Moodle sometimes ends directory names with an '_', sometimes not
# Maybe this is a moodle-exam behaviour?
# Anyway this regexp accepts both
dirregexp="(^.*)_[0-9]+_assignsubmission_file_?"

# erase potential previous log
rm -f $destination/grades.log

# Assignment name to search for
assignment_name=$(echo "$zip_file" | awk -F'-' '{print $2}')

# Get the header row and find the column number of the assignment
header=$(head -n 1 "$csv_file")
columns=$(echo "$header" | tr ',' '\n')
column_number=$(echo "$columns" | grep -n "$assignment_name" | cut -d ':' -f 1)

NB_OK=0
NB_BAD=0
NB_ERROR=0
NB=0

TOTAL=$(ls -d "$destination"/to_process/*/ -1 | wc -l)
for student in "$destination"/to_process/*; do
    dirname=$(basename "$student")
    if [[ "$dirname" =~ $dirregexp ]]; then
        ((NB++))
        echo -en "\r\033[K$NB/$TOTAL"
        # if the student has already been graded (on a previous
        # interupted run), we skip it
        if [ -d "$destination/done/$dirname" ]; then
            ((NB_OK++))
            continue
        fi
        if [ -d "$destination/manual_grading/$dirname" ]; then
            ((NB_BAD++))
            continue
        fi
        name="${BASH_REMATCH[1]}"
        printf "$name\n" >> "$destination"/grades.log
        eval $command '"$student"' >> "$destination"/grades.log
        ret=$?
        g=$(tail -n 1 "$destination"/grades.log)
        if [[ $ret == 0 ]]; then
            gradeCSV "$csv_file" "$name" $g $column_number >> "$destination"/grades.csv
            ret=$?
            if [[ $ret == 0 ]]; then
                ((NB_OK++))
                mv "$student" $destination/done/
            else
                ((NB_ERROR++))
            fi
        else
            ((NB_BAD++))
            mv "$student" $destination/manual_grading/
        fi
    else
        echo "wrong dir name $dirname"
        exit
    fi
done

echo -en "\r\033[K"
echo "$NB_OK successfully graded"
echo "$NB_ERROR require fixing the script"
echo "$NB_BAD require manual grading"
echo "Results are in the $destination directory"
