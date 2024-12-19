#!/bin/bash

# Check if usage is valid (at least the separator -- and the grading
# command are provided)

if [[ "$#" -lt 2 || "$*" != *--* ]]; then
    echo "Usage: $0 [file1.zip] [file2.csv] -- <command to execute> [ command options ]"
    echo "I need a submission directory (.zip) and a CSV file (.csv), to be given or present in the current directory."
    echo "The '--' delimiter must separate the input files and the command to execute."
    exit 1
fi

# Extract arguments before and after '--'
args_before_command=()
args_after_command=()
found_delimiter=false

for arg in "$@"; do
    if [ "$arg" == "--" ]; then
        found_delimiter=true
        continue
    fi
    if $found_delimiter; then
        args_after_command+=("$arg")
    else
        args_before_command+=("$arg")
    fi
done

if [ "${#args_after_command[@]}" -eq 0 ]; then
    echo "Error: No command specified after '--'."
    exit 1
fi

# Assign files and command
zip_file=""
csv_file=""
command="${args_after_command[@]}"

# Check the file extensions of the provided arguments before '--'
for file in "${args_before_command[@]}"; do
    if [[ "$file" == *.zip ]]; then
        zip_file="$file"
    elif [[ "$file" == *.csv ]]; then
        csv_file="$file"
    fi
done

# If not provided, search for a single .zip file in the current directory
if [ -z "$zip_file" ]; then
    zip_files=( *.zip )
    # Check if the array contains actual files and not the literal pattern
    if [ ${#zip_files[@]} -eq 1 ] && [ -f "${zip_files[0]}" ]; then
        zip_file="${zip_files[0]}"
        echo "Found single .zip file: $zip_file"
    else
        echo "Error: Either no .zip file or multiple .zip files found in the current directory."
        exit 1
    fi
fi

# If not provided, search for a single .csv file in the current directory
if [ -z "$csv_file" ]; then
    csv_files=( *.csv )
    # Check if the array contains actual files and not the literal pattern
    if [ ${#csv_files[@]} -eq 1 ] && [ -f "${csv_files[0]}" ]; then
        csv_file="${csv_files[0]}"
        echo "Found .csv file: $csv_file"
    else
        echo "Error: Either no .csv file or multiple .csv files found in the current directory."
        exit 1
    fi
fi

# Check if both actually exist
[ ! -f "$zip_file" ] && { echo "Error: zip file $zip_file not found!"; exit 1; }
[ ! -f "$csv_file" ] && { echo "Error: csv file $csv_file not found!"; exit 1; }

# Create a directory to store the results of the autograding
printf -v date '%(%Y-%m)T'
destination=submissions_"$date"
mkdir -p "$destination"
# when things go bad, faulty submissions are copied here
mkdir -p "$destination"/manual_grading
# graded
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
        # interrupted run), we skip it
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
