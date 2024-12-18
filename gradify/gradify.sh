#!/bin/bash

# Ensure that at least one argument is given
if [[ $# -lt 1 ]]; then
    echo "Usage: $0 <scale> [grades_file] [-total]"
    exit 1
fi

# Parse the options
TOTAL_OPTION=false
for arg in "$@"; do
    if [[ "$arg" == "-total" ]]; then
        TOTAL_OPTION=true
        break
    fi
done

# Read the question file from the first argument
QUESTION_FILE="$1"

# Check if the question file exists
if [[ ! -f "$QUESTION_FILE" ]]; then
    echo "Error: File '$QUESTION_FILE' not found"
    exit 1
fi

total=0
# Create an associative array to store maximum grades for each question
declare -A max_grades

# Read the question:maximum_grade file and populate the associative array
while IFS=":" read -r question max_grade; do
    max_grades["$question"]="$max_grade"
done < "$QUESTION_FILE"

# Check if a grades file is provided as the second argument
if [[ $# -ge 2 && "$2" != "-total" ]]; then
    GRADES_FILE="$2"

    # Check if the grades file exists
    if [[ ! -f "$GRADES_FILE" ]]; then
        echo "Error: File '$GRADES_FILE' not found"
        exit 1
    fi

    # Read grades from the grades file
    GRADE_INPUT="$GRADES_FILE"
else
    # Read grades from standard input
    GRADE_INPUT="/dev/stdin"
fi

# Read from the grades input, calculate, and output the corresponding grades
while IFS=":" read -r question actual_grade; do
    question=$(echo "$question" | tr -d ' ')
    actual_grade=$(echo "$actual_grade" | tr -d ' ')
    if ! [[ "$actual_grade" =~ ^0*(0(\.[0-9]+)?|1(\.0*)?)$ ]]; then
        echo "Error: Invalid grade '$actual_grade' for question '$question'. Grade must be between 0 and 1." >&2
        continue
    fi
    if [[ -n "${max_grades[$question]}" ]]; then
        max_grade="${max_grades[$question]}"
        result=$(echo "$actual_grade * $max_grade" | bc -l)
        total=$(echo "$total + $result" | bc -l)
        printf "%s:%.2f\n" "$question" "$result"
    else
        echo "Error: No maximum grade found for question '$question'" >&2
    fi
done < "$GRADE_INPUT"

# Print the total only if the -total option is active
if $TOTAL_OPTION; then
    printf "%.2f\n" "$total"
fi
