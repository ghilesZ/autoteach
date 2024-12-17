# Gradify

This script processes a set of grades for questions, where each grade
is given as a fraction between 0 and 1, and scales them according to
maximum grades defined in a separate file. The script outputs the
scaled grades for each question and calculates the total score. It can
accept grades from either a file or standard input.

## Usage
```bash
./gradify.sh <question_file> [grades_file]
```

## Example

`scale.txt` :
```
Q1:5
Q2:10
Q3:3
```

`grades.txt` :
```
Q1:0.8
Q2:0.6
Q3:1
```

```./script.sh questions.txt grades.txt```

```
Q1:4.00
Q2:6.00
Q3:3.00
13.00
```