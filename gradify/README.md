# Gradify

This script processes a set of grades for questions, where each grade
is given as a fraction between 0 and 1, and scales them according to
maximum grades defined in a separate file. The script outputs the
scaled grades for each question and calculates the total score. It can
accept grades from either a file or standard input.

It can also display the total grade if the -total option is used.

## Usage
```sh
./gradify.sh <scale> [grades_file] [-total]
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

```./gradify.sh scale.txt grades.txt```

```
Q1:4.00
Q2:6.00
Q3:3.00
```

Or,  from standard input:

```sh
echo -e "q2:0\nq3:0.5"| ./gradify.sh scale.txt  -total
```
which outputs:
```
q2:0.00
q3:1.5
1.5
```
