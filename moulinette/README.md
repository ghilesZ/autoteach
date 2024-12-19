# moulinette
 
This script automates the process of grading several submissions,
packed within a zip archive (as downloaded from moodle) and fills a
grade book in csv format (as downloaded from moodle).

```sh
moulinette grade-book.csv submission.zip -- echo $(( RANDOM % 21 ))
```

The `moulinette` command takes three arguments (the first two are
optional), the third one being separated by `--`:

- a submission directory (.zip)
- a csv file to complte (.csv)
- an actual command line to launch on all directories that must
 respect the specification below.

If the zip/csv files are not given, the current directory is scanned
(not recursively) to find them.

It is also possible to pass a `-timeout n` option which cancels the
grading of a single student after n seconds (in which case it will
have to be manually graded)

Moulinette creates a directory `submissions_date` with:
- file `grades.csv` which is filled with the grades
- file `grades.log` which has some information about the execution
- directory `to_process/` that are the files that are yet to grade
- directory `done/` that are the files that were successfully graded
- directory `manual_grading/` that are the files that could no be graded
  automatically because something went wrong

### grading command
the grading command line must:

- Print on stdout the grade of the student. (It can print some other information, but the last print should be a line containing only the grade)

- have the following return status:
  * 0 when everything went well 
  * 1 for an internal error
  * 2 for students errors
  * 3 for students suspicion of cheat
