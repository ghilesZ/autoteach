# moulinette
 
This script automates the process of gradin several submissions,
packed within a zip archive (as downloaded from moodle):

```sh
moulinette grade-book.csv submission.zip echo 0
```

The `moulinette` command take three arguments:
- a submission directory (.zip)
- a csv file to complte (.csv)
- an actual command line to launch on all directories that must respect the specification below:

It must return:
- 0 when everything went well
- 1 for an internal error
- 2 for students errors
- 3 for students suspicion of cheat

It creates a directory `submissions_date` with three sub-directories
- `to_process` that are the files that are yet to grade
- `done` that are the files that were successfully graded
- `manual_grading` that are the files that could no be graded automatically because something went wrong