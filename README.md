# autoteach

This repo regroups some scripts that helps automate common teaching
tasks.

## studentize

This script automates the process of creating a "studentized" version
of a source file or directory. It has two modes of operation based on
the type of input:

- If the source is a single file: applies "studentize" transformations
to the file (removing specific patterns and blocks of text).  Saves
the processed file to the specified destination.

- If the source is a directory: copies the directory to the
destination.  applies "studentize" transformations to all text files
in the directory.  If a Makefile exists, it verifies that make can run
without errors. Creates a compressed .tgz archive of the processed
directory.

The studentize transformation removes inplace:
- Lines containing "sujet"
- Lines containing "/sujet"
- Blocks of text between lines containing "corrige" and "/corrige" (inclusive).

For example: 

```coq
Proposition q1 :
  forall a:nat, a * 0 = 0.
Proof.
(* corrige *)
  intros.
  induction a.
  - simpl.
    reflexivity.
  - simpl.
    assumption.
Qed.
(* /corrige *)
(* sujet
   admit.
Admitted.
/sujet*)
```

is rewritten into:

```coq
Proposition q1 :
  forall a:nat, a * 0 = 0.
Proof.
   admit.
Admitted.
```

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