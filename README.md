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