#!/bin/bash

# Check for arguments
if [ "$#" -ne 2 ]; then
    echo "Usage: $0 <source> <destination>"
    exit 1
fi

# Variables
SRC="$1"
DST="$2"

# This function takes as input the path to the file to be
# processed. It removes inplace:
#  - Lines containing "sujet"
#  - Lines containing "/sujet"
#  - Blocks of text between lines containing "corrige" and "/corrige" (inclusive).
apply_studentize() {
    local target="$1"
    sed -i \
        -e '/sujet/d' \
        -e '/\/sujet/d' \
        -e '/corrige/,/\/corrige/d' "$target"
}

if [ -d "$SRC" ]; then
    # If SRC is a directory

    # Recreate the destination directory from scratch
    rm -rf "$DST"
    mkdir "$DST"

    # Copy the source directory
    cp -R "$SRC" "$DST"

    # Apply studentize logic to text files
    find "$DST" -type f -exec file --mime-type {} \; | awk -F: '/text\// {print $1}' | while read -r file; do
        apply_studentize "$file"
    done

    # Build the archive
    subdir="$DST/$(basename "$SRC")"
    pushd "$subdir" > /dev/null

    # Check if a Makefile exists and if the `make` command works
    if [ -f Makefile ]; then
        echo "Makefile found, running 'make' command..."
        if ! make --dry-run > /dev/null 2>&1; then
            echo "Error: 'make' command failed in $subdir. Exiting."
            popd > /dev/null
            exit 1
        fi

        # Check if 'make test' is a valid target
        if make --dry-run test > /dev/null 2>&1; then
            echo "'make test' target found, running 'make test'..."
            if ! make test; then
                echo "Error: 'make test' failed in $subdir. Exiting."
                popd > /dev/null
                exit 1
            fi
        else
            echo "'make test' target not found, skipping test."
        fi

        # Check if 'make clean' is a valid target
        if make --dry-run clean > /dev/null 2>&1; then
            echo "'make clean' target found, running 'make clean'..."
            if ! make clean > /dev/null 2>&1; then
                echo "Error: 'make clean' failed in $subdir. Exiting."
                popd > /dev/null
                exit 1
            fi
        else
            echo "'make clean' target not found, skipping clean."
        fi
    fi


    tarname="$DST.tgz"
    tar -czf "$tarname" *
    mv "$tarname" "../../"
    popd > /dev/null
    rm -r "$DST"
    echo "Directory processed and archive created: $tarname"

elif [ -f "$SRC" ]; then
    # If SRC is a single file

    # Apply studentize logic directly to the file and save it to DST
    cp "$SRC" "$DST"
    apply_studentize "$DST"

    echo "File processed and saved as: $DST"

else
    echo "Error: $SRC is not a valid file or directory. Exiting."
    exit 1
fi
