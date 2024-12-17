#!/bin/bash

install_script() {
    local script_name="$1"
    chmod +x "$script_name"
    cp "$script_name" ~/.local/bin/$(basename ${script_name%.*})
}

install_script "studentize/studentize.sh"
install_script "gradify/gradify.sh"
install_script "moulinette/moulinette.sh"
install_script "moulinette/gradeCSV.py"
