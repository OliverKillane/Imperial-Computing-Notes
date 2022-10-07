#!/bin/bash
# Reformats every file in the repository using latexindent

find .. -type f -name '*.tex' -print0 | 
while IFS= read -r -d '' file; do
    printf '%s\n\n' "$file"
    latexindent -w "$file"
done