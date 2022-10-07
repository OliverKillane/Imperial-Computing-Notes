#!/bin/bash
# Creates a new directory in chapters/ for a new chapter.

directory=$(basename "$PWD")
chaptername="$1"

cd ..
if [ $(basename "$PWD") == "Imperial-Computing-Year-3-Notes" ]; then
    echo "✅ Directory Check "
else
    echo "❌ Must be in Imperial year 3 notes directory"
    exit
fi
cd "$directory"

echo "Creating chapter $chaptername"

mkdir "$chaptername" && 
cd "$chaptername" && 
mkdir "diagrams" && 
touch "diagrams/.gitkeep" && 
mkdir "images" && 
touch "images/.gitkeep" && 
mkdir "code" && 
touch "code/.gitkeep" && 
touch "$chaptername.tex" && 
echo "\chapter{$chaptername}" > "$chaptername.tex" && 
echo "Complete! Please insert: \addchapter{$chaptername} into the main notes tex"

