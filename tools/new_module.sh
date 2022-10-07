#!/bin/bash
# Creates a new module with required tex file title page and chapters.

# Format Contants




code='00000'
module='New Module'
user='Oliver Killane'
date=$(date +'%d/%m/%y')
help='
Creates a skeleton for notes for a new module
 ...
 ├── {module code} - {module name}
 │   ├── titlepage
 │   │   ├── images
 │   │   │   └── {empty}
 │   │   │
 │   │   └── titlepage.tex
 │   │
 │   ├── {module name}.tex
 │   └── README.md
 |
 ...
 ├── common ── ...
 └── tools  ── ...
'

# Check we are in the correct folder.
directory=$(basename "$PWD")

if [ $(basename "$PWD") == "Imperial-Computing-Year-3-Notes" ]; then
    echo "✅ Directory Check "
else
    echo "❌ Must be in Imperial year 3 notes directory"
    exit
fi

while getopts hm:c:u:d: flag;
do
    case "${flag}" in
        h) echo "$help"; exit;;
        m) module=${OPTARG};;
        c) code=${OPTARG};;
        u) user=${OPTARG};;
        d) date=${OPTARG};;
    esac
done

echo "
User:   $user
Code:   $code
Module: $module
Date:   $date
"

mkdir "$code - $module" && cd "$code - $module" &&
mkdir 'titlepage' && cd 'titlepage' &&
mkdir 'images' &&
echo "
\begin{titlepage}
    \DeclareFixedFont{\modulecodefont}{T1}{ppl}{b}{n}{1.45in}
    \DeclareFixedFont{\moduletitlefont}{T1}{ppl}{b}{n}{0.232in}
    \DeclareFixedFont{\imperialfont}{T1}{ppl}{b}{n}{0.31in}

    % \begin{tikzpicture}
    %     \node[inner sep=0pt, outer sep=0pt, anchor=north east]{
    %     \makebox[\textwidth]{\includegraphics[width=\paperwidth]{titlepage/images/i386 die shot.png}}
    %     };
    % \end{tikzpicture}

    \begin{flushright}
        \modulecodefont $code \\\\
        \vspace{4mm}
        \moduletitlefont $module \\\\
        \vspace{1mm}
        \imperialfont Imperial College London
    \end{flushright}
\end{titlepage}
" > titlepage.tex &&
cd .. &&
echo "
\documentclass{report}
    \title{$code - $module}
    \author{$user}
    \date{$date}

\usepackage[a4paper, total={7in, 10in}]{geometry}
\input{../common/common.tex}

\begin{document}
\include{titlepage/titlepage}

\tableofcontents
\newpage

\end{document}
" > "$code - $module.tex"
