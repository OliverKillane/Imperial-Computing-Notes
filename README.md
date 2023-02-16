# Imperial College year 3 Notes

## What is this repo?
This repo is the collection of notes for my chosen third year modules. 

It is designed as an improvement in quality over the [second year repo](https://github.com/OliverKillane/Imperial-Computing-Year-2-Notes).

## Where are the notes!
- [50008 - Probability and Statistics](50008%20-%20Probability%20and%20Statistics/README.md)
- [60001 - Advanced Computer Architecture](60001%20-%20Advanced%20Computer%20Architecture/README.md)
- [60007 - Theory and Practice of Concurrent Programming](60007%20-%20Theory%20and%20Practice%20of%20Concurrent%20Programming/README.md)
- [60009 - Distributed Algorithms](60009%20-%20Distributed%20Algorithms/README.md)
- [60017 - System Performance Engineering](60017%20-%20System%20Performance%20Engineering/README.md)
- [60023 - Type Systems for Programming Languages](60023%20-%20Type%20Systems%20for%20Programming%20Languages/README.md)
- [60029 - Data Processing Systems](60029%20-%20Data%20Processing%20Systems/README.md)

## How do I build this?
### Dependencies
1. A tex distribution. [See options here](https://www.latex-project.org/get/)

2. Inkscape (required for tikz). Needs to be added to path
```powershell
# Check inkscape is installed and on path
inkscape --version
```

3. [Pygments](https://pygments.org/) - used by minted (code listings), which requires [python & pip](https://www.python.org/downloads/).
```powershell
pip install Pygments
```

4. Correctly configured editor (minted and tikz need shell escape).

5. `latexindent` for code formatting

6. [draw.io](https://app.diagrams.net/) for diagrams. This can also be downloaded.

### My Setup
I am editing on windows 11.
1. Tex Distribution is [MikTex](https://miktex.org/).
2. Inkscape 0.92.4 installed from, their website. `C:\Program Files\Inkscape` added to `Path`.
3. Python 3.10.7 installed with Pip 22.2.2. Pygments 2.13.0 installed.
5. I use wsl as my default terminal, so I run latexindent from there as part of texlive. 
```bash
sudo apt install texlive-extra-utils
```
4. I edit using VSCode using the [Latex Workshop extension](https://marketplace.visualstudio.com/items?itemName=James-Yu.latex-workshop). To allow shell escape I have added:
```json
{
    ...

    "latex-workshop.latex.tools": [
        {
            "name": "latexmk",
            "command": "latexmk",
            "args": [
                "-shell-escape", // Shell Escape enabled!
                "-synctex=1",
                "-interaction=nonstopmode",
                "-file-line-error",
                "-pdf",
                "-outdir=%OUTDIR%",
                "%DOC%"
            ],
            "env": {}
        },
        ...
    ],
    ...
}
```

## I've found a mistake!
Simply [add a new issue](https://github.com/OliverKillane/Imperial-Computing-Year-3-Notes/issues/new/choose) and attach the relevant labels.

![Screenshot 2022-10-09 015053](https://user-images.githubusercontent.com/44177991/194732526-54cca108-9fa7-4b0e-a4af-b0baad625af9.png)

## I want to contribute!
Fork the repository and create a [pull request](https://github.com/OliverKillane/Imperial-Computing-Year-3-Notes/pulls).
- I will review as soon as I can
- PRs need to be formatted correctly (using latexindent)
- If there are merge conflicts, rebase!
- PDFs need to be rebuilt.
