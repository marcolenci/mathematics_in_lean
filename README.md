# Mathematics in Lean

This tutorial depends on Lean 4, VS Code, and Mathlib.
You can find the textbook both online and in this repository
in
[html format](https://leanprover-community.github.io/mathematics_in_lean/)
or as a
[pdf document](https://leanprover-community.github.io/mathematics_in_lean/mathematics_in_lean.pdf).
The book is designed to be read as you
work through examples and exercises,
using a copy of this repository on your computer.
Alternatively, you can use Gitpod to run Lean and VS Code in the cloud.

This version of *Mathematics in Lean* is designed for [Lean 4](https://leanprover.github.io/) and
[Mathlib](https://github.com/leanprover-community/mathlib4).
For the Lean 3 version, see [github.com/leanprover-community/mathematics_in_lean3](github.com/leanprover-community/mathematics_in_lean3).


## To use this repository on your computer

Do the following:

1. Install Lean 4 and VS Code following the
   "regular install" section of these [instructions](https://leanprover-community.github.io/get_started.html#regular-install).
   It isn't enough just to install the Lean 4 extension for VSCode; make sure you complete the steps so that Lean 4 and elan are installed.

2. Make sure you have [git](https://git-scm.com/) installed.
   In a terminal, navigate to the folder where you want to put a copy of the
   repository, and type `git clone https://github.com/leanprover-community/mathematics_in_lean.git`
   to fetch it from github.

3. Navigate to `mathematics_in_lean`, and execute `lake exe cache get` to fetch a compiled
   version of the library, `Mathlib`.

4. Type `code .` to open the folder in `VS Code`, or you can run `VS Code` and
   choose `Open Folder` from the `File` menu. Be sure to open the folder `mathematics_in_lean`,
   not any other folder.

5. Each section in the textbook has an associated Lean file with examples and exercises.
   You can find them in the folder `MIL`, organized by chapter.
   We strongly recommend making a copy of that folder and experimenting and doing the
   exercises in that copy.
   This leaves the originals intact, and it also makes it easier to update the repository as it changes (see below).
   You can call the copy `my_files` or whatever you want and use it to create
   your own Lean files as well.

At that point, you can open the textbook in a side panel in VS Code as follows:

1. Type `ctrl-shift-P`.

2. Type `Lean 4: Open Documentation View` in the bar that appears, and then
  press return. (You can press return to select it as soon as it is highlighted
  in the menu.)

3. In the window that opens, click on `Open documentation of current project`.

The textbook and this repository are still a work in progress.
You can update the repository by typing `git pull`
followed by `lake exe cache get` inside the `mathematics_in_lean` folder.
(This assumes that you have not changed the contents of the `MIL` folder,
which is why we suggested making a copy.)


## To use this repository with Gitpod

If you have a Gitpod account or are willing to sign up for one,
just point your browser to [https://gitpod.io/#/https://github.com/leanprover-community/mathematics_in_lean](https://gitpod.io/#/https://github.com/leanprover-community/mathematics_in_lean).
This creates a virtual machine in the cloud,
and installs Lean and mathlib.
It then presents you with a VS Code window, running in a virtual
copy of the repository.
We still suggest making a copy of the `MIL` directory, as described
in step 5 in the last section.
You can update the repository by opening a terminal in the browser
and typing `git pull` followed by `lake exe cache get` as above.

Gitpod gives you 50 free hours every month.
When you are done working, choose `Stop workspace` from the menu on the left.
The workspace should also stop automatically
30 minutes after the last interaction or 3 minutes after closing the tab.

To restart a previous workspace, go to [https://gitpod.io/workspaces/](https://gitpod.io/workspaces/).
If you change the filter from Active to All, you will see all your recent workspaces. You can pin a workspace to keep it on the list of active ones.

## Contributing

PRs and issues should be opened at the upstream
[source repository](https://github.com/avigad/mathematics_in_lean_source).
