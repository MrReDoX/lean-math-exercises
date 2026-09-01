# Getting Started with Lean and lean-math-exercises

This guide is for readers who are new to Lean. It explains how to set up an editor, obtain the
Lean toolchain used by this repository, find results in Mathlib, and begin working on an exercise.

## Contents

1. [VS Code](#1-vs-code)
2. [The Lean 4 extension](#2-the-lean-4-extension)
3. [Mathlib](#3-mathlib)
4. [Learn basic Lean](#4-learn-basic-lean)
5. [Set up this repository](#5-set-up-this-repository)
6. [Work on an exercise](#6-work-on-an-exercise)
7. [When something goes wrong](#7-when-something-goes-wrong)

## 1. VS Code

[Visual Studio Code](https://code.visualstudio.com/) is the recommended editor for Lean. Install
it for your operating system, then use **File > Open Folder** to open a Lean project. Open the
repository folder itself, rather than an individual `.lean` file, so that VS Code can find its
`lean-toolchain`, Mathlib dependency, and build configuration.

You will also need a terminal. VS Code includes one: choose **Terminal > New Terminal**. The
commands below should be run from the repository root, the folder containing `lakefile.toml`.

## 2. The Lean 4 extension

Install the official [Lean 4 VS Code extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4).
The extension installs and selects Lean through `elan`, Lean's version manager. It reads the
project's `lean-toolchain` file, so different Lean projects can use different Lean versions.

When you open a `.lean` file, the extension provides:

- diagnostics in the editor for errors and warnings;
- hover information for definitions, theorems, and inferred types;
- code completion;
- the **Infoview**, which shows the current proof goal and local hypotheses.

If the setup page does not appear after installation, open a Lean file, click the `∀` icon in the
upper-right corner, and select **Documentation > Show Setup Guide**. The official
[Lean installation guide](https://lean-lang.org/install/) gives platform-specific instructions.

## 3. Mathlib

[Mathlib](https://github.com/leanprover-community/mathlib4) is Lean's main
mathematical library. It provides definitions and proved theorems for algebra, analysis,
topology, number theory, and much more.

This repository already declares the required Mathlib version in `lakefile.toml`; you do not need to install
Mathlib separately. Running `lake update` obtains the declared dependencies, and
`lake exe cache get` downloads their prebuilt compiled files.

Useful ways to explore Mathlib:

- Ask your favorite AI tool, “Is there a theorem for X in Mathlib and how do I use it?”
- Search the [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/).
- Write `#check theorem_name` in a Lean file to see a theorem's full statement.
- Hover over names and use VS Code completion to inspect nearby declarations.
- Each exercise sheet has a **Potentially helpful results** section containing relevant `#check`
  declarations.

## 4. Learn basic Lean

[The Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/NNG4) is an excellent
first introduction to basic Lean syntax and concepts in a gamified environment. It introduces
propositions, equality, implication, quantifiers, induction, and elementary tactics through
short interactive exercises.

[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
is a useful next resource. It develops common proof methods and mathematical topics using
Mathlib. You do not need to finish it before using this repository; consult the chapters that
match the area you are studying.

See also [Exercises/Toolbox.lean](Exercises/Toolbox.lean) for a compilation of Lean proof
patterns used throughout this repository.

## 5. Set up this repository

Git is version-control software: Lean does not require it, but it lets you keep a history of your
own work and easily get the latest exercises. Install [Git](https://git-scm.com/downloads) if
you do not already have it. In a terminal, clone the repository and enter its directory:

```bash
git clone https://github.com/aimmerwahr/lean-math-exercises.git
cd lean-math-exercises
```

Later, run `git pull` from this directory to download the latest changes.

Alternatively, download the repository as a [ZIP archive](https://github.com/aimmerwahr/lean-math-exercises/archive/refs/heads/main.zip),
extract it, and open the extracted folder locally. You can use Lean without Git, but you will need
to download a fresh archive to get later updates.

Once you have a local copy of the repository, fetch the dependencies and their compiled cache:

```bash
lake update
lake exe cache get
```

Then open this directory in VS Code. You can confirm that the project builds with:

```bash
lake build
```

The first setup may take several minutes. Later, the extension checks the file you are editing as
you work.

### Using Git for your own work

You can use Git to manage your own work even if you never contribute to this repository. A branch
is an independent line of work, and a commit is a saved snapshot. For example, you can create a
branch for your solutions and commit your progress:

```bash
git switch -c my-solutions
git add <file>
git commit -m "Solve an exercise"
```

See the [Git tutorial](https://git-scm.com/docs/gittutorial) for the basics. If you want to keep
a copy of the repository on GitHub, you can also
[fork the repository](https://docs.github.com/en/get-started/quickstart/fork-a-repo); a fork is
your own GitHub-hosted copy.

## 6. Work on an exercise

1. Start with a subject overview such as [Linear Algebra](Exercises/LinearAlgebra/00LinearAlgebra.md).
2. Open a sheet under `Exercises/`, for example `Exercises/LinearAlgebra/01Subspaces.lean`.
3. Read the question in the docstring above a theorem.
4. Replace that theorem's `sorry` with a proof and use the Infoview to inspect the goal after
   each step.
5. If you want to compare your work, open the matching theorem in `Solutions/`.

Keep your own proofs outside the tracked exercise sheets. The files under `Exercises/` are kept as
statements with `sorry`, while `Solutions/` contains the canonical proofs.

For a fast command-line check of one file, run:

```bash
lake env lean Exercises/LinearAlgebra/01Subspaces.lean
```

## 7. When something goes wrong

- If Lean cannot find Mathlib or project imports, check that VS Code opened the repository folder
  and that the terminal is in that folder.
- If `lake` is not found, finish the extension setup or follow the official Lean installation
  guide so that `elan` is on your `PATH`.
- If dependencies fail to build, run `lake update` and then `lake exe cache get` again.
- If the Infoview is stale after changing an imported file, use the Command Palette and run
  **Lean 4: Refresh File Dependencies**.
- Read the full error message and inspect the goal in the Infoview before changing a proof. Lean
  reports the expected type and the local hypotheses at the point where it cannot proceed.
- Ask your favorite AI tool for help fixing it.

For contribution guidelines, see [CONTRIBUTING.md](CONTRIBUTING.md).
