# Formalized Class Group Computations and Integral Points on Mordell Elliptic Curves

This repository contains the source code for the paper "Formalized Class Group Computations and Integral Points on Mordell Elliptic Curves", submitted to CPP 2023.

Diophantine equations are a popular and active area of research in number theory.
In this paper we consider Mordell equations, which are of the form `y^2 = x^3 + d`,
where `d` is a (given) nonzero integer number and all solutions in integers `x` and `y` have to be determined.
One non-elementary approach for this problem is the resolution via descent and class groups.
Along these lines we formalized in Lean 3 the resolution of Mordell equations for several instances of `d < 0`.
In order to achieve this, we needed to formalize several other theories from number theory that are interesting on their own as well,
such as ideal norms, quadratic fields and rings, and explicit computations of the class number.
Moreover we introduced new computational tactics in order to carry out efficiently computations in quadratic rings and beyond.

## Installation instructions

The formalization has been developed for the community fork of Lean 3.
To install a full Lean development environment, please follow the "Regular install" instructions at <https://leanprover-community.github.io/get_started.html>.
After installation, you can run the following commands to set up the dependencies for this project and open VS Code to explore the files:
```
cd path/to/class-group-and-mordell-equation
leanpkg configure
leanproject get-mathlib-cache
lean --make src
code .
```

When opening a Lean project in VS Code, you must use the "Open Folder" menu option to open the project's root directory.
On the command line, you can run `code path/to/class-group-and-mordell-equation`.

The step `lean --make src` precompiles our source files. Although this step is not strictly needed it improves the editing experience, especially on systems with less memory.

## File structure

The sections of our paper correspond with the following files:

 * Section 3: `src/number_theory/quad_ring/basic.lean`
 * Section 4.1: `src/number_theory/class_number_bound.lean`
 * Section 4.2: `src/number_theory/class_number_computing.lean`
 * Section 5: `src/number_theory/mordell.lean`
 * Section 6.1: `src/number_theory/quad_ring/basic.lean`
 * Section 6.2: `src/tactic/times_table.lean`
 * Section 7: `src/tactic/sageify/sageify.lean`
