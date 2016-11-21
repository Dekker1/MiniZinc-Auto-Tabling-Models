# MiniZinc Auto-Tabling Models

This repository contains models that improved by intrinsic auto-tabling with the
MiniZinc compiler. The models accompany a paper send in to CPAIOR 2017.

### Repository Structure

Each folder contains a MinZinc model. The data files for this model are supplied
in a sub-directory called `instances/`.

### Compiling the models

The auto-tabling intrinsic is currently not part of the MiniZinc compiler. To
use this intrinsic [this fork](https://github.com/jjdekker/libminizinc) of the
compiler can be used.
