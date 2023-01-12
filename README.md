# Formal methods for Cyber-Physical systems assignments

FMCS as in Formal Methods for Cyber-Physical Systems. 
FMCS is a course from the master degree in computer science of the University of Padova.
This repository contains source code and documentation for 2 course assignments,
both of them rely on the python library `PyNuSMV` (<https://pynusmv.readthedocs.io/>).
The topic of the assignments is to implement different kinds of model checkers.

## First assignment

The goal of this assignment is to build an algorithm that verifies invariants (safety properties).
The [report](assignment_1/ass_1_report.md) contains further details on the python function and a proof of correctness.

## Second assignment

This second assignment builds on the first one, but now the goal is to build a model checker for
a liveness property called "reactivity" property, which has the following form (in liner temporal logic): `GF f -> GF g`.
For further details, refer to the [report](assignment_2/ass_2_report.md).
