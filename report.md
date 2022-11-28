---
title:  'Formal Methods for Cyberphisical Systems: Assignment 1'
author:
- Alessandro Flori
institution: 
- 'Department of Mathematics "Tullio Levi-Civita"'
- "University of Padua"
date: 13 December, 2022
abstract: |
  This is the report of the the master's degree course 
  Formal Methods for Cyberphisical Systems first assignment.
  The goal was to develop an algorithm for symbolic model checking of invariants. The report contains description and proof of correctness of the algorithms developed. 
highlight-style: kate
...

# Introduction

This report contains a description and a justification of the correctness of the symbolic model checking algorithm implemented. This project uses the library [Pynusmv](https://pynusmv.readthedocs.io/). The goal of the project is to create the algorithm(s) necessary in order to check invariant properties against finite state machines. Such state machines are encoded ad reduced ordered binary decision diagrams.

Follows a description and correctness of the functions implemented:

 - `simbolicReachable`: which outputs if a property is reachable and in such case a witness.
 - `generate_witness`: builds the witness.

# Symbolic model checking function

```python
def symbolicReachable(fsm, spec):
    reach = fsm.init
    new = fsm.init
    trace = [fsm.init]

    while new.isnot_false():

        final = new.intersection(spec)
        if final.isnot_false():
            return True, generate_witness(fsm, trace, final)

        new = fsm.post(new) - reach
        trace = trace + [new]
        reach = reach + new

    return False, None
```

## Description

The parameters are:

 - `fsm`: a `pynusmv.fsm.BddFsm` object which represents the finite state machine we want to check
 - `spec`: the property we want to see if is reachable in `fsm`.

## Correctness

The algorithm starts from the set of initial states and then checks if such set contains the property `spec`, computes the set of the following states (`new`), removing the states already checked (`reach`), and repeats, this time checking the `new` set of states:

 - if it is reached a point where there aren't any new states (when the `new` bdd is false), then we have reached a fixed point, thus `spec` is not reachable, the function returns false and None, meaning there is no witness
 - if otherwise the intersection between `new` and `spec` is not empty, we have found a state which verifies the property and then the algorithm returns true and the a path from the initial state to the aforementioned last state
 - at each step a trace is kept, meaning a list of set of states representing the states checked during each step of the iteration.

# Witness generation

```python
def generate_witness(fsm, trace, final_states):
    state = fsm.pick_one_state(final_states & trace[-1])
    if len(trace) == 1: return (state, )
    return generate_witness(
        fsm, 
        trace[:-1], 
        fsm.pre(final_states)) + (fsm.pick_one_inputs(state), state)
```

## Description

`generate_witness` has the following parameters:

 - `fsm`: a `pynusmv.fsm.BddFsm` object
 - `trace`: which is a list of set of states which represent at each element of the list the states checked during one iteration of `symbolicReachable`
 - `final_states` a `pynusmv.dd.BDD` object which represents the set of states from which we pick the current node of the witness execution, when `generate_witness` is first called `first_states` is the spec we have reached during the execution of `symbolicReachable`.

The output is a `tuple` of `pynusmv.dd.BDD` object and in particular alternating `pynusmv.dd.State` and `pynusmv.dd.Inputs` objects, starting and ending with a state.
Each `pynusmv.dd.Inputs` object in the resulting tuple is a suitable input to the element that follows it, which is a state, such input is found via the `pick_one_inputs(bdd)` function.

The execution is recursive: it starts from the final element of the trace and it generates (recursively) the previous element in the witness path which is inside the trace passed as input. The assumption is that in each element of the trace list there is one or more nodes of a witness path and that once a node of a witness path is found, the next element of the list contains the next node of that path.

## Proof

Since this is a recursive function, the proof is by induction on the size of the trace and we want to prove that the `generate_witness` function always returns a correct witness, where correct witness means a valid execution from the initial state of the finite state machine we are checking to the final state which reaches the property `P`.

**Assumptions**: 

 - the trace is a list of set of states, the trace contains a witness execution with the size of trace
 - `P` is the property the `symbolicReachable` algorithm reached.

**Base case**:

- if the size is $1$ then the witness is a state from the intersection between a bdd which represents a set of states $S_0$ and the only element of the trace, which is the bdd representing all the initial states, then if `final_states` is a set of states that verifies the property, the function returns exactly a state verifying the property `P`, which is indeed a witness

- we ignore the case where the size is 0, in that case no witness needs to be generated.

**Inductive case**:

 - we consider the hypothesis that the property is true for a trace of size $k$, thus there is a path of size $k$ which is a correct witness execution and a final set of states $S_k$ (`final_states`), follows the proof for a size $k + 1$: 
 
    1. we then consider the states $S_{k+1}$
    2. and we select one of the states resulting from the intersection of $S_{k+1}$ and the corresponding piece of the trace, call such state $s_{k+1}$
    2. since $S_k = pre(s_{k+1})$ by function definition, follows that $s_{k+1}$ is exactly the $k + 1$ step in the witness path.

# Final remarks

The function `symbolicReachable` receives as input the negation of the invariant, this way we can check if a state negating the invariant can be reached: it follows that the result of `symbolicReachable` must be negated which is in fact what is done inside the body if the main function:

```python
def check_explain_inv_spec(spec):

    fsm = pynusmv.glob.prop_database().master.bddFsm
    res, trace = symbolicReachable(fsm, spec_to_bdd(fsm, pynusmv.prop.not_(spec)))
    return not res, tuple(
        map(lambda var: var.get_str_values(), trace)) if res else None
```

Note that we can no longer talk about "witness" but about "counter-example".
