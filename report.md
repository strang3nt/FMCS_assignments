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
...

# Introduction

In the following paragraphs the terms witness and counter-example will be used interchangeably.

Initially the witness generation started along the model checking algorithm itself: this is wrong because at any step if I pick a state,
I cannot possibly know whether if such state is in a witness execution.

Follows a description and proof of correctness of the two functions developed:

 - `simbolicReachable`
 - `generate_witness`.

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


# Witness generation

```python
def generate_witness(fsm, trace, curr_states):
    state = fsm.pick_one_state(curr_states & trace[-1])
    if len(trace) == 1: return (state, )
    return generate_witness(
        fsm, 
        trace[:-1], 
        fsm.pre(curr_states)) + (fsm.pick_one_inputs(state), state)
```

> **Proof**: since this is a recursive function, the proof is by induction on the size of the trace and we want to prove that the `generate_witness` function always returns a correct witness, where correct witness means a valid execution from the initial state of the final state machine we are checking to the final state which reaches the property.

Base case:

- if the size is 1 then the witness is the intersection between a bdd which represents the current state and the only element of trace which is the bdd representing the initial states, and since the first curr_state is a state that verifies(violates) the invariant the function returns exacly a state verifying the invariant.

- we ignore the case where the size is 0, in that case no witness is generated.

Inductive case:

 - we have the hypothesis that the property is true for a trace of size `k`, thus there is a path of size `k` which is a correct witness execution, follows the proof for a size `k + 1`: if we add 1 element to the trace, since the witness is built from the last state the element added is the final states set, thus the last state is a state in the intersection between the final states and the states verifying the property, just like the base case.

# Final remarks

- symbolicReachable returns true if the negation of the spec is reached, and provides a witness execution, which is indeed a counter-example of the original invariant
- finally if `symbolicReachable` is true the invariant is not verified then counter-example is pretty printed otherwise `None` is returned.
