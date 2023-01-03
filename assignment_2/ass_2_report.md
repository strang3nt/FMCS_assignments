---
title:  'Formal Methods for Cyberphisical Systems: Assignment 2'
author:
- Alessandro Flori
institution: 
- 'Department of Mathematics "Tullio Levi-Civita"'
- "University of Padua"
date: 21 January, 2023
abstract: |
  This is the report of the the master's degree course 
  Formal Methods for Cyberphisical Systems second assignment. The goal is to implement a symbolic algorithm for the verification of a special class of LTL formulas, using BDDs as data structure to represent and manipulate regions. The class of formulas considered by the algorithm is called "reactivity" properties and have the special form $\square\lozenge f\rightarrow\square\lozenge g$. The report contains description and proof of correctness of the algorithms developed. 
highlight-style: kate
geometry: margin=1in

references:
- type: article-journal
  id: bloem2012
  title: 'Synthesis of Reactive(1) designs'
  journal: 'Journal of Computer and System Sciences'
  volume: 78
  number: 3
  pages: 911-938
  year: 2012
  note: 'In Commemoration of Amir Pnueli'
  ISSN: 0022-0000
  DOI: '10.1016/j.jcss.2011.08.007'
  URL: 'https://www.sciencedirect.com/science/article/pii/S0022000011000869'
  author: 
    - Roderick Bloem
    - Barbara Jobstmann 
    - Nir Piterman 
    - Amir Pnueli 
    - Yaniv Sa'ar
  keywords: Property synthesis, Realizability, Game theory

...

<!-- 
  Compiled to pdf via Pandoc's docker distribution:
  docker run --rm --volume "$(pwd):/data" --user $(id -u):$(id -g) pandoc/latex ass_2_report.md --citeproc -o outfile.pdf
 -->

# Introduction

This report contains a description and a justification of the correctness of the symbolic model checking algorithm implemented. This project uses the library [Pynusmv](https://pynusmv.readthedocs.io/). The goal of the project is to create the necessary algorithm(s) in order to check liveness properties in the following form $\square\lozenge f\rightarrow\square\lozenge g$. Such formulas are called reactivity properties [@bloem2012].

Follows a description and a correctness sketch of the functions implemented:

 - `symbolic_repeatable`, which looks for a cycle that negates the reactivity property, if such cycle exists it outputs `True` and the witness, `False` otherwise
 - 3 auxiliary functions which given the required inputs generate the lazo-shaped witness, namely `generate_witness_first`, `find_cycle_start` and `build_loop`.


# Model checking reactivity properties

The reactivity property has the following form: $\square\lozenge f\rightarrow\square\lozenge g$. $g$ and $f$ are properties without temporal operators.
The negation of a reactivity property is the following: $\square\lozenge f\wedge\lozenge\square\neg g$

In order to perform model checking one must find a path in the model that satisfies the negated property: which means to find a 
path containing a cycle such that $\square\lozenge f\wedge\square\neg g$ is true.
The symbolic model checking algorithm does just that.

# Symbolic model checking function

```python
def compute_reach(model):
    reach = model.init
    new = model.init
    trace = [model.init]
    while new.isnot_false():
        new = model.post(new) - reach
        trace = trace + [new]
        reach = reach + new
    return reach, trace
```

First the `compute_reach` is executed, compute reach returns both the reach itself, which is
all the reachable states of the model, and a trace, which is a collection of the values of new.
Note that the last value inside the trace is an empty BDD.

```python
def symbolic_repeatable(model, f, not_g):
  
    reach, trace = compute_reach(model)

    recur = reach & f & not_g
    while recur.isnot_false():
        pre_reach = pynusmv.dd.BDD.false() # empty BDD
        new = model.pre(recur) & not_g
        
        while new.isnot_false():
            pre_reach = pre_reach + new
            if recur.entailed(pre_reach):
                state_loop, new_trace = find_cycle_start(model, recur, pre_reach)
                first_trace = generate_witness_first(
                    model, 
                    list(
                        takewhile(lambda x: not(state_loop.entailed(x)), 
                        trace)) + [state_loop], 
                    state_loop)

                return True, first_trace[:-1] + list(build_loop(model, state_loop, new_trace))
                
            new = (model.pre(new) - pre_reach) & not_g
        recur = recur & pre_reach
    return False, None
```

After computing the reach, starting from the final states, the generation of recur and pre_reach starts.
`recur` represents all the state where the cycle starts, while `pre_reach` represents all the reachable states
from recur, going backwards. If exists a set of states such that recur is a subset of pre_reach, this means that a cycle can be build,
and such cycle will respect the following property: $\square\lozenge f\wedge\square\neg g$: the function returns
a lasso-shaped witness which is a list of:

 - states from the initial trace found by the function compute_reach, the trace is cut in order to contain only the initial
 state and the following transitions until the first element of the cycle
 - the cycle.

 If otherwise we reach a situation where there are no unvisited states and recur is still not a subset of pre_reach, then
 we cannot possibly build a cycle and the model respects the initial reactivity property: the function returns `False` and no witness.

## Correctness

Note that in order to print a cycle which respects the following property $\square\lozenge f\wedge\square\neg g$, it is necessary to restrict
all new states to respect the property $\neg g$: otherwise it would not be very difficult, and not necessarily possible, to build the loop
needed in order to provide the counter example to the reactivity property.

# Witness generation

```python
def find_cycle_start(model, recur, pre_reach):
    s = model.pick_one_state(recur)
    while True:
        r = pynusmv.dd.BDD.false()
        new = model.post(s) & pre_reach
        new_reach = [new]
        while new.isnot_false():
            r = r + new
            new = model.post(new) & pre_reach
            new = new - r
            new_reach.append(new)
        r = r & recur
        if s.entailed(r):
            return s, new_reach
        else:
            s = model.pick_one_state(r)

def build_loop(model, state, new_reach):
    k = [i for i in range(len(new_reach)) if state.entailed(new_reach[i])][0]
    path = [model.pick_one_inputs(state)] + [state]
    curr = state

    for i in reversed(range(k)):
        pred = model.pre(curr) & new_reach[i]
        curr = model.pick_one_state(pred)
        path = [model.pick_one_inputs(curr)] + [curr] + path # insert to head
        
    return [state] + path

def generate_witness_first(model, trace, final_states):
    """
    final_states is the state that starts the loop.
    Generation of witness should start from init and finish from 
    the previous element of trace s.t. trace[i] contains final_states.
    """
    state = model.pick_one_state(final_states & trace[-1])
    if len(trace) == 1: return [state]
    return generate_witness_first(
        model, 
        trace[:-1], 
        model.pre(final_states)) + [model.pick_one_inputs(state), state]
```

## Description

## Correctness

# Final remarks
