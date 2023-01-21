---
title:  'Formal Methods for Cyber-Physical Systems: Assignment 2'
author:
- Alessandro Flori
institution: 
- 'Department of Mathematics "Tullio Levi-Civita"'
- "University of Padua"
date: 21 January, 2023
abstract: |
  This is the report of the the master's degree course 
  Formal Methods for Cyber-Physical Systems second assignment. The goal is to implement a symbolic algorithm for model checking using special class of LTL formulas, using BDDs as data structure to represent and manipulate regions. The class of formulas considered by the algorithm is called "reactivity" properties and have the special form $\square\lozenge f\rightarrow\square\lozenge g$. The report contains description and proof of correctness of the algorithms developed. 
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

This report contains a description and a justification of the correctness of the symbolic model checking algorithm implemented. This project uses the library [Pynusmv](https://pynusmv.readthedocs.io/). The goal of the project is to implement an algorithm that check liveness properties in the following form $\square\lozenge f\rightarrow\square\lozenge g$. Such class of formulas are called reactivity properties [@bloem2012].

Follows a description and a sketch of correctness of the functions implemented:

 - `symbolic_repeatable`, which looks for a cycle that negates the reactivity property, if such cycle exists it outputs true and the witness, false otherwise
 - 3 auxiliary functions that generate the lazo-shaped witness, namely `generate_witness_first`, `find_cycle_start` and `build_cycle`.

# Model checking reactivity properties

The reactivity property has the following form: $\square\lozenge f\rightarrow\square\lozenge g$. $g$ and $f$ are properties without temporal operators.
The negation of a reactivity property is the following: $\square\lozenge f\wedge\lozenge\square\neg g$.

In order to perform model checking a path satisfying the negated property must be found: which means to find a 
path containing a cycle such that $\square\lozenge f\wedge\square\neg g$ is a property for that cycle.
The symbolic model checking algorithm does just that.

# Symbolic model checking function

```{.python .numberLines}
def compute_reach(model):
    reach = model.init
    new = model.init
    trace = []
    while new.isnot_false():
        trace = trace + [new]
        new = model.post(new) - reach
        reach = reach + new
    return reach, trace
```

First `compute_reach` is executed, compute reach returns both the reach itself, which is
a BDD representing all reachable states of the model, and a trace, which is a list of the values of the different state sets computed while looking for the reach.

```{#symbolic_reachable .python .numberLines caption="symbolic_repeatable function. Computes a witness for a property respected by the model, otherwise returns false."}
def symbolic_repeatable(model, f, not_g):
    reach, trace = compute_reach(model)

    recur = reach & f & not_g
    while recur.isnot_false():
        pre_reach = pynusmv.dd.BDD.false() # empty BDD
        new = model.pre(recur) & not_g
        
        while new.isnot_false():
            pre_reach = pre_reach + new
            if recur.entailed(pre_reach):
                s, cycle_trace = find_cycle_start(model, recur, pre_reach)
                first_trace = generate_witness(
                    model, 
                    list(takewhile(lambda x: not(s.entailed(x)), trace)) + [s], 
                    s
                )
                return True, first_trace[:-1] + list(build_cycle(model, s, cycle_trace))
                
            new = (model.pre(new) - pre_reach) & not_g
        recur = recur & pre_reach # removes states that cannot form loop
    return False, None
```

After computing the reach, starting from the final states, the generation of recur and pre_reach starts:

- recur represents all the state where the cycle starts
- pre_reach represents all the reachable states from recur, going backwards. 

If a set of states such that recur is a subset of pre_reach exists, it means that a cycle can be built,
and such cycle will respect the following property: $\square\lozenge f\wedge\square\neg g$.
The function returns a lasso-shaped witness which is comprised of:

 - states from the initial trace, the trace is cut in order to contain only the initial
 state and the following transitions until the last state before the cycle
 - the cycle states.

 If otherwise we reach a situation where there are no unvisited states and recur is still not a subset of pre_reach, then
 we cannot possibly build a cycle and the model respects the initial reactivity property: the function returns false and no witness.

## Correctness

Note that in order to print a cycle which respects the following property $\square\lozenge f\wedge\square\neg g$, it is necessary that all states respect the property $\neg g$. 
Follows a proof of correctness for the algorithm, without considering the witness generation.

> symbolic_repeatable returns True if and only if $F$ is repeatable and $G$ is persistent in the transition system, where $F$ and $G$ are the sets formed by the states that satisfy the properties $f$ and $\neg g$, respectively.

The following are the claims to prove.

1. If there is a reachable state $s$, such that $s\in F\wedge s\in G$, and there is an infinite execution starting in $s$ satisfying
$\mbox{Repeatedly}\ F \wedge \mbox{Persistently}\ G$, then s will always stay in recur (and thus, recur cannot get empty).
2. If the inner loop finds that from every state in recur, some state in recur is reachable with $\geq 1$
transitions, then indeed there is an infinite execution satisfying $\mbox{Repeatedly}\ F \wedge \mbox{Persistently}\ G$.

I prove the claims.

1. Such state $s$, will always be found while computing the frontiers (the value of new), thus, since pre_reach is the union of all frontiers, it will always be true that $s\in pre\_reach$, which leads to the conclusion that $s\in reach$ at all times: this follows from how reach is updated at each iteration of the outer loop. $s\in G$ is ensured by the shape of the transitions: in fact whenever a post operation is executed, the resulting set is
intersected with $G$.

2. Since the computation of the frontiers starts from recur, it follows that whenever a new frontier contains a state from recur, such state is part of an infinite execution satisfying $\mbox{Repeatedly}\ F$. The infinite execution also satisfies $\mbox{Persistently}\ G$ because each new frontier is intersected with the set $G$, and because recur itself is a set of states that satisfy $F\wedge G$.

# Witness generation

```{.python .numberLines}
def find_cycle_start(model, recur, pre_reach):
    s = model.pick_one_state(recur)
    while True:
        r = pynusmv.dd.BDD.false()
        new = model.post(s) & pre_reach
        cycle_trace = [new]
        while new.isnot_false():
            r = r + new
            new = (model.post(new) & pre_reach) - r
            cycle_trace.append(new)
        r = r & recur
        if s.entailed(r):
            return s, cycle_trace
        else:
            s = model.pick_one_state(r)
```

`find_cycle_start` takes as inputs the model, recur, pre_reach. The output is a state $s$, which is the initial
state of a path starting and ending with $s$, and a trace which contains the cycle itself. Such $s$ is in recur, and pre_reach is a BDD representing
all states computed during the symbolic_repeatable procedure, and contains all the states of the cycle.

```{.python .numberLines}
def build_cycle(model, s, cycle_trace):
    path = deque([model.pick_one_inputs(s), s])
    curr = s

    for new_i in reversed(list(takewhile(lambda x: not(s.entailed(x)), cycle_trace))):
        pred = model.pre(curr) & new_i
        curr = model.pick_one_state(pred)
        path.appendleft(curr)
        path.appendleft(model.pick_one_inputs(curr))
        
    path.appendleft(s)
    return path
```

`build_cycle` takes as inputs the model, a state which is the start of the cycle and a trace, such trace
contains the cycle. The output of this function is a path in the model with `state` as its 
start and end.

```{.python .numberLines}
def generate_witness(model, trace, final_states):
    state = model.pick_one_state(final_states & trace[-1])
    if len(trace) == 1: return [state]
    return generate_witness(
        model, 
        trace[:-1],
        model.pre(final_states)) + [model.pick_one_inputs(state), state]
```

`generate_witness` takes as inputs the model, a trace and a final state from which it starts
generating the witness execution, back to the initial state. This function is used to 
generate the first part of the lasso-shaped witness, meaning the part from an initial state
to the start of the cycle. In fact the final state is a state from the cycle. I used the 
same function in the previous assignment, for the generation of a witness for safety properties.

The whole 3 functions can be seen as 1 big function, its output is a lasso-shaped witness.
The functions are used in lines 12-18 of [`symbolic_reachable`](#symbolic_reachable):

1. first the initial state for the loop and a trace containing the cycle itself are generated
2. then the first part of the witness is generated, which is a path from an initial state
to the start of the loop
3. the cycle is generated
4. the two paths are appended in order to have the lasso-shaped witness.

## Correctness

### find_cycle_start

The function is comprised of 2 loops, the outer and the inner loop. 

The outer loop does the following: selects a random state $s$ from recur, which hopefully is part of a cycle, then computes the post of this state $s$, intersected with pre_reach, which contains all the states I can form a cycle with. This first new set of states is saved in a list.

The inner loop repeatedly computes the post states of the initial state $s$, intersected with pre_reach, leaving out the states already visited. 
If no new states are reachable, the cycle ends.
All of the states computed are saved inside the variable r. If at the end of this loop r contains the initial state $s$, it means there is a cycle starting and ending with $s$: otherwise the outer cycle restarts picking another random state. This new state is a state from the
intersection of r and recur: that is because if at some point in the computation of the frontiers, a state in recur is met, such state is part of a cycle, or of a path that leads to a cycle.

### build_cycle

The function is comprised of a cycle, at the end of the cycle the cycle path is formed.

The invariant of the cycle is that at each step curr is the $k - i - 1$ step of the cycle,
where $i\in [0..k-2]$,
and path contains the k downwards to the $k-i-1$ step of the cycle at all times, where the element
$k$ and the element $0$ are the same state.

At the first iteration curr is the state preceding the last state of the loop,
the $k-1$ step. At the following steps the curr is the $k - i - 1$ element of the cycle, and 
since all curr values are inside the path list, path contains the $k$ step downwards to the $k-i-1$ step.
At the last step curr is the $k - (k - 2) - 1 = 1$ element of the cycle, and path
contains all of the states of a cycle from the $k$-th element to the $1$-st element.

The function returns the path obtained through the aforementioned loop, and appends to the
start of the path, the initial state, thus forming the full cycle.

# References