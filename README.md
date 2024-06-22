# Technical Instructions

## Overview

This repository contains:

- Specialization algorithm implemented in Prolog
- Generalization algorithm implemented in ASP

Below are the instructions for running each of the implementations.



# How to Run the Specialization Algorithm

Requirements: SWI-Prolog [https://www.swi-prolog.org/](https://www.swi-prolog.org/)

The program consists of two files:

1. `input.pl`: This file encodes the input data, including:
    - Schema (relation names)
    - Table completeness statements 
    - Primary keys and foreign keys (optional)
    - Finite domain constraints (optional)

   Details on the encoding are provided in the section below.

2. `main.pl`: 
    - Contains the main methods implementing the specialization algorithm
    - Loads `input.pl` as a module. It is sufficient to call `consult(main.pl)`.

## `main.pl`

In this module, the starting predicate is `computeSpecializations/3`:

```prolog
computeSpecializations(query(OutputVars,As),Number,KSpecializationsAll).
```

This predicate takes the following inputs:
- `query(OutputVars, As)`: Where `OutputVars` is the list of output variables, and `As` is the list of body atoms of the input query.
- `Number`: A numerical value.
- `KSpecializationsAll`: An output variable that will contain a list of all maximal specializations obtainable with extensions up to `Number`.

For example, given the completeness assumptions provided below (see the next section), a query `q(N) :- pupil(N,S,C)` is not complete and does not have a 0-MCS. Therefore,

```prolog
?- computeSpecializations(query([N],[pupil(N,S,C)]),0,KSpecializationsAll).
KSpecializationsAll = [] ;
false.
```

If we change `Number` to 1:

```prolog
?- computeSpecializations(query([N],[pupil(N,S,C)]),1,KSpecializationsAll).
KSpecializationsAll = [query([N], [pupil(N, S, C), school(S, primary, 'Bolzano')])] ;
false.
```

We obtain the only 1-MCS: `q(N) :- pupil(N, S, C), school(S, primary, 'Bolzano')`.

Interestingly, `computeSpecializations/3` can also be used to check if a query is complete. In this case, the returned K-MCS is the input query itself. For instance,

```prolog
?- computeSpecializations(query([N],[learns(N, 'English'), pupil(N, S, _), school(S, primary, 'Bolzano')]),0,KSpecializationsAll).
KSpecializationsAll = [query([N], [learns(N, 'English'), pupil(N, S, _), school(S, primary, 'Bolzano')])] ;
false.
```

## `input.pl`

The table completeness (TC) statements from our running example and experiments are encoded as:

```prolog
tc(school(_,'primary',_), []). 
tc(pupil(_,Sname,_) , [school(Sname,_,'Bolzano')]).    
tc(learns(Pname,'English'), [pupil(Pname,Sname,_), school(Sname,'primary', _)]).
tc(learns(Pname,'English'), [pupil(Pname,Sname,_), school(Sname,'middle', _)]).
tc(class(_,_,'halfDay'), []).  
tc(class(_,_,'fullDay'), []).
```

Additionally, relations must be declared and assigned a unique number. For instance:

```prolog
relation(rel(4,class(_,_,_))).
relation(rel(3,school(_,_,_))).
relation(rel(2,pupil(_,_,_))).
relation(rel(1,learns(_,_))).
```

Our specialization algorithm also supports completeness reasoning in the presence of primary keys (PKs), foreign keys (FKs), and finite domain constraints (FDCs). Although this is outside the scope of our paper, these predicates must be defined, even if left empty:

```prolog
pks([]).
fks([]).
fdcs([]).
```


## Running the Generalization Algorithm

### Requirements

You need an answer-set programming solver, such as DLV. Download it from [DLV System](https://www.dlvsystem.it/).

To run the code on Clingo (another popular ASP solver), change the DLV-specific arithmetic functions (e.g., in DLV `#succ(X,Y)` becomes `Y=X+1` in Clingo).

### Program Structure

The program consists of a single file that contains the encoding of the query and TC statements.

We provide two example files:

- `generalization/query1.pl`
- `generalization/query2.pl`

`query1.pl` encodes the running example from the paper. `query2.pl` slightly alters that example to illustrate a fixpoint that is not a safe query.

### Running the Program

To run the code, it is sufficient to execute the following:

```console
foo@bar:~$ ./dlvMac generalization/query2.pl
DLV [build BEN/Dec 21 2011   gcc 4.2.1 (Apple Inc. build 5666) (dot 3)]

{index(0), index(1),...., fixpoint(1), safe}
```
where `./dlvMac` is the dlv engine. 

### Interpreting the Output

The output will be a single answer set. Look for the atoms `fixpoint/1` and `safe/0`. 

- The atom `fixpoint/1` contains a number (e.g., `fixpoint(1)`) that indicates how many iterations of the `G_C` operator are required to reach the fixpoint. This means `G_C^i(Q)` is the fixpoint.
- The atoms that determine the query `G_C^i(Q)` will have `i` as the last component.

For example, in our running example:

```console
foo@bar:~$ ./dlvMac generalization/query2.pl
DLV [build BEN/Dec 21 2011   gcc 4.2.1 (Apple Inc. build 5666) (dot 3)]

{index(0), index(1),...., pupil(frozen_N,frozen_C,frozen_S,1), school(frozen_S,primary,bolzano,1), ...   fixpoint(1), safe}
```

This output means that the query `G_C^i(Q)` is:

```
Q(N) :- pupil(N,C,S), school(S,primary,bolzano)
```

Finally, if each output variable is present in the body of MCG, the answer set contains the predicate `safe`. Otherwise, it contains the predicate `notsafe`.
