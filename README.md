# How to Run the Specialization Algorithm

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
