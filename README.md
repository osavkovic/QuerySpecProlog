
# How to Run the Specialization Algorithm in Prolog

The program consists of two files:

1. `input.pl` that encodes the input, which includes:
    - schema (relation names)
    - table completeness statements
    - primary keys and foreign keys (optional)
    - finite domain constraints (optional)

In the section below, we provide exact details on the encoding.

2. `main.pl`:
    - contains the main methods that implement the specialization algorithm
    - loads `input.pl` as a module. Thus, it is sufficient to call `consult(main.pl)`.

# main.pl

In this module, the starting predicate is `computeSpecializations/3`:

```prolog
        computeSpecializations(query(OutputVars,As),Number,KSpecializationsAll).
```

It takes as input a given `query(OutputVars,As)`, where `OutputVars` is the list of output variables, `As` is the list of body atoms of the input query, `Number` is a number, and `KSpecializationsAll` is an output variable that contains a list of all maximal specializations that can be obtained with extension up to `Number`.

For example, given the assumptions about completeness provided below (see next section), a query `q(N) :- pupil(N,S,C)` is not complete, and moreover, it does not have 0-MCS. Hence,

```prolog
    ?- computeSpecializations(query([N],[pupil(N,S,C)]),0,KSpecializationsAll).
    KSpecializationsAll = [] ;
    false.
```

Now if we change `Number=1`:

```prolog
  ?- computeSpecializations(query([N],[pupil(N,S,C)]),1,KSpecializationsAll).
  KSpecializationsAll = [query([N], [pupil(N, S, C), school(S, primary, 'Bolzano')])] ;
  false.
```

we obtain the only 1-MCS `q(N) :- pupil(N, S, C), school(S, primary, 'Bolzano').`

# input.pl

The TC statements from our running example and experiments are encoded as:

```prolog
    tc(school(_,'primary',_), []). 
    tc(pupil(_,Sname,_) , [school(Sname,_,'Bolzano')]).    
    tc(learns(Pname,'English'), [pupil(Pname,Sname,_), school(Sname,'primary', _)]).
    tc(learns(Pname,'English'), [pupil(Pname,Sname,_), school(Sname,'middle', _)]).
    tc(class(_,_,'halfDay'), []).  
    tc(class(_,_,'fullDay'), []).
```

In addition, one must declare the relation and assign a unique number. For instance:

```prolog
    relation(rel(4,class(_,_,_))).
    relation(rel(3,school(_,_,_))).
    relation(rel(2,pupil(_,_,_))).
    relation(rel(1,learns(_,_))).
```

Finally, our specialization algorithm also supports completeness reasoning in the presence of primary and foreign keys (pks and fks, respectively) and finite domain constraints (fdcs). However, this is out of the scope of our paper, so we leave those predicates empty (but we still have to define them):

```prolog
    pks([]).
    fks([]).
    fdcs([]).
```

