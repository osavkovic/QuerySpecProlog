# How to run the Specialization Algorithm
 
 The program consists of two files

* input.pl that encodes the input, that is
    - schema (relation names)
    - table completness statemnts 
    - primary keys and foreign keys (optional)
    - finite domain constraits (optional)

In the section below we provide exact details on the encoding.
 
* main.pl 
    - contains the main methods the implement the specialization algorithm
    - loads input.pl as a module. That is, it is suffiecent to call ``consult(main.pl)``.
     


# main.pl

In this module, starting predicate is ``computeSpecializations/3``

```prolog
        computeSpecializations(query(OutputVars,As),Number,KSpecializationsAll).
```

that takes as input a given ``query(OutputVars,As)``, where ``OutputVars`` is the list of output variables, ``As`` is the list of body atoms of the input query, ``Number`` is a number, and ``KSpecializationsAll`` is an output variables that contains a list of all maximal specializations that can be obtained with extension up to ``Number``.

For example, given the assumptions about completeness provided below (see next section) a query ``q(N) :- pupil(N,S,C)`` is not complete, and moreover, it does not have 0-MCS. 
Hence, 

```prolog
    ?- computeSpecializations(query([N],[pupil(N,S,C)]),0,KSpecializationsAll).
    KSpecializationsAll = [] ;
    false.
```

Now if we change ``Number=1``.

```prolog
  ?- computeSpecializations(query([N],[pupil(N,S,C)]),1,KSpecializationsAll).
KSpecializationsAll = [query([N], [pupil(N, S, C), school(S, primary, 'Bolzano')])] ;
false.
```
we get obtain the only 1-MCS  ``q(N) :- pupil(N, S, C), school(S, primary, 'Bolzano').``


# input.pl

The TC statements from our running example and experiements are encoded as:

```prolog
    tc(school(_,'primary',_), []). 
    tc( pupil(_,Sname,_) , [school(Sname,_,'Bolzano')] ).    
    tc(learns(Pname,'English'), [pupil(Pname,Sname,_), school(Sname,'primary', _)]).
    tc(learns(Pname,'English'), [pupil(Pname,Sname,_), school(Sname,'middle', _)]).
    tc(class(_,_,'halfDay'), []).  
    tc(class(_,_,'fullDay'), []).
```

In addition, one has to declare the relation and assign a unique number. For instance, 

```prolog
    relation(rel(4,class(_,_,_))).
    relation(rel(3,school(_,_,_))).
    relation(rel(2,pupil(_,_,_))).
    relation(rel(1,learns(_,_))).
```

Finally, our specialization algorithm also supports completeness reasoning in the presence of primary and foreign keys (pks and fks, resp.), and finite domain constraints (fdcs). However, this is out of the scope of our paper and leave those predicates empty (but we have to define them).

```prolog
    pks([]).
    fks([]).
    fdcs([]).
```



