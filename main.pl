 :- use_module(input). 
 :- use_module(library(gui_tracer)).   
     
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% 	 module
%:-  module(meta-new,[computeSpecializations/3]). 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% META-PROGRAM   
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

computeSpecializations(query(OutputVars,As),Number,SpecsWithVars):- 
	getAllRelCombUpToSizeWONumbers(Number,Extensions),
	Extensions2=[[]|Extensions],  
	reverse(Extensions2,Extensions3),			 				% to ensure we get smaller quries after maximamizing them
	computeSpecializationsForALLExtensions(As,Extensions3,Specs2),
	findMaximal_query_containment(Specs2,Specs),			   % still not complete for  output variables
	setOutputVars(Specs,OutputVars,As,SpecsWithVars).   
  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% predicates that set output vars for specializations
   
setOutputVars([],_,_,[]).
setOutputVars([Spec | Specs],OutputVars,As,[SpecWithVars | SpecsWithVars]):-
	setOutputVars(Specs,OutputVars,As,SpecsWithVars),
	copy_term(query(OutputVars,As),query(NewOutputVars,AsNew)),
	setOriginalQueryAtoms(AsNew,Spec),	%implicitly NewOutputVars becomes the same as in Spec
	SpecWithVars=query(NewOutputVars,Spec).
	
%%

setOriginalQueryAtoms([],_).				% method sets spec only to an original part of the query (the rest can remain unchanged)
setOriginalQueryAtoms([ANew|AsNew],[S|Spec]):-
	setOriginalQueryAtoms(AsNew,Spec),
	ANew=S.
   
% WITHOUT OUTPUT VARS 
%computeSpecializations(As,Number,Specs):-
%	getAllRelCombUpToSizeWONumbers(Number,Extensions),
%	Extensions2=[[]|Extensions], 
%	reverse_magik(Extensions2,Extensions3),			 				% to ensure we get smaller quries after maximamizing them
%	computeSpecializationsForALLExtensions(As,Extensions3,Specs2),
%	findMaximal_query_containment(Specs2,Specs).
%%	member(Spec,Specs).

	  
%%
	
computeSpecializationsForALLExtensions(_,[],[]).
computeSpecializationsForALLExtensions(As,[Extension | Extensions],Specs):-
	append(As,Extension,AsExt),
	computeSpecializations(AsExt,SpecsAsExt),
	computeSpecializationsForALLExtensions(As,Extensions,Specs2),
	append(SpecsAsExt,Specs2,Specs).
	
%
reverse_magik([X|Y],Z,W) :- reverse_magik(Y,[X|Z],W).
reverse_magik([],X,X).
reverse_magik(A,R) :- reverse_magik(A,[],R).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% query containment, finding most general quries wrt query containment
findMaximal_query_containment(Quries,MaxQuries):-								% interface of the predicate below
	findMaximal_query_containment2(Quries,[],MaxQuries).

findMaximal_query_containment2([],MaxQueries,MaxQueries).
findMaximal_query_containment2([Query | Quries],MaxQueriesCurrent,MaxQueriesFinal):-
		(  not(query_containment_list(Quries,Query)), not(query_containment_list(MaxQueriesCurrent, Query))
		-> append(MaxQueriesCurrent,[Query],MaxQueriesCurrent2),
		   findMaximal_query_containment2(Quries,MaxQueriesCurrent2,MaxQueriesFinal)
		;  findMaximal_query_containment2(Quries,MaxQueriesCurrent,MaxQueriesFinal)
		). 

% 
query_containment_list([Generic | GenericList],Specific):-
	(	query_containment(Generic,Specific)
	->	true
	;	query_containment_list(GenericList,Specific)  
	).

%	
query_containment(Generic,Specific):-
	freeze_magik(Specific,SpecificFroozen),
	verify_magik(unifyAtoms(Generic,SpecificFroozen)).
					
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% META-PROGRAM: Compute all Query extensions of the certain size given schema
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%

getAllRelCombUpToSizeWONumbers(Number,Combs):-
	getAllRelCombUpToSize(Number,CombsWNumbers),
	removeNumbersInCombs(CombsWNumbers,Combs).
 
%%

removeNumbersInCombs([],[]).
removeNumbersInCombs([Comb |Combs],[CleanComb | CleanCombs]):-
		removeNumbersInCombs(Combs,CleanCombs),
		removeNumbersInComb(Comb,CleanComb).

removeNumbersInComb([],[]).
removeNumbersInComb([C | Comb],[CClean | CombClean]):-
		removeNumbersInComb(Comb,CombClean),
		C=rel(_,Rel),
		CClean=Rel.
%%

getAllRelCombUpToSize(0,[]).				% stopping point
getAllRelCombUpToSize(Size,AllCombs):-
	0 < Size,
	Size1 is Size -  1,
	getAllRelCombUpToSize(Size1,AllCombs1),
	getAllRelCombOfSize(Size,AllCombs2),
	append(AllCombs1,AllCombs2,AllCombs).

%%  

getAllRelCombOfSize(Size,AllComb):- 
	findall(Comb,getRelCombOfSize(Comb,Size),AllComb).

%%


getRelCombOfSize([],0).
getRelCombOfSize(Comb,N):-
	0 < N,
	N1 is N-1, 
	relation(Rel),							% given by input.pl
	getRelCombOfSize(Comb1,N1),
	relation_preceded_all_in_comb(Rel,Comb1),
	Comb=[Rel | Comb1].
	

	
%%

relation_preceded_all_in_comb(_,[]).				% the new relation to add has to have number smaller or equal
relation_preceded_all_in_comb(Rel,[Rel2 | Comb]):-	% then all already added relations
	Rel=rel(Num,_),
	Rel2=rel(Num2,_),
	Num =< Num2,
	relation_preceded_all_in_comb(Rel,Comb).
	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% META-PROGRAM: Compute all Query specialization (without extending the query)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

computeSpecializations(As,Specs):-
	instantiate_Q(As,SpecsNonPromoted),
	computePromotedSpecs(As,SpecsNonPromoted,Specs).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
					
	
computePromotedSpecs(As,SpecsNonPromoted,SpecsPromoted):-
	fdcs_var_bindings(As,Bindings),
	getAssigments_from_Specs(As,SpecsNonPromoted,Assigs),
	term_variables_spec(As,OrigVars),
	find_eligable_var_Assigs(Assigs,Assigs,OrigVars,Bindings,AssigsPromoted),
	getSpecs_from_Assigments(As,AssigsPromoted,SpecsPromoted).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% META-PROGRAM: COMPUTING PROMOTION OF SPECIALIZTION USING FDCS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
find_eligable_var_Assigs([],AssigsCurrent,_,_,AssigsCurrent).	% all Assigs are iterated and no eligable Promotions has been found
																% therefore, from this point we return AssigsCurrent as the final list
																% of Assigs (where no promotion is possible)
																

											% find_eligable_var_Assigs(AssigsIterate, AssigsCurrent,OrigVars,Bindings,AssigsFinal)
											% AssigsIterate - list of Assigs over which we iterate, initially it is AssigsCurrent
											% AssigsCurrent - list of Assigs over which is iterated. Once we discover a promotion
											%				  we take this list and preform promotion (and later max filtering)
											% OrigVars		- keeps the list of origVars at al times
											% AssigsFinal	- is set to AssigsCurrent when new promotion is not possible	
find_eligable_var_Assigs([Assig | AssigsIterate], AssigsCurrent,OrigVars,Bindings,AssigsFinal):-
	find_eligable_var_Assig(Assig,AssigsCurrent,OrigVars,Bindings,PromotedAssig),
	( 	PromotedAssig==[]																% no eligable has been foundis Assig
	-> 	find_eligable_var_Assigs(AssigsIterate,AssigsCurrent,OrigVars,Bindings,AssigsFinal)		% check next Assig
	; 	AssigsCurrentNew=[PromotedAssig | AssigsCurrent],
		findMaximalAssigs(AssigsCurrentNew,AssigsCurrentNewMax),
		find_eligable_var_Assigs(AssigsCurrentNewMax,AssigsCurrentNewMax,OrigVars,Bindings,AssigsFinal)
	).


%%
															% predicate iterates over Assig and succeeds if it finds a place in Assig
															% that is specialized to a constant and that is eliagalbe for promotion
find_eligable_var_Assig(Assig,AssigsCurrent,OrigVars,Bindings,PromotedAssig):-
	find_eligable_var_Assig2(Assig,Assig,AssigsCurrent,OrigVars,OrigVars,Bindings,PromotedAssig).


find_eligable_var_Assig2([],_,_,[],_,_,[]).						% the same as the above predicate just iterates over Assig
find_eligable_var_Assig2([Term | AssigIterate],Assig,AssigsCurrent,[OrigVar|OrigVarsIterate],OrigVars,Bindings,PromotedAssig):-
	getFiniteDomainBindings(OrigVar,Bindings,Values),	
	(	Values\=[], ground(Term),		% there are bindings,  
		are_all_bidnigns_in_assigs(Assig,AssigsCurrent,OrigVar,OrigVars,Values)
	->	renameAssigToOrigName(Assig,OrigVars,OrigVar,PromotedAssig)
	;	find_eligable_var_Assig2(AssigIterate,Assig,AssigsCurrent,OrigVarsIterate,OrigVars,Bindings,PromotedAssig)
	).
	 
%%
																			% predicate succseeds if AssigsCurrent exist assignments
are_all_bidnigns_in_assigs(Assig,AssigsCurrent,OrigVar,OrigVars,Values):- 	% the same as Assig except that on position OrigVar they have constants from Values
	create_assigments_at_var(Assig,OrigVars,OrigVar,Values,LookingAssigs),  % LookingAssigs are such assignments
	assigs_lists_contain(LookingAssigs,AssigsCurrent).						% and now we check whether AssigsCurrent contains all of them 
	

getFiniteDomainBindings(OrigVar,[Binding | Bindings],Values):-
	Binding=binding(Var,VarValues),
	(	Var==OrigVar 
	->	Values=VarValues
	;	getFiniteDomainBindings(OrigVar,Bindings,Values)
	).
	
	
%%%%%%%%%%%%%
% MICS:


%%%%%%%%%%%%
%getFiniteDomainBindings(OrigVar,Values):-
%	fdcs_var_bindings(Bindings),								% Bindings=[ binding(Code,[a,b]), binding(Lang,['En','Fr'])]
%	getFiniteDomainBindings2(Bindings,OrigVar,Values).
%
%% 
%getFiniteDomainBindings2([],_,[]).								% stopping point
%
%getFiniteDomainBindings2([Binding | Bindings],OrigVar,Values):-
%	Binding=bindings(Var,VarValues),
%	(	Var==OrigVar
%	->	Values=VarValues
%	;	getFiniteDomainBindings2(Bindings,OrigVar,Values)
%	).

%%%%%%%%%%%%
	
create_assigments_at_var(_,_,_,[],[]).							% predeciate creates list of assignments LookingAssigs where
																% on OrigVar position one finds the Values of a FDC that applies theree 
																% and the other positions are terms the same as in Assig
create_assigments_at_var(Assig,OrigVars,OrigVar,[Value | Values],[FreshAssig|LookingAssigs]):-
		create_assigments_at_var(Assig,OrigVars,OrigVar,Values,LookingAssigs),
		renameAssigToOrigName(Assig,OrigVars,OrigVar,NewAssig),				% Assig=[Pname,Lang,Pname1,Sname1,Code1,Sname2,primary,District2] -> [Pname,Lang,Pname1,Sname1,Code1,Sname2,Type2,District2]
		copy_term(tmp(OrigVar,NewAssig),tmp(FreshOrigVar,FreshAssig)),		% tmp(Type,[Pname,Lang,Pname1,Sname1,Code1,Sname2,Type2,District2]) ->tmp(TypeX,[PnameX,LangX,Pname1X,Sname1X,Code1X,Sname2X,Type2X,District2X]) 
		FreshOrigVar=Value,													% TypeX = middle
		setVarOrigNames_Terms(FreshAssig,OrigVars,OrigVars).				% FreshAssig==[Pname,Lang,Pname1,Sname1,Code1,Sname2,middle,District2]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% Predicates that operates on ASSIGNMENTS 
% (i.e., on guys like [Pname,'English',Pname,Sname1,halfDay,Sname1,'primary','Bolzano']

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% comparing assignments

findMaximalAssigs(Assigs,MaxAssigs):-								% interface of the predicate below
	findMaximalAssigs2(Assigs,[],MaxAssigs).

findMaximalAssigs2([],MaxAssigsCurrent,MaxAssigsCurrent).
findMaximalAssigs2([Assig | Assigs],MaxAssigsCurrent,MaxAssigsFinal):-
		(  not(subsumes_list_magik(Assigs,Assig)), not(subsumes_list_magik(MaxAssigsCurrent, Assig))
		-> append(MaxAssigsCurrent,[Assig],MaxAssigsCurrent2),
		   findMaximalAssigs2(Assigs,MaxAssigsCurrent2,MaxAssigsFinal)
		;  findMaximalAssigs2(Assigs,MaxAssigsCurrent,MaxAssigsFinal)
		).

% not confuse the predicate above with the predicates below that compares on exactness (respecting the var names) not containment

assigs_lists_contain([],_).								% predicate succeeds if first assignment list is contained in the other	
assigs_lists_contain([Assig | AssigList1],AssigList2):-
		assig_list_contains(Assig,AssigList2),
		assigs_lists_contain(AssigList1,AssigList2).
			
assig_list_contains(Assig,[Assig2| AssigList]):-		% predicate succeeds if exact Assig exists in List
	(	assig_equals(Assig,Assig2)
	->	true
	;	assig_list_contains(Assig,AssigList)
	).  
	
assig_equals([],[]).									% predicates succeeds if two assignents are exact	
assig_equals([Term1 | Assig1],[Term2 | Assig2]):-
	Term1==Term2,
	assig_equals(Assig1,Assig2).	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

										% renameAssigToOrigName(Assig,OrigVars,OrigVar,NewAssig)
										% renames all occurances of (potentially instantiated OrigVar in Assig) with original 
										% name of the variable
										% e.g., Assing=[X, a, b], OrigVars=[X,Y,Z], OrigVar=Y -> NewAssig=[X,Y,b]
renameAssigToOrigName([],[],_,[]).		% stopping point
	
renameAssigToOrigName([AssigTerm | Assig],[Var |  OrigVars],OrigVar,[NewTerm | NewAssig]):-
	(	Var==OrigVar
	->	NewTerm=OrigVar
	;	NewTerm=AssigTerm
	),
	renameAssigToOrigName(Assig,OrigVars,OrigVar,NewAssig).		

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% MICS: predicates that converts Assignments (list of output vars) to Specializations
% and vice-versa 

getSpecs_from_Assigments(_,[],[]).								% stopping point

getSpecs_from_Assigments(As,[Assig | Assigs],[Spec | Specs]):-  % Given set of assignments Assigs, the predicate creates a list of
			getSpecs_from_Assigments(As,Assigs,Specs),			% of specializations Specs
			getSpec_from_Assigment(As,Assig,Spec).
																% given the origal query As, and a Assign to it's variables
																% the predicate produces an Specializatin for this Assignments
getSpec_from_Assigment(As,Assig,Spec):-							% e.g., [pupil(N,S,C)] [N,'Goethe','a'] produces [pupil(N,'Goethe','a')] 
			copy_term(As,Spec),									% Spec=[pupil(Fresh_N,Fresh_S,Fresh_C)] 		
			term_variables_spec(Spec,AssigSpec),						% AssigSpec=[Fresh_N,Fresh_S,Fresh_C]
			AssigSpec=Assig.									% AssigSpec=[N,'Goethe','a'], and implicitly Spec=[pupil(N,'Goethe','a')]
			
%%

getAssigments_from_Specs(_, [],[]).								% stopping point

getAssigments_from_Specs(As, [Spec | Specs],[Assig |Assigs]):- 	% For every Spec in Specs the predicate obtains
			getAssigments_from_Specs(As, Specs,Assigs),			% a list of assignments for this Spec
			getAssigment_from_Spec(As, Spec,Assig).				% (see method below)
	
														% Given orignal query As, and it's specialization Spec this predicate obtains the set of assignments Assig
														% e.g., (pupil(N,S,C),pupil(N,'Goethe','a') -> [Pname,'Goethe','a'] 
getAssigment_from_Spec(As,Spec,Assig):-					% This is done without unifying vars in As!!!	
			copy_term(As,AsFresh),						% As=[pupil(N,S,C)] then AsFresh=[pupil(F_N,F_S,F_C)]
			term_variables_spec(AsFresh,Assig),		% Assig=[F_N,F_S,F_C]
			AsFresh=Spec,								% Spec=[pupil(N,'Goethe','a')] then AsFresh=[pupil(F_N,Goethe','a')] (implicitly Assig=[F_N,,Goethe','a'])
			term_variables_spec(As,OrigVars),					% OrigVars=[N,S,C]
			setVarOrigNames_Terms(Assig,OrigVars,OrigVars). % Assig=[N,'Goethe','a']
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
%%%	VARIABLE FDCS BINDINGS: Predicates compute for every variable in Query a list
%%% of constants that applies to them according to the FDCs

fdcs_var_bindings(Query,Bindings):-
		term_variables_spec(Query,Vars),
		initiate_var_bindings(Vars,BindingsInit),
		iterate_var_fdcs(Query,BindingsInit,Bindings).
	
	%	
initiate_var_bindings([],[]).
initiate_var_bindings([Var | Vars],[Binding | BindingsInit]):-
		initiate_var_bindings(Vars,BindingsInit),
		Binding=binding(Var,[]).
	
	%	
iterate_var_fdcs([],Bindings,Bindings).					%stopping point
iterate_var_fdcs([Atom | Query],Bindings,BindingsFinal):-
		fdcs(FDCs),
		iterate_var_fdcs_2(Atom,FDCs,Bindings,BindingsCurrent),
		iterate_var_fdcs(Query,BindingsCurrent,BindingsFinal).
		
	%
iterate_var_fdcs_2(_,[],BindingsFinal,BindingsFinal).			% iterate over FDCs to find appropiate 
iterate_var_fdcs_2(Atom,[FDC | FDCs],Bindings,BindingsFinal):-
		FDC = [B |  [ Var | [Values]]],							% [class(_,_,SchemeX), SchemeX,  [ 'halfDay' ,'fullDay' ]
		(	B=Atom												% class(_,_,Scheme)
		->	updateBindings(Bindings,Var,Values,BindingsNew)		% BindingsNew=[...binding(Scheme,['halfDay' ,'fullDay'])...]
		;	BindingsNew=Bindings
		),
		iterate_var_fdcs_2(Atom,FDCs,BindingsNew,BindingsFinal).
		
	%
updateBindings([],_,_,[]).										
updateBindings([Binding | Bindings],Var,Values,[BindingNew | BindingsNew]):-
		updateBindings(Bindings,Var,Values,BindingsNew),
		Binding=binding(Var2,Values2),
		(	Var2==Var										% we find bindings for this Var
		->	
			(	Values2==[]									% if there were no bindings
			->	Values3 = Values
			;	intersect_magik(Values, Values2, Values3)		% otherwise, new bindings is the intersecion with 
			),												% the one computed so far
			BindingNew=binding(Var,Values3)
		;	BindingNew=Binding								% otherwise, binding remains the same
		).
		
					
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% META-PROGRAM: FINDIND SPECIALIZATION FOR A GIVEN QUERY As
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	
% new 
instantiate_Q(As,Specs):- 
		atomsFKCons(As,Bs), 							% Bs are all fks consequences of As according the rules in FKs
		applyAssignmentsFDC(Bs,Bss), 					% Bss list of all BS  FDC-instantiations of skolem terms 
		( 	Bss=[[]]									% no FKS (therefore nor finite domains)
		->	instantiate_As_Bs(As,As, [], Specs)
		;	%writeln(Bss), 
			instantiate_Ass_Bss(As,[As],Bss, Specs)	% otherwise, find specializations for every Bs in Bss
		).   											
    
%%%%%%%   
   
												 			
instantiate_Ass_Bss(As, Specs, [Bs | Bss], Specs4):- 		% initally called with instantiateAtomsBss([As],Bss,Sols). 
	 	%write('Specs::='),writeln(Specs),
	 	%write('Bs::='),writeln(Bs),
	 	instantiate_Ass_Bs(As, Specs, Bs, Specs2),
	 	%write('Specs::='),writeln(Specs),
	 	%write('Bs::='),writeln(Bs),
	 	remove_skolem_Specs(Bs,Specs2,Specs3),				% replace skolem terms  with fresh vars in Specs	
	 	%setVarOrigNames_Specs(Specs3,As),					% rename those fresh vars with their orignal names		
	 	findMaximalSpecs(Specs3,[],MaxSpecs),				% extract maximal specializations		
	 	instantiate_Ass_Bss(As, MaxSpecs, Bss, Specs4).		% call specialization for the remaining Bss
 
instantiate_Ass_Bss(_, Specs, [], Specs). 					% stopping point. Specs obtained till this point are returned.
 
%%%%%% 

findMaximalSpecs([Spec | Specs],MaxSpecCurrent,MaxSpecsFinal):-
		(  not(subsumes_list_magik(Specs, Spec)), not(subsumes_list_magik(MaxSpecCurrent, Spec))
		-> append([Spec],MaxSpecCurrent,MaxSpecCurrent2),
		   findMaximalSpecs(Specs,MaxSpecCurrent2,MaxSpecsFinal)
		;  findMaximalSpecs(Specs,MaxSpecCurrent,MaxSpecsFinal) 
		).

findMaximalSpecs([],MaxSpecCurrent,MaxSpecCurrent).
%%%%%

instantiate_Ass_Bs(_, [], _, []).					% stopping point 

instantiate_Ass_Bs(As, [Spec | Specs], Bs, Specs3):-
		instantiate_As_Bs(As,Spec,Bs,Spec2),
		instantiate_Ass_Bs(As,Specs, Bs, Specs2), 
		append(Specs2,Spec2,Specs3). 
		  

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% MOST IMPORTANT NON-DETERMINISTIC STEPS ARE DONE WITHIN FINDALL
	
instantiate_As_Bs(As,Spec,Bs,MaxSpecs):-
		append(Spec,Bs,SpecBs),						% optimization: this step precomputes SpecBs before findall for optimization reasons
		findall(Spec,instantiateAtoms(Spec, Spec, Bs, SpecBs), Specs),
		setVarOrigNames_Specs(Specs,As),
		findMaximalSpecs(Specs,[],MaxSpecs).		% optimization:...

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

instantiateAtoms([],_,_,_).			% instantiateAtoms
instantiateAtoms([C | Cs ], As, Bs, AsBs):-
	instantiateAtom(C, As, Bs, AsBs),
	instantiateAtoms(Cs, As, Bs, AsBs).

%%

instantiateAtom(C, As, Bs, AsBs):-
	findall([C | As],instantiateAtom2(C, As, Bs, AsBs),Assigs),
	findMaximalSpecs(Assigs,[],AssigsMax),
	setVarOrigNames_Specs(AssigsMax,[C | As]),
	member(Assig,AssigsMax),						% nondeterministic step !!!
	[C|As]=Assig.

%%

instantiateAtom2(C, _, _, AsBs):- 					% instantiateAtom
	tc(C,G), 
	unifyAtoms(G,AsBs).		
%%
								
instantiateAtom2(C, As , Bs, AsBs):-				% if FKs semantics is enforced
	%fksSemantics('enforced'),
	%fks_enforced_closure(Source,C),					% and Source is 'complete'
	fks_enforced(Source,C),							
	%append(As,Bs,AsBs),							% Target should also be considered complete
	unifyAtom(C,AsBs),		 						% inspired with the rule: pupil_a(N,S,C):-pupil(N,S,C),learns_a(N,_).
	unifyAtom(Source,AsBs),							% Safety rule (new): Preventing Source atoms that do not exists in AsBs (i.e. in available db) to become true.
	instantiateAtom2(Source,As,Bs,AsBs).			% Does it work recursivly. predicate terminates becuase FKs are acyclic	 

%%

unifyAtoms([], _). 					% unify Atoms	 
unifyAtoms([C | Cs], Bs) :-
	unifyAtom(C, Bs),
	unifyAtoms( Cs, Bs). 
	 
unifyAtom(C,[C | _]).				% unify Atom
unifyAtom(C,[_ |Bs]):-
	unifyAtom(C,Bs).	
 
		
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Optimization: Precompute FKs dependecies, in a way...

fks_enforced_closure(Source,Target):-
	fks_enforced(Source,Target).
	
fks_enforced_closure(Source,Target):-
	fks_enforced(Source,Target2),
	fks_enforced_closure(Target2,Target).	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% predicates that renames variables to their original names (after findall is applied)

setVarOrigNames_Specs([Spec | Specs],As):-			% predicate instatiate original for every Specs
	getOrigVars(As,OrigVars),
	setVarOrigNames_Spec(Spec,As,OrigVars),
	setVarOrigNames_Specs(Specs,As).

setVarOrigNames_Specs([],_).		 					% stopping point


%%
setVarOrigNames_Spec([],[],_).						 % stopping point
													 % ASSUMPTION: ATOMS in SPECS are keeping their original order (the one that is in As)
setVarOrigNames_Spec([S | Spec],[A | As],OrigVars):- % predicate instatiate variable names in Spec with original variable names in As
	setVarOrigNames_Atom(S,A,OrigVars),
	setVarOrigNames_Spec(Spec,As,OrigVars).
 

		
%%
setVarOrigNames_Atoms([],_,_).						% used only in Instantiate_Atoms(...)
setVarOrigNames_Atoms([S | Ss],A,OrigVars):-
	setVarOrigNames_Atom(S,A,OrigVars),
	setVarOrigNames_Atoms(Ss,A,OrigVars).

%%


setVarOrigNames_Atom(S,A,OrigVars):- 
	S =.. TermListS,								% learns(Pname,'En') ->[learns,Pname,'En ']
	A =.. TermListA,
	setVarOrigNames_Terms(TermListS,TermListA,OrigVars).

setVarOrigNames_Terms([], [], _).											 % stopping point = when both lists are empty
setVarOrigNames_Terms( [TermS | TermListS], [TermA | TermListA], OrigVars):- % only varaibles in S are ranamed to their orignal name
	(  var(TermS), not(exact_member(TermS,OrigVars))						 % if TermS is already unified with some original Var then
	->	TermS=TermA															 % then unifying it again may crete unificiation in orignal atoms 
	;  true																	 % becuase some vars are shared....
	),
	setVarOrigNames_Terms(TermListS, TermListA,OrigVars).
	


%%

setVarOrigNames_Termss([],_).
setVarOrigNames_Termss([Terms | Termss],OrigVars):-		% used only in Instantiate_Atoms(...)
	setVarOrigNames_Terms(Terms,OrigVars,OrigVars),
	setVarOrigNames_Termss(Termss,OrigVars).
	
%%% END OF MAIN PREDICATES
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 


%%%%%%%%%%%%%%%%%%% 
% MISC predicateS %
%%%%%%%%%%%%%%%%%%%


freeze_magik(List,ListCopy):-						% freezing :)
	copy_term(List,ListCopy), 
	numvars(ListCopy).
%	numbervars_magik(ListCopy,0,_). 
	 
verify_magik(Goal):-								% checks if the goal is true without binding variables
	not(not(Goal)). 
	
subsumes_magik(Generic,Specific):-					% check if Generic is more general then Specific (without binding vars)
	subsumes_chk_magik(Generic,Specific).
	%
	%freeze_magik(Specific,SpecificFrozen),
	%subsumes_term(Generic, SpecificFrozen).			
	%verify_magik(Generic=SpecificFrozen).
	
%

subsumes_list_magik([Generic | GenericList],Specific):-		    % succseeds if Specific is less general then at least one in GenericList
	(	subsumes_magik(Generic,Specific)
	->	true
	;	subsumes_list_magik(GenericList,Specific)
	).
	
%subsumes_list_magik([],[]).							


%subsumes_list_magik([],Specific):-					% this line is not necessary. However, it makes clear when subsumes_list_magik can fail
%	Specific\=[],
%	fail.

%%%

getOrigVars([A | As],Vars):-							% methog extract var names from list of atoms As
		term_variables_spec(A,VarsA),
		getOrigVars(As,VarsAs),
		append(VarsAs,VarsA,Vars).
		
getOrigVars([],[]).									 	% stopping point


%subsitute__magik(OldTerm,NewTerm,List,NewList):-
%	subsitute_magik2(OldList,OldTerm,NewTerm,List,NewLisCurrent,NewList)


%substitute_magik2([],_,_ NewList, NewList).			%stopping point
 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% START: predicate for replacing skolem terms with a fresh variable
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

remove_skolem_Specs(_,[],[]).

remove_skolem_Specs(Bs,[Spec | Specs],SpecsNoSkolem2):-		% replace skolem terms with fresh variable
	remove_skolem_Specs(Bs,Specs,SpecsNoSkolem),
	remove_skolem_Spec(Bs,Spec,SpecNoSkolem),
	(	SpecNoSkolem == 'illegeal_skolem_join'				% means that atom in Spec is unfied with skolem term which 
	->	SpecsNoSkolem2 = SpecsNoSkolem						% we ingore it if is illegal
	;	SpecsNoSkolem2 = [SpecNoSkolem | SpecsNoSkolem]
	).
	
   
remove_skolem_Spec(Bs,AsSpec,AsSpecNew):-										% replace skolem term with fresh variable
		remove_skolem_Spec2(AsSpec,Bs,AsSpec,AsSpec,AsSpecNew).
%%%
 
remove_skolem_Spec2(_,_,[],AsSpecNewCurrent,AsSpecNewCurrent).					% stopping point - no more atoms 

remove_skolem_Spec2(AsSpec,Bs,[Atom | AsSpecIter],AsSpecNewCurrent,AsSpecNew):-			% find a skolem in Atom then replace all occurances
		Atom =.. AtomTerms,																% of this skolem in AtomNewCurrent and obtain AtomsNew
		remove_skolem_Atom(AsSpec,Bs,AtomTerms,AsSpecNewCurrent,AsSpecNewCurrent2),
		(	AsSpecNewCurrent2 == 'illegeal_skolem_join'	
		->	AsSpecNew = 'illegeal_skolem_join'											% stopping removing procedure and return with error
		; 	remove_skolem_Spec2(AsSpec,Bs,AsSpecIter,AsSpecNewCurrent2,AsSpecNew) 		% otherwise continue with removing skolem terms
		). 
 
%%    
  
remove_skolem_Atom(_,_,[], AsSpecNewCurrent,AsSpecNewCurrent). 
 
remove_skolem_Atom(AsSpec,Bs,[Term|Terms], AsSpecNewCurrent,AsSpecNew) :-			% find a skolem in Term then replace all occurances
 	( 	compound(Term)
		->  (	legeal_skolem_join(AsSpec,Bs,Term, AsSpec)							% checks if a skolem Term is legel (see method below)
  			
  			->  copy_term(X,X), 
  				substitute_in_atom_list(Term,AsSpecNewCurrent,X,AsSpecNewCurrent2),	% legal skolem -> replace is consistently with a fresh var
  				remove_skolem_Atom(AsSpec,Bs,Terms,AsSpecNewCurrent2,AsSpecNew)		% then -> go the next term
  			
  			;   AsSpecNew = 'illegeal_skolem_join'									% (EXIT) illegeal skolem term so discard this specialization
  			
  			)
  		; 	AsSpecNewCurrent2=AsSpecNewCurrent,										% constnant or var are preserved -> go to next Term
  			remove_skolem_Atom(AsSpec,Bs,Terms,AsSpecNewCurrent2,AsSpecNew)	
  	).
 
%%																			
																			% predicate checks if a skolem Term is legal
																			% i.e. if exists in another atom in As that is from Bs
legeal_skolem_join(AsSpec,Bs,Term, [Atom |AsSpecIter]):-						% no stopping point - becuase it AtamsNewCurrent==[] is a failure 
	Atom =.. AtomTerms,
	(	exact_member(Term,AtomTerms),										% if Term in some Atom
		exact_member(Atom,AsSpec),												% from As
		exact_member(Atom,Bs)												% and that atom is instanitated with some from Bs
	->	true																% then skolem is OK
	;	legeal_skolem_join(AsSpec,Bs,Term,AsSpecIter)							% otherwise try next atom in AtomsNewCurrent
	).
	
%%% 

substitute_in_atom_list(_,[],_,[]).											% stopping point

substitute_in_atom_list(Term,[Atom | AtomsNewCurrent], NewVar,[AtomNew | AtomsNewCurrent2]):-
	substitute_in_atom_list(Term,AtomsNewCurrent,NewVar,AtomsNewCurrent2),	% Substitute Term with NewVar in AtomsNewCurrent
	Atom =.. AtomTerms,														% and obtain AtomsNewCurrent2
	substitute_swi(AtomTerms, Term,NewVar,AtomTermsNew), 
	AtomNew =.. AtomTermsNew.

%%%
																			% this predicates definiton is copied from SWI 
substitute_swi([], _, _, []).												% stopping point
substitute_swi([O|T0], Old, New, [V|T]) :-									% in term T0 the predicate substitutes all occurances of Old 
  	(   Old == O															% with New. Outcome is a new term T
  	->  V = New
  	;   V = O
  	),
substitute_swi(T0, Old, New, T).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% END: predicate for replacing skolem term with a fresh variable
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% not used predicates (so far)
isSubset([],_).
isSubset([HeadA|ListA],ListB):-
    exact_member(HeadA,ListB),
    isSubset(ListA,ListB).
    
equal_lists(ListA,ListB):-
    isSubset(ListA,ListB),
    isSubset(ListB,ListA). 
    
%% 
    
exact_member(Element,[Head | List]):-
		(Element==Head
		->	true
		; exact_member(Element,List)
		).
				
exact_member(_,[]):-fail.		
		
		
%%% END OF THE MAIN PREDICATES
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
		
%%%%%%%%%%%%%%%%%%%%
% DEPRICATED METHODS
%%%%%%%%%%%%%%%%%%%%

instantiateQ(As):- 
		atomsFKCons(As,Bs), 					% Bs are all fks consequences of As according the rules in FKs
		applyAssignmentsFDC(Bs,Bss), 			% Bss list of all BS  FDC-instantiations of skolem terms 
		%write('WRITE in instantiateQ(As)  Bss:='),writeln(Bss).
	 	instantiateAtomsBss(As, As, Bss).   	% instantiate As with atoms in As and Bs from Bss
  
												% SPECIAL CASES (all tested with examples):
instantiateAtomsBss(As, As, [[]]):-				% CASE1: if fdcs=([]) it means no FDC exists. applyAssignmentsFDC produce Bss=[[Bs]]
		%writeln('ENTERINGinstantiateAtomsBss(As, As, [[]])'),
		%read(X),writeln(X),
		%write('WRITE  As:='),writeln(As),
		instantiateAtoms2(As, As, []).			% CASE2: if fdcs\=([]) but non of the fdcs apply on the atoms from Bs
												%		 not apply means: either FDCs are defined on the atom different from one in Bs
												%		 or arguments eligable for FDCS application are not skolem ones so FDCs cannot be applied	
												% CASE3: if Bs = [] then Bss=[[]]
												% CASE4: there exists a FDC with single value. Then only instantiations for this value 
												%		 has to be checked for completness.		
												% CASE5: The last iteration of the iteration below. Then to succed we need only to check the 
												%		 this last instantiations of FDCs - which is exactly what will happen.

instantiateAtomsBss(As, As, [Bs	| Bss]):-		% Bss=[Bs1,..., Bsk] if none of the above special cases (1-4) apply,
		%writeln('ENTERING instantiateAtomsBss(As, As, [Bs	| Bss])'),
		%write('WRITE As:='),writeln(As),
		%write('WRITE Bs:='),writeln(Bs),
		%write('WRITE Bss:='),writeln(Bss),
		%read(X),writeln(X),
		instantiateAtoms2(As, As, Bs),			% then for every Bsi we check if As is possible to specialize - for the same assigmnent on As vars!,
		%write('WRITE As:='),writeln(As),
		instantiateAtomsBss(As, As, Bss).
		
	
instantiateAtomsBss(As, As, []).				% the stopping point for the above iteration on Bss. 
												% If it succeeds, it means we sucseeded for all Bs in Bss 
		%writeln('ENTERING instantiateAtomsBss(As, As, [])'),
		%read(X),writeln(X). 
		 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
instantiateAtoms2(Cs, As, Bs):-
		%writeln('ENTERING instantiateAtoms2(Cs, As, Bs)'),
		instantiateAtoms(Cs, As, Bs).
 
%%


 	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% applyAssignmentsFDC
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 	
% module
%:- module(fdcsinstantiate,[instantiateFDCs/2,applyAssignmentsFDC/2]). 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
applyAssignmentsFDC(Bs,Bss):-									% predicate computes all instantiations of Bs according to FDCs and 
	getAssignmentsFDC(Bs,Assigns),								% creates a list of instantiatins Bss
	applyAssignmentsFDC1by1([Bs],Assigns,Bss).					% e.g., ?-applyAssignmentsFDC( [leanrs(N,f_l(N)), pupil(N,f_p1(N),f_p2(N)), school(f_p1(N),f_s1(f_p1(N)),f_s2(f_p1(N))) ],Bss)
																% 		Bss=[
																%		[leanrs(N,f_l(N)),pupil(N,Dante,a),school(Dante,primary,f_s2(f_p1(N)))],
																%		[leanrs(N,f_l(N)),pupil(N,Dante,a),school(Dante,middle,f_s2(f_p1(N)))],
																%		[leanrs(N,f_l(N)),pupil(N,Goethe,a),school(Goethe,primary,f_s2(f_p1(N)))],
																%		[leanrs(N,f_l(N)),pupil(N,Goethe,a),school(Goethe,middle,f_s2(f_p1(N)))],
																%		[leanrs(N,f_l(N)),pupil(N,Dante,b),school(Dante,primary,f_s2(f_p1(N)))],
																%		[leanrs(N,f_l(N)),pupil(N,Dante,b),school(Dante,middle,f_s2(f_p1(N)))],
																%		[leanrs(N,f_l(N)),pupil(N,Goethe,b),school(Goethe,primary,f_s2(f_p1(N)))],
																%		[leanrs(N,f_l(N)),pupil(N,Goethe,b),school(Goethe,middle,f_s2(f_p1(N)))]
																%			]
																
																% Note: A

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% getAssignmentsFDC and depended predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
												% get all fdcs assigments for complex terms 	
getAssignmentsFDC([ B | Bs ],Assigns):-			% for every atom in Bs and the variables that is eligable fro FDC instantiations
	getAssignmentsFDCatom(B,Assigns2),			% get the assignment (e.g., [f(X), [a,b] ]). Collect those assignments in Assigns.
	getAssignmentsFDC(Bs,Assigns3),				% e.g., call ?- getAssignmentsFDC( [leanrs(N,f_l(N)), pupil(N,f_p1(N),f_p2(N)), school(f_p1(N),f_s1(f_p1(N)),f_s2(f_p1(N))) ], Ass).
	append(Assigns3,Assigns2,Assigns).			% Ass = [[f_s1(f_p1(N)), [primary, middle]], [f_p1(N), ['Dante', 'Goethe']], [f_p2(N), [a, b]]] 
	
getAssignmentsFDC([],[]).						% stopping point = no atoms -> empty assignments

%%%%%%%%%%

getAssignmentsFDCatom(B,Assigns):- 				% get all fdcs assignments for atom B
		fdcs(FDCs),
		getAssignmentsFDCatom2(B,FDCs,Assigns).

%%%%%%%%%%%										
												

getAssignmentsFDCatom2(B, [FDC | FDCs], Assigns):-	% if a term in B is complex and 
		FDC = [B |  [Term | Values]],				% there is a fdcs that applies on the position of the term
		%not(simple(Term)),							% add this assignment into Assigns
		compound(Term),
		Assigns2=[ [ Term | Values]],
		getAssignmentsFDCatom2(B,FDCs,Assigns3),
		append(Assigns3,Assigns2,Assigns).
	
getAssignmentsFDCatom2(B, [FDC | FDCs], Assigns):-	% if the term is not complex (we skip this term)
		FDC = [B |  [Term | _]],					% Note 4: that if the term is not complex it is Var or Const
		%simple(Term),								% We assume that it cannot be const - otherwise FDCs or Query is incosistent and therefore complete
		not(compound(Term)),
		getAssignmentsFDCatom2(B,FDCs,Assigns).		% If it is Var it is subject to specializtion.  
													% WE (plan to) DO  PROMOTION OF SPECIALIZED VARS INTO NEW VARS AT THE PROLOG OUTPUT !!!
													
getAssignmentsFDCatom2(B, [FDC | FDCs], Assigns):-	% if FDC doesn't apply to the atom go the the next FDC
		FDC \= [B |  [_ | _]],
		getAssignmentsFDCatom2(B,FDCs,Assigns).



getAssignmentsFDCatom2(_,[],[]).					% stopping point = no fdcs -> empty assignments
						
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% applyAssignmentsFDC1by1 and depended predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	
																% predicates applies all assigments on Bss for all values and creates Bss3
applyAssignmentsFDC1by1(Bss,[Assign | Assigns],Bss3):-			% NOTE: We assume that all Assignments we generate are REAL, i.e, the Term 
	applySingleAssignmentFDC(Bss,Assign,Bss2),					% that we want to substitute exists in Bss. See NOTE1 (applySingleAssignmentFDCValues)
	applyAssignmentsFDC1by1(Bss2,Assigns,Bss3).					% Otherwise, for FASLE Assignments we get repeatatins of Bs in Bss as many times as |Values| size
																% e.g., applyAssignmentsFDC1by1([ [pupil(N,f1(N),f2(N)),learns(N,'french')], [pupil(N,f1(N),f2(N)),learns(N,'english')]],  [[f1(N), [ 'Dante','Goethe' ]], [f2(N), [a, b]] ], Bss3), writeln(Bss3)
																% Bss3=[[pupil(N,Dante,a),learns(N,french)],[pupil(N,Dante,a),learns(N,english)],
																%       [pupil(N,Goethe,a),learns(N,french)],[pupil(N,Goethe,a),learns(N,english)],
																%		[pupil(N,Dante,b),learns(N,french)],[pupil(N,Dante,b),learns(N,english)],
																%		[pupil(N,Goethe,b),learns(N,french)],[pupil(N,Goethe,b),learns(N,english)]]
																
applyAssignmentsFDC1by1(Bss,[],Bss).							% stopping point, no more assignments to apply 

%%%%%%%%%%%
	
applySingleAssignmentFDC(Bss,Assign,Bss2):-						 % this predicate just decomposes Assing into Term and Values
	Assign=[Term | [Values]],									 % and does the same as the predicate applySingleAssignmentFDCValues  
	applySingleAssignmentFDCValues(Bss,Term,Values,Bss2).						
																 % NOTE1: this predicate will multiply Bss into Bss4 as many times there are Values
																 % In principle, the Term substitutuon may not apply if there is no Term in Bss
																 % However, the only Assignments we generate are REAL ONE!!!
applySingleAssignmentFDCValues(Bss,Term,[Value | Values],Bss4):- % for each value in Values it replaces all occurances of Term with that value
	applyInstantiationBss(Bss,Term,Value,Bss2),					 % replaces are NOT DONE simulataniously but independently for each value
	applySingleAssignmentFDCValues(Bss,Term,Values,Bss3),		 % e.g., ?-applySingleAssignmentFDCValues([ [pupil(N,f1(N),f2(N)),learns(N,'french')], [pupil(N,f1(N),f2(N)),learns(N,'english')]], f2(N), [a,b], Bss4).
	append(Bss2,Bss3,Bss4). 									 % Bss4 = [[pupil(N, f1(N), a), learns(N, french)], [pupil(N, f1(N), a), learns(N, english)], [pupil(N, f1(N), b), learns(N, french)], [pupil(N, f1(N), b), learns(N, english)]]
	
applySingleAssignmentFDCValues(_,_,[],[]).

%%%%%

applyInstantiationBss([Bs | Bss],Term,Value,Bss3):-		% replaces each occurance of Term in Bss with Value 
	applyInstantiationBs(Bs,Term,Value,Bs2),			% and collect them in Bss3
	applyInstantiationBss(Bss,Term,Value,Bss2),			% e.g., ?- applyInstantiationBss([ [pupil(N,f1(N),f2(N)),learns(N,'french')], [pupil(N,f1(N),f2(N)),learns(N,'english')]], f2(N), a, Bss3).
	append([Bs2],Bss2,Bss3).							% Bss3 = [[pupil(N, f1(N), a), learns(N, english)], [pupil(N, f1(N), a), learns(N, french)]]
	
applyInstantiationBss([],_,_,[]).						%stopping point, for no atomss we get no instantiationss

%%%%%	
	
applyInstantiationBs([B | Bs],Term,Value,Bs3):-			% replaces each occurance of Term in Bs with Value 
	applyInstantiationB(B,Term,Value,B2),				% and collect them in Bs3
	applyInstantiationBs(Bs,Term,Value,Bs2),			% e.g., ?-applyInstantiationBs([pupil(N,f1(N),f2(N)),class(f2(N),f2(f1(N)),f4(N))], f2(N), a, Bs3).
	append([B2],Bs2,Bs3).								% Bs3 = [pupil(N, f1(N), a), class(a, f2(f1(N)), f4(N))] ;
	

applyInstantiationBs([],_,_,[]).						%stopping point, for no atomss we get no instantiationss	

%%%%%	
													%	applyInstantiationB(+B,+Term,+Value,-B2)
applyInstantiationB(B,Term,Value,B2):-				% 	replaces each occurance of Term in B with Value 
	B =.. TermList,									% 	e.g., ?-applyInstantiationB(pupil(N,f1(N),f2(N)), f2(N), a, B2).
	applyInstantiationTermList(TermList, Term, Value, NewTermList),
	B2 =.. NewTermList.								%  B2 = pupil(N, f1(N), a)
	

			
applyInstantiationTermList([Member | TermList], Term, Value, NewTermList2):-	%  applyInstantiationTermList( TermList, Term, Value, NewTermList2)
	applyInstantiationTermList(TermList, Term, Value, NewTermList),				% Given a TermList the predicate replaces each (exact) occurance of Term 
	applyInstantiationTerm(Member, Term, Value, NewTerm),						% with Value and collects them in NewTermList2
	append([NewTerm], NewTermList, NewTermList2).								
																				% E.g.,  applyInstantiationTermList([pupil, X, f1(X), f2(X)], f2(X), a, NewTermList).
applyInstantiationTermList([], _, _, []).										%			NewTermList = [pupil, X, f1(X), a]

%%%%

applyInstantiationTerm(Member, Term, Value, Value):-							% applyInstantiationTerm(+Member,+Term,+Value,-NewMember)
	Member==Term.

applyInstantiationTerm(Member, Term, _, Member):-								% if Member is equal to Term then replace it with return the Value,
	Member\==Term.																% otherwise return the old Member



	
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% DEPRICATED predicateS	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% instantiateFDCs(+Bs, -Cs), given a list of atoms it return list of lists of all FDCs instantiations of Bs
instantiateFDCs(Bs,Cs):-			% !!!!Assuming that we have at most 1 fdcs (allowing it to be over multiple attributes)
	instantiateFDCs2(Bs,Css),
	cartprod(Css,Cs).

instantiateFDCs2([],[]).			% stopping point

% instantiateFDCs2(+Bs, -Cs), given a list of atoms it return list of lists of all FDCs instantiations of Bs
instantiateFDCs2([B | Bs],Css):-		%
	fdcs(FDCs),						% from input.pl
	instantiateFDCs3([B], FDCs, C),	%
	write('writeln C:='),writeln(C), 
	write('writeln B:='),writeln(B),
	instantiateFDCs2(Bs, Cs),		% assuming that we have at most one finite domain per atom
	append(Cs,C,Css).			
	
% instantiateFDCs2(+Bs, -Cs) 		% for every atom create all fd instantiations of B
instantiateFDCs3(BsX ,[FDC | FDCs ], Css):-
	BsX	= [B | _],					% first atom (we can pick any)
	write('writeln BsX='),writeln(BsX), 
	FDC = [B |  [Var | [_]]],		% if B unifies with FDC atom then we apply it 
	%write('writeln FDC='),writeln(FDC),
	%not(simple(Var)),				% Var has to be term of dept >0 (e.g., f(X), f(g(X)))
	compound(Var),
	write('writeln Var='),writeln(Var), 
	write('writeln instantiateFDCs4(BsX, FDC ,Cs) then BsX='),writeln(BsX),
	write('writeln instantiateFDCs4(BsX, FDC ,Cs) then FDC='),writeln(FDC),
	instantiateFDCs4(BsX, FDC ,Cs),	% (assuming that FDCs are correctly defined)
	writeln('writeln instantiateFDCs4(BsX, FDC ,Cs)'),
	write('writeln instantiateFDCs4(BsX, FDC ,Cs) then Cs='),writeln(Cs),
	instantiateFDCs3(Cs, FDCs, Css),
	write('writeln instantiateFDCs3(Cs, FDCs, Css) then FDCs='),writeln(FDCs),
	write('writeln instantiateFDCs3(Cs, FDCs, Css) then Css='),writeln(Css).  
	 
instantiateFDCs3(BsX,[FDC | FDCs ],Css):-
	BsX = [B | _],					% first atom (we can pick any)
	FDC = [B |  [Var | [_]]],		% if B unifies with FDC atom then we apply it 
	%simple(Var),					% BUT, Var is either constant or variable
	not(compound(Var)),
	instantiateFDCs3(BsX,FDCs,Css).  % the WE DON'T SPECIALIZE (we do it at the output)

	
instantiateFDCs3(BsX,[FDC | FDCs],Css):- % if B do not unify with FDC atom then we apply it 
	BsX = [B | _ ],						% go to the next FDC
	FDC \= [B | _ ],				
	instantiateFDCs3(BsX,FDCs,Css).
	

instantiateFDCs3(BsX,[],BsX).			% stopping point - no mor finite domain constraints
  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
%	instantiateFDCs4(+Bs, +FDC, -Cs3)		
%	Given a list of atoms Bs,and a FDC, the predicate creates FDC instantiation 
%	for each atom B in Bs. For example,  
%   call with 
%		 ?- instantiateFDCs4([pupil(PnameX,'Dante',CodeX)], 
%					[pupil(Pname,Sname,Code), Code,  [ pupil(Pname,Sname,'a'), 	pupil(Pname,Sname,'b') ] ], Cs3).
%			PnameX = Pname,
%			CodeX = Code,
%			Sname = 'Dante',
%			Cs3 = [pupil(Pname, 'Dante', a), pupil(Pname, 'Dante', b)].

instantiateFDCs4([B | Bss], FDC,Cs3):-	% (assuming that FDCs are correctly defined)
	FDC = [B |  [_ | [Values]]], 
	instantiateFDCs4(Bss,FDC, Cs2),
	append(Values,Cs2,Cs3).
	%writeln(Bss),
   
instantiateFDCs4([],_,[]).					% stopping point




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% Auxilary Predicates	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% Verison 1.0 for the cartesian product implementation based on 
% double recursion ,one for all of the elements of the set and the other
% for all the elements-(lists) of the cartesian product.

cartprod([H], L) :-
   cartprod2([[]], H, L).
cartprod([H | T], L) :-
   cartprod(T, R),
   cartprod2(R, H, L).

cartprod2([], _, []).
cartprod2([H | IT], T, L) :-
   distribute(H, T, F),
   cartprod2(IT, T, R),
   append(F, R, L).

% distribute takes an element and a list of elements and combine
% the element with each element from the list creating a new list of lists.

distribute(_, [], []).
distribute(X, [H | T], [L | R]) :-
   append([H], X, L),
   distribute(X, T, R).		
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% END DEPRICATED predicateS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 
 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% META (FK consequences) predicates for compting chase of a given set of atoms As 
% (not including As)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% call with ?- atomsFKCons([ learns(Pname,Lang),pupil(Pname,Sname,Code), school(Sname,Type, District) ],Cons).
%			Cons = [] ;
%			false.
% call with ?- atomsFKCons([ learns(Pname,Lang) ],Cons).
%			Cons = [pupil(Pname, f1(Pname), f2(Pname)), school(f1(Pname), f3(f1(Pname)), f4(f1(Pname)))] ;
%			false.
% This predicate, in contrast to "fks(FKs), fkConsenquences([learns(Pname,Lang)],FKs,Bs)." keeps
% the variable names as given in the base (As). 

atomsFKCons(As,Cons):-  
		%consult('/Volumes/DATA/DATA2013/PHD_2013/Implementation/MAGIK/prolog/MAGIK/spezialization_meta/input.pl'), 
		atomsFKCons1(As, Cons, As). 

% Decription: 
%	Layer 1: In the first step it collects fk consequences of As in New2. If New2=[] it terminates
%			 If not it collects the fk consequencess of New2 and so forth.
%			 At the end it creates transitive closure of all fk-consequences of As.
%			 ! Assuming that FKs are acyclic we know that such procedure terminates.

%	Layer 2: Collects all immediate fk consequences of As in Cons2. 
%			 It also keeps track 


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%		
% Layer 1
% atomsFKCons1( +Atoms, -ImmediateConsequnces, +AllConsequences)
%
% test with: ?- atomsFKCons1( [learns(Pname,Lang)], Cons, [] ).
%			Cons = [pupil(Pname, leanrs_pupil1(Pname), leanrs_pupil2(Pname)), 
%					class(leanrs_pupil2(Pname), pupil_class1(leanrs_pupil2(Pname)), pupil_class2(leanrs_pupil2(Pname))), 
%					school(leanrs_pupil1(Pname), pupil_school1(leanrs_pupil1(Pname)), pupil_school2(leanrs_pupil1(Pname)))] ;
%			false.


atomsFKCons1([],[],_).							% stopping condition 

atomsFKCons1(As, Cons1, AllCons):-
		As \= [],								% fails if As=[] (to prevent to have superfluous succesful branching)
		atomsFKCons2(As, Cons2, AllCons),		% collect all fk conseqeunces of As 
		append(AllCons,Cons2,AllCons2),
		atomsFKCons1(Cons2, Cons3, AllCons2),	% collect all fk consequences of Cons2 atoms in Cons3
		append(Cons2,Cons3,Cons1).				% all fk consequences (from As and from previous iterations)
		
		

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%		
% Layer 2
% atomsFKCons( Atoms, AllConsequences)
atomsFKCons2([A | As], Cons3, AllCons) :-
		atomFKCons2(A, Cons1, AllCons), 
		append(AllCons,Cons1,AllCons2),		
		atomsFKCons2(As, Cons2,AllCons2),	
		append(Cons1,Cons2,Cons3).	
		
atomsFKCons2([], [],_). 						% stopping condition 
		
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%		
% Layer 3
% atomFKCons( Atom, Cons) - generates all FK consequences of Atom and places them into Cons
% if a key projection of a consequence is already in AllCons (generated so far we do not add new 
% consequence. That's required to apply chase correctly.		

% test with:
%	?-atomFKCons2( learns(Pname,Lang), Cons , [] ).
%		Cons = [pupil(Pname, leanrs_pupil1(Pname)), leanrs_pupil2(Pname)] ;

atomFKCons2(A, Cons, AllCons):-
	fks(FKs), 
	atomFKCons3(A, FKs, Cons, AllCons). 
	
atomFKCons3(A, [ FK  | FKs], ConsNew, AllCons):-
	FK = [A | [B] ],
	keyAtom(B,KeyB),							% get a key projection of atom B2
	keyAtoms(AllCons,KeyAllCons),				% get keys from AllCons 
	nonmember(KeyB,KeyAllCons),	 
	append(AllCons, [B], AllCons2),				% append B iff there is no B in AllCons.
	atomFKCons3(A, FKs, Cons, AllCons2),
	append(Cons, [B], ConsNew).
	
atomFKCons3(A, [ FK | FKs], Cons, AllCons):-
		FK = [A | [B]],
		keyAtom(B,KeyB),							% get a key projection of atom B2
		keyAtoms(AllCons,KeyAllCons),				% get keys from AllCons
		not(nonmember(KeyB,KeyAllCons)),			% if B2 key is alrady in some of keys from AllCons 
		atomFKCons3(A, FKs, Cons, AllCons).			% we do not add B2 into the AllCons
	
atomFKCons3(A, [ [A1 | _ ] | FKs], Cons, AllCons):-
			A \= A1, % A and A1 cannot unify
			atomFKCons3(A, FKs, Cons, AllCons).

atomFKCons3(_, [], [], _).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% Auxilary Predicates	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% keyAtoms(+As, -KeyAs) get primary key atoms from As and put it in KeyAs
keyAtoms([A | As],KeyAs):-
		keyAtom(A, KeyA),
		keyAtoms(As, KeyAs2),
		append(KeyAs2, [KeyA], KeyAs).
	
keyAtoms([],[]).							% stopping point

% keyAtom(+A, -KeyA) get primary key atom from A and put it in KeyA
keyAtom(A,KeyA):-
		pks(Keys),
		keyAtom1(Keys,A,KeyA).
	
keyAtom1([ [A | [KeyA]] | _ ], A, KeyA ).	% KeyA is a key projection of A 

keyAtom1([ [A2 | _] | Keys ], A, AKey ):-	% serach next key in Keys
		A2\=A,								% preventing the program from irrelevant branching
		keyAtom1(Keys , A, AKey).	
	 
keyAtom1([], _, []). 						%stopping condition
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	
%	nonmember(+B, +As). succseed if B is a EXACT (w/o unification) member of As
nonmember(_, []).
nonmember(B, [A|As]):-
	B \== A , 			% i.e., B and A have not been bound to or share same value
	nonmember(B, As).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%bla(Sname,Pname):- 
%	member(		school(Sname, f3(Sname), f4(Sname)), 
%				[ pupil(Pname, f1(Pname), f2(Pname)), school(f1(Pname), f3(f1(Pname)), f4(f1(Pname)))]
%		 ).
%	
%bla2(Sname,Pname):- 
% 	not(
% 		member(school2(f1(Pname), f3(f1(Pname)), f4(f1(Pname))), 
% 		[ pupil(Pname, f1(Pname), f2(Pname)), school(Sname, f3(Sname), f4(Sname))] 
% 				)
% 		).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% EXTRA PREDICATES
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



term_variables_spec(Spec, Vars):-
	term_variables_magik(Spec,Vars).
%	term_variables(Spec,Vars).
%	term_variables_spec2(Spec, Vars2),			% possibly with duplicates
%	findMaximal_vars(Vars2,[],Vars).
%%
	
findMaximal_vars([],MaxVars,MaxVars2):-			% to keep the order
		reverse(MaxVars,MaxVars2).
findMaximal_vars([Var | Vars],MaxVarsCurrent,MaxVarsFinal):-
		(  not(exact_member(Var,MaxVarsCurrent))
		-> MaxVarsCurrent2 =[ Var| MaxVarsCurrent ],		% faster then append
		   findMaximal_vars( Vars,MaxVarsCurrent2,MaxVarsFinal)
		;  findMaximal_vars( Vars,MaxVarsCurrent,MaxVarsFinal)
		).
			
%%

term_variables_spec2([], []).
term_variables_spec2([A | Specs], Vars):-
	A =..TermsA,
	term_variables_terms2(TermsA,VarsA),
	term_variables_spec2(Specs, Vars2),
	append(VarsA,Vars2,Vars).
	
%%
			
term_variables_terms2([],[]).
term_variables_terms2([Term | Terms],Vars2):-
	term_variables_terms2(Terms,Vars),
	( var(Term)
	->	Vars2=[Term | Vars]
	;	Vars2=Vars
	).
%%	
	
%



%   The previous two predicates operate on ground arguments, and have some
%   pretence of being logical (though at the next level up).  The next one
%   is thoroughly non-logical.  Given a Term,
%	variables(Term, VarList)
%   returns a list whose elements are the variables occuring in Term, each
%   appearing exactly once in the list.  var_member_check(L, V) checks
%   that the variable V is *not* a member of the list L.  The original
%   version of variables/2 had its second argument flagged as ?, but this
%   is actually no use, because the order of elements in the list is not
%   specified, and may change from implementation to implementation.
%   The only application of this routine I have seen is in Lawrence's code
%   for tidy_withvars.  The new version of tidy uses copy_ground (next page).
%   If that is the only use, this routine could be dropped.

 
term_variables_magik(Term, VarList):-
%	term_variables(Term,VarList). 
	term_variables2(Term, VarList).
 
term_variables2(Term, Vars) :-
	listofvars(Term, Vars, []).

term_variables2(Term, Vars,Tail) :-
	listofvars(Term, Vars, Tail).

listofvars(Term, Vh, Vt) :-
	(var(Term)
	 ->	Vh = [Term | Vt]
	 ;	Term =.. [_|Args],
		listofvars1(Args, Vh, Vt)
	).

listofvars1([], V, V).
listofvars1([T|Ts], Vh, Vt) :-
	listofvars(T, Vh, Vm),
	listofvars1(Ts, Vm, Vt).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
intersect_magik([], _, []).

intersect_magik([Element|Residue], Set, Result) :-
	member(Element, Set),		% Need not be memberchk because of
	!,				% the cut here
	Result = [Element|Intersection],
	intersect_magik(Residue, Set, Intersection).

intersect_magik([_|Rest], Set, Intersection) :-
	intersect_magik(Rest, Set, Intersection).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

    
 %%%%%%%
 subsumes_chk_magik(T1,T2) :-
%	subsumes_term(T1,T2).
   \+ ( numvars(T2), \+ (T1 = T2) ).


% numvars(+Term,-NewTerm)
%  Instantiates each variable in Term to a unique
%  term in the series vvv(0), vvv(1), vvv(2)...
    
numvars(Term) :-
   numvars_aux(Term,0,_).

numvars_aux(Term,N,N) :- atomic(Term), !.

numvars_aux(Term,N,NewN) :-
   var(Term), !,
   Term = vvv(N),
   NewN is N+1.

numvars_aux(Term,N,NewN) :-
   Term =.. List,
   numvars_list(List,N,NewN).

numvars_list([],N,N).

numvars_list([Term|Terms],N,NewN) :-
   numvars_aux(Term,N,NextN),
   numvars_list(Terms,NextN,NewN).
   
   
  %%%%%%%%%%%
  