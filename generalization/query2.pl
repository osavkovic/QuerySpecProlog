%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% We consider the schema: 
% pupil(pname , code , sname ), school(sname , type , district ), learns(pname , lang ).
% we extend relation atom with an indexing argument 
% pupil(pname , code , sname, index ), school(sname , type , district,index ), learns(pname , lang,index).
% that will corspond the number of application of the G_C operator (G_C^i).
% the atoms from the initial query Qpbl will have index 0, 
% then atoms in  Qpbl' = G_C(Qpbl) will have index 1, etc 
% Since we know that the fix-point has to be obtained after at most |Q| steps
% we also define max for index (see below)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% QUERY
% CANONICAL_DATABASE_OVER_THE_IDEAL_SCHEMA.
% Qpbl(N) <- pupil(N,C,S),school(S,primary,bolzano),learns(N,L)
pupil(frozen_N,frozen_C,frozen_S,0).	
school(frozen_S,primary,bolzano,0).
learns(frozen_N,frozen_L,0).
index(0). % aux predicate
index(1).
index(2).
index(3).
max_index(3). 
% fixpoint(_). % fix_point(i) is true iff G_C^i(Q) is the least fix point (up to syntactic equivalence)
#maxint=3.    % dlv requires this to set for our TC encoding. Since it does the grounding... 
			  % i hope it does ground somewhat meaningfully 
			  % we also cannot use numbers as arguments but constants under quotes since we set here to 
			  % the number of atoms
outputVars(frozen_N). % listing all output variables.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TC_STATEMENTS.
%  Csp: 	Compl(school(S, primary , Y ); true), 
%  Cpb:		Compl(pupil(N, C, S); learns(N, english)), // more conditions than for q1
%  Cenp:	Compl(learns(N, english); pupil(N, C, S), school(S, primary, Y )), 
%  Cenm:	Compl(learns(N,english); pupil(N,C,S),school(S,middle,Y)).

school(S, primary , Y, Ind1) :- school(S, primary , Y , Ind), aux_index(Ind,Ind1,MI).
pupil(N, C, S, Ind1)		 :- pupil(N, C, S, Ind), learns(N, L,Ind), aux_index(Ind,Ind1,MI).
learns(N, english,Ind1)		 :- learns(N, english,Ind), pupil(N, C, S,Ind), 
						  		school(S, primary, Y ,Ind), aux_index(Ind,Ind1,MI).
learns(N, english,Ind1)		 :- learns(N, english,Ind), pupil(N, C, S,Ind), 
						  		school(S, middle, Y,Ind),aux_index(Ind,Ind1,MI).

aux_index(Ind,Ind1,MI) :- index(Ind), #succ(Ind, Ind1), max_index(MI), Ind1 <= MI. % auxiliary predicate


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% We check if the number of atoms after apply T_C is the same as before 
% if it is the same we have a fix point 
% otherwise, we continue
% predicate num_ot_atoms(Count, Ind) contains number of atoms for each Ind

% To do so, for each relation and at each index we introduce a counter and then we sum-up all counters
pupil_atoms(Count,Ind)	:- index(Ind), Count = #count{N,C,S : pupil(N,C,S,Ind)}.
school_atoms(Count,Ind)	:- index(Ind), Count = #count{S,T,P : school(S,T,P,Ind)}.
learns_atoms(Count,Ind) :- index(Ind), Count = #count{N,L : learns(N,L,Ind)}.
num_ot_atoms(Count, Ind):- pupil_atoms(Count1,Ind),school_atoms(Count2,Ind),learns_atoms(Count3,Ind),
						   +(Count1,Count2,CountTmp), +(Count3,CountTmp,Count).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Finally we check we want to find what is the minimal Ind for which 
%  	num_ot_atoms(Count, Ind)  and 	num_ot_atoms(Count, Ind+1) 		
fixpoint(LeastFixPoint) :- LeastFixPoint = #min{Ind : num_ot_atoms(Count, Ind), #succ(Ind, Ind1), num_ot_atoms(Count, Ind1)}.
					

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Finding if the returned query is safe					
vars(X) :- fixpoint(LFP), pupil(X,_,_,LFP).
vars(X) :- fixpoint(LFP), pupil(_,X,_,LFP).
vars(X) :- fixpoint(LFP), pupil(_,_,X,LFP).
vars(X) :- fixpoint(LFP), school(X,_,_,LFP).
vars(X) :- fixpoint(LFP), school(_,X,_,LFP).
vars(X) :- fixpoint(LFP), school(_,_,X,LFP).
vars(X) :- fixpoint(LFP), learns(X,_,LFP).
vars(X) :- fixpoint(LFP), learns(_,X,LFP).

notsafe :- outputVars(X), not vars(X).
safe 	:- not notsafe.

% checking if the least fix point atoms contain all safe variables 
% ie., if for every output variable there exists at least one atom that contains it.


% Alternatively, we can also check at each Ind to see if we already created a fix point 
% and then prevent further application of TC statements. 
% However, due the grounding procedure of ASP solvers this would 
%  - create longer rules with more variables thus more grounding instances of the rule
%  - moreover, the grounding would anyhow would ground all rules in all possible ways 
% using all integers in the program, regardless of additional conditions.
% Hence this approach might be even slower (which is bit counter intuitive)
% Yet, one would need to test two approaches to make final conclusion.