%module definition
:-  module(input,[relation/1,pks/1,fks/1,fks_enforced/2, fdcs/1,tc/2]). 
%
:-dynamic 
%	relation/1,
%	pks/1,
%	fks/1,
	fks_enforced/2.
%	fksSemantics/1, 
%	fdcs/2,
%	tc/2,
%	fdcs/1.
	 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% Schema Constraints
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% schema

relation(rel(3,school(_,_,_))).
relation(rel(2,pupil(_,_,_))).
relation(rel(4,class(_,_,_))).
relation(rel(1,learns(_,_))).

%%

	
% primary keys
pks([  
	[ learns(Pname,_),		learns_key(Pname)	], 
	[ pupil(Pname,_,_),		pupil_key(Pname)	],
	[ school(Sname,_,_),	school_key(Sname)	],
	[ class(Code,_,_),		class_key(Code)		] 
	]).

% foreign keys 
fks([	
%% %	[learns(Pname,_),	pupil(Pname,f_pupil_1(Pname),f_pupil_2(Pname))		],	% FK: learns[Pname] REFERENCES pupil[PName] (in pupil(Name,School,Code))
%% %	[pupil(_,Sname,_),	school(Sname,f_school_1(Sname),f_school_2(Sname))	]  % FK: pupil[Sname] REFERECENS school[SNAME]
%% %	[pupil(_,_,Code),	class(Code,f_class_1(Code),f_class_2(Code))			]	% FK: pupil[Code] REFERENCES class[Code] (in class(Code,Level,Schema))
	]). 
	
% fks_enforced(learns(Pname,_),	pupil(Pname,_,_)).
% fks_enforced(pupil(_,Sname,_),	school(Sname,_,_)	).
% fks_enforced(pupil(_,_,Code),	class(Code,f_class_1(Code),f_class_2(Code))	).
	
%FK semantics. NOTE: This is global semantics for ALL fks!
%fksSemantics('enforced').  		
%fksSemantics('nonenforced').

% finite domain cosntraints
%fdcs([]).

		
	
% NEW ENCODING OF FDCS
	
	fdcs([ 
%% %	[learns(_,Lang1), 	Lang1,  [ 'English', 'French' ] ],
%% %	[pupil(_,_,Code2), 	Code2,  [ 'a', 'b' ] ],			% pupil[Code] in {a, b} 
%% %	[pupil(_,Sname3,_), Sname3, [ 'Dante','Goethe' ] ],			
%% % [school(_,Type4,_), Type4,  [ 'primary' ,'middle' ] ] 	% school[Type] in {primary, middle}
%% %	[class(_,_,Scheme), Scheme,  [ 'halfDay' ,'fullDay' ] ] 	
	]).
	   

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% TC-statements 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	
% tc(pupil(Pname,Sname,'a'), []). % no condition
% tc(pupil(Pname,Sname,'b'), []). % no condition

%tc1: school_a(Sname,'primary',District)	:- school_i(Sname,'primary',District). 
% tc(school(Sname,'primary',District), []).
tc(school(_,'primary',_), []).

%tc(school(Sname,'middle',District), []).
%% tc(school(_,'middle','Bolzano'), []).
 
% tc(pupil(_,Sname,_), [school(Sname,_,'Bolzano')]).

%tc2: pupil_a(Pname,Sname,Code)	:- pupil_i(Pname,Sname,Code).
%% tc( pupil(_,_,_) , [] ). 
% tc( pupil(Pname,Sname,'a') , [] ).  
% tc( pupil(_,_,'a') , [] ).
%% tc( pupil(_,_,C) , [class(C,_,'halfDay')] ). 
%% tc( pupil(_,_,C) , [class(C,_,'fullDay')] ). 
tc( pupil(_,Sname,_) , [school(Sname,_,'Bolzano')] ). 

%tc( pupil(Pname,Sname,'b') , [] ). 
% tc( pupil(_,_,'b') , [] ).    

%tc3: class_a(Code,Level,'halfDay') :- class_i(Code,Level,'halfDay').
%tc(class(Code,Level,'halfDay'), []). 
tc(class(_,_,'halfDay'), []).  

%tc4: class_a(Code,Level,'fullDay') :- class_i(Code,Level,'fullDay').
%tc(class(Code,Level,'fullfDay'), []). 
tc(class(_,_,'fullDay'), []).

%tc4: learns_a(Pname,'English'):- learns_i(Pname,'English'), pupil_i(Pname,Sname,Code), school_i(Sname,'primary', District).
%tc(learns(Pname,'English'), [pupil(Pname,Sname,Code), school(Sname,'primary', District)]).
tc(learns(Pname,'English'), [pupil(Pname,Sname,_), school(Sname,'primary', _)]).

%tc5: learns_a(Pname,'English'):- learns_i(Pname,'English'), pupil_i(Pname,Sname,Code), school_i(Sname,'middle', District).
%tc(learns(Pname,'English'), [pupil(Pname,Sname,Code), school(Sname,'middle', District)]).
tc(learns(Pname,'English'), [pupil(Pname,Sname,_), school(Sname,'middle', _)]).

%tc(learns(Pname,'English'), [pupil(Pname,Sname,_), school(Sname,_, _)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Queries
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% query1([Pname1,Sname1,Code1]):- 
% 	instantiateQ([pupil(Pname1,Sname1,Code1)]). % WORKS! 
%
%query2([Pname,Sname,Code,Lang]):- 
%	instantiateQ([pupil(Pname,Sname,Code), school(Sname,'primary', 'Bolzano'), learns(Pname,Lang)]). % WORKS!
%
%query3([Pname,Lang,Pname1,Sname1,Code1,Sname2, Type2, District2]):-
%	 instantiateQ([ learns(Pname,Lang), pupil(Pname1,Sname1,Code1), school(Sname2, Type2, District2)]). % WORKS!
%	
%query4([Pname,Lang,Sname,Code,Type, District]):-
%	instantiateQ([ learns(Pname,Lang),pupil(Pname,Sname,Code), school(Sname,Type, District) ]). % WORKS!
%
%query5([Pname,Lang]):- 
%	instantiateQ([learns(Pname,Lang)]). % WORKS!
%	
%query6([Pname,Lang,Sname,Code,Schema]):-
%	instantiateQ([pupil(Pname,Sname,Code),school(Sname,'primary','Bolzano'), class(Code,'1',Schema),  learns(Pname,Lang)]). 	
%	
% 