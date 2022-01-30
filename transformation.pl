
:- dynamic verbose/0.

main :- 
    prolog_flag(argv,ArgV),
    get_options(ArgV,Options,_RemArgV), !,
    %%print(Options),nl,print(RemArgV),
    (member(verbose,Options) -> assert(verbose) ; true),
    (member(file(F),Options) -> trans(F,Options) 
     ; trans('sample_file.trs',Options)
    ).
    %%trans_files(RemArgV,Options).

%%trans_files([],Opt) :- !, trans('sample_file.trs',Opt).
trans_files([H|T],Opt) :-
    member(F,[H|T]), trans(F,Opt),
    fail.
trans_files(_,_).

get_options([],Rec,Rem) :- !,Rec=[],Rem=[].
get_options(Inputs,RecognisedOptions,RemOptions) :-
   (recognise_option(Inputs,Flag,RemInputs)
     -> (RecognisedOptions = [Flag|RecO2], RemO2 = RemOptions)
     ;  (Inputs = [H|RemInputs], RemOptions = [H|RemO2], RecO2 = RecognisedOptions)
   ),
   get_options(RemInputs,RecO2,RemO2).

recognise_option(Inputs,Flag,RemInputs) :-
   recognised_option(Heads,Flag),
   append(Heads,RemInputs,Inputs).
   
recognised_option(['-v'],verbose).
recognised_option(['-file',NT],file(NT)).
recognised_option(['-o',F],output(F)).
recognised_option(['-f',G],filter(G)).
recognised_option(['-l'],labeling).

welcome :-
    print('Program filtering for analyzing'),nl,
    print('the termination of narrowing'),nl,nl,
    print('**Technical University of Valencia'),nl,
    print('**German Vidal (August 2007)'),nl,nl,
    print('Type h for help...'),nl,nl.

/* --------------------------------- */
/*    The program to be analyzed     */
/* --------------------------------- */

:- use_module(library(lists)).
%:- use_module(prolog_reader).

:- op(500,xfx,=>).  %% for program rules, e.g., f(x,y) => x.
:- op(500,xfx,==>). %% for filtered program rules

%%:- dynamic filters/1.
:- dynamic current_division/1.

:- dynamic output_ann/1.
aprint(X) :- (output_ann(S)
              -> (write_term(S,X,[ignore_ops(true)])) ; print(X)).
anl :- (output_ann(S) -> nl(S) ; nl).
aformat(X) :- (output_ann(S)
              -> (format(S,X,[])) ; format(X,[])).

:- dynamic filter/3.

trans(File,Options) :-
    %%welcome,
    retractall(current_division(_)),
    retractall(filter(_,_,_)),
    retractall(from(_)),
    retractall(userVars(_)),
    retractall(userFuns(_)),
    retractall(rule(_)),
    %%prolog_reader:load_file(File),
    readFile(File),
    %%%print('% File parsed and loaded'),nl,
    %%prolog_reader:get_clause(filter(Pred,Arity,BTs),true,_),
    (member(filter(AtomC),Options),
     name(AtomC,AtomS),
     pterm(AtomS,[],Atom),
     functor(Atom,Pred_,Arity),
     Atom =.. [_|BTs_],
     (member(labeling,Options) ->
      name(Pred_,Pred_S),
      append(Pred_S,"_",Pred__S),
      appendAll(BTs_,"",BTs_S),
      append(Pred__S,BTs_S,PredS),
      name(Pred,PredS)
      ;
      Pred_ = Pred
     ),
     change_gv_for_sd(BTs_,BTs),
     assert(filter(Pred,Arity,BTs)),
     %print(assert(filter(Pred,Arity,BTs))),
     fail
     ;
     true),
    %%print(filter(Pred,Arity,BTs)),nl,
    %%%findall((A1,A2,A3),filter(A1,A2,A3),ListA123),
    %%%print('%   initial filters: '),print(ListA123),nl,
    %%%statistics(runtime,[_,T1]),
    /* main */
    get_nonvar_funs, %%computes the set of functions in which
                     %%extra vars should no be replaced by bottom
    initial_div,
    bta_loop,
    transform,
    /* main */
    %%%statistics(runtime,[_,T2]),
    %%%T is T2-T1,
    %%%print('% Total time: '), print(T), print(' ms'),nl,
    %%%print('% Writing filtered program to '),
    (member(output(F),Options) -> open(F,write,Stream) 
                                ; (F=Stream,Stream = user_output)),
    %%%print(F),nl,
    assert(output_ann(Stream)),
    print_filtered_program,
    (member(output(F),Options) -> close(Stream) ; true),
    retractall(output_ann(_)).

appendAll([],Str,Str).
appendAll([H|R],Str,Str__) :-
    name(H,HS),
    append(Str,HS,Str_),
    appendAll(R,Str_,Str__).

change_gv_for_sd([],[]).
change_gv_for_sd([g|R],[s|Q]) :- change_gv_for_sd(R,Q).
change_gv_for_sd([v|R],[d|Q]) :- change_gv_for_sd(R,Q).

print_filtered_program :-
    from(Txt),
    aprint('(from '),
    aformat(Txt),
    aprint(')'),
    anl,
    fail.
print_filtered_program :-
    aprint('(VAR'),
    userVars(UVars),
    member(Var,UVars),
    aprint(' '),aprint(Var),
    fail.
print_filtered_program :-
    aprint(')'),anl,
    aprint('(RULES'),anl,
    fail.
print_filtered_program :-
    ==>(A,B),
    aprint(A),aprint(' -> '),aprint(B),anl,
    fail.
print_filtered_program :-
    aprint(')'),anl,
    aprint('(COMMENT TRS filtered for: '),
    %%findall((P,N,BTs),filter(P,N,BTs),FList),
    current_division(FList),
    aprint_division(FList),
    %%aprint(A),aprint('/'),aprint(B),
    %%aprint(' with '),aprint(C),aprint(' '),
    fail.
print_filtered_program :-
    aprint(')'),anl.

aprint_division([(A,_,C)]) :- 
    !,
    aprint(A),aprint('('),aprint_args(C),aprint(')').
aprint_division([(A,_,C)|R]) :-
    aprint(A),aprint('('),aprint_args(C),aprint('), '),
    aprint_division(R).

aprint_args([]) :- !.
aprint_args([s]) :-
    !,aprint(g).
aprint_args([d]) :-
    !,aprint(v).
aprint_args([s|RA]) :-
    !,aprint(g),aprint(','),aprint_args(RA).
aprint_args([d|RA]) :-
    aprint(v),aprint(','),aprint_args(RA).
  

/* main loop of the BTA algorithm */

:- use_module(library(ugraphs)).
:- dynamic unsafe_funs/1.


get_nonvar_funs :-
  retractall(unsafe_funs(_)),
  findall(A-B,dependency(A,B),List),
  %nl,nl,print(List),nl,
  add_edges([],List,DepGraph),
  
  findall((P,N,BTs),filter(P,N,BTs),FList),
  get_funs(FList,FunsList),
  
  get_reachable_funs(FunsList,DepGraph,UnsafeFuns),
  %%nl,print(get_reachable_funs(FunsList,DepGraph,UnsafeFuns)),nl,
  sort(UnsafeFuns,UnsafeFuns_),
  %nl,nl,print(assert(unsafe_funs(UnsafeFuns_))),nl,
  filter_noninnerfuns(UnsafeFuns_,InnerUnsafeFuns), %%rough approximation!
  %nl,nl,print(assert(unsafe_funs(InnerUnsafeFuns))),nl,
  assert(unsafe_funs(InnerUnsafeFuns)).

filter_noninnerfuns([],[]).
filter_noninnerfuns([(F,N)|R],[(F,N)|RR]) :-
	rule(_A,B),
	innerCall(B,(F,N)),!,
	filter_noninnerfuns(R,RR).
filter_noninnerfuns([_|R],RR) :-
	filter_noninnerfuns(R,RR).
	

get_reachable_funs([],_,[]).
get_reachable_funs([(F,N)|R],Graph,SF) :-
	(reachable((F,N),Graph,Funs) -> true; Funs=[]),
	get_reachable_funs(R,Graph,RFuns),
	append(Funs,RFuns,SF).

dependency((F,N),(G,M)) :-  % only non-maximal functions are considered
  rule(A,B),
  functor(A,F,N),
  funCall(B,(G,M)).



innerCall(T,Call) :-
    functor(T,F,N),
    isUserFun((F,N)),
    T =.. [_|Args],
    member(S,Args),
    funCall(S,Call).
innerCall(T,Call) :-
    functor(T,F,N),
    isUserCon((F,N)),
    T =.. [_|Args],
    member(S,Args),
    innerCall(S,Call).

funCall(S,(F,N)) :-
    functor(S,F,N),
    isUserFun((F,N)).
funCall(S,Call) :-
    S =.. [_|Args],
    member(T,Args),
    funCall(T,Call).



get_funs([],[]).
get_funs([(F,N,_)|R],[(F,N)|RR]) :-
	get_funs(R,RR).

:- dynamic change/0.
:- dynamic new_division/1.

bta_loop :-
    retractall(change),
    current_division(Div),
    userFuns(UFuns),
    member((F,N),UFuns),
%    print('FUNCTION:' ),print((F,N)),nl,
    rule(A,B),
%    print('rule: '),print(=>(A,B)),nl,
    functor(A,G,M),
    A =.. [G|Args],
    lookupDiv(Div,(G,M),DivG),
    div2Tau(DivG,Args,Tau),
    bv(B,Tau,(F,N),Div,NDivF),
    updateDiv(Div,(F,N),NDivF,NewDiv),
    (Div==NewDiv 
     -> true ; (assert_change, 
	       retract(current_division(Div)), 
	       assert(current_division(NewDiv)))),
    fail.

bta_loop :-
    %current_division(Div),
    %print('*** new division ***'),nl,
    %print(Div),nl,
    (change -> bta_loop ; true). %%%; (print('% BTA finished'),nl,print_division,nl)).

print_division :-
    current_division(Div),
    print('%   computed division: '),print(Div).

assert_change :- change -> true ; assert(change).

updateDiv([],_,_,[]).
updateDiv([(F,N,DivF)|R],(F,N),NDivF,[(F,N,Div)|R]) :- 
    !,lubList(DivF,NDivF,Div).
updateDiv([DivG|R],(F,N),NDivF,[DivG|NR]) :-
    updateDiv(R,(F,N),NDivF,NR).

div2Tau([],[],[]) :- !.
div2Tau([],_,_) :- nl,print('SOMETHING WENT WRONG WITH div2Tau!!'),nl,abort.
div2Tau(_,[],_) :- nl,print('SOMETHING WENT WRONG WITH div2Tau!!'),nl,abort.
div2Tau([BT|R],[A|AR],Tau) :-
    btVars(BT,A,TauA),
    div2Tau(R,AR,TauAR),
    append(TauA,TauAR,Tau).

btVars(BT,T,BTvars) :- 
    isUserVar(T),!,
    BTvars = [(T,BT)].
btVars(BT,T,BTvars) :-
    functor(T,F,N),
    isUserCon((F,N)),!,
    T =.. [_|Args],
    btVarsList(Args,BT,BTvars).
btVars(BT,T,BTvars) :-
    functor(T,F,N),
    isUserFun((F,N)),!,
    T =.. [_|Args],
    btVarsList(Args,BT,BTvars).
    
btVarsList([],_,[]).
btVarsList([A|AR],BT,BTvars) :-
    btVars(BT,A,BTvarsA),
    btVarsList(AR,BT,BTvarsAR),
    append(BTvarsA,BTvarsAR,BTvars).

/* initial division */

initial_div :-
    findall((P,N,BTs),filter(P,N,BTs),FList),
%%    assert(filters(FList)),
    userFuns(UFuns),
    complete_initial_div(UFuns,FList,Div),
    assert(current_division(Div))
    %print('*** initial division ***'),nl,
    %print(Div),nl
    .

complete_initial_div([],_,[]).
complete_initial_div([(F,N)|R],FList,[(F,N,BTs)|Div]) :-
    (member((F,N,BTs),FList) -> true
     ;
     listS(N,BTs)
    ),
    complete_initial_div(R,FList,Div).

/* function Be */

be(T,Tau,_,BT) :- %% variables
    isUserVar(T),!,
    lookupBT(Tau,T,BT).

be(T,Tau,Div,BT) :- %% constructor-rooted calls
    functor(T,F,N),
    isUserCon((F,N)),!,
    T =.. [_|Args],
    beArgs(Args,Tau,Div,BT).

be(T,Tau,Div,BT) :- %% user-defined function calls
    functor(T,F,N),
    isUserFun((F,N)),!,
    filtering(T,Div,TF), %%here we filter the atom using the current division!
    TF =.. [_|Args],
    beArgs(Args,Tau,Div,BT).

beArgs([],_,_,s).
beArgs([A|B],Tau,Div,BT) :-
    be(A,Tau,Div,BT1),
    beArgs(B,Tau,Div,BT2),
    lub(BT1,BT2,BT).

/* function Bv */

bv(T,_,G,_,Div) :- %% variables
    isUserVar(T),!,
    G = (_,N),
    listS(N,Div).

bv(T,Tau,G,Div,DivG) :- %% constructor-rooted calls
    functor(T,F,N),
    isUserCon((F,N)),!,
    T =.. [_|Args],
    bvArgs(Args,Tau,G,Div,DivG).
    
bv(T,Tau,G,Div,DivG) :- %% user-defined function calls
    functor(T,F,N),
    isUserFun((F,N)),!,
    T =.. [_|Args],
    bvArgs(Args,Tau,G,Div,Div_),
    ((F,N)==G -> listBe(Args,Tau,Div,Div__),
     lubList(Div_,Div__,DivG)
     ; 
     DivG = Div_).

bvArgs([],_,(_,N),_,Div) :-
    listS(N,Div).
bvArgs([A],Tau,F,Div,DivA) :-
    !,bv(A,Tau,F,Div,DivA).
bvArgs([A|B],Tau,F,Div,DivAB) :-
    bv(A,Tau,F,Div,DivA),
    bvArgs(B,Tau,F,Div,DivB),
    lubList(DivA,DivB,DivAB).

listBe([],_,_,[]).
listBe([A|R],Tau,Div,[BT|BTR]) :-
    be(A,Tau,Div,BT),
    listBe(R,Tau,Div,BTR).

/* lub */

lub(s,s,s).
lub(s,d,d).
lub(d,s,d).
lub(d,d,d).

lubList([],[],[]) :- !.
lubList([],_,_) :- nl,print('SOMETHING WENT WRONG WITH lubList!!'),nl,abort.
lubList(_,[],_) :- nl,print('SOMETHING WENT WRONG WITH lubList!!'),nl,abort.
lubList([A|RA],[B|RB],[C|RC]) :-
    lub(A,B,C),
    lubList(RA,RB,RC).


/* program transformation */

transform :- 
    current_division(Div),
    unsafe_funs(UFuns),
    rule(A,B),
    filtering(A,Div,FA),
    vars(FA,VFA),
    %%print(filtering(A,Div,FA)),nl,
    filtering(B,Div,FB_),
    (functor(A,FunA,ArA),
     member((FunA,ArA),UFuns) -> FB_ = FB
     ; dummyExtraVars(FB_,VFA,FB)
     ),
    %%print(filtering(B,Div,FB)),nl,
    assertz(==>(FA,FB)),
    %%print(==>(FA,FB)),nl,
    decPi(B,Div,Bs),
    member(T,Bs),
    filtering(T,Div,FT_),
    dummyExtraVars(FT_,VFA,FT),
    %%print(filtering(T,Div,FT)),nl,
    assertz(==>(FA,FT)),
    %%print(==>(FA,FT)),nl,
    fail.
transform :-
    %%%print('% Filtering finished'),nl.
    true.

vars(T,[T]) :- 
    isUserVar(T),!.
vars(T,VArgs) :-
    T =.. [_|Args],
    varsArgs(Args,VArgs).

varsArgs([],[]).
varsArgs([A|RA],Vars) :-
    vars(A,VA),
    varsArgs(RA,VRA),
    append(VA,VRA,Vars).

dummyExtraVars(T,VFA,T) :-
    isUserVar(T),member(T,VFA),!.
dummyExtraVars(T,_,nullVar) :-
    isUserVar(T),!.
dummyExtraVars(T,VFA,NT) :-
    functor(T,F,N),
    isUserCon((F,N)),!,
    T =.. [F|Args],
    dummyExtraVarsArgs(Args,VFA,NArgs),
    NT =.. [F|NArgs].
dummyExtraVars(T,_,T) :-
    functor(T,F,N),
    isUserFun((F,N)).

dummyExtraVarsArgs([],_,[]).
dummyExtraVarsArgs([A|RA],VFA,[NA|NRA]) :-
    dummyExtraVars(A,VFA,NA),
    dummyExtraVarsArgs(RA,VFA,NRA).

/* main filtering */

filtering(T,_,T) :- 
    isUserVar(T),!.
filtering(T,Div,NT) :-
    functor(T,F,N),
    isUserCon((F,N)),!,
    T =.. [F|Args],
    filteringArgs(Args,Div,NArgs),
    NT =.. [F|NArgs].
filtering(T,Div,NT) :-
    functor(T,F,N),
    isUserFun((F,N)),
    T =.. [F|Args],
    lookupDiv(Div,(F,N),DivF),
    selectArgs(Args,DivF,Args_),
    filteringArgs(Args_,Div,NArgs),
    NT =.. [F|NArgs].

filteringArgs([],_,[]).
filteringArgs([A|R],Div,[AF|RF]) :-
    filtering(A,Div,AF),
    filteringArgs(R,Div,RF).

selectArgs([],_,[]).
selectArgs([A|RA],[s|RD],[A|RAD]) :- 
    selectArgs(RA,RD,RAD).
selectArgs([_|RA],[d|RD],RAD) :- 
    selectArgs(RA,RD,RAD).

/* function dec_pi */

decPi(T,_,[]) :-
    isUserVar(T),!.
decPi(T,Div,Ts) :-
    functor(T,F,N),
    isUserCon((F,N)),!,
    T =.. [F|Args],
    decPiArgs(Args,Div,Ts).
decPi(T,Div,Ts) :-
    functor(T,F,N),
    isUserFun((F,N)),!,
    T =.. [F|Args],
    lookupDiv(Div,(F,N),DivF),
    unselectArgs(Args,DivF,NArgs),
    delCons(NArgs,Terms),
    decPiArgs(Args,Div,ArgsTerms),
    append(Terms,ArgsTerms,Ts).

decPiArgs([],_,[]).
decPiArgs([A|RA],Div,Terms) :-
    decPi(A,Div,As),
    decPiArgs(RA,Div,RAs),
    append(As,RAs,Terms).

delCons([],[]).
delCons([A|RA],RB) :-
    isConstructor(A),!,
    delCons(RA,RB).
delCons([A|RA],[A|RB]) :-
    delCons(RA,RB).

isConstructor(T) :-
    isUserVar(T),!.
isConstructor(T) :-
    functor(T,F,N),
    isUserCon((F,N)),!,
    T =.. [F|Args],
    isConstructorArgs(Args).

isConstructorArgs([]).
isConstructorArgs([A|RA]) :-
    isConstructor(A),
    isConstructorArgs(RA).

unselectArgs([],_,[]).
unselectArgs([A|RA],[d|RD],[A|RAD]) :- 
    unselectArgs(RA,RD,RAD).
unselectArgs([_|RA],[s|RD],RAD) :- 
    unselectArgs(RA,RD,RAD).

/* utilities */
isUserVar(X) :- userVars(UVars),
                member(X,UVars),!.
isUserFun(X) :- userFuns(UFuns),
                member(X,UFuns),!.
isUserCon(X) :- \+(isUserVar(X)),\+(isUserFun(X)).

lookupBT([],_,_) :- nl,print('SOMETHING WENT WRONG WITH LOOKUP!!'),nl,abort.
lookupBT([(X,BT)|_],X,BT) :- !.
lookupBT([_|R],X,BT) :- lookupBT(R,X,BT).

lookupDiv([],_,_) :- nl,print('SOMETHING WENT WRONG WITH LOOKUP!!'),nl,abort.
lookupDiv([(F,N,Div)|_],(F,N),Div) :- !.
lookupDiv([_|R],F,Div) :- lookupDiv(R,F,Div).

listS(0,[]) :- !.
listS(N,[s|R]) :- N>0, M is N-1, listS(M,R).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/* parsing the source file */

readFile(File) :-
    open(File,read,Stream),
    load_string([],Stream,Text),
    close(Stream),
%%    print('***processing file***'),nl,
%%    format(Text,[]),
%%    print('*********************'),nl,
    parse_trs_file(Text,[]),
    assert_user_funs.

load_string(Program,Stream,L) :-
	get_code(Stream,C), C \== -1, !,
  	append(Program,[C],Result),
  	load_string(Result,Stream,L).

load_string(Program,_,Program).

parse_trs_file([],[]) :- !.

parse_trs_file(S,S_) :-
    pfrom(S,S__),!,
    parse_trs_file(S__,S_).

parse_trs_file(S,S_) :-
    pvar(S,S__),!,
    parse_trs_file(S__,S_).

parse_trs_file(S,S_) :-
    prules(S,S__),!,
    parse_trs_file(S__,S_).

parse_trs_file(S,S_) :-
    pcomment(S,S__),!,
    parse_trs_file(S__,S_).

parse_trs_file(S,S_) :-
    pblanks(S,S__),!,
    parse_trs_file(S__,S_).

:- dynamic from/1.

pfrom(S,S_) :-
    append("(from",S2,S),   %% S  = "(from" + S2
    pblanks(S2,S3),
    ptext(S3,S4,Comment),
    append(")",S_,S4),      %% S4 = ")" + S_
    assert(from(Comment)).

:- dynamic userVars/1.

pvar(S,S_) :-
    append("(VAR",S2,S),    %% S  = "(VAR" + S2
    pblanks(S2,S3),
    pvarlist(S3,S4,Vars),
    (pblanks(S4,S5) ; S4 = S5),
    append(")",S_,S5),      %% S5 = ")" + S_
    assert(userVars(Vars)).

pvarlist(S,S_,[Vn]) :-
    pid(S,S_,V),
    name(Vn,V).
pvarlist(S,S_,[Vn|Vars]) :-
    pid(S,S2,V),
    name(Vn,V),
    pblanks(S2,S3),
    pvarlist(S3,S_,Vars).


:- dynamic comment/1.

pcomment(S,S_) :-
    append("(COMMENT",S2,S),   %% S  = "(COMMENT" + S2
    pblanks(S2,S3),
    ptext(S3,S4,Comment),
    append(")",S_,S4),         %% S4 = ")" + S_
    assert(comment(Comment)).

pcomment(S,S_) :-
    append("ARCH=x86; OPSYS=linux; HEAP_SUFFIX=x86-linux",S2,S),   %% to solve problem with sml
    pblanks(S2,S_).

:- dynamic rule/2.

prules(S,S_) :-
    append("(RULES",S2,S),
    pblanks(S2,S3),
    prulelist(S3,S4,Rules),
    (pblanks(S4,S5) ; S4=S5),
    append(")",S_,S5),
    assert_rules(Rules).

assert_rules([]).
assert_rules([(Lhs,Rhs)|R]) :-
    assertz(rule(Lhs,Rhs)),
    assert_rules(R).

prulelist(S,S_,[Rule|Rules]) :-
    prule(S,S2,Rule),
    pblanks(S2,S3),
    prulelist(S3,S_,Rules).

prulelist(S,S_,[Rule]) :-
    prule(S,S_,Rule).

prule(S,S_,(Lhs,Rhs)) :-
    pterm(S,S2,Lhs),
    pblanks(S2,S3),
    append("->",S4,S3),
    pblanks(S4,S5),
    pterm(S5,S_,Rhs).

pterm(S,S_,T) :-
    pid(S,S2,Fl),
    name(F,Fl),
    append("(",S3,S2),
    ptermseq(S3,S4,Args),
    append(")",S_,S4),
    T =.. [F|Args]. %% term reconstruction
pterm(S,S_,Id) :-
    pid(S,S_,Idl),
    name(Id,Idl).

ptermseq(S,S_,[T1|TR]) :-
    pterm(S,S2_,T1),
    pblanks(S2_,S2),
    append(",",S3_,S2),
    pblanks(S3_,S3),
    ptermseq(S3,S_,TR).
ptermseq(S,S_,[T]) :-
    pterm(S,S_,T).

:- dynamic userFuns/1.

assert_user_funs :-
    assert(userFuns([])),
    rule(A,_),
    functor(A,F,N),
    userFuns(Funs),
    (member((F,N),Funs) -> true; retract(userFuns(Funs)), assert(userFuns([(F,N)|Funs]))),
    fail.
assert_user_funs.


%% valid identifier

pid(S,S_,Id) :- pid(S,S_,"",Id).

%pid([H|R],Rest,"",Id) :- % start id
%  !, 
%  pminus(H),
%  pid(R,Rest,[H],Id).

pid([H|R],Rest,Id_,Id) :- % rest id
  pvalido(H), !,
  append(Id_,[H],Id2), 
  pid(R,Rest,Id2,Id).

pid(S,S,Id,Id). % end id 


% numbers, letter, etc

psymbol(A) :- A=95 ; A=34 ; A=39 ; A=96. %% _ ' " `
pnum(A) :- 48 =< A, A =< 57.        % 48 = '0', 57 = '9'
pmayus(A) :- 65 =< A, A =< 90.      % 65 = 'A', 90 = 'Z'
pminus(A) :- 97 =< A, A =< 122.     % 97 = 'a', 122 = 'z'
pletra(A) :- pminus(A) ; pmayus(A).
pvalido(A) :- pletra(A) ; pnum(A) ; psymbol(A).

pblanks([C|S],S_) :-
   (C < 33; C = 127),!, %% layout chars
   pblanks(S,S_).
pblanks(S,S).

/* pblanks([C|S],S) :-
   (C < 33; C = 127). %% layout chars
*/

%% valid text

ptext(S,S_,Id) :- ptext(S,S_,"",Id).

ptext([40|R],Rest,Id_,Id) :-
  append(Id_,"(",Id2),
  ptext(R,[41|R_],Id2,Id3),  %% 41 is ')'
  !,
  ptext(R_,Rest,Id3,Id).

ptext([H|R],Rest,Id_,Id) :-
  pt(H), !,
  append(Id_,[H],Id2), 
  ptext(R,Rest,Id2,Id).

ptext(S,S,Id,Id).

pt(C) :- C\=41.

/* better but incomplete version...

pt(C) :- C=<32 ; C=127      %% layout chars
         ; (C>=65, C=<90)   %% capital-letters
         ; (C>=97, C=<122)  %% small letters
         ; (C>=48, C=<57)   %% digits
         ; C= ... (see pag. 790 of SICStus Manual)
*/
