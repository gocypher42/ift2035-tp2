%% -*- mode: prolog; coding: utf-8 -*-

%% GNU Prolog défini `new_atom`, mais SWI Prolog l'appelle `gensym`.
genatom(X, A) :-
    %% Ugly hack, âmes sensibles s'abstenir.
    (predicate_property(new_atom/2, built_in);    % Older GNU Prolog
     predicate_property(new_atom(_,_), built_in)) % Newer GNU Prolog
    -> new_atom(X, A);
    gensym(X, A).

debug_print(E) :- write(user_error, E), nl(user_error).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Description de la syntaxe des termes %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Ces règles sont inutiles en soit, elle ne servent qu'à documenter pour
%% vous la forme des termes du langage H2035, ainsi que vous montrer quelques
%% primitives de Prolog qui peuvent vous être utiles dans ce TP, telles que
%% `=..`.

%% wf_type(+T)
%% Vérifie que T est un type syntaxiquement valide.
wf_type(int).
wf_type(bool).
wf_type(list(T)) :- wf_type(T).
wf_type((T1 -> T2)) :- wf_type(T1), wf_type(T2).
wf_type(Alpha) :- identifier(Alpha).
wf_type(forall(X,T)) :- atom(X), wf_type(T).
wf_type(X) :- var(X). %Une métavariable, utilisée pendant l'inférence de type.

%% wf(+E)
%% Vérifie que E est une expression syntaxiquement valide.
wf(X) :- integer(X).
wf(X) :- identifier(X).                   %Une constante ou une variable.
wf(lambda(X, E)) :- identifier(X), wf(E). %Une fonction.
wf(app(E1, E2)) :- wf(E1), wf(E2).        %Un appel de fonction.
wf(if(E1, E2, E3)) :- wf(E1), wf(E2), wf(E3).
wf((E : T)) :- wf(E), wf_type(T).
wf(?).                                  %Infère le code.
wf(E) :- E =.. [Head|Tail],
         (Head = let -> wf_let(Tail);
          identifier(Head), wf_exps(Tail)).

%% identifier(+X)
%% Vérifie que X est un identificateur valide, e.g. pas un mot réservé.
identifier(X) :- atom(X),
                 \+ member(X, [lambda, app, if, let, (:), (?)]).

wf_exps([]).
wf_exps([E|Es]) :- wf(E), wf_exps(Es).

wf_let([E]) :- wf(E).
wf_let([Rdecl|Tail]) :- wf_rdecl(Rdecl), wf_let(Tail).

wf_rdecl([]).
wf_rdecl(D) :- wf_decl(D).
wf_rdecl([D|Ds]) :- wf_decl(D), wf_rdecl(Ds).

wf_decl(X = E) :-
    wf(E),
    (identifier(X);
     X =.. [F|Args], identifier(F), wf_args(Args)).

wf_args([]).
wf_args([Arg|Args]) :- wf_args(Args), identifier(Arg).

%%%%%% ELABORATION %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% elaborate(+Env, +Exp, ?Type, -NewExp)
%% Infère/vérifie le type de Exp, élimine le sucre syntaxique, et remplace
%% les variables par des indexes de deBruijn.
%% Note: Le cut est utilisé pour éviter de tomber dans la dernière clause
%% (qui signale un message d'erreur) en cas d'erreur de type.
elaborate(_, E, _, _) :-
    var(E), !,
    debug_print(elaborate_nonclos(E)), fail.
elaborate(_, N, T, N) :- number(N), !, T = int.
elaborate(Env, lambda(X,E), T, lambda(DE)) :-
    !, elaborate([(X,T1)|Env], E, T2, DE), T = (T1 -> T2).
elaborate(Env, +(E1, E2), T, V):- 
    !,
    elaborate(Env, app(app((+),E1),E2), T, V).
elaborate(Env, =(E1, E2), T, V) :-
    !,
    elaborate(Env, app(app((=), E1), E2), T, V).
elaborate(Env, -(E1, E2), T, V) :-
    !,
    elaborate(Env, app(app((-), E1), E2), T, V).
elaborate(Env, ?, T, V) :-
    build_inc_type(Env, TInc),
    find_func_var(TInc, Env, Env, T, V).
elaborate(Env, N, T, V) :- 
    atom(N), !,
    find_idx(N, Env, Id),
    nth_elem(Id, Env,(_,T)),
    V = var(Id).
elaborate(Env, app(E1, E2), T, V) :- 
    !,
    (   atom(E2) 
    ->  find_elem_idx(E2, Env, Aidx), 
        V2 = var(Aidx), 
        nth_elem(Aidx, Env, (_,T2_))
    ;   elaborate(Env, E2, T2_, V2)
    ),
    (   not(var(T2_)), T2_ = forall(t, TA2)
    ->  rebuild_forall(TA2, TU, T2)
    ;   T2 = T2_
    ),
    (   find_inc_idx(?, Env, IdInc) 
    ->  nth_elem(IdInc, Env, Inc), Inc = (_, T2) ; T2 = T2),
    elaborate(Env, E1, TF, V1),
    (   not(var(TF)), TF = forall(t, _) 
    ->  rebuild_forall(TF, TU, TI),
        TI = ->(_,T)
    ;   TF = ->(T2, TO),
        (T2 = ->(TI, T) ; T = TO)
    ),
    V = app(V1, V2).
elaborate(Env, let([X|XS], E), T, V) :-
    !,
    decompose(Env, [X|XS], NewEnv, LetExp),
    elaborate(NewEnv, E, T, VE),
    V = let(LetExp, VE).
elaborate(Env, if(E1,E2,E3), T, V) :- !, 
    elaborate(Env, E1, _, V1),
    elaborate(Env, E2, T2, V2),
    elaborate(Env, E3, T3, V3),
    T = T2,
    T = T3,
    V = if(V1, V2, V3).
elaborate(Env, F, T, V) :- 
    F =.. [Name|Args], 
    not(Args = []),
    !,
    split_last_arg(Args, NewArgs, Arg),
    (   Name = let 
    ->  Args = [LV|LVS],
        NL =.. [Name|LVS],
        (   LVS = [] 
        ->  elaborate(Env, LV, T, V) 
        ;   elaborate(Env, let([LV], NL), T, V)
        )
    ;   NF =.. [Name|NewArgs],
        (   Name = ?
        ->  add_last((?, _), Env, NEnv) 
        ;   NEnv = Env),
        elaborate(NEnv, app(NF, Arg), T, V)
    ).
elaborate(_, E, _, _) :-
    debug_print(elab_unknown(E)), fail.

add_last(Name, [], [Name]).
add_last(Name, [X|Envs], [X|Env]) :- add_last(Name, Envs, Env).

rebuild_forall(t, T, T).
rebuild_forall(bool, _, bool).
rebuild_forall(list(t), T, list(T)).
rebuild_forall(forall(t, TI), T,  TO) :- rebuild_forall(TI, T, TO).
rebuild_forall(->(T1,T2), T, ->(T1O, T2O)) :- 
    rebuild_forall(T1,T, T1O), 
    rebuild_forall(T2,T, T2O).

decompose(Env, Vars, NewEnv, LetExp) :-
    get_var_names(Vars, VarNames),
    gen_env(VarNames, Env, NewEnv),
    decompose_elab(NewEnv, Vars, LetExp).

decompose_elab(Env, [], []).
decompose_elab(Env, [=(X,E)|XS], [V|LetExp]):-
     X =.. [VarName|Args],
    gen_lambda(Args, E, El),
    elaborate(Env, El, T, V),
    decompose_elab(Env, XS, LetExp),
    set_type(Env, VarName, T).

set_type([(Var, T)|_], Var, T).
set_type([_|Env], Var, T) :- set_type(Env, Var, T).

gen_lambda([], E, E).
gen_lambda([A|AS], E, lambda(A, Lambda)) :-
    gen_lambda(AS, E, Lambda).

get_var_names([], []).
get_var_names([=(X,E)|XS], [Name|VarNames]) :-
    X =.. [Name|_],
    get_var_names(XS, VarNames).

gen_env([], Env, Env).
gen_env([V|VS], Env, NEnv) :-
    gen_env(VS, [(V,_)|Env], NEnv).

build_inc_type(Env, T) :- 
    split_last_inc(Env, NEnv, Last), 
    Last = (_, T1),
    (   find_idx(?,NEnv,_) 
    ->  build_inc_type(NEnv, T2), T = (T1 -> T2)
    ;   T = T1
    ).

find_func_var(TInc, [(_,TE)|Envs], Env, T, V) :-
    (   TE = forall(_,TFA)
    ->  rebuild_forall(TFA, _, TV)
    ;   TV = TE
    ),
    remove_output_type(TV, TN),
    (   Tinc = TN 
    ->  find_func_idx(Var, Env, Idx), nth_elem(Idx, Env, (_,T)), V = var(Idx)
    ; find_func_var(Tinc, Envs, Env, T, V)
    ).


remove_output_type(->(T1,T2), TN) :- 
    (   T2 = ->(T3,T4) 
    ->  remove_output_type(T2, T5), TN = (T1 -> T5) 
    ; TN = T1
    ).

reverse([],Z,Z).
reverse([H|T],Z,Acc) :- reverse(T,Z,[H|Acc]).

find_idx(Var, [(Var,_)| _], Idx) :- !, Idx = 0.
find_idx(Var, [_|Envs], Idx):- find_idx(Var, Envs, Idx_), Idx is Idx_ + 1.

find_inc_idx(Var, [(Var,T)| Envs], Idx) :- var(T),! , Idx = 0.
find_inc_idx(Var, [_|Envs], Idx):- find_inc_idx(Var, Envs, Idx_), Idx is Idx_ + 1.

find_func_idx(Var, [(Var, forall(T, ->(T2, T3)))|_], Idx) :- Idx = 0.
find_func_idx(Var, [(Var, ->(_,_))|_], Idx) :- Idx = 0.
find_func_idx(Var, [_|Envs], Idx):- 
    find_func_idx(Var, Envs, Idx_), Idx is Idx_ + 1.

find_elem_idx(Var, [(Var, T)|Envs], Idx) :- 
    (   var(T) 
    ->  Idx = 0 
    ;   T =.. [HEAD|TAIL], 
        (   HEAD = (->) 
        ->  find_elem_idx(Var, Envs, Idx_),
            Idx is Idx_ + 1
        ;   ( HEAD = forall, TAIL = [_| [->(_,_)]] 
            -> find_elem_idx(Var, Envs, Idx_), Idx is Idx_ + 1
            ;Idx = 0
            )
        ) 
    ).
find_elem_idx(Var, [_|Envs], Idx):- 
    find_elem_idx(Var, Envs, Idx_), Idx is Idx_ + 1.

split_last_arg([X|[]], [], X) :- !. 
split_last_arg([X|XS], [X|T], Last) :- 
    split_last_arg(XS, T, Last).

split_last_inc([(?, T)|[]], [], (?,T)) :- !. 
split_last_inc([X|XS], [X|T], Last) :- 
    split_last_inc(XS, T, Last).

%% Ci-dessous, quelques prédicats qui vous seront utiles:
%% - instantiate: correspond à la règle "σ ⊂ τ" de la donnée.
%% - freelvars: correspond au "fv" de la donnée.
%% - generalize: fait le travail du "gen" de la donnée.

%% instantiate(+PT, -T)
%% Choisi une instance d'un type polymorphe PT.
instantiate(V, T) :- var(V), !, T = V.
instantiate(forall(X,T), T2) :-
    !, substitute(T, X, _, T1), instantiate(T1, T2).
instantiate(T, T).              %Pas de polymorphisme à instancier.


%% substitute(+Type1, +TVar, +Type2, -Type3)
%% Remplace TVar par Type2 dans Type1, i.e. `Type3 = Type1[Type2/TVar]`.
substitute(T1, _, _, T3) :- var(T1), !, T3 = T1.
substitute(X, X, T, T) :- !.
substitute(T1, X, T2, T3) :-
    %% T1 a la forme Head(Tail).  E.g. Head='->' et Tail=[int,int].
    %% Ça peut aussi être Head='int' et Tail=[].
    T1 =.. [Head|Tail],
    mapsubst(Tail, X, T2, NewTail),
    T3 =.. [Head|NewTail].

%% Applique `substitute' sur une liste.
mapsubst([], _, _, []).
mapsubst([T1|T1s], X, T2, [T3|Ts]) :-
    substitute(T1, X, T2, T3), mapsubst(T1s, X, T2, T3s).

%% freelvars(+E, -Vs)
%% Trouve toutes les variables logiques (i.e. variables Prolog) non
%% instanciées qui apparaissent dans le terme Prolog E, et les renvoie
%% dans la liste Vs.
freelvars(E, Vs) :- freelvars([], E, Vs).

%% freelvars(+Vsi, +E, -Vso)
%% Règle auxiliaire de freelvars/2.
freelvars(Vsi, V, Vso) :-
    var(V), !,
    (member(V, Vsi) -> Vso = Vsi; Vso = [V|Vsi]).
freelvars(Vsi, E, Vso) :-
    (E = [T|Ts], !; E =.. [_,T|Ts]) ->
        freelvars(Vsi, T, Vs1),
        freelvars(Vs1, Ts, Vso);
    Vso = Vsi.

%% generalize(+FVenv, +Env, -GEnv)
%% Généralise un morceau d'environnement Env en un morceau d'environnement
%% GEnv où chaque variable a été rendue aussi polymorphe que possible.
%% FVenv est la liste des variables libres de l'environnement externe.
generalize(_, [], []).
generalize(FVenv, [(X,T)|DeclEnv], [(X,GT)|GenEnv]) :-
    freelvars(T,FVs),
    gentype(FVenv, FVs, T, GT),
    generalize(FVenv, DeclEnv, GenEnv).

%% gentype(+FVenv, +FV, +T, -GT)
%% Généralise le type T en un type GT aussi polymorphe que possible.
%% FVenv est la liste des variables libres de l'environnement, et FV
%% est la liste des variables libres de T.
gentype(_, [], T, T).
gentype(FVenv, [V|Vs], T, GT) :-
    gentype(FVenv, Vs, T, GT1),
    (member(V, FVenv) -> GT = GT1;
     genatom(t, V), GT = forall(V, T)).
 


%%%%%% EVALUATION %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% eval(+Env, +Exp, -Val)
%% Évalue Exp dans le context Env et renvoie sa valeur Val.
%% Note: Le cut est utilisé pour éviter de tomber dans la dernière clause
%% (qui signale un message d'erreur) en cas d'échec après l'évaluation,
%% i.e. pour distinguer le cas d'une expression que notre code ne couvre pas
%% des autres cas d'échec.
eval(_, E, _) :-
    var(E), !,
    debug_print(eval_nonclos(E)), fail.
eval(_, N, N) :- number(N), !.
eval(Env, var(Idx), V) :- !, nth_elem(Idx, Env, V).
eval(Env, lambda(E), closure(Env, E)) :- !.
eval(Env, app(E1, E2), V) :-
    !, 
    eval(Env, E1, V1_),
    (   V1_ = closure(CEnv, F)
    ->  close_lambda(CEnv, NEnv), V1 = closure(NEnv, F)
    ;   NEnv = Env, V1 = V1_
    ),
    eval(Env, E2, V2),
    apply(V1, V2, VA),
    ( VA = var(_)  
    ->  eval(NEnv, VA, V)
    ; V = VA
    ).
eval(Env, let(Elements, E), V) :-
    !,
    reverse(Elements, RElements, []),
    append(RElements, Env, TEnv),
    close_lambda(TEnv, NEnv),
    eval(NEnv, E, V).
eval(Env, if(E1,E2,E3), V) :- !,
    eval(Env, E1, V1),
    (V1 = true -> eval(Env, E2, V) ; eval(Env, E3, V)).
%% ¡¡ REMPLIR ICI !!
eval(_, E, _) :-
    debug_print(eval_unknown(E)), fail.

close_lambda(IEnv, OEnv) :- close_lambda(IEnv, IEnv, OEnv).
close_lambda([], _, []).
close_lambda([V|VS], BEnv, [VO|OEnv]) :- 
    (   V = lambda(_) 
    ->  eval(BEnv, V, VO)
    ;   VO = V
    ),
    close_lambda(VS, BEnv, OEnv).

pop_last(0, Env, Env).
pop_last(N, [_|Envs], Env) :- N_ is N - 1, pop_last(N, Envs, Env).

%% apply(+Fun, +Arg, -Val)
%% Evaluation des fonctions et des opérateurs prédéfinis.
apply(closure(Env, Body), Arg, V) :- eval([Arg|Env], Body, V).
apply(builtin(BI), Arg, V) :- builtin(BI, Arg, V).
%% builtin(list, V, list(V)).
builtin((+), N1, builtin(+(N1))).
builtin(+(N1), N2, N) :- N is N1 + N2.
builtin(cons, X, builtin(cons(X))).
builtin(cons(X), XS, [X|XS]).
builtin(empty, X, Res) :- X = [] -> Res = true; Res = false.
builtin(car, [X|_], X).
builtin(cdr, [_|XS], XS).
builtin(cdr, [], []).
builtin((-), N1, builtin(-(N1))).
builtin(-(N1), N2, N) :- N is N1 - N2.
builtin((=), N1, builtin(=(N1))).
builtin(=(N1), N2, N) :- N1 =:= N2 -> N = true ; N = false.

%% nth_elem(+I, +VS, -V)
%% Renvoie le I-ème élément de la liste Vs.
nth_elem(0, [V|_], V).
nth_elem(I, [_|Vs], V) :- I > 0, I1 is I - 1, nth_elem(I1, Vs, V).

%%%%%% TOP-LEVEL %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%% env0(-Env)
%% Renvoie l'environnement initial combiné (types et valeurs).
env0([((+), (int -> int -> int), builtin(+)),
      ((-),   (int -> int -> int), builtin(-)),
      ((=),   (int -> int -> bool), builtin(=)),
      (true, bool, true),
      (false, bool, false),
      (nil, forall(t, list(t)), []),
      (cons, forall(t, (t -> list(t) -> list(t))), builtin(cons)),
      (empty, forall(t, (list(t) -> bool)), builtin(empty)),
      (car, forall(t, (list(t) -> t)), builtin(car)),
      (cdr, forall(t, (list(t) -> list(t))), builtin(cdr))]).

%% Extrait l'environnement de typage de l'environnement combiné.
get_tenv([], []).
get_tenv([(X,T,_)|Env], [(X,T)|TEnv]) :- get_tenv(Env, TEnv).

%% tenv0(-TEnv)
%% Renvoie l'environnment de types initial.
tenv0(TEnv) :- env0(Env), get_tenv(Env, TEnv).

%% Extrait l'environnement de valeurs de l'environnement combiné.
get_venv([], []).
get_venv([(_,_,V)|Env], [V|VEnv]) :- get_venv(Env, VEnv).

%% venv0(-VEnv)
%% Renvoie l'environnment de valeurs initial.
venv0(VEnv) :- env0(Env), get_venv(Env, VEnv).

%% runelab(+Prog, -Type, -Elab)
%% Elabore Prog et renvoie le code élaboré et son type.
runelab(E, T, El) :- tenv0(TEnv), elaborate(TEnv, E, T, El).

%% runeval(+Prog, -Type, -Val)
%% Type et exécute le programme Prog dans l'environnement initial.
runeval(E, T, V) :- tenv0(TEnv), elaborate(TEnv, E, T, DE),
                   !,
                   venv0(VEnv), eval(VEnv, DE, V).

%% Exemples d'usage:
%% runeval(1 + 2, T, V).
%% runeval(app(lambda(x,x+1),3), T, V).
%% runeval(app(lambda(f,f(3)),lambda(x,x+1)), T, V).
%% runeval(let([x = 1], 3 + x), T, V).
%% runeval(let(f(x) = x+1, f(3)), T, V).
%% runeval(let([x = 1, x = lambda(a, a + 1)], (3 + x(x))), T, V).
%% runeval(cons(1,nil), T, V).
%% runeval(let([length = lambda(x, if(empty(x), 0, 1 + length(cdr(x))))],
%%             length(cons(42,cons(41,cons(40,nil))))
%%             + length(cons(1,nil))),
%%         T, V).
%% runeval(let([length(x) = if(empty(x), 0, 1 + length(cdr(x)))],
%%             length(cons(42,cons(41,cons(40,nil)))) 
%%            + length(cons(4,nil))),
%%         T, V)
%% runeval(let([length = lambda(x, if(empty(x), 0, 1 + length(cdr(x))))],
%%             length(cons(42,cons(41,cons(40,nil))))
%%             + length(cons(true,nil))),
%%         T, V).
%% runeval(let([length = lambda(x, if(empty(x), 0, 1 + length(cdr(x))))],
%%             length(?(42,?(41,?(40,nil))))
%%             + length(cons(true,nil))),
%%         T, V).


%% runeval(?(1,nil), T, V).
%% runeval(let([length = lambda(x, if(empty(x), 0, 1 + length(cdr(x))))], length(?(42,?(41,?(40,nil)))) + length(cons(1,nil))), T, V).
%% runeval(let([length(x) = if(empty(x), 0, 1 + length(cdr(x)))],
%%             length(?(42,?(41,?(40,nil)))) + length(cons(4,nil))),
%%         T, V).
