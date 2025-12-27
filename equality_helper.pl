% =========================================================================
% EQUALITY HELPER - NATIVE RULES (nanoCoP-inspired)
% =========================================================================
% =========================================================================
% TPTP OPERATORS (input syntax)
% =========================================================================
:- op( 500, fy, ~).             % negation
:- op(1000, xfy, &).            % conjunction
:- op(1100, xfy, '|').          % disjunction
:- op(1110, xfy, =>).           % conditional
:- op(1120, xfy, <=>).          % biconditional
:- op( 500, fy, !).             % universal quantifier:  ![X]:
:- op( 500, fy, ?).             % existential quantifier:  ?[X]:
:- op( 500, xfy, :).            % quantifier separator
% Input syntax: sequent turnstile
% Equivalence operator for sequents (bidirectional provability)
:- op(800, xfx, <>).
% =========================================================================
% LATEX OPERATORS (formatted output)
% ATTENTION: Respect spaces exactly!
% =========================================================================
:- op( 500, fy, ' \\lnot ').     % negation
:- op(1000, xfy, ' \\land ').    % conjunction
:- op(1100, xfy, ' \\lor ').     % disjunction
:- op(1110, xfx, ' \\to ').      % conditional
:- op(1120, xfx, ' \\leftrightarrow ').  % biconditional
:- op( 500, fy, ' \\forall ').   % universal quantifier
:- op( 500, fy, ' \\exists ').   % existential quantifier
:- op( 500, xfy, ' ').           % space for quantifiers
:- op(400, fx, ' \\bot ').      % falsity (#)
% LaTeX syntax: sequent turnstile
:- op(1150, xfx, ' \\vdash ').
% =========================================================================
% =========================================================================
% NATIVE EQUALITY RULES
% =========================================================================

% Réflexivité
prove(_G>[eq(T,T)],_,_,J,J,_,_,eq_refl) :- !.

% Symétrie
prove(G>[eq(A,B)],_,_,J,J,_,_,eq_sym) :- member(eq(B,A),G),!.

% Transitivité
prove(G>[eq(A,C)],_,_,J,J,_,_,eq_trans) :-
    member(eq(A,B),G),member(eq(B,C),G),!.

% Substitution prédicat (arité 1)
prove(G>[Goal],_,_,J,J,_,_,eq_subst_pred_1) :-
    Goal=.. [P,T2],
    P\=eq,
    member(eq(T1,T2),G),
    Premise=.. [P,T1],
    member(Premise,G),!.

% Substitution prédicat (arité 2)
prove(G>[Goal],_,_,J,J,_,_,eq_subst_pred_2) :-
    Goal=..[P,A2,B2],
    P\= eq,
    args_equal_in_context([A2,B2],[A1,B1],G),
    Premise=..[P,A1,B1],
    member(Premise,G),!.

% Substitution prédicat (arité 3)
prove(G>[Goal],_,_,J,J,_,_,eq_subst_pred_3):-
    Goal=..[P,A2,B2,C2],
    P\= eq,
    args_equal_in_context([A2,B2,C2],[A1,B1,C1],G),
    Premise=..[P,A1,B1,C1],
    member(Premise,G),!.

% Substitution fonction (arité 1)
prove(G>[eq(F1,F2)],_,_,J,J,_,_,eq_subst_func_1):-
    F1=.. [Func,Arg1],
    F2=.. [Func,Arg2],
    Func\=eq,
    (member(eq(Arg1,Arg2),G);member(eq(Arg2,Arg1),G)),!.

% Substitution fonction (arité 2)
prove(G>[eq(F1,F2)],_,_,J,J,_,_,eq_subst_func_2):-
    F1=..[Func,A1,B1],
    F2=..[Func,A2,B2],
    Func\=eq,
    args_equal_in_context([A1,B1],[A2,B2],G),!.

% =========================================================================
% HELPER:  Vérifier égalité des arguments
% =========================================================================

args_equal_in_context([],[],_).
args_equal_in_context([A|As],[A|Bs],G):-!,args_equal_in_context(As,Bs,G).
args_equal_in_context([A|As],[B|Bs],G) :-
    (member(eq(A,B),G);member(eq(B,A),G)),
    args_equal_in_context(As,Bs,G).
