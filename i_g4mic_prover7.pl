% =========================================================================
% G4-mic FOL Prover - prove/7 (without Registry parameter)
% Simplified from i_g4mic_prover.pl
% =========================================================================

:- set_prolog_flag(occurs_check, true).

% prove/7 - SIMPLIFIED (no registry)
% prove(Sequent, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, Proof)

% =========================================================================
% AXIOMS
% =========================================================================

prove(Gamma > Delta, _, _, J, J, _, ax(Gamma>Delta, ax)) :-
    member(A, Gamma),
    A\=(_&_), A\=(_|_), A\=(_=>_),
    A\=(!_), A\=(?_),
    Delta = [B],
    unify_with_occurs_check(A, B).

prove(Gamma > Delta, _, _, J, J, LogicLevel, lbot(Gamma>Delta, #)) :-
    member(LogicLevel, [intuitionistic, classical]),
    member(#, Gamma), !.

% =========================================================================
% PROPOSITIONAL RULES
% =========================================================================

prove(Gamma > Delta, FV, I, J, K, L, land(Gamma>Delta, P)) :-
    select((A&B), Gamma, G1), !,
    prove([A,B|G1] > Delta, FV, I, J, K, L, P).

prove(Gamma > Delta, FV, I, J, K, L, l0cond(Gamma>Delta, P)) :-
    select((A=>B), Gamma, G1),
    member(A, G1), !,
    prove([B|G1] > Delta, FV, I, J, K, L, P).

prove(Gamma > Delta, FV, I, J, K, L, landto(Gamma>Delta, P)) :-
    select(((A&B)=>C), Gamma, G1), !,
    prove([(A=>(B=>C))|G1] > Delta, FV, I, J, K, L, P).

prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, tne(Gamma>Delta, P)) :-
    Delta = [(A => B)],
    member(LongNeg, Gamma),
    is_nested_negation(LongNeg, A => B, Depth),
    Depth >= 2,
    !,
    prove([A|Gamma]>[B], FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).

prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, classical, ip(Gamma>Delta, P)) :-
    Delta = [A],
    A \= #,
    \+ member((A => #), Gamma),
    Threshold > 0,
    prove([(A => #)|Gamma]>[#], FreeVars, Threshold, SkolemIn, SkolemOut, classical, P).

prove(Gamma > Delta, FV, I, J, K, L, lorto(Gamma>Delta, P)) :-
    select(((A|B)=>C), Gamma, G1), !,
    ( member(A, G1), member(B, G1) ->
        prove([A=>C, B=>C|G1] > Delta, FV, I, J, K, L, P)
    ; member(A, G1) ->
        prove([A=>C|G1] > Delta, FV, I, J, K, L, P)
    ; member(B, G1) ->
        prove([B=>C|G1] > Delta, FV, I, J, K, L, P)
    ;
        prove([A=>C, B=>C|G1] > Delta, FV, I, J, K, L, P)
    ).

prove(Gamma > Delta, FV, I, J, K, L, lor(Gamma>Delta, P1, P2)) :-
    select((A|B), Gamma, G1), !,
    prove([A|G1] > Delta, FV, I, J, J1, L, P1),
    prove([B|G1] > Delta, FV, I, J1, K, L, P2).

% =========================================================================
% QUANTIFIER RULES
% =========================================================================

prove(Gamma > Delta, FV, I, J, K, L, rall(Gamma>Delta, P)) :-
    select((![_Z-X]:A), Delta, D1), !,
    copy_term((X:A, FV), (f_sk(J, FV):A1, FV)),
    J1 is J+1,
    prove(Gamma > [A1|D1], FV, I, J1, K, L, P).

prove(Gamma > Delta, FV, I, J, K, L, lall(Gamma>Delta, P)) :-
    member((![_Z-X]:A), Gamma),
    \+ length(FV, I),
    copy_term((X:A, FV), (Y:A1, FV)),
    prove([A1|Gamma] > Delta, [Y|FV], I, J, K, L, P).

prove(Gamma > Delta, FV, I, J, K, L, rcond(Gamma>Delta, P)) :-
    Delta = [A=>B], !,
    prove([A|Gamma] > [B], FV, I, J, K, L, P).

prove(Gamma > Delta, FV, I, J, K, L, ltoto(Gamma>Delta, P1, P2)) :-
    select(((A=>B)=>C), Gamma, G1), !,
    prove([A, (B=>C)|G1] > [B], FV, I, J, J1, L, P1),
    prove([C|G1] > Delta, FV, I, J1, K, L, P2).

prove(Gamma > Delta, FV, I, J, K, L, lex_lor(Gamma>Delta, P1, P2)) :-
    select((?[_Z-X]:(A|B)), Gamma, G1), !,
    ground(FV),
    copy_term((X:(A|B), FV), (f_sk(J, FV):(A1|B1), FV)),
    J1 is J+1,
    prove([A1|G1] > Delta, FV, I, J1, J2, L, P1),
    prove([B1|G1] > Delta, FV, I, J2, K, L, P2).

prove(Gamma > Delta, FV, I, J, K, L, ror(Gamma>Delta, P)) :-
    Delta = [(A|B)], !,
    (   prove(Gamma > [A], FV, I, J, K, L, P)
    ;   prove(Gamma > [B], FV, I, J, K, L, P)
    ).

prove(Gamma > Delta, FV, I, J, K, L, rand(Gamma>Delta, P1, P2)) :-
    Delta = [(A&B)], !,
    prove(Gamma > [A], FV, I, J, J1, L, P1),
    prove(Gamma > [B], FV, I, J1, K, L, P2).

prove(Gamma > Delta, FV, I, J, K, L, lex(Gamma>Delta, P)) :-
    select((?[_Z-X]:A), Gamma, G1), !,
    copy_term((X:A, FV), (f_sk(J, FV):A1, FV)),
    J1 is J+1,
    prove([A1|G1] > Delta, FV, I, J1, K, L, P).

prove(Gamma > Delta, FV, I, J, K, L, rex(Gamma>Delta, P)) :-
    select((?[_Z-X]:A), Delta, D1), !,
    \+ length(FV, I),
    copy_term((X:A, FV), (Y:A1, FV)),
    prove(Gamma > [A1|D1], [Y|FV], I, J, K, L, P).

% =========================================================================
% QUANTIFIER CONVERSIONS
% =========================================================================

prove(Gamma > Delta, FV, I, J, K, classical, cq_c(Gamma>Delta, P)) :-
    select((![Z-X]:A) => B, Gamma, G1),
    \+ member_term(X, FV),
    ( member((?[ZTarget-YTarget]: ATarget) => B, G1),
      \+ \+ ((A => B) = ATarget) ->
        prove([?[ZTarget-YTarget]:ATarget|G1] > Delta, FV, I, J, K, classical, P)
    ;
        prove([?[Z-X]:(A => B)|G1] > Delta, FV, I, J, K, classical, P)
    ).

prove(Gamma > Delta, FV, I, J, K, LogicLevel, cq_m(Gamma>Delta, P)) :-
    member(LogicLevel, [minimal, intuitionistic]),
    select((?[Z-X]:A)=>B, Gamma, G1),
    \+ member_term(X, FV),
    prove([![Z-X]:(A=>B)|G1] > Delta, FV, I, J, K, LogicLevel, P).

% =========================================================================
% EQUALITY RULES
% =========================================================================

prove(_Gamma > Delta, _, _, J, J, _, eq_refl(Delta)) :-
    Delta = [T = T],
    ground(T), !.

prove(Gamma > Delta, _, _, J, J, _, eq_sym(Gamma>Delta)) :-
    Delta = [A = B],
    member(B = A, Gamma), !.

prove(Gamma > Delta, _, _, J, J, _, eq_trans(Gamma>Delta)) :-
    Delta = [A = C],
    A \== C,
    (   (member(A = B, Gamma), member(B = C, Gamma))
    ;   (member(B = A, Gamma), member(B = C, Gamma))
    ;   (member(A = B, Gamma), member(C = B, Gamma))
    ;   (member(B = A, Gamma), member(C = B, Gamma))
    ), !.

prove(Gamma > Delta, _, _, J, J, _, eq_trans_chain(Gamma>Delta)) :-
    Delta = [A = C],
    A \== C,
    \+ member(A = C, Gamma),
    \+ member(C = A, Gamma),
    find_equality_path(A, C, Gamma, [A], _Path), !.

prove(Gamma > Delta, _, _, J, J, _, eq_cong(Gamma>Delta)) :-
    Delta = [LHS = RHS],
    LHS =..  [F|ArgsL],
    RHS =.. [F|ArgsR],
    length(ArgsL, N), length(ArgsR, N), N > 0,
    find_diff_pos(ArgsL, ArgsR, _Pos, TermL, TermR),
    (member(TermL = TermR, Gamma) ; member(TermR = TermL, Gamma)), !.

prove(Gamma > Delta, _, _, J, J, _, eq_subst_eq(Gamma>Delta)) :-
    Delta = [Goal_LHS = Goal_RHS],
    member(Ctx_LHS = Ctx_RHS, Gamma),
    Ctx_LHS \== Goal_LHS,
    member(X = Y, Gamma), X \== Y,
    (   (substitute_in_term(X, Y, Ctx_LHS, Goal_LHS), Ctx_RHS == Goal_RHS)
    ;   (substitute_in_term(Y, X, Ctx_LHS, Goal_LHS), Ctx_RHS == Goal_RHS)
    ;   (substitute_in_term(X, Y, Ctx_RHS, Goal_RHS), Ctx_LHS == Goal_LHS)
    ;   (substitute_in_term(Y, X, Ctx_RHS, Goal_RHS), Ctx_LHS == Goal_LHS)
    ), !.

prove(Gamma > Delta, _, _, J, J, _, eq_subst(Gamma>Delta)) :-
    Delta = [Goal],
    Goal \= (_ = _), Goal \= (_ => _), Goal \= (_ & _),
    Goal \= (_ | _), Goal \= (!_), Goal \= (?_),
    member(A = B, Gamma),
    member(Pred, Gamma),
    Pred \= (_ = _), Pred \= (_ => _), Pred \= (_ & _), Pred \= (_ | _),
    Pred =.. [PredName|Args],
    Goal =.. [PredName|GoalArgs],
    member_pos(A, Args, Pos),
    nth0(Pos, GoalArgs, B), !.

% =========================================================================
% ANTISEQUENT
% =========================================================================

prove([] > Delta, _, I, J, J, classical, asq([] < Delta, _)) :-
    nb_current(asq_enabled, true),
    I >= 5,
    Delta = [B],
    B \= asq, B \= asq(_,_), !.

prove(Gamma > Delta, _, I, J, J, classical, asq(Gamma < Delta, _)) :-
    nb_current(asq_enabled, true),
    I >= 5,
    Gamma \= [],
    Delta = [B],
    B \= asq, B \= asq(_,_),
    member(A, Gamma),
    A \= asq, A \= asq(_,_),
    \+ member(A, Delta), !.

% =========================================================================
% HELPERS
% =========================================================================

member_pos(X, [X|_], 0) :- !.
member_pos(X, [_|T], N) :-
    member_pos(X, T, N1),
    N is N1 + 1.

substitute_in_term(Old, New, Old, New) :- !.
substitute_in_term(Old, New, Term, Result) :-
    compound(Term), !,
    Term =.. [F|Args],
    maplist(substitute_in_term(Old, New), Args, NewArgs),
    Result =.. [F|NewArgs].
substitute_in_term(_, _, Term, Term).

find_diff_pos([X|_], [Y|_], 0, X, Y) :- X \= Y, !.
find_diff_pos([X|RestL], [X|RestR], Pos, TermL, TermR) :-
    find_diff_pos(RestL, RestR, Pos1, TermL, TermR),
    Pos is Pos1 + 1.

find_equality_path(X, X, _, _, [X]) :- !.
find_equality_path(X, Z, Context, Visited, [X|Path]) :-
    (member(X = Y, Context) ; member(Y = X, Context)),
    Y \== X,
    \+ member(Y, Visited),
    find_equality_path(Y, Z, Context, [Y|Visited], Path).

is_nested_negation(Target, Target, 0) :- !.
is_nested_negation((Inner => #), Target, N) :-
    is_nested_negation(Inner, Target, N1),
    N is N1 + 1.

member_term(Term, List) :-
    member(Element, List),
    contains_term(Term, Element).

contains_term(Term, Term) :- !.
contains_term(Term, Structure) :-
    compound(Structure),
    Structure =.. [_|Args],
    member(Arg, Args),
    contains_term(Term, Arg).
