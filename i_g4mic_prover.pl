% =========================================================================
% G4-mic FOL Prover - CORRECTED with LOCAL eigenvariable registry
% Key fix: Registry passed as parameter, not global state
% CRITICAL: Enable occurs_check to prevent circular unifications
% =========================================================================

% Enable occurs check globally to prevent circular term structures
:- set_prolog_flag(occurs_check, true).

% prove/8 - NOW WITH REGISTRY PARAMETER
% prove(Sequent, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, EigenRegistry, Proof)
% LogicLevel: minimal | intuitionistic | classical
% EigenRegistry: list of eigenvariables used in current branch

% =========================================================================
% AXIOMS
% =========================================================================

% Axiom (atomic formula match)
prove(Gamma > Delta, _, _, J, J, _, _, ax(Gamma>Delta, ax)) :-
    member(A, Gamma),
    A\=(_&_), A\=(_|_), A\=(_=>_),
    A\=(!  _), A\=(? _),
    Delta = [B],
    unify_with_occurs_check(A, B).

% L-bot (explosion rule for intuitionistic/classical)
prove(Gamma > Delta, _, _, J, J, LogicLevel, _, lbot(Gamma>Delta, #)) :-
    member(LogicLevel, [intuitionistic, classical]),
    member(#, Gamma), !.

% =========================================================================
% PROPOSITIONAL RULES (G4 specific)
% =========================================================================

% 1. L∧ - Left conjunction
prove(Gamma > Delta, FV, I, J, K, L, Reg, land(Gamma>Delta, P)) :-
    select((A&B), Gamma, G1), !,
    prove([A,B|G1] > Delta, FV, I, J, K, L, Reg, P).

% 2. L0→ - Modus ponens (G4 optimization)
prove(Gamma > Delta, FV, I, J, K, L, Reg, l0cond(Gamma>Delta, P)) :-
    select((A=>B), Gamma, G1),
    member(A, G1), !,
    prove([B|G1] > Delta, FV, I, J, K, L, Reg, P).

% 3. L∧→ - Left conjunction-implication (G4 specific)
prove(Gamma > Delta, FV, I, J, K, L, Reg, landto(Gamma>Delta, P)) :-
    select(((A&B)=>C), Gamma, G1), !,
    prove([(A=>(B=>C))|G1] > Delta, FV, I, J, K, L, Reg, P).

% 4. TNE : Odd Negation Elimination (CORRECTED to prove/8)
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, Reg, tne(Gamma>Delta, P)) :-
    Delta = [(A => B)],
    member(LongNeg, Gamma),
    is_nested_negation(LongNeg, A => B, Depth),
    Depth >= 2,
    !,
    prove([A|Gamma]>[B], FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, Reg, P).

% 5. IP (Indirect Proof - CORRECTED to prove/8)
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, classical, Reg, ip(Gamma>Delta, P)) :-
    Delta = [A],
    A \= #,
    \+ member((A => #), Gamma),
    Threshold > 0,
    prove([(A => #)|Gamma]>[#], FreeVars, Threshold, SkolemIn, SkolemOut, classical, Reg, P).

% 6. L∨→ - Left disjunction-implication (G4 specific, optimized)
prove(Gamma > Delta, FV, I, J, K, L, Reg, lorto(Gamma>Delta, P)) :-
    select(((A|B)=>C), Gamma, G1), !,
    ( member(A, G1), member(B, G1) ->
        prove([A=>C, B=>C|G1] > Delta, FV, I, J, K, L, Reg, P)
    ; member(A, G1) ->
        prove([A=>C|G1] > Delta, FV, I, J, K, L, Reg, P)
    ; member(B, G1) ->
        prove([B=>C|G1] > Delta, FV, I, J, K, L, Reg, P)
    ;
        prove([A=>C, B=>C|G1] > Delta, FV, I, J, K, L, Reg, P)
    ).
% 7.  L∨ - Left disjunction (CRITICAL: each branch gets its own registry copy)
prove(Gamma > Delta, FV, I, J, K, L, Reg, lor(Gamma>Delta, P1, P2)) :-
    select((A|B), Gamma, G1), !,
    prove([A|G1] > Delta, FV, I, J, J1, L, Reg, P1),
    prove([B|G1] > Delta, FV, I, J1, K, L, Reg, P2).

% 8.  R∀ - Universal introduction (eigenvariable with LOCAL registry check)
prove(Gamma > Delta, FV, I, J, K, L, Reg, rall(Gamma>Delta, P)) :-
    select((![_Z-X]:A), Delta, D1), !,
    copy_term((X:A, FV), (f_sk(J, FV):A1, FV)),
    % CHECK: f_sk must not be in the CURRENT BRANCH registry
    \+ member_check(f_sk(J, FV), Reg),
    % Add to registry for this branch
    NewReg = [f_sk(J, FV)|Reg],
    J1 is J+1,
    prove(Gamma > [A1|D1], FV, I, J1, K, L, NewReg, P).

% 9.  L∀ - Universal elimination (Otten's limitation)
prove(Gamma > Delta, FV, I, J, K, L, Reg, lall(Gamma>Delta, P)) :-
    member((![_Z-X]:A), Gamma),
    \+ length(FV, I),
    copy_term((X:A, FV), (Y:A1, FV)),
    prove([A1|Gamma] > Delta, [Y|FV], I, J, K, L, Reg, P).

% 10. R→ - Right implication
prove(Gamma > Delta, FV, I, J, K, L, Reg, rcond(Gamma>Delta, P)) :-
    Delta = [A=>B], !,
    prove([A|Gamma] > [B], FV, I, J, K, L, Reg, P).

% 11. L→→ - Left implication-implication (G4 specific)
prove(Gamma > Delta, FV, I, J, K, L, Reg, ltoto(Gamma>Delta, P1, P2)) :-
    select(((A=>B)=>C), Gamma, G1), !,
    prove([A, (B=>C)|G1] > [B], FV, I, J, J1, L, Reg, P1),
    prove([C|G1] > Delta, FV, I, J1, K, L, Reg, P2).

% 12. L∃∨ - Combined existential-disjunction (G4 specific with groundness check)
prove(Gamma > Delta, FV, I, J, K, L, Reg, lex_lor(Gamma>Delta, P1, P2)) :-
    select((?[_Z-X]:(A|B)), Gamma, G1), !,
    ground(FV),
    copy_term((X:(A|B), FV), (f_sk(J, FV):(A1|B1), FV)),
    J1 is J+1,
    prove([A1|G1] > Delta, FV, I, J1, J2, L, Reg, P1),
    prove([B1|G1] > Delta, FV, I, J2, K, L, Reg, P2).

% 13  R∨ - Right disjunction (CRITICAL: each branch gets its own registry copy)
prove(Gamma > Delta, FV, I, J, K, L, Reg, ror(Gamma>Delta, P)) :-
    Delta = [(A|B)], !,
    (   prove(Gamma > [A], FV, I, J, K, L, Reg, P)
    ;   prove(Gamma > [B], FV, I, J, K, L, Reg, P)
    ).

% 14. R∧ - Right conjunction
prove(Gamma > Delta, FV, I, J, K, L, Reg, rand(Gamma>Delta, P1, P2)) :-
    Delta = [(A&B)], !,
    prove(Gamma > [A], FV, I, J, J1, L, Reg, P1),
    prove(Gamma > [B], FV, I, J1, K, L, Reg, P2).


% =========================================================================
% QUANTIFIER RULES - WITH LOCAL REGISTRY
% =========================================================================


% 15. L∃ - Existential elimination (eigenvariable with LOCAL registry check)
prove(Gamma > Delta, FV, I, J, K, L, Reg, lex(Gamma>Delta, P)) :-
    select((?[_Z-X]:A), Gamma, G1), !,
    copy_term((X:A, FV), (f_sk(J, FV):A1, FV)),
    % CHECK: f_sk must not be in the CURRENT BRANCH registry
    \+ member_check(f_sk(J, FV), Reg),
    % Add to registry for this branch
    NewReg = [f_sk(J, FV)|Reg],
    J1 is J+1,
    prove([A1|G1] > Delta, FV, I, J1, K, L, NewReg, P).

% 16.  R∃ - Existential introduction (free variable)
prove(Gamma > Delta, FV, I, J, K, L, Reg, rex(Gamma>Delta, P)) :-
    select((?[_Z-X]:A), Delta, D1), !,
    \+ length(FV, I),
    copy_term((X:A, FV), (Y:A1, FV)),
    prove(Gamma > [A1|D1], [Y|FV], I, J, K, L, Reg, P).

% =========================================================================
% QUANTIFIER CONVERSIONS (G4 specific - WITH FRESHNESS CONSTRAINTS)
% =========================================================================

% 17 . CQ_c - Classical quantifier conversion (with freshness constraint)
prove(Gamma > Delta, FV, I, J, K, classical, Reg, cq_c(Gamma>Delta, P)) :-
    select((![Z-X]:A) => B, Gamma, G1),
    \+ member_term(X, FV),
    ( member((?[ZTarget-YTarget]: ATarget) => B, G1),
      \+ \+ ((A => B) = ATarget) ->
        prove([?[ZTarget-YTarget]:ATarget|G1] > Delta, FV, I, J, K, classical, Reg, P)
    ;
        prove([?[Z-X]:(A => B)|G1] > Delta, FV, I, J, K, classical, Reg, P)
    ).

% 18 . CQ_m - Minimal quantifier conversion (with freshness constraint)
prove(Gamma > Delta, FV, I, J, K, LogicLevel, Reg, cq_m(Gamma>Delta, P)) :-
    member(LogicLevel, [minimal, intuitionistic]),
    select((?[Z-X]:A)=>B, Gamma, G1),
    \+ member_term(X, FV),
    prove([![Z-X]:(A=>B)|G1] > Delta, FV, I, J, K, LogicLevel, Reg, P).

% =========================================================================
% EQUALITY RULES
% =========================================================================

% Reflexivity
prove(_Gamma > Delta, _, _, J, J, _, _, eq_refl(Delta)) :-
    Delta = [T = T],
    ground(T), !.

% Symmetry
prove(Gamma > Delta, _, _, J, J, _, _, eq_sym(Gamma>Delta)) :-
    Delta = [A = B],
    member(B = A, Gamma), !.

% Transitivity
prove(Gamma > Delta, _, _, J, J, _, _, eq_trans(Gamma>Delta)) :-
    Delta = [A = C],
    A \== C,
    (   (member(A = B, Gamma), member(B = C, Gamma))
    ;   (member(B = A, Gamma), member(B = C, Gamma))
    ;   (member(A = B, Gamma), member(C = B, Gamma))
    ;   (member(B = A, Gamma), member(C = B, Gamma))
    ), !.

% Chained transitivity
prove(Gamma > Delta, _, _, J, J, _, _, eq_trans_chain(Gamma>Delta)) :-
    Delta = [A = C],
    A \== C,
    \+ member(A = C, Gamma),
    \+ member(C = A, Gamma),
    find_equality_path(A, C, Gamma, [A], _Path), !.

% Congruence
prove(Gamma > Delta, _, _, J, J, _, _, eq_cong(Gamma>Delta)) :-
    Delta = [LHS = RHS],
    LHS =..  [F|ArgsL],
    RHS =.. [F|ArgsR],
    length(ArgsL, N), length(ArgsR, N), N > 0,
    find_diff_pos(ArgsL, ArgsR, _Pos, TermL, TermR),
    (member(TermL = TermR, Gamma) ; member(TermR = TermL, Gamma)), !.

% Substitution in equality
prove(Gamma > Delta, _, _, J, J, _, _, eq_subst_eq(Gamma>Delta)) :-
    Delta = [Goal_LHS = Goal_RHS],
    member(Ctx_LHS = Ctx_RHS, Gamma),
    Ctx_LHS \== Goal_LHS,
    member(X = Y, Gamma), X \== Y,
    (   (substitute_in_term(X, Y, Ctx_LHS, Goal_LHS), Ctx_RHS == Goal_RHS)
    ;   (substitute_in_term(Y, X, Ctx_LHS, Goal_LHS), Ctx_RHS == Goal_RHS)
    ;   (substitute_in_term(X, Y, Ctx_RHS, Goal_RHS), Ctx_LHS == Goal_LHS)
    ;   (substitute_in_term(Y, X, Ctx_RHS, Goal_RHS), Ctx_LHS == Goal_LHS)
    ), !.

% Leibniz substitution
prove(Gamma > Delta, _, _, J, J, _, _, eq_subst(Gamma>Delta)) :-
    Delta = [Goal],
    Goal \= (_ = _), Goal \= (_ => _), Goal \= (_ & _),
    Goal \= (_ | _), Goal \= (!_), Goal \= (?_),
    member(A = B, Gamma),
    member(Pred, Gamma),
    Pred \= (_ = _), Pred \= (_ => _), Pred \= (_ & _), Pred \= (_ | _),
    Pred =.. [PredName|Args],
    Goal =.. [PredName|GoalArgs],
    member_pos(A, Args, Pos),
    nth0(Pos, GoalArgs, B), ! .

% =========================================================================
% ANTISEQUENT (only when enabled)
% =========================================================================

prove([] > Delta, _, I, J, J, classical, _, asq([] < Delta, _)) :-
    nb_current(asq_enabled, true),
    I >= 5,
    Delta = [B],
    B \= asq, B \= asq(_,_), !.

prove(Gamma > Delta, _, I, J, J, classical, _, asq(Gamma < Delta, _)) :-
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
% Helper: check if term is in registry (using =@= for structural equivalence)
member_check(Term, [Elem|_]) :-
    Term =@= Elem,
    !.
member_check(Term, [_|Rest]) :-
    member_check(Term, Rest).


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

contains_term(Term, Term) :- ! .
contains_term(Term, Structure) :-
    compound(Structure),
    Structure =.. [_|Args],
    member(Arg, Args),
    contains_term(Term, Arg).

% =========================================================================
% END of Prover section
% =========================================================================
