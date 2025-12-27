% =========================================================================
% G4-mic FOL Prover - CORRECTED with Tamura's eigenvariable approach
% Key fix: Using freeze/2 + dif/2 instead of registry
% CRITICAL: Enable occurs_check to prevent circular unifications
% =========================================================================

% Enable occurs check globally to prevent circular term structures
:- set_prolog_flag(occurs_check, true).

% prove/8 - Registry parameter kept for compatibility but not used for eigenvariables
% prove(Sequent, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, EigenRegistry, Proof)
% LogicLevel: minimal | intuitionistic | classical
% EigenRegistry: kept for compatibility, but eigenvariable constraints are now declarative

% =========================================================================
% EIGENVARIABLE MANAGEMENT (Tamura style)
% =========================================================================

% eigen_variable(V, Sequent)
%   V is a fresh eigenvariable that must remain different from all free variables
%   Tamura's approach: freeze + dif
eigen_variable(V, Gamma > Delta) :-
    % Freeze V: any attempt to unify it will fail
    freeze(V, fail),
    % Collect all free variables in the sequent
    collect_free_vars(Gamma > Delta, FreeVars),
    % Ensure V is different from all of them
    ensure_different(V, FreeVars).

% ensure_different(V, FreeVars)
%   Impose dif/2 constraints between V and each free variable
ensure_different(_, []).
ensure_different(V, [U|Us]) :-
    dif(V, U),
    ensure_different(V, Us).

% collect_free_vars(Sequent, Vars)
%   Collect all free variables appearing in the sequent
collect_free_vars(Gamma > Delta, Vars) :-
    collect_from_list(Gamma, [], Vars1),
    collect_from_list(Delta, Vars1, Vars).

collect_from_list([], Acc, Acc).
collect_from_list([F|Fs], Acc, Vars) :-
    free_vars_formula(F, [], Acc, Acc1),
    collect_from_list(Fs, Acc1, Vars).

% free_vars_formula(Formula, BoundVars, VarsIn, VarsOut)
%   Collect free variables from a formula
%   BoundVars = currently bound variables (by quantifiers)
%   VarsIn/VarsOut = accumulator
free_vars_formula(V, BV, Acc, Acc) :-
    var(V),
    (member_var(V, BV) ; member_var(V, Acc)),
    !.
free_vars_formula(V, BV, Acc, [V|Acc]) :-
    var(V),
    \+ member_var(V, BV),
    !.
free_vars_formula(F, _BV, Acc, Acc) :-
    atomic(F),
    !.

% Quantifiers: add bound variable
free_vars_formula((![_-X]:A), BV, Acc, Vars) :- !,
    free_vars_formula(A, [X|BV], Acc, Vars).
free_vars_formula((?[_-X]:A), BV, Acc, Vars) :- !,
    free_vars_formula(A, [X|BV], Acc, Vars).

% Binary connectives
free_vars_formula(A & B, BV, Acc, Vars) :- !,
    free_vars_formula(A, BV, Acc, Acc1),
    free_vars_formula(B, BV, Acc1, Vars).
free_vars_formula(A | B, BV, Acc, Vars) :- !,
    free_vars_formula(A, BV, Acc, Acc1),
    free_vars_formula(B, BV, Acc1, Vars).
free_vars_formula(A => B, BV, Acc, Vars) :- !,
    free_vars_formula(A, BV, Acc, Acc1),
    free_vars_formula(B, BV, Acc1, Vars).
free_vars_formula(A <=> B, BV, Acc, Vars) :- !,
    free_vars_formula(A, BV, Acc, Acc1),
    free_vars_formula(B, BV, Acc1, Vars).

% Negation
free_vars_formula((A => #), BV, Acc, Vars) :- !,
    free_vars_formula(A, BV, Acc, Vars).

% Equality
free_vars_formula(A = B, BV, Acc, Vars) :- !,
    free_vars_formula(A, BV, Acc, Acc1),
    free_vars_formula(B, BV, Acc1, Vars).

% Compound terms
free_vars_formula(Term, BV, Acc, Vars) :-
    compound(Term),
    Term =.. [_|Args],
    free_vars_list(Args, BV, Acc, Vars).

free_vars_list([], _BV, Acc, Acc).
free_vars_list([T|Ts], BV, Acc, Vars) :-
    free_vars_formula(T, BV, Acc, Acc1),
    free_vars_list(Ts, BV, Acc1, Vars).

% member_var: identity test for variables
member_var(X, [Y|_]) :- X == Y, !.
member_var(X, [_|Ys]) :- member_var(X, Ys).

% =========================================================================
% SUBSTITUTION
% =========================================================================

% substitute(OldVar, NewVar, Formula, Result)
%   Replace all occurrences of OldVar by NewVar in Formula
substitute(X, Y, Var, Y) :-
    var(Var),
    X == Var,
    !.
substitute(_, _, Var, Var) :-
    var(Var),
    !.
substitute(_, _, Atom, Atom) :-
    atomic(Atom),
    !.
substitute(X, Y, (![Z-V]:A), (![Z-V]:B)) :- !,
    (X == V -> B = A ; substitute(X, Y, A, B)).
substitute(X, Y, (?[Z-V]:A), (?[Z-V]:B)) :- !,
    (X == V -> B = A ; substitute(X, Y, A, B)).
substitute(X, Y, A & B, A1 & B1) :- !,
    substitute(X, Y, A, A1),
    substitute(X, Y, B, B1).
substitute(X, Y, A | B, A1 | B1) :- !,
    substitute(X, Y, A, A1),
    substitute(X, Y, B, B1).
substitute(X, Y, A => B, A1 => B1) :- !,
    substitute(X, Y, A, A1),
    substitute(X, Y, B, B1).
substitute(X, Y, A <=> B, A1 <=> B1) :- !,
    substitute(X, Y, A, A1),
    substitute(X, Y, B, B1).
substitute(X, Y, A = B, A1 = B1) :- !,
    substitute(X, Y, A, A1),
    substitute(X, Y, B, B1).
substitute(X, Y, Term, Result) :-
    compound(Term),
    Term =.. [F|Args],
    subst_list(X, Y, Args, NewArgs),
    Result =.. [F|NewArgs].

subst_list(_, _, [], []).
subst_list(X, Y, [T|Ts], [T1|Ts1]) :-
    substitute(X, Y, T, T1),
    subst_list(X, Y, Ts, Ts1).

% =========================================================================
% AXIOMS
% =========================================================================

% Axiom (atomic formula match)
prove(Gamma > Delta, _, _, J, J, _, _, ax(Gamma>Delta, ax)) :-
    member(A, Gamma),
    A\=(_&_), A\=(_|_), A\=(_=>_),
    A\=(!  _), A\=(? _),
    member(A, Delta).  % Pattern matching: same variable A on both sides

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

% 4. TNE : Odd Negation Elimination
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, Reg, tne(Gamma>Delta, P)) :-
    Delta = [(A => B)],
    member(LongNeg, Gamma),
    is_nested_negation(LongNeg, A => B, Depth),
    Depth >= 2,
    !,
    prove([A|Gamma]>[B], FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, Reg, P).

% 5. IP (Indirect Proof)
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

% 7. L∨ - Left disjunction
prove(Gamma > Delta, FV, I, J, K, L, Reg, lor(Gamma>Delta, P1, P2)) :-
    select((A|B), Gamma, G1), !,
    prove([A|G1] > Delta, FV, I, J, J1, L, Reg, P1),
    prove([B|G1] > Delta, FV, I, J1, K, L, Reg, P2).

% 10. R→ - Right implication
prove(Gamma > Delta, FV, I, J, K, L, Reg, rcond(Gamma>Delta, P)) :-
    Delta = [A=>B], !,
    prove([A|Gamma] > [B], FV, I, J, K, L, Reg, P).

% 11. L→→ - Left implication-implication (G4 specific)
prove(Gamma > Delta, FV, I, J, K, L, Reg, ltoto(Gamma>Delta, P1, P2)) :-
    select(((A=>B)=>C), Gamma, G1), !,
    prove([A, (B=>C)|G1] > [B], FV, I, J, J1, L, Reg, P1),
    prove([C|G1] > Delta, FV, I, J1, K, L, Reg, P2).

% 13. R∨ - Right disjunction
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
% QUANTIFIER RULES - TAMURA STYLE with freeze/dif
% =========================================================================

% 8. R∀ - Universal introduction (Tamura style with eigenvariable)
prove(Gamma > Delta, FV, I, J, K, L, Reg, rall(Gamma>Delta, P)) :-
    select((![_Z-X]:A), Delta, D1), !,
    % Tamura's order: substitute first (creates fresh variable V1)
    substitute(X, V1, A, A1),
    % Then impose constraints on V1 using ORIGINAL sequent
    eigen_variable(V1, Gamma > Delta),
    % Prove with the substituted formula
    prove(Gamma > [A1|D1], FV, I, J, K, L, Reg, P).

% 9. L∀ - Universal elimination (Otten's limitation)
prove(Gamma > Delta, FV, I, J, K, L, Reg, lall(Gamma>Delta, P)) :-
    member((![_Z-X]:A), Gamma),
    \+ length(FV, I),
    substitute(X, T, A, A1),
    prove([A1|Gamma] > Delta, [T|FV], I, J, K, L, Reg, P).

% 12. L∃∨ - Combined existential-disjunction (G4 specific)
prove(Gamma > Delta, FV, I, J, K, L, Reg, lex_lor(Gamma>Delta, P1, P2)) :-
    select((?[_Z-X]:(A|B)), Gamma, G1), !,
    ground(FV),
    % Tamura's order: substitute first (creates fresh variable V1)
    substitute(X, V1, A, A1),
    substitute(X, V1, B, B1),
    % Then impose constraints on V1 using ORIGINAL sequent
    eigen_variable(V1, Gamma > Delta),
    % Prove both branches
    prove([A1|G1] > Delta, FV, I, J, J1, L, Reg, P1),
    prove([B1|G1] > Delta, FV, I, J1, K, L, Reg, P2).

% 15. L∃ - Existential elimination (Tamura style with eigenvariable)
prove(Gamma > Delta, FV, I, J, K, L, Reg, lex(Gamma>Delta, P)) :-
    select((?[_Z-X]:A), Gamma, G1), !,
    % Tamura's order: substitute first (creates fresh variable V1)
    substitute(X, V1, A, A1),
    % Then impose constraints on V1 using ORIGINAL sequent
    eigen_variable(V1, Gamma > Delta),
    % Prove with the substituted formula
    prove([A1|G1] > Delta, FV, I, J, K, L, Reg, P).

% 16. R∃ - Existential introduction (free variable)
prove(Gamma > Delta, FV, I, J, K, L, Reg, rex(Gamma>Delta, P)) :-
    member((?[_Z-X]:A), Delta),
    \+ length(FV, I),
    substitute(X, T, A, A1),
    prove(Gamma > [A1|Delta], [T|FV], I, J, K, L, Reg, P).

% =========================================================================
% QUANTIFIER CONVERSIONS (G4 specific)
% =========================================================================

% 17. CQ_c - Classical quantifier conversion
prove(Gamma > Delta, FV, I, J, K, classical, Reg, cq_c(Gamma>Delta, P)) :-
    select((![Z-X]:A) => B, Gamma, G1),
    \+ member_term(X, FV),
    ( member((?[ZTarget-YTarget]: ATarget) => B, G1),
      \+ \+ ((A => B) = ATarget) ->
        prove([?[ZTarget-YTarget]:ATarget|G1] > Delta, FV, I, J, K, classical, Reg, P)
    ;
        prove([?[Z-X]:(A => B)|G1] > Delta, FV, I, J, K, classical, Reg, P)
    ).

% 18. CQ_m - Minimal quantifier conversion
prove(Gamma > Delta, FV, I, J, K, LogicLevel, Reg, cq_m(Gamma>Delta, P)) :-
    member(LogicLevel, [minimal, intuitionistic]),
    select((?[Z-X]:A)=>B, Gamma, G1),
    \+ member_term(X, FV),
    prove([![Z-X]:(A=>B)|G1] > Delta, FV, I, J, K, LogicLevel, Reg, P).

% =========================================================================
% EQUALITY RULES (unchanged)
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
    nth0(Pos, GoalArgs, B), !.

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
% HELPERS (unchanged)
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

% =========================================================================
% END of Prover section
% =========================================================================
