%% File: minimal_driver.pl  -  Version: 3.0
%%
%% Purpose: Minimal interface for nanoCoP (CLASSICAL ONLY - no nanoCop-i)
%% Usage:   nanoCop_decides(Formula).
%%
%% Author: Joseph Vidal-Rosset
%% Based on: nanoCoP by Jens Otten
%% Version 3.0: Removed nanoCop-i, only classical nanoCop
% =========================================================================

% =========================================================================
% LOADING REQUIRED MODULES
% =========================================================================
:- catch([system_check], _, true).

% Load nanoCoP core (CLASSICAL ONLY)
:- catch([nanocop20_swi], _,
        format('WARNING: nanoCoP core not found!~n')).

% CRITICAL: Load nanocop_tptp2 for equality axioms
:- catch([nanocop_tptp2], _,
    format('WARNING: nanocop_tptp2 not found - equality support disabled!~n')).

% =========================================================================
% MAIN INTERFACE - CLASSICAL NANOCOP ONLY
% =========================================================================
% =========================================================================
% G4MIC INTERFACE - prove/1
% =========================================================================
%% nanoCop_decides(+Formula) - Prove formula with automatic equality axioms
%%
%% CRITICAL: This predicate manages occurs_check flag:
%% - nanoCop requires occurs_check=true
%% - g4mic requires occurs_check=false
%% - This wrapper ensures proper isolation
nanoCop_decides(Formula) :-
    % Save current state
    current_prolog_flag(occurs_check, OriginalOccursCheck),

    % Force occurs_check=false for formula processing
    set_prolog_flag(occurs_check, false),

    % Use setup_call_cleanup to guarantee proper flag management
    setup_call_cleanup(
        % Setup: Set occurs_check=true for nanoCop
        set_prolog_flag(occurs_check, true),
        % Call: execute nanoCop proof
        nanocop_prove_core(Formula),
        % Cleanup: Restore to false (g4mic-safe state)
        set_prolog_flag(occurs_check, false)
    ),

    % Final cleanup: restore original state
    set_prolog_flag(occurs_check, OriginalOccursCheck).

%% nanocop_prove_core(+Formula) - Core nanoCop logic
%% Assumes occurs_check=true is already set
nanocop_prove_core(Formula) :-
    % Step 1: Detect equality BEFORE translation
    (nanocop_contains_equality(Formula) ->
        HasEquality = true
    ;
        HasEquality = false
    ),

    % Step 2: Translate formula (![X]: → all X:)
    translate_formula(Formula, InternalFormula),

    % Step 3: Add equality axioms AFTER translation (if needed)
    (HasEquality = true ->
        (current_predicate(leancop_equal/2) ->
            leancop_equal(InternalFormula, TempFormula),
            (InternalFormula \= TempFormula ->
                FormulaWithEq = TempFormula
            ;
                basic_equality_axioms(EqAxioms),
                FormulaWithEq = (EqAxioms => InternalFormula)
            )
        ;
            basic_equality_axioms(EqAxioms),
            FormulaWithEq = (EqAxioms => InternalFormula)
        )
    ;
        FormulaWithEq = InternalFormula
    ),

    % Step 4: Prove (occurs_check is true here)
    prove2(FormulaWithEq, [cut,comp(7)], _Proof),
    !.

% =========================================================================
% EQUALITY DETECTION
% =========================================================================

nanocop_contains_equality((_ = _)) :- !.

nanocop_contains_equality(~A) :- !,
    nanocop_contains_equality(A).

nanocop_contains_equality(A & B) :- !,
    (nanocop_contains_equality(A) ; nanocop_contains_equality(B)).

nanocop_contains_equality(A | B) :- !,
    (nanocop_contains_equality(A) ; nanocop_contains_equality(B)).

nanocop_contains_equality(A => B) :- !,
    (nanocop_contains_equality(A) ; nanocop_contains_equality(B)).

nanocop_contains_equality(A <=> B) :- !,
    (nanocop_contains_equality(A) ; nanocop_contains_equality(B)).

nanocop_contains_equality(![_]: A) :- !,
    nanocop_contains_equality(A).

nanocop_contains_equality(?[_]:A) :- !,
    nanocop_contains_equality(A).

nanocop_contains_equality(all _:A) :- !,
    nanocop_contains_equality(A).

nanocop_contains_equality(ex _:A) :- !,
    nanocop_contains_equality(A).

% Compound terms (check arguments recursively)
nanocop_contains_equality(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    nanocop_contains_equality(Arg), !.

% Base case: no equality
nanocop_contains_equality(_) :- fail.

% =========================================================================
% BASIC EQUALITY AXIOMS
% =========================================================================

%% basic_equality_axioms(-Axioms)
%% The three fundamental equality axioms
basic_equality_axioms((
    (all X:(X=X)),                                      % Reflexivity
    (all X:all Y:((X=Y)=>(Y=X))),                      % Symmetry
    (all X:all Y:all Z:(((X=Y),(Y=Z))=>(X=Z)))         % Transitivity
)).

% =========================================================================
% FORMULA TRANSLATION
% =========================================================================

%% translate_formula(+InputFormula, -OutputFormula)
%% Translates from TPTP syntax to nanoCoP internal syntax
translate_formula(F, F_out) :-
    translate_operators(F, F_out).

% =========================================================================
% OPERATOR TRANSLATION
% =========================================================================

% Bottom/falsum: # is translated to ~(p0 => p0) which represents ⊥
translate_operators(F, (~(p0 => p0))) :-
    nonvar(F),
    (F == '#' ; F == f ; F == bot ; F == bottom ; F == falsum),
    !.

% Top/verum: t is translated to (p0 => p0) which represents ⊤
translate_operators(F, (p0 => p0)) :-
    nonvar(F),
    (F == t ; F == top ; F == verum),
    !.

% Atomic formulas
translate_operators(F, F) :-
    atomic(F),
    \+ (F == '#'), \+ (F == f), \+ (F == bot),
    \+ (F == t), \+ (F == top),
    !.

% Variables
translate_operators(F, F) :-
    var(F), !.

% Negation
translate_operators(~A, (~A1)) :-
    !, translate_operators(A, A1).

% Disjunction
translate_operators(A | B, (A1 ; B1)) :-
    !, translate_operators(A, A1), translate_operators(B, B1).

% Conjunction
translate_operators(A & B, (A1 , B1)) :-
    !, translate_operators(A, A1), translate_operators(B, B1).

% Implication
translate_operators(A => B, (A1 => B1)) :-
    !, translate_operators(A, A1), translate_operators(B, B1).

% Biconditional
translate_operators(A <=> B, (A1 <=> B1)) :-
    !, translate_operators(A, A1), translate_operators(B, B1).

% Universal quantifier with brackets: ![X]:F
translate_operators(![Var]:A, (all RealVar:A1)) :-
    !,
    substitute_var_in_formula(A, Var, RealVar, A_subst),
    translate_operators(A_subst, A1).

% Existential quantifier with brackets: ?[X]:F
translate_operators(?[Var]:A, (ex RealVar:A1)) :-
    !,
    substitute_var_in_formula(A, Var, RealVar, A_subst),
    translate_operators(A_subst, A1).

% Universal quantifier simple syntax: !X:F (alternative)
translate_operators(!Var:A, (all VarUpper:A1)) :-
    atom(Var), !,
    upcase_atom(Var, VarUpper),
    translate_operators(A, A1).

% Existential quantifier simple syntax: ?X:F (alternative)
translate_operators(?Var:A, (ex VarUpper:A1)) :-
    atom(Var), !,
    upcase_atom(Var, VarUpper),
    translate_operators(A, A1).

% General compound terms (predicates with arguments)
translate_operators(Term, Term1) :-
    compound(Term),
    Term =.. [F|Args],
    maplist(translate_operators, Args, Args1),
    Term1 =.. [F|Args1].

% =========================================================================
% VARIABLE SUBSTITUTION
% =========================================================================

%% substitute_var_in_formula(+Formula, +OldVar, +NewVar, -NewFormula)
substitute_var_in_formula(Var, OldVar, NewVar, NewVar) :-
    atomic(Var), Var == OldVar, !.
substitute_var_in_formula(Atom, _OldVar, _NewVar, Atom) :-
    atomic(Atom), !.
substitute_var_in_formula(Var, _OldVar, _NewVar, Var) :-
    var(Var), !.
substitute_var_in_formula(Term, OldVar, NewVar, NewTerm) :-
    compound(Term), !,
    Term =.. [F|Args],
    maplist(substitute_var_in_formula_curry(OldVar, NewVar), Args, NewArgs),
    NewTerm =.. [F|NewArgs].

substitute_var_in_formula_curry(OldVar, NewVar, Arg, NewArg) :-
    substitute_var_in_formula(Arg, OldVar, NewVar, NewArg).
