%% File: minimal_driver.pl  -  Version: 2.3
%%
%% Purpose: Minimal interface for nanoCoP with automatic equality support
%% Usage:   nanoCop_decides(Formula).
%%
%% Author: Joseph Vidal-Rosset
%% Based on: nanoCoP by Jens Otten
%% Fix: Added proper translation for # (bottom/falsum)
%% Fix v2.3: Isolated occurs_check flag to prevent interference with g4mic
% =========================================================================

% =========================================================================
% LOADING REQUIRED MODULES
% =========================================================================
% :- catch([operators], _, true).
:- catch([system_check], _, true).

% Load nanoCoP core
:- catch([nanocop20_swi], _,
    % catch([nanocop20], _,
        format('WARNING: nanoCoP core not found!~n')).


% CRITICAL: Load nanocop_tptp2 for equality axioms
:- catch([nanocop_tptp2], _,
    format('WARNING: nanocop_tptp2 not found - equality support disabled!~n')).

% =========================================================================
% MAIN INTERFACE with EQUALITY SUPPORT and FLAG ISOLATION
% =========================================================================
%% nanoCop_decides(+Formula) - Prove formula with automatic equality axioms
%%
%% CRITICAL: This predicate manages occurs_check flag:
%% - nanoCop requires occurs_check=true (set by its module load)
%% - g4mic requires occurs_check=false (default Prolog behavior)
%% - We force false during setup, restore to true only during nanoCop call
nanoCop_decides(Formula) :-
    % Save current state (will be true if nanoCop module is loaded)
    current_prolog_flag(occurs_check, OriginalOccursCheck),

    % CRITICAL: Force occurs_check=false IMMEDIATELY for formula processing
    % This ensures translation and preprocessing happen with correct flag
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

    % Step 2: Translate formula (![X]:  → all X:)
    translate_formula(Formula, InternalFormula),

    % Step 3: Add equality axioms AFTER translation (if needed)
    (HasEquality = true ->
        (current_predicate(leancop_equal/2) ->
            leancop_equal(InternalFormula, TempFormula),
            (InternalFormula \= TempFormula ->
                format('~n[Equality detected - axioms added by leancop_equal]~n'),
                FormulaWithEq = TempFormula
            ;
                format('~n[Equality detected - using basic axioms (leancop_equal failed)]~n'),
                basic_equality_axioms(EqAxioms),
                FormulaWithEq = (EqAxioms => InternalFormula)
            )
        ;
            format('~n[Equality detected - using basic axioms]~n'),
            basic_equality_axioms(EqAxioms),
            FormulaWithEq = (EqAxioms => InternalFormula)
        )
    ;
        FormulaWithEq = InternalFormula
    ),

    % Step 4: Prove (occurs_check is true here)
    time(prove2(FormulaWithEq, [cut,comp(7)], _Proof)),
    !.

% =========================================================================
% INTERNAL NANOCOP LOGIC (isolated from flag pollution)
% =========================================================================
%% nanocop_prove_isolated(+Formula) - Internal predicate with nanoCop logic
nanocop_prove_isolated(Formula) :-
    % Step 1: Detect equality BEFORE translation
    (nanocop_contains_equality(Formula) ->
        HasEquality = true
    ;
        HasEquality = false
    ),

    % Step 2: Translate formula (![X]:  → all X:)
    translate_formula(Formula, InternalFormula),

    % Step 3: Add equality axioms AFTER translation (if needed)
    (HasEquality = true ->
        (current_predicate(leancop_equal/2) ->
            % Try leancop_equal first
            leancop_equal(InternalFormula, TempFormula),
            % Check if axioms were actually added
            (InternalFormula \= TempFormula ->
                format('~n[Equality detected - axioms added by leancop_equal]~n'),
                FormulaWithEq = TempFormula
            ;
                % Fallback:  leancop_equal failed, use basic axioms
                format('~n[Equality detected - using basic axioms (leancop_equal failed)]~n'),
                basic_equality_axioms(EqAxioms),
                FormulaWithEq = (EqAxioms => InternalFormula)
            )
        ;
            % leancop_equal not available
            format('~n[Equality detected - using basic axioms]~n'),
            basic_equality_axioms(EqAxioms),
            FormulaWithEq = (EqAxioms => InternalFormula)
        )
    ;
        % No equality detected
        FormulaWithEq = InternalFormula
    ),

    % Step 4: Prove (occurs_check is already true from nanoCop module load)
    time(prove2(FormulaWithEq, [cut,comp(7)], _Proof)),
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

nanocop_contains_equality(? [_]:A) :- !,
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
% CRITICAL: Handle # (bottom/falsum) - must come FIRST before compound terms

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

% Atomic formulas (must come before compound terms check)
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
