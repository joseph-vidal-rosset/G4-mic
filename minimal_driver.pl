%% File: minimal_driver_enhanced.pl  -  Version: 2.0
%%
%% Purpose: Enhanced user interface for nanoCoP with full equality support
%% Usage:   nanoCop_decides(Formula).  % where Formula uses standard TPTP syntax
%%
%% Features:
%%   - Automatic equality axiom injection (reflexivity, symmetry, transitivity)
%%   - Leibniz substitution axioms for predicates and functions
%%   - Full FOL with equality support
%%   - Top (t) and Bot (f) support
%%
%% Examples:
%%   nanoCop_decides(a = a).                          % Reflexivity
%%   nanoCop_decides(a = b => b = a).                 % Symmetry
%%   nanoCop_decides(a = b & b = c => a = c).         % Transitivity
%%   nanoCop_decides(a = b & p(a) => p(b)).           % Leibniz for predicates
%%   nanoCop_decides(a = b => f(a) = f(b)).           % Leibniz for functions
%%   nanoCop_decides(![x]: (p(x) => p(x))).           % FOL identity
%%
%% Author: Joseph Vidal-Rosset with Claude
%% Based on: nanoCoP by Jens Otten
% =========================================================================
% LOADING REQUIRED MODULES
% =========================================================================
:- catch([operators], _, true).
:- catch([system_check], _, true).
:- catch([tests], _, true).

% Load nanoCoP core
:- catch([nanocop20_swi], _,
    catch([nanocop20], _,
        format('WARNING: nanoCoP core not found!~n'))).

% Load proof module
:- catch([nanocop_proof], _, true).

% CRITICAL: Load nanocop_tptp2 for equality axioms
:- catch([nanocop_tptp2], _,
    format('WARNING: nanocop_tptp2 not found - equality support disabled!~n')).

:- [tests_pelletier].

% =========================================================================
% MAIN INTERFACE with EQUALITY SUPPORT
% =========================================================================

%% nanoCop_decides(+Formula) - Prove formula with automatic equality axioms
/*
nanoCop_decides(Formula) :-
    translate_formula(Formula, InternalFormula),
    % Check if formula contains equality
    (nanocop_contains_equality(Formula) ->
        % Add equality axioms automatically
        add_equality_axioms(InternalFormula, FormulaWithEq),
        format('~n[Equality detected - axioms added automatically]~n')
    ;
        FormulaWithEq = InternalFormula
    ),
    time(prove2(FormulaWithEq, [cut,comp(7)], _Proof)),
    !.
*/
%% nanoCop_decides(+Formula) - Prove formula with automatic equality axioms
nanoCop_decides(Formula) :-
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

    % Step 4: Prove
    time(prove2(FormulaWithEq, [cut,comp(7)], _Proof)),
    !.

%% nanoCop_decides_no_eq(+Formula) - Prove formula WITHOUT equality axioms
%% Use this if you want to disable automatic equality handling
nanoCop_decides_no_eq(Formula) :-
    translate_formula(Formula, InternalFormula),
    time(prove2(InternalFormula, [cut,comp(7)], _Proof)),
    !.

% =========================================================================
% EQUALITY DETECTION
% =========================================================================
/*
nanocop_contains_equality(A = B) :-
    A \= B, !.  % Detect equality operator
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
nanocop_contains_equality(![_]:A) :- !,
    nanocop_contains_equality(A).
nanocop_contains_equality(?[_]:A) :- !,
    nanocop_contains_equality(A).
nanocop_contains_equality(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    nanocop_contains_equality(Arg).
*/
% =========================================================================
% EQUALITY DETECTION (CORRECTED)
% =========================================================================

nanocop_contains_equality((_ = _)) :- !.  % Any equality, even X = X

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
    \+ (Term = (_ = _)),  % Already handled above
    Term =.. [_|Args],
    member(Arg, Args),
    nanocop_contains_equality(Arg), !.

% Base case:  no equality
nanocop_contains_equality(_) :- fail.
% =========================================================================
% EQUALITY AXIOM INJECTION
% =========================================================================

%% add_equality_axioms(+Formula, -FormulaWithAxioms)
%% Adds basic equality axioms and Leibniz substitution axioms
add_equality_axioms(Formula, (EqAxioms, Formula)) :-
    % Use nanoCop's leancop_equal/2 if available
    (current_predicate(leancop_equal/2) ->
        leancop_equal(Formula, FormulaWithAxioms1),
        % Extract just the axioms part
        (FormulaWithAxioms1 = (Axioms => _) ->
            EqAxioms = Axioms,
            _FormulaWithAxioms = FormulaWithAxioms1
        ;
         FormulaWithAxioms1 = (Axioms, _) ->
            EqAxioms = Axioms,
            _FormulaWithAxioms = FormulaWithAxioms1
        ;
            % No axioms added, use basic ones
            basic_equality_axioms(EqAxioms),
            _FormulaWithAxioms = (EqAxioms, Formula)
        )
    ;
        % Fallback: use basic axioms only
        format('~n[WARNING: leancop_equal/2 not available - using basic axioms only]~n'),
        basic_equality_axioms(EqAxioms),
        _FormulaWithAxioms = (EqAxioms, Formula)
    ).

%% add_equality_axioms(+Formula, -FormulaWithAxioms)
%% Adds basic equality axioms and Leibniz substitution axioms
add_equality_axioms(Formula, FormulaWithAxioms) :-
    % Use nanoCop's leancop_equal/2 if available
    (current_predicate(leancop_equal/2) ->
         % SIMPLE:  Just use the result directly!
         leancop_equal(Formula, FormulaWithAxioms)
    ;
    % Fallback: use basic axioms only
    format('~n[WARNING:  leancop_equal/2 not available - using basic axioms only]~n'),
    basic_equality_axioms(EqAxioms),
    FormulaWithAxioms = (EqAxioms => Formula)
    ).

%% basic_equality_axioms(-Axioms)
%% The three fundamental equality axioms

basic_equality_axioms((
    (all X:(X=X)),                                      % Reflexivity
    (all X:all Y:((X=Y)=>(Y=X))),                      % Symmetry
    (all X:all Y:all Z:(((X=Y),(Y=Z))=>(X=Z)))         % Transitivity
)).

% =========================================================================
% FORMULA TRANSLATION (with top and bot)
% =========================================================================

%% translate_formula(+InputFormula, -OutputFormula)
% Translates from TPTP syntax to nanoCoP internal syntax
translate_formula(F, F_out) :-
    translate_operators(F, F_out).

% Recursive operator translation
translate_operators(F, (~(p0 => p0))) :-
    nonvar(F), F == f, !.  % bot/falsum
translate_operators(F, (p0 => p0)) :-
    nonvar(F), F == t, !.  % top/verum
translate_operators(F, F) :-
    atomic(F), !.
translate_operators(F, F) :-
    var(F), !.
translate_operators(~A, (~A1)) :-
    !, translate_operators(A, A1).
translate_operators(A | B, (A1 ; B1)) :-
    !, translate_operators(A, A1), translate_operators(B, B1).
translate_operators(A & B, (A1 , B1)) :-
    !, translate_operators(A, A1), translate_operators(B, B1).
translate_operators(A => B, (A1 => B1)) :-
    !, translate_operators(A, A1), translate_operators(B, B1).
translate_operators(A <=> B, (A1 <=> B1)) :-
    !, translate_operators(A, A1), translate_operators(B, B1).
% Quantifiers - creating real Prolog variables
translate_operators(![Var]:A, (![RealVar]:A1)) :-
    !,
    substitute_var_in_formula(A, Var, RealVar, A_subst),
    translate_operators(A_subst, A1).
translate_operators(?[Var]:A, (?[RealVar]:A1)) :-
    !,
    substitute_var_in_formula(A, Var, RealVar, A_subst),
    translate_operators(A_subst, A1).
% Quantifiers with simple variable (alternative syntax)
translate_operators(!Var:A, (all VarUpper:A1)) :-
    !, upcase_atom(Var, VarUpper),
    translate_operators(A, A1).
translate_operators(?Var:A, (ex VarUpper:A1)) :-
    !, upcase_atom(Var, VarUpper),
    translate_operators(A, A1).
% General predicates and terms
translate_operators(Term, Term1) :-
    compound(Term),
    Term =.. [F|Args],
    maplist(translate_operators, Args, Args1),
    Term1 =.. [F|Args1].
% Base case: atoms and variables
translate_operators(Term, Term) :-
    (atomic(Term) ; var(Term)).

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

% =========================================================================
% EXAMPLES WITH EQUALITY
% =========================================================================

run_equality_examples :-
    format('~n=== EQUALITY EXAMPLES ===~n'),

    % Basic equality axioms
    format('~n1. Reflexivity (a = a):~n'),
    nanoCop_decides(a = a),

    format('~n2. Symmetry (a = b => b = a):~n'),
    nanoCop_decides(a = b => b = a),

    format('~n3. Transitivity (a = b & b = c => a = c):~n'),
    nanoCop_decides(a = b & b = c => a = c),

    % Leibniz law
    format('~n4. Leibniz for predicates (a = b & p(a) => p(b)):~n'),
    nanoCop_decides(a = b & p(a) => p(b)),

    format('~n5. Leibniz for functions (a = b => f(a) = f(b)):~n'),
    nanoCop_decides(a = b => f(a) = f(b)),

    % Complex examples
    format('~n6. Substitution in binary predicate:~n'),
    nanoCop_decides(a = b & r(a, c) => r(b, c)),

    format('~n7. FOL with equality:~n'),
    nanoCop_decides(![x]:(x = x)),

    format('~n8. Existential with equality:~n'),
    nanoCop_decides(?[x]:(x = a)).

% =========================================================================
% TESTS
% =========================================================================

test_equality :-
    format('~n=== EQUALITY TESTS ===~n'),

    % Test 1: Reflexivity
    format('~nTest 1: a = a~n'),
    (nanoCop_decides(a = a) ->
        format('✓ SUCCESS~n') ;
        format('✗ FAIL~n')),

    % Test 2: Symmetry
    format('~nTest 2: a = b => b = a~n'),
    (nanoCop_decides(a = b => b = a) ->
        format('✓ SUCCESS~n') ;
        format('✗ FAIL~n')),

    % Test 3: Transitivity
    format('~nTest 3: a = b & b = c => a = c~n'),
    (nanoCop_decides(a = b & b = c => a = c) ->
        format('✓ SUCCESS~n') ;
        format('✗ FAIL~n')),

    % Test 4: Leibniz (predicate)
    format('~nTest 4: a = b & p(a) => p(b)~n'),
    (nanoCop_decides(a = b & p(a) => p(b)) ->
        format('✓ SUCCESS~n') ;
        format('✗ FAIL~n')),

    % Test 5: Leibniz (function)
    format('~nTest 5: a = b => f(a) = f(b)~n'),
    (nanoCop_decides(a = b => f(a) = f(b)) ->
        format('✓ SUCCESS~n') ;
        format('✗ FAIL~n')),

    % Test 6: FOL equality
    format('~nTest 6: ![x]:(x = x)~n'),
    (nanoCop_decides(![x]:(x = x)) ->
        format('✓ SUCCESS~n') ;
        format('✗ FAIL~n')).

% =========================================================================
% UTILITIES
% =========================================================================

nanocop_help :-
    format('~n=== nanoCoP Enhanced HELP (with full equality) ===~n'),
    format('~nMain commands:~n'),
    format('  nanoCop_decides(Formula).                   - Prove with automatic equality axioms~n'),
    format('  nanoCop_decides_no_eq(Formula).             - Prove without equality axioms~n'),
    format('  run_equality_examples.             - Run equality examples~n'),
    format('  test_equality.                     - Test equality support~n'),
    format('  help.                              - Display this help~n'),
    format('~nFormula syntax:~n'),
    format('  Propositional: ~, &, |, =>, <=>~n'),
    format('  FOL:          ![x]:, ?[x]:~n'),
    format('  Equality:     a = b~n'),
    format('  Constants:    f (bot), t (top)~n'),
    format('~nEquality features:~n'),
    format('  ✓ Automatic axiom injection~n'),
    format('  ✓ Reflexivity:  a = a~n'),
    format('  ✓ Symmetry:    a = b => b = a~n'),
    format('  ✓ Transitivity: a = b & b = c => a = c~n'),
    format('  ✓ Leibniz:     a = b & p(a) => p(b)~n'),
    format('  ✓ Functions:   a = b => f(a) = f(b)~n'),
    format('~nExamples:~n'),
    format('  nanoCop_decides(a = a).~n'),
    format('  nanoCop_decides(a = b & p(a) => p(b)).~n'),
    format('  nanoCop_decides(![x]:(x = x)).~n'),
    format('  nanoCop_decides(a = b => f(a) = f(b)).~n'),
    format('~n').

% =========================================================================
% INITIALIZATION
% =========================================================================

:- format('nanoCoP Enhanced Interface with Full Equality Support loaded.~n').
:- format('Type nanocop_help. for help.~n').
:- format('Type run_equality_examples. to see equality examples.~n').
:- format('Type test_equality. to test equality support.~n').
