%% File: minimal_driver_pure.pl  -  Version: 1.0
%%
%% Purpose: PURE translation interface for nanoCoP
%%          Translates TPTP syntax to nanoCoP internal syntax
%%          NOTHING MORE - respects Jens Otten's work
%%
%% Usage:   decide(Formula).  % translates and calls prove/2
%%          decide_with_proof(Formula, Proof). % returns proof
%%
%% Philosophy: This is ONLY a translator - no logic added
%%             All reasoning is done by nanoCoP itself
%%
%% Author: Joseph Vidal-Rosset
%% Based on: nanoCoP by Jens Otten
% =========================================================================
% LOADING REQUIRED MODULES
% =========================================================================

% Load nanoCoP core - THE authoritative prover
:- catch([nanocop20_swi], _, 
    catch([nanocop20], _, 
        (format('ERROR: nanoCoP core not found!~n'), halt(1)))).

% Load equality support if available
:- catch([nanocop_tptp2], _, true).

% Load proof display if available (errors are normal for version incompatibility)
:- catch([nanocop_proof], _, true).

% =========================================================================
% PURE TRANSLATION INTERFACE
% =========================================================================

%% nanocop_decide(+Formula) 
%% Pure translation interface - calls nanoCoP's prove/2 directly
nanocop_decide(Formula) :-
    translate_to_nanocop(Formula, InternalFormula),
    prove(InternalFormula, _Proof).

%% nanocop_decide_with_proof(+Formula, -Proof)
%% Returns the proof term from nanoCoP
nanocop_decide_with_proof(Formula, Proof) :-
    translate_to_nanocop(Formula, InternalFormula),
    prove(InternalFormula, Proof).

%% nanocop_decide_with_settings(+Formula, +Settings)
%% Calls nanoCoP's prove2/3 with custom settings
nanocop_decide_with_settings(Formula, Settings) :-
    translate_to_nanocop(Formula, InternalFormula),
    prove2(InternalFormula, Settings, _Proof).

%% nanocop_decide_with_equality(+Formula)
%% Uses nanoCoP's leancop_equal/2 for automatic equality axioms
nanocop_decide_with_equality(Formula) :-
    translate_to_nanocop(Formula, InternalFormula),
    (current_predicate(leancop_equal/2) ->
        leancop_equal(InternalFormula, FormulaWithEq),
        prove(FormulaWithEq, _Proof)
    ;
        % If leancop_equal not available, just prove normally
        prove(InternalFormula, _Proof)
    ).

% =========================================================================
% TRANSLATION: TPTP SYNTAX → NANOCOP INTERNAL SYNTAX
% =========================================================================

%% translate_to_nanocop(+TPTP, -NanoCopInternal)
%% This is the ONLY place where we modify the formula
%% Everything else is pure nanoCoP
translate_to_nanocop(F, F_out) :-
    translate_operators(F, F_out).

% Top and Bot (as per nanoCoP conventions)
translate_operators(F, (p0 => p0)) :- 
    nonvar(F), F == t, !.  % top/verum
translate_operators(F, ~(p0 => p0)) :- 
    nonvar(F), F == f, !.  % bot/falsum

% Atomic formulas (unchanged)
translate_operators(F, F) :- 
    atomic(F), !.
translate_operators(F, F) :- 
    var(F), !.

% Logical operators (TPTP → nanoCoP)
translate_operators(~A, ~A1) :- 
    !, translate_operators(A, A1).
translate_operators(A | B, (A1 ; B1)) :- 
    !, translate_operators(A, A1), translate_operators(B, B1).
translate_operators(A & B, (A1 , B1)) :- 
    !, translate_operators(A, A1), translate_operators(B, B1).
translate_operators(A => B, (A1 => B1)) :- 
    !, translate_operators(A, A1), translate_operators(B, B1).
translate_operators(A <=> B, (A1 <=> B1)) :- 
    !, translate_operators(A, A1), translate_operators(B, B1).

% Quantifiers: ![X]: → all X:
translate_operators(![Var]:A, all VarUpper:A1) :- 
    !, 
    (atom(Var) -> upcase_atom(Var, VarUpper) ; VarUpper = Var),
    translate_operators(A, A1).

translate_operators(?[Var]:A, ex VarUpper:A1) :- 
    !, 
    (atom(Var) -> upcase_atom(Var, VarUpper) ; VarUpper = Var),
    translate_operators(A, A1).

% Alternative quantifier syntax (already in nanoCoP format)
translate_operators(all Var:A, all Var:A1) :- 
    !, translate_operators(A, A1).
translate_operators(ex Var:A, ex Var:A1) :- 
    !, translate_operators(A, A1).

% Compound terms (predicates, functions)
translate_operators(Term, Term1) :-
    compound(Term),
    Term =.. [F|Args],
    maplist(translate_operators, Args, Args1),
    Term1 =.. [F|Args1].

% Base case
translate_operators(Term, Term) :-
    (atomic(Term) ; var(Term)).

% =========================================================================
% THAT'S IT - NO MORE LOGIC
% =========================================================================
% Everything above is PURE TRANSLATION
% All reasoning is done by nanoCoP's prove/2
% We respect Jens Otten's work - we don't modify it
% =========================================================================

% =========================================================================
% EXAMPLES (showing the translation)
% =========================================================================

show_translation_examples :-
    format('~n=== TRANSLATION EXAMPLES ===~n'),
    format('Shows how TPTP syntax is translated to nanoCoP internal syntax~n~n'),
    
    Examples = [
        (p | ~p),
        (p => q),
        ((p => q) & p => q),
        (![x]:p(x)),
        (?[x]:p(x)),
        (![x]:(p(x) => q(x))),
        t,
        f,
        (a = b)
    ],
    
    forall(member(Ex, Examples),
        (translate_to_nanocop(Ex, Internal),
         format('TPTP:     ~w~n', [Ex]),
         format('nanoCoP:  ~w~n~n', [Internal]))).

% =========================================================================
% HELP
% =========================================================================

nanocop_help :-
    format('~n=== PURE NANOCOP INTERFACE ===~n'),
    format('~nThis is a PURE TRANSLATION interface.~n'),
    format('It translates TPTP syntax to nanoCoP internal syntax.~n'),
    format('ALL reasoning is done by nanoCoP (Jens Otten).~n'),
    format('~nCommands:~n'),
    format('  decide(Formula).                    - Translate and prove~n'),
    format('  decide_with_proof(Formula, Proof).  - Get proof term~n'),
    format('  decide_with_settings(F, Settings).  - Use custom settings~n'),
    format('  decide_with_equality(Formula).      - Use equality axioms~n'),
    format('  show_translation_examples.          - See translations~n'),
    format('~nInput syntax (TPTP):~n'),
    format('  ~, &, |, =>, <=>   - logical operators~n'),
    format('  ![x]:, ?[x]:       - quantifiers~n'),
    format('  t, f               - top, bot~n'),
    format('  a = b              - equality~n'),
    format('~nOutput syntax (nanoCoP internal):~n'),
    format('  ~, \',\', \';\', =>, <=>  - operators~n'),
    format('  all X:, ex X:      - quantifiers (uppercase)~n'),
    format('  (p0 => p0)         - top~n'),
    format('  ~(p0 => p0)        - bot~n'),
    format('~nExamples:~n'),
    format('  decide(p | ~p).~n'),
    format('  decide(![x]:(p(x) => p(x))).~n'),
    format('  decide_with_equality(a = b & p(a) => p(b)).~n'),
    format('~n').

% =========================================================================
% INITIALIZATION
% =========================================================================

:- format('~nPure nanoCoP Interface loaded.~n').
:- format('Translation only - all reasoning by nanoCoP (Jens Otten).~n').
:- format('Type nanocop_help. for help.~n~n').
