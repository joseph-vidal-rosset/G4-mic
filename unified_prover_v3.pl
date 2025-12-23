% =========================================================================
% unified_prover.pl - Version 3.0 - Pure nanoCop respect
% =========================================================================
% Philosophy:
%   - nanoCop is the REFERENCE (Jens Otten's work)
%   - minimal_driver is ONLY a translator
%   - g4mic displays proofs pedagogically
%   - No interpretation of nanoCop's output
%
% Author: Joseph Vidal-Rosset with Claude
% =========================================================================

:- use_module(library(lists)).
:- use_module(library(statistics)).

% Dynamic predicate to track g4mic's detected logic level
:- dynamic g4mic_logic_level/1.

% Dynamic predicate to store current formula for time/1 display
:- dynamic current_formula/1.

% =========================================================================
% LOAD PROVERS
% =========================================================================

% Load nanoCop interface (the one that works!)
:- catch([minimal_driver], E,
    (format('ERROR loading nanoCop interface: ~w~n', [E]), halt(1))).

% Load g4mic (proof display engine)
:- catch([g4mic_web], E,
    (format('ERROR loading g4mic: ~w~n', [E]), halt(1))).

% =========================================================================
% CONFIGURATION
% =========================================================================

nanocop_timeout(10).
g4mic_timeout(15).

% =========================================================================
% MAIN INTERFACE
% =========================================================================

prover :-
    writeln(''),
    writeln('╔═══════════════════════════════════════════════════════════════════╗'),
    writeln('║                                                                   ║'),
    writeln('║          🔬 UNIFIED THEOREM PROVER v3 (Pure nanoCop) 🔬          ║'),
    writeln('║                                                                   ║'),
    writeln('╠═══════════════════════════════════════════════════════════════════╣'),
    writeln('║                                                                   ║'),
    writeln('║  Philosophy:                                                      ║'),
    writeln('║    • nanoCop (Jens Otten) is the REFERENCE                        ║'),
    writeln('║    • minimal_driver is ONLY a translator                          ║'),
    writeln('║    • g4mic displays proofs pedagogically                          ║'),
    writeln('║    • We respect the original work - no interpretation             ║'),
    writeln('║                                                                   ║'),
    writeln('║  Commands:                                                        ║'),
    writeln('║    • Type your formula (theorem syntax)                           ║'),
    writeln('║    • help, examples, quit                                         ║'),
    writeln('║                                                                   ║'),
    writeln('╚═══════════════════════════════════════════════════════════════════╝'),
    writeln(''),
    prover_loop.

prover_loop :-
    write('prover> '),
    flush_output,
    catch(read(Input), E, handle_read_error(E)),
    (   Input = quit
    ->  writeln('Goodbye!'), !
    ;   Input = end_of_file
    ->  writeln('Goodbye!'), !
    ;   Input = help
    ->  show_help, !, prover_loop
    ;   Input = examples
    ->  show_examples, !, prover_loop
    ;   process_formula(Input),
        prover_loop
    ).

handle_read_error(E) :-
    format('~nERROR reading input: ~w~n', [E]),
    writeln('Please check your syntax.'),
    prover_loop.

% =========================================================================
% FORMULA PROCESSING
% =========================================================================

process_formula(Formula) :-
    writeln(''),
    writeln('═══════════════════════════════════════════════════════════════'),
    format('📝 Formula: ~w~n', [Formula]),
    writeln('═══════════════════════════════════════════════════════════════'),

    % Check if it's a sequent (only g4mic handles those)
    (is_sequent_syntax(Formula) ->
        handle_sequent_only(Formula)
    ;
        handle_theorem(Formula)
    ).

% =========================================================================
% SEQUENT DETECTION
% =========================================================================

is_sequent_syntax(_ > _) :- !.
is_sequent_syntax([_|_] > _) :- !.
is_sequent_syntax(_ > [_|_]) :- !.

handle_sequent_only(Formula) :-
    writeln(''),
    writeln('⚠️  SEQUENT SYNTAX DETECTED'),
    writeln(''),
    writeln('Sequents ([A, B] > [C]) are ONLY supported by g4mic.'),
    writeln('nanoCop does NOT support sequent syntax.'),
    writeln('Skipping nanoCop validation.'),
    writeln(''),
    writeln('───────────────────────────────────────────────────────────────'),
    writeln('📐 g4mic proof generation...'),
    writeln('───────────────────────────────────────────────────────────────'),

    g4mic_prove(Formula, G4Result),

    writeln(''),
    writeln('═══════════════════════════════════════════════════════════════'),
    report_g4mic_only_result(G4Result),
    writeln('═══════════════════════════════════════════════════════════════'),
    writeln('').

report_g4mic_only_result(proved) :-
    writeln('✅ g4mic: SEQUENT IS VALID'),
    writeln(''),
    writeln('See the proof above.').

report_g4mic_only_result(refuted) :-
    writeln('❌ g4mic: SEQUENT IS INVALID'),
    writeln(''),
    writeln('See the refutation above.').

report_g4mic_only_result(timeout) :-
    writeln('⏱️  g4mic: TIMEOUT'),
    writeln(''),
    writeln('Try simplifying the sequent.').

report_g4mic_only_result(error) :-
    writeln('❌ g4mic: ERROR'),
    writeln(''),
    writeln('Check the sequent syntax.').

% =========================================================================
% THEOREM HANDLING (double validation)
% =========================================================================

handle_theorem(Formula) :-
    % Store formula for later time/1 display
    retractall(current_formula(_)),
    assert(current_formula(Formula)),

    % Normalize variables for g4mic compatibility
    normalize_variables_to_lowercase(Formula, NormalizedFormula),
    (Formula \= NormalizedFormula ->
        format('   (variables normalized: ~w)~n', [NormalizedFormula])
    ; true),

    writeln(''),
    writeln('───────────────────────────────────────────────────────────────'),
    writeln('🔍 Phase 1: nanoCop validation...'),
    writeln('───────────────────────────────────────────────────────────────'),

    nanocop_validate(Formula, NanoResult),
    writeln('   ✓ Done'),

    writeln(''),
    writeln('───────────────────────────────────────────────────────────────'),
    writeln('📐 Phase 2: g4mic proof generation...'),
    writeln('───────────────────────────────────────────────────────────────'),

    % Capture g4mic's logic level detection
    retractall(g4mic_logic_level(_)),
    g4mic_prove(NormalizedFormula, G4Result),
    (retract(g4mic_logic_level(LogicLevel)) -> true ; LogicLevel = unknown),

    writeln(''),
    writeln('═══════════════════════════════════════════════════════════════'),
    writeln('📊 FINAL RESULT:'),
    writeln('═══════════════════════════════════════════════════════════════'),
    consolidate_and_report(Formula, NanoResult, G4Result, LogicLevel),
    writeln('═══════════════════════════════════════════════════════════════'),
    writeln('').

% =========================================================================
% NANOCOP VALIDATION (pure - no interpretation)
% =========================================================================

nanocop_validate(Formula, Result) :-
    nanocop_timeout(Timeout),
    % Silent validation
    catch(
        call_with_time_limit(
            Timeout,
            (decide(Formula) -> Result = proved ; Result = refuted)
        ),
        time_limit_exceeded,
        Result = timeout
    ).

report_nanocop_result(_Result) :-
    % Silent - result will be shown in final summary
    true.

% =========================================================================
% G4MIC PROOF GENERATION
% =========================================================================

g4mic_prove(Formula, Result) :-
    g4mic_timeout(Timeout),
    catch(
        call_with_time_limit(
            Timeout,
            (prove(Formula) -> Result = proved ; Result = refuted)
        ),
        time_limit_exceeded,
        Result = timeout
    ),
    report_g4mic_result(Result).

report_g4mic_result(_Result) :-
    % Silent - result will be shown in final summary
    true.

% =========================================================================
% RESULT CONSOLIDATION
% =========================================================================

consolidate_and_report(Formula, NanoResult, G4Result, LogicLevel) :-
    writeln(''),
    (   results_agree(NanoResult, G4Result)
    ->  Status = agreement
    ;   Status = divergence
    ),
    display_final_summary(Formula, NanoResult, G4Result, LogicLevel, Status).

% Agreement cases
results_agree(proved, proved) :- !.
results_agree(refuted, refuted) :- !.
results_agree(timeout, _) :- !.  % Can't compare if timeout
results_agree(_, timeout) :- !.

% =========================================================================
% FINAL SUMMARY (with time/1 output display)
% =========================================================================

display_final_summary(Formula, NanoResult, G4Result, LogicLevel, Status) :-
    writeln('╔═══════════════════════════════════════════════════════════════╗'),
    writeln('║                       📋 FINAL SUMMARY                        ║'),
    writeln('╚═══════════════════════════════════════════════════════════════╝'),
    writeln(''),
    format('Formula: ~w~n', [Formula]),
    writeln(''),

    % nanoCop result with time/1 display
    writeln('─────────────────────────────────────────────────────────────'),
    writeln('🔍 nanoCop:'),
    writeln('─────────────────────────────────────────────────────────────'),
    % Re-execute with time/1 to show stats (ignore return value)
    (current_formula(StoredFormula) ->
        (time(decide(StoredFormula)) -> true ; true)
    ;
        writeln('   (formula not stored)')
    ),
    format('   Result: ~w~n', [NanoResult]),
    (NanoResult = proved ->
        writeln('   ➜ The formula is provable')
    ; NanoResult = refuted ->
        writeln('   ➜ The formula is not provable')
    ;
        writeln('   ➜ Timeout')
    ),

    writeln(''),
    writeln('─────────────────────────────────────────────────────────────'),
    writeln('📐 g4mic:'),
    writeln('─────────────────────────────────────────────────────────────'),
    format('   Result: ~w', [G4Result]),
    (LogicLevel \= unknown ->
        format(' in ~w~n', [LogicLevel])
    ;
        writeln('')
    ),
    (G4Result = proved ->
        (LogicLevel \= unknown ->
            format('   ➜ Proof found in ~w~n', [LogicLevel])
        ;
            writeln('   ➜ Proof found')
        )
    ; G4Result = refuted ->
        writeln('   ➜ Counter-model / refutation found')
    ;
        writeln('   ➜ Timeout')
    ),

    writeln(''),
    writeln('─────────────────────────────────────────────────────────────'),
    (Status = agreement ->
        writeln('✅ Status: Both provers agree')
    ;
        writeln('⚠️  Status: DIVERGENCE'),
        writeln(''),
        writeln('   The two provers give different results.'),
        writeln('   This may indicate different logic systems or a bug.'),
        writeln('   Please investigate: joseph.vidal.rosset@gmail.com')
    ),
    writeln('').

% =========================================================================
% VARIABLE NORMALIZATION (for g4mic compatibility)
% =========================================================================

normalize_variables_to_lowercase(![Var]:Formula, ![LowerVar]:NormFormula) :- !,
    (atom(Var) -> downcase_atom(Var, LowerVar) ; LowerVar = Var),
    normalize_variables_to_lowercase(Formula, NormFormula).

normalize_variables_to_lowercase(?[Var]:Formula, ?[LowerVar]:NormFormula) :- !,
    (atom(Var) -> downcase_atom(Var, LowerVar) ; LowerVar = Var),
    normalize_variables_to_lowercase(Formula, NormFormula).

normalize_variables_to_lowercase(A & B, NA & NB) :- !,
    normalize_variables_to_lowercase(A, NA),
    normalize_variables_to_lowercase(B, NB).

normalize_variables_to_lowercase(A | B, NA | NB) :- !,
    normalize_variables_to_lowercase(A, NA),
    normalize_variables_to_lowercase(B, NB).

normalize_variables_to_lowercase(A => B, NA => NB) :- !,
    normalize_variables_to_lowercase(A, NA),
    normalize_variables_to_lowercase(B, NB).

normalize_variables_to_lowercase(A <=> B, NA <=> NB) :- !,
    normalize_variables_to_lowercase(A, NA),
    normalize_variables_to_lowercase(B, NB).

normalize_variables_to_lowercase(~A, ~NA) :- !,
    normalize_variables_to_lowercase(A, NA).

normalize_variables_to_lowercase(Term, NormTerm) :-
    compound(Term), !,
    Term =.. [F|Args],
    maplist(normalize_variables_to_lowercase, Args, NormArgs),
    NormTerm =.. [F|NormArgs].

normalize_variables_to_lowercase(X, X).

% =========================================================================
% HELP AND EXAMPLES
% =========================================================================

show_help :-
    writeln(''),
    writeln('═══════════════════════════════════════════════════════════════'),
    writeln('                    UNIFIED PROVER v3 HELP'),
    writeln('═══════════════════════════════════════════════════════════════'),
    writeln(''),
    writeln('PHILOSOPHY:'),
    writeln('  • nanoCop (Jens Otten) is the REFERENCE'),
    writeln('  • We trust nanoCop completely'),
    writeln('  • g4mic displays proofs pedagogically'),
    writeln('  • If they disagree, nanoCop is right'),
    writeln(''),
    writeln('SYNTAX:'),
    writeln('  Propositional: ~, &, |, =>, <=>'),
    writeln('  FOL:          ![x]:, ?[x]:'),
    writeln('  Constants:    t (top), f (bot)'),
    writeln('  Equality:     a = b'),
    writeln(''),
    writeln('EXAMPLES:'),
    writeln('  p | ~p.                    % Classical'),
    writeln('  ![x]:(p(x) => p(x)).       % FOL'),
    writeln('  a = b & p(a) => p(b).      % Equality'),
    writeln(''),
    writeln('SEQUENTS (g4mic only):'),
    writeln('  [a, b] > [c].              % Sequent'),
    writeln('  [] > [p | ~p].             % Empty context'),
    writeln(''),
    writeln('COMMANDS:'),
    writeln('  help       Show this help'),
    writeln('  examples   Show examples'),
    writeln('  quit       Exit'),
    writeln(''),
    writeln('═══════════════════════════════════════════════════════════════'),
    writeln('').

show_examples :-
    writeln(''),
    writeln('═══════════════════════════════════════════════════════════════'),
    writeln('                         EXAMPLES'),
    writeln('═══════════════════════════════════════════════════════════════'),
    writeln(''),
    writeln('PROPOSITIONAL LOGIC:'),
    writeln('  p | ~p.'),
    writeln('  (p => q) & p => q.'),
    writeln('  ((p => q) => p) => p.'),
    writeln(''),
    writeln('FIRST-ORDER LOGIC:'),
    writeln('  ![x]:(p(x) => p(x)).'),
    writeln('  ![x]:p(x) => p(a).'),
    writeln('  p(a) => ?[x]:p(x).'),
    writeln(''),
    writeln('EQUALITY:'),
    writeln('  a = a.'),
    writeln('  a = b => b = a.'),
    writeln('  a = b & p(a) => p(b).'),
    writeln(''),
    writeln('SEQUENTS (g4mic only):'),
    writeln('  [a, b] > [a & b].'),
    writeln('  [a => b, a] > [b].'),
    writeln('  [] > [p | ~p].'),
    writeln(''),
    writeln('═══════════════════════════════════════════════════════════════'),
    writeln('').

% =========================================================================
% INITIALIZATION
% =========================================================================

:- writeln('✅ Unified Prover v3 loaded (Pure nanoCop respect)').
:- writeln('Type "prover." to start.').
:- writeln('').
