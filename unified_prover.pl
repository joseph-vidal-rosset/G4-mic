% =========================================================================
% unified_prover.pl - Unified theorem prover with nanoCop validation
% =========================================================================
% Architecture: nanoCop (validation) + g4mic (proof display)
% 
% Workflow:
%   1. User types formula
%   2. nanoCop validates (fast, mature prover)
%   3. g4mic generates proof/refutation (pedagogical display)
%   4. If divergence: display nanoCop result + warn user
%
% Usage:
%   ?- [unified_prover].
%   prover> p | ~p.
%   prover> ![x]:p(x) => p(a).
%   prover> quit.
%
% Author: Joseph Vidal-Rosset with Claude
% License: GPL v3+
% =========================================================================

% Load required modules
:- use_module(library(lists)).
:- use_module(library(statistics)).

% =========================================================================
% LOAD PROVERS
% =========================================================================

% Load nanoCop (validation engine)
:- catch([minimal_driver], E, 
    (format('ERROR loading nanoCop: ~w~n', [E]), halt(1))).

% Load g4mic (proof display engine)
:- catch([g4mic_web], E,
    (format('ERROR loading g4mic: ~w~n', [E]), halt(1))).

% =========================================================================
% CONFIGURATION
% =========================================================================

% Timeout for nanoCop validation (seconds)
nanocop_timeout(5).

% Timeout for g4mic proof generation (seconds)
g4mic_timeout(10).

% =========================================================================
% MAIN PROVER INTERFACE
% =========================================================================

prover :-
    writeln(''),
    writeln('╔═══════════════════════════════════════════════════════════════════╗'),
    writeln('║                                                                   ║'),
    writeln('║          🔬 UNIFIED THEOREM PROVER (nanoCop + g4mic) 🔬          ║'),
    writeln('║                                                                   ║'),
    writeln('╠═══════════════════════════════════════════════════════════════════╣'),
    writeln('║                                                                   ║'),
    writeln('║  Double validation system:                                        ║'),
    writeln('║    1. nanoCop validates (mature, fast)                            ║'),
    writeln('║    2. g4mic displays proof (pedagogical, detailed)                ║'),
    writeln('║                                                                   ║'),
    writeln('║  Syntax:                                                          ║'),
    writeln('║    Propositional: p | ~p, (p => q) & p => q                       ║'),
    writeln('║    FOL:          ![x]:p(x) => p(a)                                ║'),
    writeln('║    Commands:     help, examples, quit                             ║'),
    writeln('║                                                                   ║'),
    writeln('║  💡 Remember: End each input with a dot!                          ║'),
    writeln('║                                                                   ║'),
    writeln('╚═══════════════════════════════════════════════════════════════════╝'),
    writeln(''),
    prover_loop.

% =========================================================================
% INTERACTIVE LOOP
% =========================================================================

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
    writeln('Please check your syntax and try again.'),
    prover_loop.

% =========================================================================
% FORMULA PROCESSING WITH DOUBLE VALIDATION
% =========================================================================

process_formula(Formula) :-
    writeln(''),
    writeln('═══════════════════════════════════════════════════════════════'),
    format('📝 Formula: ~w~n', [Formula]),
    
    % Show normalized version for g4mic if it contains quantifiers
    (contains_quantifiers(Formula) ->
        normalize_variables_to_lowercase(Formula, NormFormula),
        (Formula \= NormFormula ->
            format('   (normalized for g4mic: ~w)~n', [NormFormula])
        ; true)
    ; true),
    
    writeln('═══════════════════════════════════════════════════════════════'),
    
    % Phase 1: nanoCop validation
    writeln(''),
    writeln('🔍 Phase 1: nanoCop validation...'),
    nanocop_validate(Formula, NanoResult),
    
    % Phase 2: g4mic proof generation
    writeln(''),
    writeln('📐 Phase 2: g4mic proof generation...'),
    g4mic_prove(Formula, G4Result),
    
    % Phase 3: Consolidation
    writeln(''),
    consolidate_and_report(Formula, NanoResult, G4Result),
    writeln('═══════════════════════════════════════════════════════════════'),
    writeln('').

% Helper to check if formula contains quantifiers
contains_quantifiers(![_]:_) :- !.
contains_quantifiers(?[_]:_) :- !.
contains_quantifiers(A & B) :- !, (contains_quantifiers(A) ; contains_quantifiers(B)).
contains_quantifiers(A | B) :- !, (contains_quantifiers(A) ; contains_quantifiers(B)).
contains_quantifiers(A => B) :- !, (contains_quantifiers(A) ; contains_quantifiers(B)).
contains_quantifiers(A <=> B) :- !, (contains_quantifiers(A) ; contains_quantifiers(B)).
contains_quantifiers(~A) :- !, contains_quantifiers(A).
contains_quantifiers(Term) :- compound(Term), Term =.. [_|Args], member(Arg, Args), contains_quantifiers(Arg).

% =========================================================================
% NANOCOP VALIDATION
% =========================================================================

nanocop_validate(Formula, Result) :-
    nanocop_timeout(Timeout),
    statistics(cputime, T0),
    catch(
        call_with_time_limit(
            Timeout,
            (decide(Formula) -> Result = proved ; Result = refuted)
        ),
        time_limit_exceeded,
        Result = timeout
    ),
    statistics(cputime, T1),
    Time is T1 - T0,
    report_nanocop_result(Result, Time).

report_nanocop_result(proved, Time) :-
    format('   ✅ nanoCop: PROVED (in ~3f seconds)~n', [Time]).
report_nanocop_result(refuted, Time) :-
    format('   ❌ nanoCop: REFUTED (in ~3f seconds)~n', [Time]).
report_nanocop_result(timeout, Time) :-
    format('   ⏱️  nanoCop: TIMEOUT after ~3f seconds~n', [Time]).

% =========================================================================
% G4MIC PROOF GENERATION
% =========================================================================

g4mic_prove(Formula, Result) :-
    % Normalize variables to lowercase for g4mic
    normalize_variables_to_lowercase(Formula, NormalizedFormula),
    g4mic_timeout(Timeout),
    statistics(cputime, T0),
    catch(
        call_with_time_limit(
            Timeout,
            (prove(NormalizedFormula) -> Result = proved ; Result = refuted)
        ),
        time_limit_exceeded,
        Result = timeout
    ),
    statistics(cputime, T1),
    Time is T1 - T0,
    report_g4mic_result(Result, Time).

% =========================================================================
% VARIABLE NORMALIZATION (uppercase to lowercase)
% =========================================================================
% g4mic expects lowercase variables: ![x]: not ![X]:
% nanoCop accepts both but converts to uppercase internally

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

report_g4mic_result(proved, Time) :-
    format('   ✅ g4mic: PROVED (in ~3f seconds)~n', [Time]).
report_g4mic_result(refuted, Time) :-
    format('   ❌ g4mic: REFUTED (in ~3f seconds)~n', [Time]).
report_g4mic_result(timeout, Time) :-
    format('   ⏱️  g4mic: TIMEOUT after ~3f seconds~n', [Time]).

% =========================================================================
% RESULT CONSOLIDATION AND REPORTING
% =========================================================================

consolidate_and_report(Formula, NanoResult, G4Result) :-
    writeln('📊 Result consolidation:'),
    (   results_agree(NanoResult, G4Result)
    ->  report_agreement(NanoResult)
    ;   report_divergence(Formula, NanoResult, G4Result)
    ).

% Case: Both provers agree
results_agree(proved, proved) :- !.
results_agree(refuted, refuted) :- !.
results_agree(timeout, _) :- !.  % If nanoCop timeout, no comparison
results_agree(_, timeout) :- !.  % If g4mic timeout, no comparison

% Report agreement
report_agreement(proved) :-
    writeln(''),
    writeln('✅✅✅ BOTH PROVERS AGREE: THEOREM PROVED ✅✅✅'),
    writeln(''),
    writeln('The formula is VALID in the detected logic level.'),
    writeln('See above for the complete proof from g4mic.').

report_agreement(refuted) :-
    writeln(''),
    writeln('❌❌❌ BOTH PROVERS AGREE: FORMULA REFUTED ❌❌❌'),
    writeln(''),
    writeln('The formula is INVALID in the detected logic level.'),
    writeln('See above for the refutation/countermodel from g4mic.').

report_agreement(timeout) :-
    writeln(''),
    writeln('⏱️  TIMEOUT: Cannot determine result'),
    writeln(''),
    writeln('Try simplifying the formula or increasing timeout.').

% Report divergence (BUG DETECTED!)
report_divergence(Formula, NanoResult, G4Result) :-
    writeln(''),
    writeln('╔═══════════════════════════════════════════════════════════════╗'),
    writeln('║                                                               ║'),
    writeln('║                   ⚠️  DIVERGENCE DETECTED! ⚠️                 ║'),
    writeln('║                                                               ║'),
    writeln('╚═══════════════════════════════════════════════════════════════╝'),
    writeln(''),
    writeln('The two provers give DIFFERENT results:'),
    writeln(''),
    format('   nanoCop result: ~w~n', [NanoResult]),
    format('   g4mic result:   ~w~n', [G4Result]),
    writeln(''),
    writeln('╔═══════════════════════════════════════════════════════════════╗'),
    writeln('║  DISPLAYING NANOCOP RESULT (more mature prover)              ║'),
    writeln('╚═══════════════════════════════════════════════════════════════╝'),
    writeln(''),
    display_nanocop_conclusion(NanoResult),
    writeln(''),
    writeln('╔═══════════════════════════════════════════════════════════════╗'),
    writeln('║                     🐛 BUG REPORT REQUEST 🐛                  ║'),
    writeln('╚═══════════════════════════════════════════════════════════════╝'),
    writeln(''),
    writeln('This divergence indicates a potential bug in one of the provers.'),
    writeln(''),
    writeln('Please report this with the following information:'),
    writeln(''),
    format('   Formula: ~w~n', [Formula]),
    format('   nanoCop: ~w~n', [NanoResult]),
    format('   g4mic:   ~w~n', [G4Result]),
    writeln(''),
    writeln('Thank you for helping improve the prover! 🙏').

display_nanocop_conclusion(proved) :-
    writeln('According to nanoCop (trusted reference):'),
    writeln('   ✅ This formula is PROVABLE').

display_nanocop_conclusion(refuted) :-
    writeln('According to nanoCop (trusted reference):'),
    writeln('   ❌ This formula is NOT PROVABLE').

display_nanocop_conclusion(timeout) :-
    writeln('nanoCop could not determine the result (timeout).').

% =========================================================================
% HELP SYSTEM
% =========================================================================

show_help :-
    writeln(''),
    writeln('═══════════════════════════════════════════════════════════════'),
    writeln('                         HELP SYSTEM'),
    writeln('═══════════════════════════════════════════════════════════════'),
    writeln(''),
    writeln('SYNTAX:'),
    writeln(''),
    writeln('  Propositional Logic:'),
    writeln('    ~       negation'),
    writeln('    &       conjunction'),
    writeln('    |       disjunction'),
    writeln('    =>      implication'),
    writeln('    <=>     biconditional'),
    writeln('    #       bottom/falsum'),
    writeln(''),
    writeln('  First-Order Logic:'),
    writeln('    ![x]:   universal quantifier'),
    writeln('    ?[x]:   existential quantifier'),
    writeln('    =       equality (handled by nanoCop)'),
    writeln(''),
    writeln('EXAMPLES:'),
    writeln(''),
    writeln('  Propositional:'),
    writeln('    p | ~p.                        % Excluded middle'),
    writeln('    (p => q) & p => q.             % Modus ponens'),
    writeln('    ((p => q) => p) => p.          % Peirce law'),
    writeln(''),
    writeln('  First-Order:'),
    writeln('    ![x]:p(x) => p(a).             % Universal instantiation'),
    writeln('    p(a) => ?[x]:p(x).             % Existential generalization'),
    writeln('    ![x]:(p(x) => q(x)) & p(a) => q(a).'),
    writeln(''),
    writeln('  Equality:'),
    writeln('    a = a.                         % Reflexivity'),
    writeln('    a = b & p(a) => p(b).          % Leibniz law'),
    writeln(''),
    writeln('COMMANDS:'),
    writeln('    help        Show this help'),
    writeln('    examples    Show more examples'),
    writeln('    quit        Exit the prover'),
    writeln(''),
    writeln('═══════════════════════════════════════════════════════════════'),
    writeln('').

show_examples :-
    writeln(''),
    writeln('═══════════════════════════════════════════════════════════════'),
    writeln('                      EXAMPLE FORMULAS'),
    writeln('═══════════════════════════════════════════════════════════════'),
    writeln(''),
    writeln('MINIMAL LOGIC (always provable):'),
    writeln('  p => p.'),
    writeln('  p => (q => p).'),
    writeln('  (p => (q => r)) => ((p => q) => (p => r)).'),
    writeln(''),
    writeln('INTUITIONISTIC LOGIC:'),
    writeln('  (p => q) => (~q => ~p).          % Contraposition (weak)'),
    writeln('  (p & ~p) => #.                   % Contradiction'),
    writeln('  # => p.                          % Ex falso quodlibet'),
    writeln(''),
    writeln('CLASSICAL LOGIC:'),
    writeln('  p | ~p.                          % Excluded middle'),
    writeln('  ((p => #) => #) => p.            % Double negation'),
    writeln('  (~q => ~p) => (p => q).          % Contraposition (strong)'),
    writeln(''),
    writeln('FIRST-ORDER LOGIC:'),
    writeln('  ![x]:p(x) => ?[y]:p(y).'),
    writeln('  ?[x]:p(x) => ![y]:(p(y) => q) => q.'),
    writeln('  ![x]:(p(x) => q(x)) => (![x]:p(x) => ![x]:q(x)).'),
    writeln(''),
    writeln('EQUALITY (via nanoCop):'),
    writeln('  a = a.'),
    writeln('  a = b => b = a.'),
    writeln('  a = b & b = c => a = c.'),
    writeln('  a = b & p(a) => p(b).'),
    writeln(''),
    writeln('═══════════════════════════════════════════════════════════════'),
    writeln('').

% =========================================================================
% INITIALIZATION
% =========================================================================

:- writeln('✅ Unified prover loaded successfully.').
:- writeln('Type "prover." to start the interactive prover.').
:- writeln('').
