%% File: nanocop_interface_en.pl  -  Version: 1.0
%%
%% Purpose: Enhanced user interface for nanoCoP
%% Usage:   decide(Formula).  % where Formula uses standard TPTP syntax
%%
%% Examples:
%%   decide(p | ~p).                    % Law of excluded middle
%%   decide(![X]: (p(X) => p(X))).     % Identity principle
%%   decide((p => q) & p => q).        % Modus ponens
%%
%% Author: Assistant interface for nanoCoP by Jens Otten

% =========================================================================
% LOADING REQUIRED MODULES
% =========================================================================
:- [test_loading].
% Load common operators
:- [operators].

% Load nanoCoP core (adapt according to your system)
:- (exists_file('nanocop20_swi.pl') -> 
      (format('Loading nanocop20_swi.pl...~n'), [nanocop20_swi]) ; 
    exists_file('nanocop20.pl') -> 
      (format('Loading nanocop20.pl...~n'), [nanocop20]) ; 
    (format('WARNING: nanoCoP core not found!~n'), fail)).

% Load proof module if available
:- (exists_file('nanocop_proof.pl') -> [nanocop_proof] ; true).

% =========================================================================
% MAIN INTERFACE
% =========================================================================

%% decide(+Formula) - Main prover interface
% Proves a formula with execution time display and result
decide(Formula) :-
    format('~n=== nanoCoP Enhanced Interface ===~n'),
    format('Formula to prove: ~w~n', [Formula]),
    format('Translating...~n'),
    
    % Convert to nanoCoP internal syntax
    (   translate_formula(Formula, InternalFormula)
    ->  format('Translated formula: ~w~n', [InternalFormula])
    ;   format('ERROR: Cannot translate formula~n'),
        fail
    ),
    
    format('~nStarting proof...~n'),
    format('=====================================~n'),
    
    % Measure execution time
    get_time(StartTime),
    statistics(cputime, StartCPU),
    
    % Call prover with error handling
    (   (current_predicate(prove/2) -> 
           catch(prove(InternalFormula, Proof), Error, handle_error(Error)) ;
           (format('ERROR: Predicate prove/2 not available~n'), fail))
    ->  % Success
        get_time(EndTime),
        statistics(cputime, EndCPU),
        WallTime is EndTime - StartTime,
        CPUTime is EndCPU - StartCPU,
        
        format('=====================================~n'),
        format('RESULT: THEOREM PROVED ✓~n'),
        format('Wall time: ~3f seconds~n', [WallTime]),
        format('CPU time: ~3f seconds~n', [CPUTime]),
        
        % Display proof if available
        (   var(Proof)
        ->  format('~nNo proof generated.~n')
        ;   format('~nProof found:~n'),
            display_proof_summary(Proof)
        )
        
    ;   % Failure
        get_time(EndTime),
        statistics(cputime, EndCPU),
        WallTime is EndTime - StartTime,
        CPUTime is EndCPU - StartCPU,
        
        format('=====================================~n'),
        format('RESULT: NON-THEOREM ✗~n'),
        format('Wall time: ~3f seconds~n', [WallTime]),
        format('CPU time: ~3f seconds~n', [CPUTime])
    ),
    format('=====================================~n~n').

%% decide_with_settings(+Formula, +Settings) - Interface with custom parameters
decide_with_settings(Formula, Settings) :-
    format('~n=== nanoCoP with custom settings ===~n'),
    format('Formula: ~w~n', [Formula]),
    format('Settings: ~w~n', [Settings]),
    
    translate_formula(Formula, InternalFormula),
    
    get_time(StartTime),
    statistics(cputime, StartCPU),
    
    (   (current_predicate(prove2/3) ->
           catch(prove2(InternalFormula, Settings, Proof), Error, handle_error(Error)) ;
           (format('ERROR: Predicate prove2/3 not available~n'), fail))
    ->  get_time(EndTime),
        statistics(cputime, EndCPU),
        WallTime is EndTime - StartTime,
        CPUTime is EndCPU - StartCPU,
        
        format('THEOREM PROVED with ~w in ~3fs~n', [Settings, WallTime]),
        (var(Proof) -> true ; display_proof_summary(Proof))
        
    ;   get_time(EndTime),
        statistics(cputime, EndCPU),
        WallTime is EndTime - StartTime,
        
        format('NON-THEOREM with ~w in ~3fs~n', [Settings, WallTime])
    ).

% =========================================================================
% FORMULA TRANSLATION
% =========================================================================

%% translate_formula(+InputFormula, -OutputFormula)
% Translates from TPTP syntax to nanoCoP internal syntax
translate_formula(F, F_out) :-
    translate_operators(F, F_out).

% Recursive operator translation
translate_operators(F, F) :- 
    atomic(F), !.
translate_operators(F, F) :- 
    var(F), !.
translate_operators(~A, (-A1)) :- 
    !, translate_operators(A, A1).
translate_operators(A | B, (A1 ; B1)) :- 
    !, translate_operators(A, A1), translate_operators(B, B1).
translate_operators(A & B, (A1 , B1)) :- 
    !, translate_operators(A, A1), translate_operators(B, B1).
translate_operators(A => B, (A1 => B1)) :- 
    !, translate_operators(A, A1), translate_operators(B, B1).
translate_operators(A <=> B, (A1 <=> B1)) :- 
    !, translate_operators(A, A1), translate_operators(B, B1).
translate_operators(![X]:A, (all X:A1)) :- 
    !, translate_operators(A, A1).
translate_operators(?[X]:A, (ex X:A1)) :- 
    !, translate_operators(A, A1).
translate_operators(Term, Term1) :-
    Term =.. [F|Args],
    maplist(translate_operators, Args, Args1),
    Term1 =.. [F|Args1].

% =========================================================================
% ERROR HANDLING
% =========================================================================

handle_error(Error) :-
    format('~nERROR DURING PROOF:~n'),
    format('  ~w~n', [Error]),
    fail.

% =========================================================================
% PROOF DISPLAY
% =========================================================================

display_proof_summary(Proof) :-
    format('Proof structure: '),
    (   is_list(Proof)
    ->  length(Proof, Len),
        format('list of ~w elements~n', [Len])
    ;   format('~w~n', [Proof])
    ),
    
    % Use proof module if loaded
    (   current_predicate(nanocop_proof/2)
    ->  format('~nDetailed proof available.~n')
    ;   format('~nProof module not loaded.~n')
    ).

% =========================================================================
% EXAMPLES AND TESTS
% =========================================================================

%% run_examples - Execute a series of examples
run_examples :-
    format('~n=== nanoCoP EXAMPLES ===~n'),
    
    % Example 1: Law of excluded middle
    format('~n1. Law of excluded middle (p ∨ ¬p):~n'),
    decide(p | ~p),
    
    % Example 2: Identity principle
    format('~n2. Identity principle (∀x: P(x) → P(x)):~n'),
    decide(![X]: (p(X) => p(X))),
    
    % Example 3: Modus ponens
    format('~n3. Modus ponens ((P → Q) ∧ P → Q):~n'),
    decide((p => q) & p => q),
    
    % Example 4: Quantifiers
    format('~n4. Predicate logic (∀x P(x) → ∃x P(x)):~n'),
    decide(![X]: p(X) => ?[Y]: p(Y)).

%% benchmark_settings - Compare different settings
benchmark_settings(Formula) :-
    format('~n=== SETTINGS BENCHMARK ===~n'),
    format('Formula: ~w~n~n', [Formula]),
    
    Settings = [
        [cut, comp(7)],
        [scut],
        [cut],
        []
    ],
    
    forall(member(S, Settings),
           (format('Settings ~w: ', [S]),
            decide_with_settings(Formula, S))).

% =========================================================================
% UTILITIES
% =========================================================================

%% help - Display help
help :-
    format('~n=== nanoCoP Enhanced HELP ===~n'),
    format('~nMain commands:~n'),
    format('  decide(Formula)                 - Prove a formula~n'),
    format('  decide_with_settings(F, S)      - Prove with settings~n'),
    format('  run_examples                    - Run examples~n'),
    format('  benchmark_settings(Formula)     - Compare settings~n'),
    format('  help                            - Display this help~n'),
    format('~nFormula syntax (TPTP):~n'),
    format('  ~                               - negation~n'),
    format('  &                               - conjunction~n'),
    format('  |                               - disjunction~n'),
    format('  =>                              - implication~n'),
    format('  <=>                             - biconditional~n'),
    format('  ![X]:                           - universal quantifier~n'),
    format('  ?[X]:                           - existential quantifier~n'),
    format('~nExamples:~n'),
    format('  decide(p | ~p).~n'),
    format('  decide(![X]: (p(X) => q(X))).~n'),
    format('  decide((p => q) & p => q).~n'),
    format('~n').

% =========================================================================
% INITIALIZATION
% =========================================================================

:- format('nanoCoP Enhanced Interface loaded.~n').
:- format('Type help. for help.~n').
:- format('Type run_examples. to see examples.~n').
