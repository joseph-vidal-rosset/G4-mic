%% File: nanocop_interface_en.pl  -  Version: 1.0
%%
%% Purpose: Enhanced user interface for nanoCoP
%% Usage:   decide(Formula).  % where Formula uses standard TPTP syntax
%%
%% Examples:
%%   decide(p | ~p).                    % Law of excluded middle
%%   decide(![X]: (p(X) => p(X))).     % Identity principle
%%   decide((p => q) & p => q).        % Modus ponens
%%   decide(f).                        % Bot (should fail)
%%   decide(t).                        % Top (should succeed)
%%   decide(t <=> ~f).                 % Top iff not-bot
%%
%% Author: Assistant interface for nanoCoP by Jens Otten
% =========================================================================
% LOADING REQUIRED MODULES
% =========================================================================
% Load common operators
:- [operators].
% System check. 
:- [system_check].
% Tests on FOL theorems
:- [tests]. 
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
        statistics(cputime, _EndCPU),
        WallTime is EndTime - StartTime,
        
        format('=====================================~n'),
        format('RESULT: NON-THEOREM ✗~n'),
        format('Wall time: ~3f seconds~n', [WallTime])
        % Note: CPU time not displayed for failed proofs to avoid singleton warning
    ),
    format('=====================================~n~n').

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
    !, % Create a real Prolog variable
    substitute_var_in_formula(A, Var, RealVar, A_subst),
    translate_operators(A_subst, A1).
translate_operators(?[Var]:A, (?[RealVar]:A1)) :- 
    !, % Create a real Prolog variable
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
% Substitutes a specific variable throughout the formula
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
% EXAMPLES AND TESTS (with top/bot)
% =========================================================================

%% run_examples - Execute a series of examples including top/bot
run_examples :-
    format('~n=== nanoCoP EXAMPLES (with top/bot) ===~n'),
    
    % Examples with bot
    format('~n1. Bot is unprovable:~n'),
    decide(f),
    
    % Examples with top  
    format('~n2. Top is provable:~n'),
    decide(t),
    
    % Relation top <=> ~bot
    format('~n3. Top is equivalent to not-bot (t <=> ~f):~n'),
    decide(t <=> ~f),
    
    % Ex falso quodlibet
    format('~n4. Ex falso quodlibet (f => p):~n'),
    decide(f => p),
    
    % Top doesn't imply bot
    format('~n5. Top doesn''t imply bot (~ (t => f)):~n'),
    decide(~(t => f)),
    
    % Law of excluded middle with bot
    format('~n6. Law of excluded middle reformulated ((p => f) | p):~n'),
    decide((p => f) | p),
    
    % Classical examples
    format('~n7. Law of excluded middle (p ∨ ¬p):~n'),
    decide(p | ~p),
    
    format('~n8. Identity principle (∀x: P(x) → P(x)):~n'),
    decide(![X]: (p(X) => p(X))),
    
    format('~n9. Modus ponens ((P → Q) ∧ P → Q):~n'),
    decide((p => q) & p => q),
    
    % Quantifiers
    format('~n10. Predicate logic (∀x P(x) → ∃x P(x)):~n'),
    decide(![X]: p(X) => ?[Y]: p(Y)).

% =========================================================================
% SPECIFIC TESTS for top/bot
% =========================================================================

test_top_bot :-
    format('~n=== TOP/BOT TESTS ===~n'),
    
    % Test 1: bot is unprovable
    format('~nTest 1: bot unprovable~n'),
    (decide(f) -> 
        format('❌ FAIL: bot should not be provable~n') ; 
        format('✓ SUCCESS: bot is not provable~n')),
    
    % Test 2: top is provable
    format('~nTest 2: top provable~n'),
    (decide(t) -> 
        format('✓ SUCCESS: top is provable~n') ; 
        format('❌ FAIL: top should be provable~n')),
    
    % Test 3: t <=> ~f
    format('~nTest 3: t <=> ~~f~n'),
    (decide(t <=> ~f) -> 
        format('✓ SUCCESS: top is equivalent to not-bot~n') ; 
        format('❌ FAIL: top should be equivalent to not-bot~n')),
    
    % Test 4: ~t <=> f  
    format('~nTest 4: ~~t <=> f~n'),
    (decide(~t <=> f) -> 
        format('✓ SUCCESS: not-top is equivalent to bot~n') ; 
        format('❌ FAIL: not-top should be equivalent to bot~n')),
    
    % Test 5: f => t (bot implies top)
    format('~nTest 5: f => t~n'),
    (decide(f => t) -> 
        format('✓ SUCCESS: bot implies top~n') ; 
        format('❌ FAIL: bot should imply top~n')),
    
    % Test 6: ~(t => f) (top doesn't imply bot)
    format('~nTest 6: ~~(t => f)~n'),
    (decide(~(t => f)) -> 
        format('✓ SUCCESS: top doesn''t imply bot~n') ; 
        format('❌ FAIL: top shouldn''t imply bot~n')),
    
    % Test 7: (p | ~p) <=> t (excluded middle is equivalent to top)
    format('~nTest 7: (p | ~~p) <=> t~n'),
    (decide((p | ~p) <=> t) -> 
        format('✓ SUCCESS: excluded middle is equivalent to top~n') ; 
        format('❌ FAIL: excluded middle should be equivalent to top~n')),
    
    % Test 8: (p & ~p) <=> f (contradiction is equivalent to bot)
    format('~nTest 8: (p & ~~p) <=> f~n'),
    (decide((p & ~p) <=> f) -> 
        format('✓ SUCCESS: contradiction is equivalent to bot~n') ; 
        format('❌ FAIL: contradiction should be equivalent to bot~n')).

% =========================================================================
% UTILITIES
% =========================================================================

%% help - Display help
help :-
    format('~n=== nanoCoP Enhanced HELP ===~n'),
    format('~nMain commands:~n'),
    format('  decide(Formula).                   - Prove a formula using TPTP syntax~n'),
    format('  prove(Formula, Proof)              - Prove a formula using nanoCoP internal syntax~n'),
    format('  translate_formula(TPTP, Internal)  - Translate TPTP syntax to internal syntax~n'),
    format('  run_examples.                      - Run examples~n'),
    format('  test_top_bot.                      - Test top/bot specifically~n'),
    format('  run_all_tests.                     - Run all tests~n'),
    format('  help.                              - Display this help~n'),
    format('~nFormula syntax for decide/1 (TPTP):~n'),
    format('  f                               - falsum (bot, ⊥)~n'),
    format('  t                               - verum (top, ⊤)~n'),
    format('  ~~                              - negation~n'),
    format('  &                               - conjunction~n'),
    format('  |                               - disjunction~n'),
    format('  =>                              - implication~n'),
    format('  <=>                             - biconditional~n'),
    format('  ![x]:                           - universal quantifier~n'),
    format('  ?[y]:                           - existential quantifier~n'),
    format(' ⚠ Note that FOL symbols are all lowercase.~n'),
    format('~nFormula syntax for prove/2 (nanoCoP internal):~n'),
    format('  (~~(p0 => p0))                   - falsum (translated from f)~n'),
    format('  (p0 => p0)                      - verum (translated from t)~n'),
    format('  (~~)                             - negation~n'),
    format('  (,)                             - conjunction~n'),
    format('  (;)                             - disjunction~n'),
    format('  (=>)                            - implication~n'),
    format('  (all X:)                        - universal quantifier~n'),
    format('  (ex X:)                         - existential quantifier~n'),
    format('~nImportant differences:~n'),
    format('  • decide/1 accepts TPTP syntax and translates automatically~n'),
    format('  • prove/2 requires nanoCoP internal syntax (no translation)~n'),
    format('  • Use translate_formula/2 to convert between syntaxes~n'),
    format('~nLogical constants:~n'),
    format('  f (bot/⊥): always false, contradiction~n'),
    format('  t (top/⊤): always true, tautology~n'),
    format('  Relation: t <=> ~~f (top iff not-bot)~n'),
    format('~nExamples with decide/1 (TPTP syntax):~n'),
    format('  decide(f).                      % Bot (should fail)~n'),
    format('  decide(t).                      % Top (should succeed)~n'),
    format('  decide(t <=> ~~f).               % Top iff not-bot~n'),
    format('  decide(f => p).                 % Ex falso quodlibet~n'),
    format('  decide(~~(t => f)).              % Top doesn''t imply bot~n'),
    format('  decide((p => f) | p).           % Excluded middle variant~n'),
    format('  decide(~~p | p).                % Law of excluded middle~n'),
    format('  decide(?[y]:(d(y) => ![x]:d(x))).~n'),
    format('  decide((p => q) | (q => p)).~n'),
    format('~nExamples with prove/2 (internal syntax):~n'),
    format('  translate_formula(f => p, X), prove(X, Proof).~n'),
    format('  prove((~~(p0 => p0) => p), Proof). % Direct internal syntax~n'),
    format('  translate_formula(t <=> ~~f, X), prove(X, Proof).~n'),
    format('~n').

% =========================================================================
% INITIALIZATION
% =========================================================================

:- format('nanoCoP Enhanced Interface loaded.~n').
:- format('Type help. for help.~n').
:- format('Type run_examples. to see examples.~n').
:- format('Type test_top_bot. to test top/bot.~n').
:- format('Type run_all_tests. to see all tests.~n').
