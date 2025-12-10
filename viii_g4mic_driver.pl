% G4-mic: Automated theorem prover for minimal, intuitionistic and classical logic
% Copyright (C) 2025 Joseph Vidal-Rosset
%
% This program is free software: you can redistribute it and/or modify
% it under the terms of the GNU General Public License as published by
% the Free Software Foundation, either version 3 of the License, or
% (at your option) any later version.
%
% This program is distributed in the hope that it will be useful,
% but WITHOUT ANY WARRANTY; without even the implied warranty of
% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
% GNU General Public License for more details.
%
% You should have received a copy of the GNU General Public License
% along with this program.  If not, see <https://www.gnu.org/licenses/>.
% =========================================================================
% COMMON OPERATORS - Centralized module
% To include in all prover modules
% =========================================================================
:- use_module(library(lists)).
:- use_module(library(statistics)).
:- use_module(library(terms)).
:- ['o_g4mic_operators'].
:- ['i_g4mic_prover'].
:- ['ii_g4mic_sc-g4_printer'].
:- ['iii_g4mic_common_nd_printing'].
:- ['iv_g4mic_nd_flag_style_printer'].
:- ['v_g4mic_nd_tree_style_printer'].
:- ['vi_g4mic_latex_utilities'].
:- ['vii_g4mic_logic_level_detection'].
% =========================================================================
% STARTUP BANNER
 % =========================================================================
% Disable automatic SWI-Prolog banner
:- set_prolog_flag(verbose, silent).

%
:- initialization(show_banner).

show_banner :-
    write('Welcome to SWI-Prolog (32 bits, version 9.3.34-20-g3517bc35f)'),nl,
    write('SWI-Prolog comes with ABSOLUTELY NO WARRANTY. This is free software.'),nl,
    write('For legal details and online help, see https://www.swi-prolog.org'),nl,nl,

    write('*****************************************************************'), nl,
    write('*                   G4-mic F.O.L. PROVER  -  1.0                *'), nl,
    write('*         (mic: minimal, intuitionistic and classical logic)    *'), nl,
    write('*****************************************************************'), nl,
    nl,
    write('Because g4mic_web.pl is a Prolog program:'),nl,
    write('never forget the dot at the end of each request!'),nl,nl,
    write('Usage:'),nl,
    write('  prove(Formula).  - proof in three styles, with shareable URLs'), nl,
    write('  decide(Formula). - concise mode '), nl,
    write('  help.            - show help'), nl,
    write('  examples.        - show examples'),nl.
% =========================================================================
% ITERATION LIMITS CONFIGURATION
% =========================================================================

logic_iteration_limit(constructive, 3).
logic_iteration_limit(classical, 15).
logic_iteration_limit(minimal, 3).
logic_iteration_limit(intuitionistic, 5).
logic_iteration_limit(fol, 15).

% =========================================================================
% UTILITY for/3
% =========================================================================

for(Threshold, M, N) :- M =< N, Threshold = M.
for(Threshold, M, N) :- M < N, M1 is M+1, for(Threshold, M1, N).

% =========================================================================
% THEOREM vs SEQUENT DETECTION (simplified)
% =========================================================================

:- dynamic current_proof_sequent/1.
:- dynamic premiss_list/1.
:- dynamic current_logic_level/1.

% =========================================================================
% OPTIMIZED CLASSICAL PATTERN DETECTION
% =========================================================================

% normalize_formula/2: Apply efficiency-improving transformations
normalize_formula(Formula, Normalized) :-
    normalize_double_negations(Formula, F1),
    normalize_biconditional_order(F1, Normalized).

% normalize_double_negations/2: Simplify ~~A patterns in safe contexts
normalize_double_negations(((A => #) => #), A) :- 
    A \= (_ => #), !.
normalize_double_negations(A & B, NA & NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(A | B, NA | NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(A => B, NA => NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(A <=> B, NA <=> NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(![X]:A, ![X]:NA) :- !,
    normalize_double_negations(A, NA).
normalize_double_negations(?[X]:A, ?[X]:NA) :- !,
    normalize_double_negations(A, NA).
normalize_double_negations(F, F).

% normalize_biconditional_order/2: Order biconditionals by complexity
normalize_biconditional_order(A <=> B, B <=> A) :-
    formula_complexity(A, CA),
    formula_complexity(B, CB),
    CB < CA, !.
normalize_biconditional_order(A <=> B, NA <=> NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(A & B, NA & NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(A | B, NA | NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(A => B, NA => NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(![X]:A, ![X]:NA) :- !,
    normalize_biconditional_order(A, NA).
normalize_biconditional_order(?[X]:A, ?[X]:NA) :- !,
    normalize_biconditional_order(A, NA).
normalize_biconditional_order(F, F).

% formula_complexity/2: Heuristic complexity measure
formula_complexity((A => #), C) :- !, 
    formula_complexity(A, CA), 
    C is CA + 2.
formula_complexity(A => B, C) :- !, 
    formula_complexity(A, CA), 
    formula_complexity(B, CB), 
    C is CA + CB + 3.
formula_complexity(A & B, C) :- !, 
    formula_complexity(A, CA), 
    formula_complexity(B, CB), 
    C is CA + CB + 2.
formula_complexity(A | B, C) :- !, 
    formula_complexity(A, CA), 
    formula_complexity(B, CB), 
    C is CA + CB + 2.
formula_complexity(A <=> B, C) :- !, 
    formula_complexity(A, CA), 
    formula_complexity(B, CB), 
    C is CA + CB + 4.
formula_complexity(![_]:A, C) :- !, 
    formula_complexity(A, CA), 
    C is CA + 5.
formula_complexity(?[_]:A, C) :- !, 
    formula_complexity(A, CA), 
    C is CA + 5.
formula_complexity(_, 1).

% =========================================================================
% CLASSICAL PATTERN DETECTION (Core)
% =========================================================================

is_classical_pattern(Formula) :-
    (   is_fol_structural_pattern(Formula) ->
        !
    ;   contains_classical_pattern(Formula)
    ).

contains_classical_pattern(Formula) :-
    is_basic_classical_pattern(Formula), !.
contains_classical_pattern(Formula) :-
    binary_connective(Formula, Left, Right),
    (contains_classical_pattern(Left) ; contains_classical_pattern(Right)), !.
contains_classical_pattern(![_-_]:A) :-
    contains_classical_pattern(A), !.
contains_classical_pattern(?[_-_]:A) :-
    contains_classical_pattern(A), !.

binary_connective(A & B, A, B).
binary_connective(A | B, A, B).
binary_connective(A => B, A, B).
binary_connective(A <=> B, A, B).

% BASIC CLASSICAL PATTERNS
is_basic_classical_pattern(A | (A => #)) :- !.
is_basic_classical_pattern((A => #) | A) :- !.
is_basic_classical_pattern(((A => #) => #) => A) :- 
    A \= (_ => #), !.
is_basic_classical_pattern(((A => _B) => A) => A) :- !.
is_basic_classical_pattern((A => B) => ((A => #) | B)) :- !.
is_basic_classical_pattern((A => B) => (B | (A => #))) :- !.
is_basic_classical_pattern((A => B) | (B => A)) :- !.
is_basic_classical_pattern(((B => #) => (A => #)) => (A => B)) :- !.
is_basic_classical_pattern((A => B) => ((B => #) => (A => #))) :- !.
is_basic_classical_pattern(((A => B) => #) => (A & (B => #))) :- !.
is_basic_classical_pattern(((A & B) => #) => ((A => #) | (B => #))) :- !.
is_basic_classical_pattern((((A => #) => B) & (A => B)) => B) :- !.
is_basic_classical_pattern(((A => B) & ((A => #) => B)) => B) :- !.

% FOL STRUCTURAL PATTERNS
is_fol_structural_pattern(((![_-_]:_ => _) => (?[_-_]:(_ => _)))) :- !.
is_fol_structural_pattern(?[_-_]:(_ => ![_-_]:_)) :- !.
is_fol_structural_pattern((![_-_]:(_ | _)) => (_ | ![_-_]:_)) :- !.
is_fol_structural_pattern((![_-_]:(_ | _)) => (![_-_]:_ | _)) :- !.
is_fol_structural_pattern((_) => ?[_-_]:(_ & ![_-_]:(_ | _))) :- !.

% =========================================================================
% MAIN INTERFACE: prove/1
% =========================================================================

% NEW: Automatic detection for sequents with premisses
prove(G > D) :-
    G \= [],  % Non-empty premisses = SEQUENT
    !,
     %  VALIDATION: Verify premisses and conclusion
    validate_sequent_formulas(G, D),
    statistics(runtime, [_T0|_]),
    write('------------------------------------------'), nl,
    write('G4 PROOF FOR SEQUENT: '),
    write_sequent_compact(G, D), nl,
    write('------------------------------------------'), nl,
    write('MODE: Sequent '), nl,
    nl,
    
    % Store premisses for display
    retractall(premiss_list(_)),
    % Prepare formulas BEFORE storing premisses
    copy_term((G > D), (GCopy > DCopy)),
    prepare_sequent_formulas(GCopy, DCopy, PrepG, PrepD),
    % Store PREPARED premisses (with ~z transformed to z => #)
    assertz(premiss_list(PrepG)),
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent(G > D)),
    
    % Detect classical pattern in conclusion
    ( DCopy = [SingleGoal], is_classical_pattern(SingleGoal) ->
        write('=== CLASSICAL PATTERN DETECTED ==='), nl,
        write('    -> Using classical logic'), nl,
        time(provable_at_level(PrepG > PrepD, classical, Proof)),
        Logic = classical,
        OutputProof = Proof
    ;
        write('=== PHASE 1: Trying Minimal -> Intuitionistic -> Classical ==='), nl,
        ( time(provable_at_level(PrepG > PrepD, minimal, Proof)) ->
            write('   Constructive proof found in MINIMAL LOGIC '), nl,
            Logic = minimal,
            OutputProof = Proof
        ; time(provable_at_level(PrepG > PrepD, constructive, Proof)) ->
            write('   Constructive proof found'), nl,
            ( proof_uses_lbot(Proof) ->
                write('  Constructive proof found in INTUITIONISTIC LOGIC'), nl,
                Logic = intuitionistic
            ),
            OutputProof = Proof
        ;
            write('    Constructive logic failed'), nl,
            write('=== TRYING CLASSICAL LOGIC ==='), nl,
            time(provable_at_level(PrepG > PrepD, classical, Proof)),
            write('    Proof found in CLASSICAL LOGIC '), nl,
            Logic = classical,
            OutputProof = Proof
        )
    ),
    output_proof_results(OutputProof, Logic, G > D, sequent).

% Biconditionals - REGROUPES PAR TYPE
prove(Left <=> Right) :- !,
         % VALIDATION: Verify both directions
    validate_and_warn(Left, _),
    validate_and_warn(Right, _),
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent(Left => Right)),
    time((decide_silent(Left => Right, Proof1, Logic1))),
    
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent(Right => Left)),
    time((decide_silent(Right => Left, Proof2, Logic2))),
    
    nl,
    write('=== BICONDITIONAL: Proving both directions ==='), nl,nl,
    output_logic_label(Logic1), nl, nl,
    write('    '), portray_clause(Proof1), nl,nl,
    output_logic_label(Logic2), nl, nl,
    write('    '), portray_clause(Proof2), nl,nl,
    write('Q.E.D.'), nl, nl,
    
    % SEQUENT CALCULUS - BOTH DIRECTIONS
    write('- Sequent Calculus -'), nl, nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof1, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof2, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('Q.E.D.'), nl, nl,
    
    % TREE STYLE - BOTH DIRECTIONS
    write('- Natural Deduction -'), nl,
    write('a) Tree Style:'), nl, nl,
    render_nd_tree_proof(Proof1), nl, nl,
    render_nd_tree_proof(Proof2), nl, nl,
    write('Q.E.D.'), nl, nl,
    
    % TREE STYLE - BOTH DIRECTIONS
    write('b) Flag Style:'), nl, nl,
    write('\\begin{fitch}'), nl,
    g4_to_fitch_theorem(Proof1),
    write('\\end{fitch}'), nl, nl,
    write('\\begin{fitch}'), nl,
    g4_to_fitch_theorem(Proof2),
    write('\\end{fitch}'), nl, nl,
    write('Q.E.D.'), nl, nl,
    
    write('This biconditional is valid:'), nl,
    write('- Direction 1 ('), write(Left => Right), write(')'),  
    write(' is valid in '), write(Logic1), write(' logic'), nl,
    write('- Direction 2 ('), write(Right => Left), write(')'),
    write(' is valid in '), write(Logic2), write(' logic.'), nl,
    !.


% Sequent equivalence: [A] <> [B] proves [A] > [B] AND [B] > [A]
prove([Left] <> [Right]) :- !,
          % VALIDATION: Verify both formulas
    validate_and_warn(Left, _),
    validate_and_warn(Right, _),
    retractall(current_proof_sequent(_)),
    % Direction 1: Left > Right
    assertz(current_proof_sequent([Left] > [Right])),
    time((prove_sequent_silent([Left] > [Right], Proof1, Logic1))),   
    % Direction 2: Right > Left
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Right] > [Left])),
    time((prove_sequent_silent([Right] > [Left], Proof2, Logic2))),
    nl,
    write('=== SEQUENT EQUIVALENCE: Proving both directions ==='), nl,
    output_logic_label(Logic1), nl, nl,
    write('    '), portray_clause(Proof1), nl, nl,
    output_logic_label(Logic2), nl, nl,
    write('    '), portray_clause(Proof2), nl, nl,
     write('Q.E.D.'), nl, nl,
    
    % SEQUENT CALCULUS - BOTH DIRECTIONS
    write('- Sequent Calculus -'), nl, nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof1, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof2, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('Q.E.D.'), nl, nl,

    % TREE STYLE - BOTH DIRECTIONS
    write('- Natural Deduction -'), nl,
    write('a) Tree Style:'), nl, nl,
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Left] > [Right])),
    retractall(premiss_list(_)),
    assertz(premiss_list([Left])),
    render_nd_tree_proof(Proof1), nl, nl,
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Right] > [Left])),
    retractall(premiss_list(_)),
    assertz(premiss_list([Right])),
    render_nd_tree_proof(Proof2), nl, nl,
    write('Q.E.D.'), nl, nl,

    % FITCH STYLE - BOTH DIRECTIONS
    write('b) Flag Style:'), nl, nl,
    write('\\begin{fitch}'), nl,
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Left] > [Right])),
    retractall(premiss_list(_)),
    assertz(premiss_list([Left])),
    g4_to_fitch_sequent(Proof1, [Left] > [Right]),
    write('\\end{fitch}'), nl, nl,
    write('\\begin{fitch}'), nl,
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Right] > [Left])),
    retractall(premiss_list(_)),
    assertz(premiss_list([Right])),
    g4_to_fitch_sequent(Proof2, [Right] > [Left]),
    write('\\end{fitch}'), nl, nl,
    write('Q.E.D.'), nl, nl,
       
    write('This sequent equivalence is valid:'), nl,
    write('- Direction 1 ('), write(Left), write(' |- '), write(Right), write(')'),  
    write(' is valid in '), write(Logic1), write(' logic'), nl,
    write('- Direction 2 ('), write(Right), write(' |- '), write(Left), write(')'),
    write(' is valid in '), write(Logic2), write(' logic.'), nl,
    !.

% Theorems (original logic)
prove(Formula) :-
         % VALIDATION: Verify the formula
    validate_and_warn(Formula, _ValidatedFormula),
    statistics(runtime, [_T0|_]),
    write('------------------------------------------'), nl,
    write('G4 PROOF FOR: '), write(Formula), nl,
    write('------------------------------------------'), nl,  
    write('MODE: Theorem '), nl,
    nl,
    
    retractall(premiss_list(_)),
    retractall(current_proof_sequent(_)),
    
    copy_term(Formula, FormulaCopy),
    prepare(FormulaCopy, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1, F2),
    
    (   F2 = ((A => #) => #), A \= (_ => #)  ->
        write('=== DOUBLE NEGATION DETECTED ==='), nl,
        write('    -> Trying constructive first'), nl,
        write('=== TRYING CONSTRUCTIVE LOGIC ==='), nl,
        ( time(provable_at_level([] > [F2], constructive, Proof)) ->
            write('   Constructive proof found'), nl,
            ( time(provable_at_level([] > [F2], minimal, _)) ->
                write('  Constructive proof found in MINIMAL LOGIC'), nl,
                Logic = minimal,
                OutputProof = Proof
            ;
                ( proof_uses_lbot(Proof) ->
                    write('  Constructive proof found in INTUITIONISTIC LOGIC'), nl,
                    Logic = intuitionistic,
                    OutputProof = Proof
                )
            )
        ;
            write('    Constructive logic failed'), nl,
            write('=== FALLBACK: CLASSICAL LOGIC ==='), nl,
            time(provable_at_level([] > [F2], classical, Proof)),
            write('   Classical proof found'), nl,
            Logic = classical,
            OutputProof = Proof
        )
    ; is_classical_pattern(F2) ->
        write('=== CLASSICAL PATTERN DETECTED ==='), nl,
        write('    -> Skipping constructive logic'), nl,
        write('=== TRYING CLASSICAL LOGIC ==='), nl,
        time(provable_at_level([] > [F2], classical, Proof)),
        write('   Classical proof found'), nl,
        Logic = classical,
        OutputProof = Proof
    ;
        write('=== PHASE 1: Trying Minimal -> Intuitionistic -> Classical ==='), nl,
        ( time(provable_at_level([] > [F2], minimal, Proof)) ->
            write('   Proof found in MINIMAL LOGIC'), nl,
            Logic = minimal,
            OutputProof = Proof
        ; time(provable_at_level([] > [F2], constructive, Proof)) ->
            write('   Constructive proof found'), nl,
            ( proof_uses_lbot(Proof) ->
                write('  -> Uses explosion explosion rule - Proof found in INTUITIONISTIC LOGIC'), nl,
                Logic = intuitionistic,
                OutputProof = Proof
            ;
                write('  -> No explosion -> INTUITIONISTIC'), nl,
                Logic = intuitionistic,
                OutputProof = Proof
            )
        ;
            write('   Constructive logic failed'), nl,
            write('=== TRYING CLASSICAL LOGIC ==='), nl,
            time(provable_at_level([] > [F2], classical, Proof)),
            write('  Proof found in Classical logic'), nl,
            Logic = classical,
            OutputProof = Proof
        )
    ),
    output_proof_results(OutputProof, Logic, Formula, theorem).

% =========================================================================
% HELPERS
% =========================================================================

% Prepare a list of formulas
prepare_sequent_formulas(GIn, DIn, GOut, DOut) :-
    maplist(prepare_and_subst, GIn, GOut),
    maplist(prepare_and_subst, DIn, DOut).

prepare_and_subst(F, FOut) :-
    prepare(F, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1, FOut).

% Compact display of a sequent
write_sequent_compact([], [D]) :- !, write(' |- '), write(D).
write_sequent_compact([G], [D]) :- !, write(G), write(' |- '), write(D).
write_sequent_compact(G, [D]) :-
    write_list_compact(G),
    write(' |- '),
    write(D).

write_list_compact([X]) :- !, write(X).
write_list_compact([X|Xs]) :- write(X), write(', '), write_list_compact(Xs).

% =========================================================================
% FORMULA AND SEQUENT VALIDATION
% =========================================================================

% Validate a sequent (premisses + conclusions)
validate_sequent_formulas(G, D) :-
    % Validate all premisses
    forall(member(Premiss, G), validate_and_warn(Premiss, _)),
    % Validate all conclusions
    forall(member(Conclusion, D), validate_and_warn(Conclusion, _)).

% =========================================================================
% OUTPUT WITH MODE DETECTION
% =========================================================================

output_proof_results(Proof, LogicType, OriginalFormula, Mode) :-
    extract_formula_from_proof(Proof, Formula),
    detect_and_set_logic_level(Formula),
    % Store logic level for use in proof rendering (e.g., DS optimization)
    retractall(current_logic_level(_)),
    assertz(current_logic_level(LogicType)),
    output_logic_label(LogicType),
    % ADDED: Display raw Prolog proof term
    nl, write('=== RAW PROLOG PROOF TERM ==='), nl,
    write('    '), portray_clause(Proof), nl, nl,
    ( catch(
          (copy_term(Proof, ProofCopy),
           numbervars(ProofCopy, 0, _),
           nl, nl),
          error(cyclic_term, _),
          (write('%% WARNING: Cannot represent proof term due to cyclic_term.'), nl, nl)
      ) -> true ; true ),
    write('- Sequent Calculus -'), nl, nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('Q.E.D.'), nl, nl,
    write('- Natural Deduction -'), nl,
    write('a) Tree Style:'), nl, nl,
    render_nd_tree_proof(Proof), nl, nl,
    write('Q.E.D.'), nl, nl,
    write('b) Flag Style:'), nl, nl,
    write('\\begin{fitch}'), nl,
    ( Mode = sequent ->
        g4_to_fitch_sequent(Proof, OriginalFormula)
    ;
        g4_to_fitch_theorem(Proof)
    ),
    write('\\end{fitch}'), nl, nl,
    write('Q.E.D.'), nl, nl,
    !.

% =========================================================================
% SILENT VERSIONS (for internal use)
% =========================================================================

decide_silent(Formula, Proof, Logic) :-
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent(Formula)),
    
    copy_term(Formula, FormulaCopy),
    prepare(FormulaCopy, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1, F2),
    progressive_proof_silent(F2, Proof, Logic).

progressive_proof_silent(Formula, Proof, Logic) :-
    ( provable_at_level([] > [Formula], minimal, Proof) ->
        Logic = minimal
    ; provable_at_level([] > [Formula], intuitionistic, Proof) ->
        Logic = intuitionistic
    ; provable_at_level([] > [Formula], classical, Proof) ->
        Logic = classical
    ).

% =========================================================================
% PROVABILITY AT A GIVEN LEVEL
% =========================================================================

provable_at_level(Sequent, constructive, P) :-
    !,
    logic_iteration_limit(constructive, MaxIter),
    for(Threshold, 0, MaxIter),
    Sequent = (Gamma > Delta),
    init_eigenvars,  % Initialize before each attempt
    ( prove(Gamma > Delta, [], Threshold, 1, _, minimal, P) -> true    % <- Essayer minimal d'abord
    ; init_eigenvars, prove(Gamma > Delta, [], Threshold, 1, _, intuitionistic, P)     % <- Then intuitionistic if failure
    ),
    !.

provable_at_level(Sequent, LogicLevel, Proof) :-
    logic_iteration_limit(LogicLevel, MaxIter),
    for(Threshold, 0, MaxIter),
    Sequent = (Gamma > Delta),
    init_eigenvars,  % Initialize before each attempt
    prove(Gamma > Delta, [], Threshold, 1, _, LogicLevel, Proof),
    !.

% =========================================================================
% DISPLAY HELPERS
% =========================================================================

% Helper: prove sequent silently (for <> operator)
prove_sequent_silent(Sequent, Proof, Logic) :-
    Sequent = (Gamma > Delta),
    prepare_sequent_formulas(Gamma, Delta, PrepGamma, PrepDelta),
    ( member(SingleGoal, PrepDelta), is_classical_pattern(SingleGoal) ->
        provable_at_level(PrepGamma > PrepDelta, classical, Proof),
        Logic = classical
    ; provable_at_level(PrepGamma > PrepDelta, minimal, Proof) ->
        Logic = minimal
    ; provable_at_level(PrepGamma > PrepDelta, intuitionistic, Proof) ->
        Logic = intuitionistic
    ;
        provable_at_level(PrepGamma > PrepDelta, classical, Proof),
        Logic = classical
    ).

output_logic_label(minimal) :- 
    write('G4 proofs in minimal logic'), nl, nl.
output_logic_label(intuitionistic) :- 
    write('G4 proofs in intuitionistic logic'), nl, nl.
output_logic_label(classical) :- 
    write('G4+IP proofs in classical logic'), nl, nl.

proof_uses_lbot(lbot(_,_)) :- !.
proof_uses_lbot(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    proof_uses_lbot(Arg).
% =========================================================================
% MINIMAL INTERFACE decide/1
% =========================================================================

decide(Left <=> Right) :- !,
    % VALIDATION
    validate_and_warn(Left, _),
    validate_and_warn(Right, _),
    time((
        decide_silent(Left => Right, _, Logic1),
        decide_silent(Right => Left, _, Logic2)
    )),
    write('Direction 1 ('), write(Left => Right), write(') is valid in '), 
    write(Logic1), write(' logic'), nl,
    write('Direction 2 ('), write(Right => Left), write(') is valid in '), 
    write(Logic2), write(' logic'), nl,
    !.

decide(Formula) :-
    copy_term(Formula, FormulaCopy),
    prepare(FormulaCopy, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1,F2),
    ( is_classical_pattern(F2) ->
        time(provable_at_level([] > [F2], classical, _)),
        write('Valid in classical logic'), nl
    ;
        time(progressive_proof_silent(F2, _, Logic)),
        write('Valid in '), write(Logic), write(' logic'), nl
    ),
    !.

% decide/1 for sequents
decide(G > D) :-
    G \= [], !,
    % VALIDATION
    validate_sequent_formulas(G, D),
    copy_term((G > D), (GCopy > DCopy)),
    prepare_sequent_formulas(GCopy, DCopy, PrepG, PrepD),
    
    ( DCopy = [SingleGoal], is_classical_pattern(SingleGoal) ->
        time(provable_at_level(PrepG > PrepD, classical, _)),
        write('Valid in classical logic'), nl
    ; time(provable_at_level(PrepG > PrepD, minimal, _)) ->
        write('Valid in minimal logic'), nl
    ; time(provable_at_level(PrepG > PrepD, constructive, Proof)) ->
        ( proof_uses_lbot(Proof) -> 
            write('Valid in intuitionistic logic'), nl
        ; 
            write('Valid in intuitionistic logic'), nl
        )
    ;
        time(provable_at_level(PrepG > PrepD, classical, _)),
        write('Valid in classical logic'), nl
    ),
    !.

% Equivalence for decide
decide([Left] <> [Right]) :- !,
    % VALIDATION
    validate_and_warn(Left, _),
    validate_and_warn(Right, _),
    time((
        prove_sequent_silent([Left] > [Right], _, Logic1),
        prove_sequent_silent([Right] > [Left], _, Logic2)
    )),
    write('Direction 1 ('), write(Left), write(' |- '), write(Right), write(') is valid in '), 
    write(Logic1), write(' logic'), nl,
    write('Direction 2 ('), write(Right), write(' |- '), write(Left), write(') is valid in '), 
    write(Logic2), write(' logic'), nl,
    !.

% =========================================================================
% HELP SYSTEM
% =========================================================================

help :-
    nl,
    write('*****************************************************************'), nl,
    write('*                      G4 PROVER GUIDE                          *'), nl,
    write('*****************************************************************'), nl,
    write('## MAIN COMMANDS '), nl,
    write('  prove(Formula).            - shows the proofs of Formula'), nl,
    write('  decide(Formula).           - says either true or false'), nl,
    write('## SYNTAX EXAMPLES '), nl,
    write('  THEOREMS:'), nl,
    write('    prove(p => p).                    - Identity'), nl,
    write('    prove((p & q) => p).              - Conjunction elimination'), nl,
    write('  SEQUENTS (syntax of G4 prover):'), nl,
    write('    prove([p] > [p]).                 - Sequent: P |- P '), nl,
    write('    prove([p, q] > [p & q]).          - Sequent: P , Q |- P & Q '), nl,
    write('    prove([p => q, p] > [q]).         - Modus Ponens in sequent form'), nl,
    write('  BICONDITIONALS:'), nl,
    write('    prove(p <=> ~ ~ p).                - Biconditional of Double Negation '), nl,
    write('    prove(p <> ~ ~ p).                 - Bi-implication of Double Negation (sequents)'), nl,
    write('## COMMON MISTAKES '), nl,
    write('   [p] => [p]          - WRONG (use > for sequents)'), nl,
    write('   [p] > [p]           - CORRECT (sequent syntax)'), nl,
    write('   p > q               - WRONG (use => for conditional)'), nl,
    write('   p => q              - CORRECT (conditional)'), nl,
    write('   x <=> y in FOL      - WRONG (use = for equality)'), nl,
    write('   x = y in FOL        - CORRECT (equality)'), nl,
    write('## LOGICAL OPERATORS '), nl,
    write('  ~ A , (A & B) , (A | B) , (A => B) , (A <=> B) ,  # , ![x]:A ,  ?[x]:A').

examples :-
    nl,
    write('*****************************************************************'), nl,
    write('*                     EXAMPLES                                  *'), nl,
    write('*****************************************************************'), nl,
    nl,
    write('  % Identity theorem'), nl,
    write('  ?- prove(p => p).'), nl,
    write('  % Sequent with single premiss'), nl,
    write('  ?- prove([p] > [p]).'), nl,
    write('  % Sequent with multiple premisses'), nl,
    write('  ?- prove([p, q] > [p & q]).'), nl,
    write('  % Sequent: modus ponens'), nl,
    write('  ?- prove([p => q, p] > [q]).'), nl,
    write('  % Law of Excluded Middle (classical)'), nl,
    write('  ?- prove(~ p | p).'), nl,
    write('  % Drinker Paradox (classical)'), nl,
    write('  ?- prove(?[y]:(d(y) => ![x]:d(x))).'), nl,
    nl.
% =========================================================================
% TRADUCTION DU BICONDITIONNELLE INTERNE
% A <=> B devient (A => B) & (B => A)
% =========================================================================

subst_bicond(A <=> B, (A1 => B1) & (B1 => A1)) :-
    !,
    subst_bicond(A, A1),
    subst_bicond(B, B1).

% Quantifiers: pass recursively into the body
subst_bicond(![Z-X]:A, ![Z-X]:A1) :-
        !,
        subst_bicond(A, A1).

subst_bicond(?[Z-X]:A, ?[Z-X]:A1) :-
        !,
        subst_bicond(A, A1).

% Propositional connectives
subst_bicond(A & B, A1 & B1) :-
        !,
        subst_bicond(A, A1),
        subst_bicond(B, B1).

subst_bicond(A | B, A1 | B1) :-
        !,
        subst_bicond(A, A1),
        subst_bicond(B, B1).

subst_bicond(A => B, A1 => B1) :-
        !,
        subst_bicond(A, A1),
        subst_bicond(B, B1).

subst_bicond(~A, ~A1) :-
        !,
        subst_bicond(A, A1).

% Base case: atomic formulas
subst_bicond(A, A).

% =========================================================================
% NEGATION SUBSTITUTION (preprocessing)
% =========================================================================
% Double negation
subst_neg(~ ~A, ((A1 => #) => #)) :-
        !,
        subst_neg(A, A1).

% Negation simple
subst_neg(~A, (A1 => #)) :-
        !,
        subst_neg(A, A1).


subst_neg(![Z-X]:A, ![Z-X]:A1) :-
        !,
        subst_neg(A, A1).

subst_neg(?[Z-X]:A, ?[Z-X]:A1) :-
        !,
        subst_neg(A, A1).

% Conjonction
subst_neg(A & B, A1 & B1) :-
        !,
        subst_neg(A, A1),
        subst_neg(B, B1).

% Disjonction
subst_neg(A | B, A1 | B1) :-
        !,
        subst_neg(A, A1),
        subst_neg(B, B1).

% Implication
subst_neg(A => B, A1 => B1) :-
        !,
        subst_neg(A, A1),
        subst_neg(B, B1).

% Biconditional
subst_neg(A <=> B, A1 <=> B1) :-
    !,
    subst_neg(A, A1),
    subst_neg(B, B1).

% Bacis case
subst_neg(A, A).
%=================================
% END OF DRIVER
%=================================
