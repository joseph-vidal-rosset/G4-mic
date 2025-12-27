%  G4-mic:  Automated theorem prover for minimal, intuitionistic and classical logic
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
% MODULES
% =========================================================================
% CRITICAL: Enable occurs_check globally to prevent circular term structures
: - use_module(library(lists)).
:- use_module(library(statistics)).
:- use_module(library(terms)).
:- ['o_g4mic_operators'].
:- ['i_g4mic_prover_nanocop'].
:- ['ii_g4mic_sc-g4_printer'].
:- ['iii_g4mic_common_nd_printing'].
:- ['iv_g4mic_nd_flag_style_printer'].
:- ['v_g4mic_nd_tree_style_printer'].
:- ['vi_g4mic_latex_utilities'].
:- ['vii_g4mic_logic_level_detection'].
% =========================================================================
% STARTUP BANNER
% =========================================================================
:- set_prolog_flag(verbose, silent).
:- initialization(show_banner).

show_banner :-
    write('Welcome to SWI-Prolog (32 bits, version 9.3.34-20-g3517bc35f)'),nl,
    write('SWI-Prolog comes with ABSOLUTELY NO WARRANTY.  This is free software.'),nl,
    write('For legal details and online help, see https://www.swi-prolog.org'),nl,nl,
    write('*****************************************************************'), nl,
    write('*                   G4-mic F. O.L.  PROVER  -  1.0                *'), nl,
    write('*         (mic: minimal, intuitionistic and classical logic)    *'), nl,
    write('*         Based on Jens Otten\'s leanSeq v5 strategy            *'), nl,
    write('*****************************************************************'), nl,
    nl,
    write('Because g4mic_web. pl is a Prolog program: '),nl,
    write('never forget the dot at the end of each request!'),nl,nl,
    write('Usage: '),nl,
    write('  prove(Formula).  - proof in three styles, with shareable URLs'), nl,
    write('  decide(Formula). - concise mode '), nl,
    write('  help.             - show help'), nl,
    write('  examples.        - show examples'),nl.

% =========================================================================
% ITERATION LIMITS CONFIGURATION
% =========================================================================
logic_iteration_limit(constructive, 5).
logic_iteration_limit(classical, 7).
logic_iteration_limit(minimal, 4).
logic_iteration_limit(intuitionistic, 7).
logic_iteration_limit(fol, 10).

% =========================================================================
% UTILITY for/3
% =========================================================================
for(Threshold, M, N) :- M =< N, Threshold = M.
for(Threshold, M, N) :- M < N, M1 is M+1, for(Threshold, M1, N).

% =========================================================================
% DYNAMIC PREDICATES
% =========================================================================
:- dynamic current_proof_sequent/1.
:- dynamic premiss_list/1.
:- dynamic current_logic_level/1.

% =========================================================================
% CLASSICAL PATTERN DETECTION
% =========================================================================
normalize_formula(Formula, Normalized) :-
    normalize_double_negations(Formula, F1),
    normalize_biconditional_order(F1, Normalized).

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
normalize_double_negations(![X]: A, ![X]:NA) :- !,
    normalize_double_negations(A, NA).
normalize_double_negations(? [X]:A, ?[X]:NA) :- !,
    normalize_double_negations(A, NA).
normalize_double_negations(F, F).

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

is_fol_structural_pattern(((![_-_]:_ => _) => (? [_-_]:(_ => _)))) :- !.
is_fol_structural_pattern(? [_-_]:(_ => ![_-_]:_)) :- !.
is_fol_structural_pattern((![_-_]:(_ | _)) => (_ | ![_-_]:_)) :- !.
is_fol_structural_pattern((![_-_]:(_ | _)) => (![_-_]:_ | _)) :- !.
is_fol_structural_pattern((_) => ? [_-_]:(_ & ![_-_]:(_ | _))) :- !.

% =========================================================================
% MAIN INTERFACE:  prove/1
% =========================================================================

% Sequents with premises
prove(G > D) :-
    G \= [],
    !,
    validate_sequent_formulas(G, D),
    % Initialize occurs_check detection flag
    nb_setval(occurs_check_detected, false),
    statistics(runtime, [_T0|_]),
    write('------------------------------------------'), nl,
    write('G4 PROOF FOR SEQUENT: '),
    write_sequent_compact(G, D), nl,
    write('------------------------------------------'), nl,
    write('MODE:  Sequent '), nl,
    nl,
    retractall(premiss_list(_)),
    copy_term((G > D), (GCopy > DCopy)),
    prepare_sequent_formulas(GCopy, DCopy, PrepG, PrepD),
    assertz(premiss_list(PrepG)),
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent(G > D)),
    ( DCopy = [SingleGoal], is_classical_pattern(SingleGoal) ->
        write('=== CLASSICAL PATTERN DETECTED ==='), nl,
        write('    -> Using classical logic'), nl,
        time(provable_at_level(PrepG > PrepD, classical, Proof)),
        Logic = classical,
        OutputProof = Proof
    ;
        write('=== PHASE 1:  Trying Minimal -> Intuitionistic -> Classical ==='), nl,
        ( time(provable_at_level(PrepG > PrepD, minimal, Proof)) ->
            write('   Proof found in MINIMAL LOGIC'), nl,
            Logic = minimal,
            OutputProof = Proof
        ; time(provable_at_level(PrepG > PrepD, constructive, Proof)) ->
            write('   Constructive proof found'), nl,
            ( proof_uses_lbot(Proof) ->
                write('  -> Proof found in INTUITIONISTIC LOGIC'), nl,
                Logic = intuitionistic
            ;
                Logic = minimal
            ),
            OutputProof = Proof
        ;
            % Check if failure was due to occurs_check
            ((nb_current(occurs_check_detected, OccursFlag), OccursFlag == true) ->
                write('   Constructive logic failed (eigenvariable constraint violated)'), nl,
                nb_setval(occurs_check_detected, false)
            ;
                write('   Constructive logic failed'), nl
            ),
            write('=== TRYING CLASSICAL LOGIC ==='), nl,
            ( time(provable_at_level(PrepG > PrepD, classical, Proof)) ->
                !,
                (is_antisequent_proof(Proof) ->
                    ((nb_current(occurs_check_detected, OccursFlag), OccursFlag == true) ->
                        write('  Formula refuted (eigenvariable constraint violated - counter-model found)'), nl,
                        nb_setval(occurs_check_detected, false)
                    ;
                        write('  Formula refuted (counter-model found)'), nl
                    )
                ;
                    write('  Proof found in Classical logic'), nl
                ),
                Logic = classical,
                OutputProof = Proof
            ;
                % Classical logic also failed
                % (The eigenvariable violation message was already displayed in catch if applicable)
                fail
            )
        )
    ),
    output_proof_results(OutputProof, Logic, G > D, sequent).

% Biconditionals
prove(Left <=> Right) :- !,
    validate_and_warn(Left, _),
    validate_and_warn(Right, _),
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent(Left => Right)),
    ( catch(time((decide_silent(Left => Right, Proof1, Logic1))), _, fail) ->
        Direction1Valid = true,
        (is_antisequent_proof(Proof1) -> IsRefutation1 = true ; IsRefutation1 = false)
    ;
        Direction1Valid = false, Proof1 = none, Logic1 = none, IsRefutation1 = false
    ),
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent(Right => Left)),
    ( catch(time((decide_silent(Right => Left, Proof2, Logic2))), _, fail) ->
        Direction2Valid = true,
        (is_antisequent_proof(Proof2) -> IsRefutation2 = true ; IsRefutation2 = false)
    ;
        Direction2Valid = false, Proof2 = none, Logic2 = none, IsRefutation2 = false
    ),
    nl,
    write('=== BICONDITIONAL:  Proving both directions ==='), nl, nl,
    write('=== DIRECTION 1: '), write(Left => Right), write(' ==='), nl, nl,
    ( Direction1Valid = true ->
        ( IsRefutation1 = true ->
            write('REFUTED (counter-model found)'), nl, nl,
            write('- Sequent Calculus (Refutation) -'), nl, nl,
            write('\\begin{prooftree}'), nl,
            render_bussproofs(Proof1, 0, _),
            write('\\end{prooftree}'), nl, nl
        ;
            output_logic_label(Logic1), nl,
            write('    '), portray_clause(Proof1), nl, nl,
            write('- Sequent Calculus -'), nl, nl,
            write('\\begin{prooftree}'), nl,
            render_bussproofs(Proof1, 0, _),
            write('\\end{prooftree}'), nl, nl,
            write('Q.E.D.'), nl, nl,
            write('- Natural Deduction -'), nl,
            write('a) Tree Style: '), nl, nl,
            render_nd_tree_proof(Proof1), nl, nl,
            write('Q.E.D.'), nl, nl,
            write('b) Flag Style:'), nl, nl,
            write('\\begin{fitch}'), nl,
            g4_to_fitch_theorem(Proof1),
            write('\\end{fitch}'), nl, nl,
            write('Q.E.D.'), nl, nl
        )
    ; write('FAILED TO PROVE OR REFUTE'), nl, nl
    ),
    write('=== DIRECTION 2: '), write(Right => Left), write(' ==='), nl, nl,
    ( Direction2Valid = true ->
        ( IsRefutation2 = true ->
            write('REFUTED (counter-model found)'), nl, nl,
            write('- Sequent Calculus (Refutation) -'), nl, nl,
            write('\\begin{prooftree}'), nl,
            render_bussproofs(Proof2, 0, _),
            write('\\end{prooftree}'), nl, nl
        ;
            output_logic_label(Logic2), nl,
            write('    '), portray_clause(Proof2), nl, nl,
            write('- Sequent Calculus -'), nl, nl,
            write('\\begin{prooftree}'), nl,
            render_bussproofs(Proof2, 0, _),
            write('\\end{prooftree}'), nl, nl,
            write('Q.E.D.'), nl, nl,
            write('- Natural Deduction -'), nl,
            write('a) Tree Style:'), nl, nl,
            render_nd_tree_proof(Proof2), nl, nl,
            write('Q.E.D.'), nl, nl,
            write('b) Flag Style:'), nl, nl,
            write('\\begin{fitch}'), nl,
            g4_to_fitch_theorem(Proof2),
            write('\\end{fitch}'), nl, nl,
            write('Q.E.D. '), nl, nl
        )
    ; write('FAILED TO PROVE OR REFUTE'), nl, nl
    ),
    write('=== SUMMARY ==='), nl,
    write('- Direction 1 ('), write(Left => Right), write('): '),
    ( Direction1Valid = true ->
        ( IsRefutation1 = true -> write('INVALID (refuted)') ; write('VALID in '), write(Logic1), write(' logic') )
    ; write('FAILED')
    ), nl,
    write('- Direction 2 ('), write(Right => Left), write('): '),
    ( Direction2Valid = true ->
        ( IsRefutation2 = true -> write('INVALID (refuted)') ; write('VALID in '), write(Logic2), write(' logic') )
    ; write('FAILED')
    ), nl, nl, ! .

% Sequent equivalence:  [A] <> [B]
prove([Left] <> [Right]) :- !,
    validate_and_warn(Left, _),
    validate_and_warn(Right, _),
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Left] > [Right])),
    ( catch(time((prove_sequent_silent([Left] > [Right], Proof1, Logic1))), _, fail) ->
        Direction1Valid = true,
        (is_antisequent_proof(Proof1) -> IsRefutation1 = true ; IsRefutation1 = false)
    ;
        Direction1Valid = false, Proof1 = none, Logic1 = none, IsRefutation1 = false
    ),
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Right] > [Left])),
    ( catch(time((prove_sequent_silent([Right] > [Left], Proof2, Logic2))), _, fail) ->
        Direction2Valid = true,
        (is_antisequent_proof(Proof2) -> IsRefutation2 = true ; IsRefutation2 = false)
    ;
        Direction2Valid = false, Proof2 = none, Logic2 = none, IsRefutation2 = false
    ),
    nl,
    write('=== SEQUENT EQUIVALENCE:  Proving both directions ==='), nl, nl,
    write('=== DIRECTION 1: '), write(Left), write(' |- '), write(Right), write(' ==='), nl, nl,
    ( Direction1Valid = true ->
        ( IsRefutation1 = true ->
            write('REFUTED (counter-model found)'), nl, nl,
            write('- Sequent Calculus (Refutation) -'), nl, nl,
            write('\\begin{prooftree}'), nl,
            render_bussproofs(Proof1, 0, _),
            write('\\end{prooftree}'), nl, nl
        ;
            output_logic_label(Logic1), nl,
            write('    '), portray_clause(Proof1), nl, nl,
            write('- Sequent Calculus -'), nl, nl,
            write('\\begin{prooftree}'), nl,
            render_bussproofs(Proof1, 0, _),
            write('\\end{prooftree}'), nl, nl,
            write('Q.E.D. '), nl, nl,
            write('- Natural Deduction -'), nl,
            write('a) Tree Style:'), nl, nl,
            retractall(current_proof_sequent(_)),
            assertz(current_proof_sequent([Left] > [Right])),
            retractall(premiss_list(_)),
            assertz(premiss_list([Left])),
            render_nd_tree_proof(Proof1), nl, nl,
            write('Q.E.D.'), nl, nl,
            write('b) Flag Style:'), nl, nl,
            write('\\begin{fitch}'), nl,
            g4_to_fitch_sequent(Proof1, [Left] > [Right]),
            write('\\end{fitch}'), nl, nl,
            write('Q.E.D.'), nl, nl
        )
    ; write('FAILED TO PROVE OR REFUTE'), nl, nl
    ),
    write('=== DIRECTION 2: '), write(Right), write(' |- '), write(Left), write(' ==='), nl, nl,
    ( Direction2Valid = true ->
        ( IsRefutation2 = true ->
            write('REFUTED (counter-model found)'), nl, nl,
            write('- Sequent Calculus (Refutation) -'), nl, nl,
            write('\\begin{prooftree}'), nl,
            render_bussproofs(Proof2, 0, _),
            write('\\end{prooftree}'), nl, nl
        ;
            output_logic_label(Logic2), nl,
            write('    '), portray_clause(Proof2), nl, nl,
            write('- Sequent Calculus -'), nl, nl,
            write('\\begin{prooftree}'), nl,
            render_bussproofs(Proof2, 0, _),
            write('\\end{prooftree}'), nl, nl,
            write('Q.E.D.'), nl, nl,
            write('- Natural Deduction -'), nl,
            write('a) Tree Style:'), nl, nl,
            retractall(current_proof_sequent(_)),
            assertz(current_proof_sequent([Right] > [Left])),
            retractall(premiss_list(_)),
            assertz(premiss_list([Right])),
            render_nd_tree_proof(Proof2), nl, nl,
            write('Q.E.D.'), nl, nl,
            write('b) Flag Style:'), nl, nl,
            write('\\begin{fitch}'), nl,
            g4_to_fitch_sequent(Proof2, [Right] > [Left]),
            write('\\end{fitch}'), nl, nl,
            write('Q.E.D. '), nl, nl
        )
    ; write('FAILED TO PROVE OR REFUTE'), nl, nl
    ),
    write('=== SUMMARY ==='), nl,
    write('- Direction 1 ('), write(Left), write(' |- '), write(Right), write('): '),
    ( Direction1Valid = true ->
        ( IsRefutation1 = true -> write('INVALID (refuted)') ; write('VALID in '), write(Logic1), write(' logic') )
    ; write('FAILED')
    ), nl,
    write('- Direction 2 ('), write(Right), write(' |- '), write(Left), write('): '),
    ( Direction2Valid = true ->
        ( IsRefutation2 = true -> write('INVALID (refuted)') ; write('VALID in '), write(Logic2), write(' logic') )
    ; write('FAILED')
    ), nl, nl, !.

% Theorems
prove(Formula) :-
    validate_and_warn(Formula, _ValidatedFormula),
    % Initialize occurs_check detection flag
    nb_setval(occurs_check_detected, false),
    statistics(runtime, [_T0|_]),
    write('------------------------------------------'), nl,
    write('G4 PROOF FOR:  '), write(Formula), nl,
    write('------------------------------------------'), nl,
    write('MODE: Theorem'), nl,
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
                write('  Proof found in MINIMAL LOGIC'), nl,
                Logic = minimal,
                OutputProof = Proof
            ;
                ( proof_uses_lbot(Proof) ->
                    write('  Proof found in INTUITIONISTIC LOGIC'), nl,
                    Logic = intuitionistic,
                    OutputProof = Proof
                ;
                    Logic = minimal,
                    OutputProof = Proof
                )
            )
        ;
            write('   Constructive logic failed'), nl,
            write('=== FALLBACK:  CLASSICAL LOGIC ==='), nl,
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
                write('  -> Proof found in INTUITIONISTIC LOGIC'), nl,
                Logic = intuitionistic
            ;
                Logic = minimal
            ),
            OutputProof = Proof
        ;
            write('   Constructive logic failed'), nl,
            write('=== TRYING CLASSICAL LOGIC ==='), nl,
            time(provable_at_level([] > [F2], classical, Proof)),
            (is_antisequent_proof(Proof) ->
                write('  Formula refuted (counter-model found)'), nl
            ;
                write('  Proof found in Classical logic'), nl
            ),
            Logic = classical,
            OutputProof = Proof
        )
    ),
    output_proof_results(OutputProof, Logic, Formula, theorem).

% =========================================================================
% HELPERS
% =========================================================================
prepare_sequent_formulas(GIn, DIn, GOut, DOut) :-
    maplist(prepare_and_subst, GIn, GOut),
    maplist(prepare_and_subst, DIn, DOut).

prepare_and_subst(F, FOut) :-
    prepare(F, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1, FOut).

write_sequent_compact([], [D]) :- !, write(' |- '), write(D).
write_sequent_compact([G], [D]) :- !, write(G), write(' |- '), write(D).
write_sequent_compact(G, [D]) :-
    write_list_compact(G),
    write(' |- '),
    write(D).

write_list_compact([X]) :- !, write(X).
write_list_compact([X|Xs]) :- write(X), write(', '), write_list_compact(Xs).

validate_sequent_formulas(G, D) :-
    forall(member(Premiss, G), validate_and_warn(Premiss, _)),
    forall(member(Conclusion, D), validate_and_warn(Conclusion, _)).

% =========================================================================
% OUTPUT
% =========================================================================
output_proof_results(Proof, LogicType, OriginalFormula, Mode) :-
    (is_antisequent_proof(Proof) ->
        IsRefutation = true
    ;
        IsRefutation = false
    ),
    extract_formula_from_proof(Proof, Formula),
    detect_and_set_logic_level(Formula),
    retractall(current_logic_level(_)),
    assertz(current_logic_level(LogicType)),
    (IsRefutation = true ->
        write('G4+IP refutation in classical logic'), nl, nl
    ;
        output_logic_label(LogicType)
    ),
    nl, write('=== RAW PROLOG PROOF TERM ==='), nl,
    write('    '), portray_clause(Proof), nl, nl,
    ( catch(
          %    (copy_term(Proof, ProofCopy),
          (copy_term_nat(Proof, ProofCopy),
           numbervars(ProofCopy, 0, _),
           nl, nl),
          error(cyclic_term, _),
          (write('%% WARNING: Cannot represent proof term due to cyclic_term. '), nl, nl)
      ) -> true ; true ),
    write('- Sequent Calculus -'), nl, nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('Q.E.D.'), nl, nl,
    (IsRefutation = false ->
        write('- Natural Deduction -'), nl,
        write('a) Tree Style:'), nl, nl,
        render_nd_tree_proof(Proof), nl, nl,
        write('Q.E.D. '), nl, nl,
        write('b) Flag Style:'), nl, nl,
        write('\\begin{fitch}'), nl,
        ( Mode = sequent ->
            g4_to_fitch_sequent(Proof, OriginalFormula)
        ;
            g4_to_fitch_theorem(Proof)
        ),
        write('\\end{fitch}'), nl, nl,
        write('Q.E.D.'), nl, nl
    ;
        true
    ),
    !.

is_antisequent_proof(asq(Seq, _)) :-
    (Seq = (_ < _) ; Seq = (_ > _)), !.
is_antisequent_proof(Proof) :-
    compound(Proof),
    Proof =.. [Functor|Args],
    member(Functor, [ip, ltoto, lall, rcond, lex, rex, lor, rand,
                     lorto, land, l0cond, landto, tne, lex_lor, rall,
                     cq_c, cq_m, eq_refl, eq_sym, eq_trans, eq_trans_chain,
                     eq_cong, eq_subst_eq, eq_subst]),
    Args = [_Sequent|SubProofs],
    member(SubProof, SubProofs),
    is_antisequent_proof(SubProof).

% =========================================================================
% SILENT VERSIONS
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
% PROVABILITY AT A GIVEN LEVEL (leanSeq strategy - no init_eigenvars)
% =========================================================================
provable_at_level(Sequent, constructive, P) :-
    !,
    logic_iteration_limit(constructive, MaxIter),
    for(Threshold, 0, MaxIter),
    Sequent = (Gamma > Delta),
    catch(
        ( prove(Gamma > Delta, [], Threshold, 1, _, minimal, P) -> true
        ; prove(Gamma > Delta, [], Threshold, 1, _, intuitionistic, P)
        ),
        error(occurs_check(_,_), _),
        (   % DEBUG: show that occurs_check was caught
            % write('[DEBUG: occurs_check caught in constructive]'), nl,
            nb_setval(occurs_check_detected, true),
            fail
        )
    ),
    !.

provable_at_level(Sequent, LogicLevel, Proof) :-
    LogicLevel \= classical,
    logic_iteration_limit(LogicLevel, MaxIter),
    for(Threshold, 0, MaxIter),
    Sequent = (Gamma > Delta),
    catch(
        prove(Gamma > Delta, [], Threshold, 1, _, LogicLevel, Proof),
        error(occurs_check(_,_), _),
        (   % DEBUG: show that occurs_check was caught
            % write('[DEBUG: occurs_check caught in non-classical]'), nl,
            nb_setval(occurs_check_detected, true),
            fail
        )
    ),
    !.

provable_at_level(Sequent, classical, Proof) :-
    Sequent = (Gamma > Delta),
    logic_iteration_limit(classical, MaxIter),
    catch(
        (   for(Threshold, 0, MaxIter),
            prove(Gamma > Delta, [], Threshold, 1, _, classical, Proof)
        ->  true
        ;   nb_setval(asq_enabled, true),
            once((
                for(Threshold, 0, MaxIter),
                prove(Gamma > Delta, [], Threshold, 1, _, classical, Proof)
            )),
            nb_setval(asq_enabled, false)
        ),
        error(occurs_check(_,_), _),
        (   % Display informative message about eigenvariable constraint
            nl,
            write('══════════════════════════════════════════════════════'), nl,
            write('    FORMULA REFUTED: Eigenvariable Constraint Violation'), nl,
            write('══════════════════════════════════════════════════════'), nl,
            write('The formula cannot be proven: it would require circular'), nl,
            write('term structures, which would violate the eigenvariable'), nl,
            write('freshness condition.                                  '), nl,
            write('This indicates that the formula is logically INVALID.   '), nl,
            write('══════════════════════════════════════════════════════'), nl,
            nl,
            nb_setval(occurs_check_detected, true),
            fail
        )
    ),
    !.

% =========================================================================
% DISPLAY HELPERS
% =========================================================================
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

decide(Left <=> Right) :-
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

decide(G > D) :-
    G \= [], !,
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

decide([Left] <> [Right]) :- !,
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
    write('## MAIN COMMANDS'), nl,
    write('  prove(Formula).            - shows the proofs of Formula'), nl,
    write('  decide(Formula).           - says either true or false'), nl,
    write('## SYNTAX EXAMPLES'), nl,
    write('  THEOREMS:'), nl,
    write('    prove(p => p).                    - Identity'), nl,
    write('    prove((p & q) => p).              - Conjunction elimination'), nl,
    write('  SEQUENTS (syntax of G4 prover):'), nl,
    write('    prove([p] > [p]).                 - Sequent: P |- P'), nl,
    write('    prove([p, q] > [p & q]).          - Sequent: P, Q |- P & Q'), nl,
    write('    prove([p => q, p] > [q]).         - Modus Ponens in sequent form'), nl,
    write('  BICONDITIONALS:'), nl,
    write('    prove(p <=> ~ ~ p).                - Biconditional of Double Negation'), nl,
    write('    prove([p] <> [~ ~ p]).             - Bi-implication (sequents)'), nl,
    write('## COMMON MISTAKES'), nl,
    write('   [p] => [p]          - WRONG (use > for sequents)'), nl,
    write('   [p] > [p]           - CORRECT (sequent syntax)'), nl,
    write('   p > q               - WRONG (use => for conditional)'), nl,
    write('   p => q              - CORRECT (conditional)'), nl,
    write('   x <=> y in FOL      - WRONG (use = for equality)'), nl,
    write('   x = y in FOL        - CORRECT (equality)'), nl,
    write('## LOGICAL OPERATORS'), nl,
    write('  ~ A, (A & B), (A | B), (A => B), (A <=> B), #, ![x]: A, ? [x]:A').

examples :-
    nl,
    write('*****************************************************************'), nl,
    write('*                     EXAMPLES                                  *'), nl,
    write('*****************************************************************'), nl,
    nl,
    write('  % Identity theorem'), nl,
    write('  ? - prove(p => p).'), nl,
    write('  % Sequent with single premiss'), nl,
    write('  ?- prove([p] > [p]).'), nl,
    write('  % Sequent with multiple premisses'), nl,
    write('  ?- prove([p, q] > [p & q]).'), nl,
    write('  % Sequent:  modus ponens'), nl,
    write('  ?- prove([p => q, p] > [q]).'), nl,
    write('  % Law of Excluded Middle (classical)'), nl,
    write('  ?- prove(~ p | p).'), nl,
    write('  % Drinker Paradox (classical)'), nl,
    write('  ?- prove(? [y]:(d(y) => ![x]: d(x))).'), nl,
    nl.

% =========================================================================
% PREPROCESSING
% =========================================================================
subst_bicond(A <=> B, (A1 => B1) & (B1 => A1)) :-
    ! ,
    subst_bicond(A, A1),
    subst_bicond(B, B1).

subst_bicond(![Z-X]: A, ![Z-X]:A1) :-
        !,
        subst_bicond(A, A1).

subst_bicond(? [Z-X]:A, ? [Z-X]:A1) :-
        !,
        subst_bicond(A, A1).

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

subst_bicond(A, A).

subst_neg(~ ~A, ((A1 => #) => #)) :-
        !,
        subst_neg(A, A1).

subst_neg(~A, (A1 => #)) :-
        !,
        subst_neg(A, A1).

subst_neg(![Z-X]:A, ![Z-X]:A1) :-
        !,
        subst_neg(A, A1).

subst_neg(?[Z-X]:A, ?[Z-X]:A1) :-
        !,
        subst_neg(A, A1).

subst_neg(A & B, A1 & B1) :-
        !,
        subst_neg(A, A1),
        subst_neg(B, B1).

subst_neg(A | B, A1 | B1) :-
        !,
        subst_neg(A, A1),
        subst_neg(B, B1).

subst_neg(A => B, A1 => B1) :-
        !,
        subst_neg(A, A1),
        subst_neg(B, B1).

subst_neg(A <=> B, A1 <=> B1) :-
    !,
    subst_neg(A, A1),
    subst_neg(B, B1).

subst_neg(A, A).

% =========================================================================
% END OF DRIVER
% =========================================================================
