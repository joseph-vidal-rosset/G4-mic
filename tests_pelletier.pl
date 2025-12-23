% =========================================================================
% tests_pelletier.pl (mise à jour : Pel_18 corrigée en formule valide)
% Suite silencieuse Pelletier + benchmarks avec safe_time_out fallback.
% =========================================================================

:- module(tests_pelletier,
    [ run_pelletier/0,
      run_pelletier_named/1,
      pelletier_tests/1,
      set_pelletier_timeout/1,
      pelletier_timeout/1,
      known_invalid/1
    ]).

:- use_module(library(lists)).

% -------------------------------------------------------------------------
% Timeout configurable (en secondes). Valeur par défaut : 10 secondes.
% -------------------------------------------------------------------------
:- dynamic pelletier_timeout/1.
pelletier_timeout(10).

set_pelletier_timeout(Secs) :-
    ( number(Secs), Secs > 0 ->
        retractall(pelletier_timeout(_)),
        assertz(pelletier_timeout(Secs))
    ;
        throw(error(domain_error(positive_number, Secs), set_pelletier_timeout/1))
    ).

% -------------------------------------------------------------------------
% safe_time_out/3: wrapper robuste pour exécuter Goal avec timeout.
% - If time_out/3 exists, uses it.
% - Else if call_with_time_limit/2 exists, uses it.
% - Else runs goal without timeout.
% Result: success | failed | time_out | error(E)
% -------------------------------------------------------------------------
safe_time_out(Goal, Secs, Result) :-
    ( current_predicate(time_out/3) ->
        catch(time_out(Goal, Secs, R), E, (Result = error(E), !)),
        !,
        map_time_out_result(R, Result)
    ; current_predicate(call_with_time_limit/2) ->
        catch((call_with_time_limit(Secs, Goal), Result = success),
              time_limit_exceeded,
              ( Result = time_out )),
        !
    ;
        catch(( (call(Goal) -> Result = success ; Result = failed) ),
              E,
              ( Result = error(E) ))
    ).

map_time_out_result(time_out, time_out) :- !.
map_time_out_result(success, success) :- !.
map_time_out_result(failed, failed) :- !.
map_time_out_result(R, success) :- R \= time_out, R \= failed, R \= success, !.

% -------------------------------------------------------------------------
% Liste des tests (Name - Formula)
% Respecte la syntaxe du driver : predicats p,q,... ; constantes a,b,c,... ; vars v,w,x,y,z
% Quantificateurs: ![x]: et ?[x]: (sans espace)
% -------------------------------------------------------------------------
:- multifile pelletier_tests/1.
pelletier_tests([
    'Pel_01_drinker' - (?[x]:(p(x) => ![y]:(p(y)))),
    'Pel_02_dn_forall_exists' - ((~(![x]:p(x))) <=> (?[x]:(~p(x)))),
    'Pel_03_forall_inst' - ((![x]:p(x)) => p(a)),
    'Pel_04_forall_preserve_exist' - ((![x]:(p(x) => q(x))) => ((?[x]:p(x)) => ?[x]:q(x))),
    'Pel_05_exists_conj_split' - ((?[x]:(p(x) & q(x))) => (?[x]:p(x) & ?[x]:q(x))),
    'Pel_06_leibniz' - (((a = b) & p(a)) => p(b)),
    'Pel_07_eq_sym' - ((a = b) <=> (b = a)),
    'Pel_08_eq_trans' - (((a = b) & (b = c)) => (a = c)),
    'Pel_09_quantifier_swap_failure' - ((![x]:(?[y]:r(x,y))) => ?[y]:(![x]:r(x,y))),
    'Pel_10_exist_forall_exchange' - ((?[y]:(![x]:p(x,y))) => (![x]:(?[y]:p(x,y)))),
    'Pel_11_existential_elim_schema' - ((?[x]:p(x)) => ((![x]:(p(x) => q)) => q)),
    'Pel_12_univ_distrib_impl' - ((![x]:(p(x) => q)) <=> ((?[x]:p(x)) => q)),
    'Pel_13_contraposition_classical' - ((p => q) <=> (~q => ~p)),
    'Pel_14_material_implication' - (((~ p | q) <=> (p => q))),
    'Pel_15_hypothetical_syllogism' - (((p => q) & (q => r)) => (p => r)),
    'Pel_16_existential_preservation' - (((![x]:(p(x) => q(x))) & ?[x]:p(x)) => ?[x]:q(x)),
    'Pel_17_biimp_to_impls' - ((p <=> q) => ((p => q) & (q => p))),
    % Pel_18 corrected: ∃x (P(x) ∨ Q(x)) ≡ (∃x P(x)) ∨ (∃x Q(x))  (valid)
    'Pel_18_classical_choice' - ((?[x]:(p(x) | q(x))) <=> (?[x]:p(x) | ?[x]:q(x))),
    'Pel_19_pelletier_sample1' - ((![x]:(p(x) => ?[y]:q(x,y))) => ?[y]:(![x]:(p(x) => q(x,y)))),
    'Pel_20_pelletier_sample2' - ((?[x]:(p(x) => ![y]:(q(y) => r(x,y)))) => (![y]:(?[x]:(p(x) => r(x,y))))),
    'Extra_01_drinker_variant' - (?[x]:(p(x) => ![y]:(p(y) | q(y)))),
    'Extra_02_swapped' - ((?[x]:p(x) & ![x]:(p(x) => q)) => ?[x]:q(x)),
    'Extra_03_choice_like' - ((![x]:(p(x) => q(x)) & ?[x]:p(x)) => ?[x]:q(x)),
    'Extra_04_equality_leibniz_pred' - (((a = b) & r(a)) => r(b)),
    'Extra_05_mixed_quant' - ((?[x]:(![y]:r(x,y))) => (![y]:(?[x]:r(x,y)))),
    'Extra_06_double_negation' - ((~ ~ p) => p),
    'Extra_07_peirce_variant' - ((((p => q) => p) => p)),
    'Extra_08_explosion' - ((p & ~p) => #),
    'Extra_09_transfer' - ((![x]:(p(x) & q(x))) => (![x]:p(x) & ![x]:q(x))),
    'Extra_10_complex' - (((![x]:(p(x) => ?[y]:q(x,y))) & (?[x]:p(x))) => ?[y]:q(a,y))
]).

% -------------------------------------------------------------------------
% known_invalid/1: tests intentionally skipped (none for Pel_18 anymore)
% -------------------------------------------------------------------------
:- dynamic known_invalid/1.
% Example: known_invalid('Pel_XX').

% -------------------------------------------------------------------------
% Runner: run_pelletier/0
% -------------------------------------------------------------------------
run_pelletier :-
    pelletier_tests(Tests),
    writeln('=== PELLETIER / HARD FOL TEST SUITE (silent, timeout enabled) ==='),
    run_pelletier_list(Tests, 1, 0, 0, 0, Tot),
    Tot = [Total, Proven, Failed, Skipped],
    nl,
    format('Done: ~d tests. Proven: ~d. Failed: ~d. Skipped: ~d.~n', [Total, Proven, Failed, Skipped]),
    writeln('===============================================================').

run_pelletier_list([], _, Proved, Failed, Skipped, [Total,Proved,Failed,Skipped]) :-
    Total is Proved + Failed + Skipped.
run_pelletier_list([Name-Formula|Rest], N, PAcc, FAcc, SAcc, Tot) :-
    format('~n[~d] ~w : ', [N, Name]),
    ( known_invalid(Name) ->
        writeln('SKIPPED (INVALID)'),
        PAcc1 is PAcc, FAcc1 is FAcc, SAcc1 is SAcc + 1
    ;
        pelletier_timeout(TOSeconds),
        catch(
            ( safe_time_out((decide(Formula) -> Status = proved ; Status = not_proved), TOSeconds, Result),
              interpret_safe_result(Result, Status, Outcome)
            ),
            E,
            Outcome = error(E)
        ),
        report_outcome(Outcome),
        ( Outcome = proved -> PAcc1 is PAcc + 1 ; PAcc1 is PAcc ),
        ( Outcome = proved -> FAcc1 is FAcc ; FAcc1 is FAcc + 1 ),
        SAcc1 is SAcc
    ),
    N1 is N + 1,
    run_pelletier_list(Rest, N1, PAcc1, FAcc1, SAcc1, Tot).

interpret_safe_result(time_out, _Status, timeout) :- !.
interpret_safe_result(success, proved, proved) :- !.
interpret_safe_result(success, not_proved, not_proved) :- !.
interpret_safe_result(failed, _Status, not_proved) :- !.
interpret_safe_result(error(E), _Status, error(E)) :- !.
interpret_safe_result(_, Status, Outcome) :- ( Status == proved -> Outcome = proved ; Outcome = not_proved ).

report_outcome(proved) :- writeln('PROVED').
report_outcome(not_proved) :- writeln('NOT PROVED').
report_outcome(timeout) :- writeln('TIMEOUT').
report_outcome(error(E)) :- format('ERROR: ~w~n', [E]).

% -------------------------------------------------------------------------
% run single named test
% -------------------------------------------------------------------------
run_pelletier_named(Name) :-
    pelletier_tests(Tests),
    ( member(Name-Formula, Tests) ->
        ( known_invalid(Name) ->
            writeln('SKIPPED (INVALID)')
        ;
            pelletier_timeout(TOSeconds),
            format('Running test ~w with timeout ~w seconds...~n', [Name, TOSeconds]),
            catch(
                ( safe_time_out((decide(Formula) -> writeln('PROVED') ; writeln('NOT PROVED')), TOSeconds, Res),
                  ( Res == time_out -> writeln('TIMEOUT') ; true )
                ),
                E, format('ERROR: ~w~n', [E])
            )
        )
    ;
        format('Test ~w not found.~n', [Name])
    ).

% =========================================================================
% FIN
% =========================================================================
