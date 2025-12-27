%% nanocop_validator.pl - Standalone nanoCop validator
%% NO conflicts with g4mic - minimal interface

% Load only nanoCop core
:- catch([nanocop20_swi], _, catch([nanocop20], _, true)).

%% validate_nanocop(+Formula)
%% Ultra-simple: takes g4mic formula, translates to nanoCop, validates
validate_nanocop(Formula) :-
    % Translate and call nanoCop's prove2 directly
    translate_for_nanocop(Formula, NanoFormula),
    catch(
        time(prove2(NanoFormula, [cut,comp(7)], _Proof)),
        _,
        fail
    ).

%% translate_for_nanocop(+G4micFormula, -NanocopFormula)
%% Minimal translation: g4mic syntax → nanoCop syntax
translate_for_nanocop(F, F) :- 
    atomic(F), !.
translate_for_nanocop(F, F) :- 
    var(F), !.
translate_for_nanocop(~A, ~A1) :- 
    !, translate_for_nanocop(A, A1).
translate_for_nanocop(A | B, (A1 ; B1)) :- 
    !, translate_for_nanocop(A, A1), translate_for_nanocop(B, B1).
translate_for_nanocop(A & B, (A1 , B1)) :- 
    !, translate_for_nanocop(A, A1), translate_for_nanocop(B, B1).
translate_for_nanocop(A => B, (A1 => B1)) :- 
    !, translate_for_nanocop(A, A1), translate_for_nanocop(B, B1).
translate_for_nanocop(A <=> B, (A1 <=> B1)) :- 
    !, translate_for_nanocop(A, A1), translate_for_nanocop(B, B1).
translate_for_nanocop(![Var]:A, all Var:A1) :- 
    !, translate_for_nanocop(A, A1).
translate_for_nanocop(?[Var]:A, ex Var:A1) :- 
    !, translate_for_nanocop(A, A1).
translate_for_nanocop(Term, Term1) :-
    compound(Term),
    Term =.. [F|Args],
    maplist(translate_for_nanocop, Args, Args1),
    Term1 =.. [F|Args1].
translate_for_nanocop(Term, Term) :-
    (atomic(Term) ; var(Term)).

:- format('nanoCop validator loaded (standalone - no conflicts)~n').
