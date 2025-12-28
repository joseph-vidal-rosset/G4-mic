%% File: nanocop_countermodel.pl
%% Extension de nanoCop pour capturer les branches ouvertes (antiséquents)
%% Usage: prove_or_refute(F, Result) où Result = proof(P) ou countermodel(AntiSeq)

:- [nanocop20_swi].

:- dynamic(open_branch/3).  % open_branch(Path, Goal, Substitutions)

%% prove_or_refute(Formula, Result)
%% Result = proof(Proof) si prouvable
%% Result = countermodel(Antisequents) si réfutable
prove_or_refute(F, Result) :-
    retractall(open_branch(_,_,_)),
    ( prove_capture(F, Proof) ->
        Result = proof(Proof)
    ;
        findall(asq(Path, Goal), open_branch(Path, Goal, _), Branches),
        ( Branches = [] ->
            Result = unknown  % Timeout ou autre problème
        ;
            Result = countermodel(Branches)
        )
    ).

%% prove_capture - Version modifiée de prove qui capture les branches ouvertes
prove_capture(F, Proof) :-
    prove2_capture(F, [cut, comp(7)], Proof).

prove2_capture(F, Set, Proof) :-
    bmatrix(F, Set, Mat), 
    retractall(lit(_,_,_,_)),
    assert_matrix(Mat), 
    prove_capture_start(Mat, 1, Set, Proof).

% Start rule avec capture
prove_capture_start(Mat, PathLim, Set, [(I^0)^V:Cla1|Proof]) :-
    member((I^0)^V:Cla, Mat), 
    positiveC(Cla, Cla1),
    prove_with_capture(Cla1, Mat, [], [I^0], PathLim, [], Set, Proof).

prove_capture_start(Mat, PathLim, Set, Proof) :-
    retract(pathlim) ->
    ( member(comp(PathLim), Set) -> 
        prove_capture_start(Mat, 1, [], Proof) 
    ;
        PathLim1 is PathLim+1, 
        prove_capture_start(Mat, PathLim1, Set, Proof) 
    ) ;
    member(comp(_), Set) -> prove_capture_start(Mat, 1, [], Proof).

% Axiom
prove_with_capture([], _, _, _, _, _, _, []).

% Decomposition rule
prove_with_capture([J:Mat1|Cla], MI, Path, PI, PathLim, Lem, Set, Proof) :- 
    !,
    member(I^_:Cla1, Mat1),
    prove_with_capture(Cla1, MI, Path, [I,J|PI], PathLim, Lem, Set, Proof1),
    prove_with_capture(Cla, MI, Path, PI, PathLim, Lem, Set, Proof2),
    Proof = [J:I^V:Proof1|Proof2].

% Reduction and extension rules - AVEC CAPTURE
prove_with_capture([Lit|Cla], MI, Path, PI, PathLim, Lem, Set, Proof) :-
    Proof = [Lit, I^V:[NegLit|Proof1]|Proof2],
    \+ (member(LitC, [Lit|Cla]), member(LitP, Path), LitC==LitP),
    (-NegLit=Lit ; -Lit=NegLit) ->
       ( member(LitL, Lem), Lit==LitL, _ClaB1=[], Proof1=[], I=l, V=[]
         ;
         member(NegL, Path), unify_with_occurs_check(NegL, NegLit),
         _ClaB1=[], Proof1=[], I=r, V=[]
         ;
         % CAPTURE AVANT L'ÉCHEC
         ( lit(NegLit, ClaB, Cla1, Grnd1) ->
             ( Grnd1=g -> true 
             ; length(Path, K), K<PathLim -> true 
             ; \+ pathlim -> assert(pathlim), fail 
             ),
             prove_ec(ClaB, Cla1, MI, PI, I^V:ClaB1, MI1),
             prove_with_capture(ClaB1, MI1, [Lit|Path], [I|PI], PathLim, Lem, Set, Proof1)
         ;
             % BRANCHE OUVERTE : lit(NegLit, ...) a échoué
             capture_open_branch(Path, [Lit|Cla]),
             fail  % Continue à échouer pour le backtracking
         )
       ),
       ( member(cut, Set) -> ! ; true ),
       prove_with_capture(Cla, MI, Path, PI, PathLim, [Lit|Lem], Set, Proof2).

% Capturer une branche ouverte comme antiséquent
capture_open_branch(Path, Goal) :-
    copy_term((Path, Goal), (PathCopy, GoalCopy)),
    \+ open_branch(PathCopy, GoalCopy, _),  % Éviter les doublons
    assert(open_branch(PathCopy, GoalCopy, [])).

%% Affichage des antiséquents
print_countermodel(countermodel(Branches)) :-
    nl,
    write('═══════════════════════════════════════════'), nl,
    write('  FORMULA IS REFUTABLE'), nl,
    write('  Counter-model (Open Branches):'), nl,
    write('═══════════════════════════════════════════'), nl,
    print_branches(Branches, 1),
    nl.

print_branches([], _).
print_branches([asq(Path, Goal)|Rest], N) :-
    write('Branch '), write(N), write(': '),
    write(Path), write(' ⊬ '), write(Goal), nl,
    N1 is N+1,
    print_branches(Rest, N1).

%% Wrapper pratique
test(F) :-
    write('Testing: '), write(F), nl,
    prove_or_refute(F, Result),
    ( Result = proof(Proof) ->
        write('✓ PROVABLE'), nl,
        write('Proof: '), write(Proof), nl
    ; Result = countermodel(Branches) ->
        print_countermodel(Result)
    ; 
        write('? UNKNOWN'), nl
    ).

%% Exemples
test_invalid :-
    test((a=>b)).  % Invalide

test_valid :-
    test((p,(p=>q))=>q).  % Valide (modus ponens)

test_drinker :-
    test(ex Y:(d(Y) => all X:d(X))).  % Valide (drinker)

test_invalid_forall :-
    test((all X:p(X)) => p(a)).  % Invalide si domaine vide

%% Help
help :-
    nl,
    write('═══════════════════════════════════════════'), nl,
    write('  nanoCop + Countermodel Extraction'), nl,
    write('═══════════════════════════════════════════'), nl,
    nl,
    write('Main predicates:'), nl,
    write('  prove_or_refute(F, Result)'), nl,
    write('    Result = proof(P) or countermodel(Branches)'), nl,
    nl,
    write('  test(Formula) - test and print result'), nl,
    nl,
    write('Examples:'), nl,
    write('  ?- test_invalid.       % a=>b (refutable)'), nl,
    write('  ?- test_valid.         % modus ponens'), nl,
    write('  ?- test_drinker.       % drinker paradox'), nl,
    nl,
    write('  ?- test((a,b)=>a).'), nl,
    write('  ?- test((a=>b)).'), nl,
    nl.

:- initialization(help).
