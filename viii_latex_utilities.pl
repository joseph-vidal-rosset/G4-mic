% =======================
% Fitch section
% ========================

% =========================================================================
% RENDERING PRIMITIVES
% =========================================================================

% render_hypo/7: Affiche une hypothese en Fitch style

render_hypo(Scope, Formula, Label, _CurLine, _NextLine, VarIn, VarOut) :-
    render_fitch_indent(Scope),
    write(' \\fh '),
    rewrite(Formula, VarIn, VarOut, LatexFormula),
    write_formula_with_parens(LatexFormula),
    write(' &  '),
    write(Label),
    write('\\\\'), nl.


% render_fitch_indent/1: Genere l'indentation Fitch (\\fa)

render_fitch_indent(0) :- !.

render_fitch_indent(N) :- 
    N > 0,
    write('\\fa '),
    N1 is N - 1,
    render_fitch_indent(N1).

render_have(Scope, Formula, Just, _CurLine, _NextLine, VarIn, VarOut) :-
    render_fitch_indent(Scope),
    % Toujours ecrire \fa au niveau 0 (pour les sequents)
    ( Scope = 0 -> write('\\fa ') ; true ),
    rewrite(Formula, VarIn, VarOut, LatexFormula),
    write_formula_with_parens(LatexFormula),
    write(' &  '),
    write(Just),
    write('\\\\'), nl.
 
render_lineno(J, K) :-
   K is J+1.

render_bars(0) :- !.
render_bars(N) :-
    write('\\fa  '),
    M is N-1,
    render_bars(M).

render_label(L) :-
    L =.. ['$ \\lor E $', DisjLine, Case1, Case2],
    Case1 = (Start1-End1),
    Case2 = (Start2-End2),
    !,
    write(' & '),
    format(' $ \\lor E $ ~w,~w-~w,~w-~w', [DisjLine, Start1, End1, Start2, End2]),
    write('\\'), write('\\\n').

render_label(L) :-
    L =.. [F,X,Y],
    !,
    write(' &  '),
    write(' '),
    write(F),
    write(' '),
    write(X),
    write(', '),
    write(Y),
    write('\\'), write('\\\n').

render_label(L) :-
    L =.. [F,X],
    !,
    write(' & '),
    write(' '),
    write(F),
    write(' '),
    write(X),
    write('\\'), write('\\\n').

render_label(L) :-
    !,
    write(' & '),
    write(' '),
    write(L),
    write('\\'), write('\\\n').

% =========================================================================
% REGLE SIMPLE : (Antecedent) => (Consequent) sauf pour les atomes
% =========================================================================

% Test si une formule est atomique
is_atomic_formula(Formula) :-
    atomic(Formula).

% -------------------------------------------------------------------------
% NOUVEAU : Test si une formule est une negation (au sens de l'affichage LaTeX)
% Une formule negative est representee comme (' \\lnot ' X) par rewrite/4.
% Nous voulons considerer toute formule commencant par ' \\lnot ' comme
% "non-parenthesable" - i.e. ne PAS entourer par des parentheses externe.
% -------------------------------------------------------------------------
is_negative_formula((' \\lnot ' _)) :- !.

% Helper: treat negative formulas as "atomic-like" for parentheses suppression
is_atomic_or_negative_formula(F) :-
    is_atomic_formula(F) ;
    is_negative_formula(F).

% =========================================================================
% TEST SI LE CORPS D'UN QUANTIFICATEUR NECESSITE PARENTHESES
% =========================================================================

quantifier_body_needs_parens((_ ' \\to ' _)) :- !.
quantifier_body_needs_parens((_ ' \\land ' _)) :- !.
quantifier_body_needs_parens((_ ' \\lor ' _)) :- !.
quantifier_body_needs_parens((_ ' \\leftrightarrow ' _)) :- !.
quantifier_body_needs_parens(_) :- fail.


quantifier_body_needs_parens(Body) :-
    (Body = (_ ' \\to ' _)
    ; Body = (_ ' \\land ' _) 
    ; Body = (_ ' \\lor ' _)
    ; Body = (_ ' \\leftrightarrow ' _)
    ).
% =========================================================================
% TOUTES LES CLAUSES DE write_formula_with_parens/1 GROUPEES
% =========================================================================

% Ecriture d'une implication avec parentheses intelligentes
write_formula_with_parens((A ' \\to ' B)) :-
    !,
    write_implication_with_parens(A, B).

write_formula_with_parens('='(A, B)) :- !,
    write('('), write_formula_with_parens(A), write(' = '), write_formula_with_parens(B), write(')').

% Autres operateurs
write_formula_with_parens((A ' \\lor ' B)) :-
    !,
    write_with_context(A, 'lor_left'),
    write(' \\lor '),
    write_with_context(B, 'lor_right').

write_formula_with_parens((A ' \\land ' B)) :-
    !,
    write_with_context(A, 'land_left'),
    write(' \\land '),
    write_with_context(B, 'land_right').

write_formula_with_parens((A ' \\leftrightarrow ' B)) :-
    !,
    write_with_context(A, 'equiv_left'),
    write(' \\leftrightarrow '),
    write_with_context(B, 'equiv_right').

write_formula_with_parens((' \\lnot ' A)) :-
    !,
    write(' \\lnot '),
    write_with_context(A, 'not').

% QUANTIFICATEURS AVEC PARENTHESES INTELLIGENTES
write_formula_with_parens((' \\forall ' X ' ' A)) :-
    !,
    write(' \\forall '),
    write(X),
    write(' '),
    ( quantifier_body_needs_parens(A) ->
        write('('),
        write_formula_with_parens(A),
        write(')')
    ;   write_formula_with_parens(A)
    ).

write_formula_with_parens((' \\exists ' X ' ' A)) :-
    !,
    write(' \\exists '),
    write(X),
    write(' '),
    ( quantifier_body_needs_parens(A) ->
        write('('),
        write_formula_with_parens(A),
        write(')')
    ;   write_formula_with_parens(A)
    ).

write_formula_with_parens(Other) :-
    write(Other).

% =========================================================================
% FONCTION SPECIALISEE POUR IMPLICATIONS
% =========================================================================

write_implication_with_parens(Antecedent, Consequent) :-
    % Antecedent : ne pas parentheser s'il est atomique OU une formule negative
    ( is_atomic_or_negative_formula(Antecedent) ->
        write_formula_with_parens(Antecedent)
    ;
        write('('),
        write_formula_with_parens(Antecedent),
        write(')')
    ),
    write(' \\to '),
    % Consequent : parentheser sauf si atomique OU formule negative
    % NOTE: on considere toute forme (' \\lnot ' _) comme "negative" meme si
    % elle contient plusieurs negations imbriquees (!!!A). Dans ce cas on ne
    % met JAMAIS de parentheses externes autour de la negation.
    ( is_atomic_or_negative_formula(Consequent) ->
        write_formula_with_parens(Consequent)
    ;
        write('('),
        write_formula_with_parens(Consequent),
        write(')')
    ).

% =========================================================================
% TOUTES LES CLAUSES DE write_with_context/2 GROUPEES
% =========================================================================

% IMPLICATIONS dans tous les contextes - utiliser write_implication_with_parens
write_with_context((A ' \\to ' B), 'lor_left') :-
    !,
    write('('),
    write_implication_with_parens(A, B),
    write(')').

write_with_context((A ' \\to ' B), 'lor_right') :-
    !,
    write('('),
    write_implication_with_parens(A, B),
    write(')').

write_with_context((A ' \\to ' B), 'land_left') :-
    !,
    write('('),
    write_implication_with_parens(A, B),
    write(')').

write_with_context((A ' \\to ' B), 'land_right') :-
    !,
    write('('),
    write_implication_with_parens(A, B),
    write(')').

write_with_context((A ' \\to ' B), 'not') :-
    !,
    write('('),
    write_implication_with_parens(A, B),
    write(')').

% CONJONCTIONS dans disjonctions
write_with_context((A ' \\land ' B), 'lor_left') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\land '),
    write_formula_with_parens(B),
    write(')').

write_with_context((A ' \\land ' B), 'lor_right') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\land '),
    write_formula_with_parens(B),
    write(')').

% CONJONCTIONS dans negations
write_with_context((A ' \\land ' B), 'not') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\land '),
    write_formula_with_parens(B),
    write(')').

% DISJONCTIONS dans negations
write_with_context((A ' \\lor ' B), 'not') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\lor '),
    write_formula_with_parens(B),
    write(')').

% DISJONCTIONS dans conjonctions
write_with_context((A ' \\lor ' B), 'land_left') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\lor '),
    write_formula_with_parens(B),
    write(')').

write_with_context((A ' \\lor ' B), 'land_right') :-
    !,
    write('('),
    write_formula_with_parens(A),
    write(' \\lor '),
    write_formula_with_parens(B),
    write(')').

% CLAUSE DE FALLBACK
write_with_context(Formula, _Context) :-
    write_formula_with_parens(Formula).

% =========================================================================
% SYSTEME BURSE adapte : rewrite direct sur formules avec operateurs standard
% VERSION AVEC SIMPLIFICATION ELEGANTE DES PREDICATS
% =========================================================================

% rewrite/4 - Version adaptee qui gere directement les formules
rewrite(#, J, J, '\\bot') :- !.
rewrite(# => #, J, J, '\\top') :- !.

% NOUVELLE CLAUSE POUR GERER LES CONSTANTES DE SKOLEM
% Convertit f_sk(K,_) en un nom simple comme 'a', 'b', etc.
rewrite(f_sk(K,_), J, J, Name) :-
    !,
    rewrite_name(K, Name).

% CAS DE BASE : formules atomiques
rewrite(A, J, J, A_latex) :-
    atomic(A),
    !,
    toggle(A, A_latex).

% Reconnait ((A => B) & (B => A)) (ou l'ordre inverse) comme A <=> B pour l'affichage LaTeX
% Doit etre place AVANT la clause generique rewrite((A & B), ...)
rewrite((X & Y), J, K, (C ' \\leftrightarrow ' D)) :-
    % cas 1 : X = (A => B), Y = (B => A)
    ( X = (A => B), Y = (B => A)
    % cas 2 : ordre inverse
    ; X = (B => A), Y = (A => B)
    ),
    !,
    rewrite(A, J, H, C),
    rewrite(B, H, K, D).

% Conjonction avec operateur standard &
rewrite((A & B), J, K, (C ' \\land ' D)) :-
    !,
    rewrite(A, J, H, C),
    rewrite(B, H, K, D).

% Disjonction avec operateur standard |
rewrite((A | B), J, K, (C ' \\lor ' D)) :-
    !,
    rewrite(A, J, H, C),
    rewrite(B, H, K, D).

% AFFICHAGE COSMETIQUE : A => # devient !A
rewrite((A => #), J, K, (' \\lnot ' C)) :-
    !,
    rewrite(A, J, K, C).


% Implication avec operateur standard =>
rewrite((A => B), J, K, (C ' \\to ' D)) :-
    !,
    rewrite(A, J, H, C),
    rewrite(B, H, K, D).

% Biconditionnelle avec operateur standard <=>
rewrite((A <=> B), J, K, (C ' \\leftrightarrow ' D)) :-
    !,
    rewrite(A, J, H, C),
    rewrite(B, H, K, D).

% Negation avec operateur standard ~
rewrite((~A), J, K, (' \\lnot ' C)) :-
    !,
    rewrite(A, J, K, C).


% QUANTIFICATEURS : Version Burse pour format X-Y
rewrite((![X-X]:A), J, K, (' \\forall ' X ' ' C)) :-
    !,
    rewrite(A, J, K, C).

rewrite((?[X-X]:A), J, K, (' \\exists ' X ' ' C)) :-
    !,
    rewrite(A, J, K, C).
/*
% QUANTIFICATEURS : Adapter les formules directement
rewrite((![_X]:A), J, K, (' \\forall ' VarName ' ' C)) :-
    !,
    rewrite_name(J, VarName),
    J1 is J + 1,
    rewrite(A, J1, K, C).

rewrite((?[_X]:A), J, K, (' \\exists ' VarName ' ' C)) :-
    !,
    rewrite_name(J, VarName),
    J1 is J + 1,
    rewrite(A, J1, K, C).
*/
rewrite((![X]:A), J, K, (' \\forall ' X ' ' C)) :-
    !,
    rewrite(A, J, K, C).  % Garder le même compteur

rewrite((?[X]:A), J, K, (' \\exists ' X ' ' C)) :-
    !,
    rewrite(A, J, K, C).  % Garder le même compteur
% =========================================================================
% SIMPLIFICATION ELEGANTE DES PREDICATS
% P(x,y,z) -> Pxyz pour tous les predicats
% =========================================================================
/*
rewrite(Pred, J, K, SimplePred) :-
    Pred =.. [F|Args],
    atom(F),
    Args \= [],
    all_simple_terms(Args),
    !,
    toggle(F, G),
    rewrite_args_list(Args, J, K, SimpleArgs),
    concatenate_all([G|SimpleArgs], SimplePred).
*/

% --- Replace the previous "concatenate predicate name and args" clause by this safer version.
% We avoid applying this cosmetic concatenation to equality and other logical operators.
rewrite(Pred, J, K, SimplePred) :-
    Pred =.. [F|Args],
    atom(F),
    Args \= [],
    % Do NOT collapse standard logical operators or equality into a single atom:
    % exclude '=' and the main logical connectives (=>, <=>, &, |, ~)
    \+ member(F, ['=', '=>', '<=>', '&', '|', '~']),
    all_simple_terms(Args),
    !,
    toggle(F, G),
    rewrite_args_list(Args, J, K, SimpleArgs),
    concatenate_all([G|SimpleArgs], SimplePred).

% PREDICATS ET TERMES (clause generale)
rewrite(X, J, K, Y) :-
    X =.. [F|L],
    toggle(F, G),
    rewrite_list(L, J, K, R),
    Y =.. [G|R].


% =========================================================================
% PREDICATS AUXILIAIRES POUR LA SIMPLIFICATION
% =========================================================================

all_simple_terms([]).
all_simple_terms([H|T]) :-
    simple_term(H),
    all_simple_terms(T).

simple_term(X) :-
    atomic(X), !.
simple_term(X) :-
    var(X), !.
simple_term(f_sk(_,_)) :-
    !.
simple_term(X) :-
    X =.. [F|Args],
    atom(F),
    Args \= [],
    length(Args, Len),
    Len =< 2,
    all_simple_terms(Args).

rewrite_args_list([], J, J, []).
rewrite_args_list([H|T], J, K, [RH|RT]) :-
    rewrite_term(H, J, TempJ, RH),
    rewrite_args_list(T, TempJ, K, RT).

concatenate_all([X], X) :-
    atomic(X), !.
concatenate_all([H|T], Result) :-
    length([H|T], Len),
    Len =< 5,
    !,
    concatenate_all_impl([H|T], Result).
concatenate_all(_, _) :-
    fail.

concatenate_all_impl([X], X) :-
    atomic(X), !.
concatenate_all_impl([H|T], Result) :-
    concatenate_all_impl(T, TempResult),
    atom_concat(H, TempResult, Result).

% =========================================================================
% TRAITEMENT DES LISTES ET TERMES
% =========================================================================

rewrite_list([], J, J, []).
rewrite_list([X|L], J, K, [Y|R]) :-
    rewrite_term(X, J, H, Y),
    rewrite_list(L, H, K, R).

rewrite_term(V, J, K, V) :-
    var(V),
    !,
    rewrite_name(J, V),
    K is J+1.

rewrite_term(f_sk(K,_), J, J, N) :-
    !,
    rewrite_name(K, N).

% NOUVEAU : Si le terme est un atome simple (constante), NE PAS le capitaliser
% Car il est argument d'un predicat/fonction
rewrite_term(X, J, J, X) :-
    atomic(X),
    !.

rewrite_term(X, J, K, Y) :-
    X =.. [F|L],
    rewrite_list(L, J, K, R),
    Y =.. [F|R].

% Generateur de noms elegants
rewrite_name(K, N) :-
    K < 3,
    !,
    J is K+0'a,
    char_code(N, J).

rewrite_name(K, N) :-
    J is (K mod 3)+0'a,
    H is K div 3,
    number_codes(H, L),
    atom_codes(N, [J|L]).

% Toggle majuscules/minuscules
toggle(X, Y) :-
    atom_codes(X, L),
    toggle_list(L, R),
    atom_codes(Y, R).

toggle_list([], []).
toggle_list([X|L], [Y|R]) :-
    toggle_code(X, Y),
    toggle_list(L, R).

toggle_code(X, Y) :-
    0'a =< X, X =< 0'z,
    !,
    Y is X - 0'a + 0'A.

toggle_code(X, Y) :-
    0'A =< X, X =< 0'Z,
    !,
    Y is X - 0'A + 0'a.

toggle_code(X, X).

% =========================================================================
% SYSTEME PREPARE
% =========================================================================

prepare_sequent(PremisesList => Conclusion, PreparedPremises, PreparedConclusion) :-
    is_list(PremisesList),
    !,
    prepare_premises_list(PremisesList, PreparedPremises),
    prepare(Conclusion, [], PreparedConclusion).

prepare_sequent(Premises => Conclusion, [PreparedPremises], PreparedConclusion) :-
    prepare(Premises, [], PreparedPremises),
    prepare(Conclusion, [], PreparedConclusion).

prepare_premises_list([], []) :- !.
prepare_premises_list([H|T], [PreparedH|PreparedT]) :-
    prepare(H, [], PreparedH),
    prepare_premises_list(T, PreparedT).

prepare(#, _, #) :- !.

prepare((A & B), Q, (C & D)) :-
    !,
    prepare(A, Q, C),
    prepare(B, Q, D).

prepare((A | B), Q, (C | D)) :-
    !,
    prepare(A, Q, C),
    prepare(B, Q, D).

prepare((A => B), Q, (C => D)) :-
    !,
    prepare(A, Q, C),
    prepare(B, Q, D).

prepare((A <=> B), Q, (C <=> D)) :-
    !,
    prepare(A, Q, C),
    prepare(B, Q, D).

prepare((~A), Q, (~C)) :-
    !,
    prepare(A, Q, C).

prepare((![Z]:A), Q, (![Z-X]:C)) :-
    !,
    prepare(A, [Z-X|Q], C).

prepare((?[Z]:A), Q, (?[Z-X]:C)) :-
    !,
    prepare(A, [Z-X|Q], C).

prepare(X, _, X) :-
    var(X),
    !.

prepare(X, Q, Y) :-
    X =.. [F|L],
    prepare_list(L, Q, R),
    Y =.. [F|R].

prepare_term(X, _, X) :-
    var(X),
    !.

prepare_term(X, Q, Y) :-
    atom(X),
    member(X-Y, Q),
    !.

prepare_term(X, Q, Y) :-
    X =.. [F|L],
    prepare_list(L, Q, R),
    Y =.. [F|R].

prepare_list([], _, []).
prepare_list([X|L], Q, [Y|R]) :-
    prepare_term(X, Q, Y),
    prepare_list(L, Q, R).

% Support lambda calculus
lambda_has(V:_, W) :-
    V == W.

lambda_has(app(P,_,_,_), W) :-
    lambda_has(P, W).

lambda_has(app(_,Q,_,_), W) :-
    lambda_has(Q, W).

lambda_has(lam(V:_,_,_,_), W) :-
    V == W,
    !,
    fail.

lambda_has(lam(_,P,_,_), W) :-
    lambda_has(P, W).

lambda_has('C'(P,_,_), W) :-
    lambda_has(P, W).

%%%%%% Sequents

% Determiner le type de preuve (theoreme ou sequent)
% RENOMME pour eviter conflit avec proof_type/2 du driver
% Cette fonction analyse la STRUCTURE d'une preuve G4, pas la syntaxe d'une formule
proof_structure_type(Proof, Type) :-
    proof_premises(Proof, Premisses),
    (   Premisses = [] 
    ->  Type = theorem
    ;   Type = sequent
    ).

% NOTE: Si proof_structure_type est utilisee quelque part, mettre a jour les appels.
% Actuellement, elle ne semble appelee nulle part dans ce fichier.

% Generer les commandes Fitch selon le type et la position
fitch_prefix(sequent, LineNum, TotalPremisses, Prefix) :-
    (   LineNum =< TotalPremisses 
    ->  (   LineNum = TotalPremisses 
        ->  Prefix = '\\fj '  % Gros drapeau pour derniere premisse
        ;   Prefix = '\\fa '  % Ligne normale pour premisses
        )
    ;   Prefix = '\\fa '      % Ligne normale apres les premisses
    ).

fitch_prefix(theorem, Depth, _, Prefix) :-
    (   Depth > 0 
    ->  Prefix = '\\fa \\fh '  % Petit drapeau pour hypotheses
    ;   Prefix = '\\fa '       % Ligne normale au niveau 0
    ).

% =========================================================================
% RENDU LATEX BUSSPROOFS
% =========================================================================

render_buss_tree(hypothesis(Num, Formula), FitchLines, HypMap) :-
    !,
    ( nonvar(Num) ->
        ( member(Num-SharedNum, HypMap) -> DisplayNum = SharedNum ; DisplayNum = Num ),
        ( hypothesis_is_discharged(Num, FitchLines) ->
            write('\\AxiomC{\\scriptsize{'), write(DisplayNum), write('}}'), nl,
            write('\\noLine'), nl
        ;
            write('\\AxiomC{}'), nl
        )
    ;
        write('\\AxiomC{}'), nl
    ),
    write('\\UnaryInfC{$'),
    ( nonvar(Formula) -> render_formula_for_buss(Formula) ; write('???') ),
    write('$}'), nl.

render_buss_tree(premise_node(Formula), _FitchLines, _HypMap) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\noLine'), nl,
    write('\\UnaryInfC{$'),
    render_formula_for_buss(Formula),
    write('$}'), nl.

render_buss_tree(reiteration_node(Formula, SubTree), FitchLines, HypMap) :-
    !,
    render_buss_tree(SubTree, FitchLines, HypMap),
    write('\\RightLabel{$\\scriptsize{R}$}'), nl,
    write('\\UnaryInfC{$'),
    render_formula_for_buss(Formula),
    write('$}'), nl.

render_buss_tree(axiom_node(Formula), _FitchLines, _HypMap) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize $Ax.$}'), nl,
    write('\\UnaryInfC{$'),
    render_formula_for_buss(Formula),
    write('$}'), nl.

render_buss_tree(unary_node(Rule, Formula, SubTree), FitchLines, HypMap) :-
    !,
    render_buss_tree(SubTree, FitchLines, HypMap),
    write('\\RightLabel{$\\scriptsize{'),
    render_rule_name(Rule),
    write('}$}'), nl,
    write('\\UnaryInfC{$'),
    render_formula_for_buss(Formula),
    write('$}'), nl.

render_buss_tree(binary_node(Rule, Formula, TreeA, TreeB), FitchLines, HypMap) :-
    !,
    render_buss_tree(TreeA, FitchLines, HypMap),
    render_buss_tree(TreeB, FitchLines, HypMap),
    write('\\RightLabel{$\\scriptsize{'),
    render_rule_name(Rule),
    write('}$}'), nl,
    write('\\BinaryInfC{$'),
    render_formula_for_buss(Formula),
    write('$}'), nl.

render_buss_tree(ternary_node(lor, HypA, HypB, Result, DisjTree, TreeA, TreeB), FitchLines, HypMap) :-
    !,
    render_buss_tree(DisjTree, FitchLines, HypMap),
    render_buss_tree(TreeA, FitchLines, HypMap),
    render_buss_tree(TreeB, FitchLines, HypMap),
    write('\\RightLabel{$\\scriptsize{\\lor E\\ '),
    ( is_vacuous_discharge(HypA, TreeA, FitchLines) -> true ; write(HypA) ),
    write(','),
    ( is_vacuous_discharge(HypB, TreeB, FitchLines) -> true ; write(HypB) ),
    write('}$}'), nl,
    write('\\TrinaryInfC{$'),
    render_formula_for_buss(Result),
    write('$}'), nl.

render_buss_tree(discharged_node(rcond, HypNum, Result, SubTree), FitchLines, HypMap) :-
    !,
    render_buss_tree(SubTree, FitchLines, HypMap),
    write('\\RightLabel{$\\scriptsize{\\to I}'),
    ( is_vacuous_discharge(HypNum, SubTree, FitchLines) -> write('$}'), nl ; write('\\ '), write(HypNum), write('$}'), nl ),
    write('\\UnaryInfC{$'),
    render_formula_for_buss(Result),
    write('$}'), nl.

render_buss_tree(discharged_node(ip, HypNum, Result, SubTree), FitchLines, HypMap) :-
    !,
    render_buss_tree(SubTree, FitchLines, HypMap),
    write('\\RightLabel{$\\scriptsize{IP}'),
    ( is_vacuous_discharge(HypNum, SubTree, FitchLines) -> write('$}'), nl ; write('\\ '), write(HypNum), write('$}'), nl ),
    write('\\UnaryInfC{$'),
    render_formula_for_buss(Result),
    write('$}'), nl.

render_buss_tree(discharged_node(lex, WitNum, Result, ExistTree, GoalTree), FitchLines, HypMap) :-
    !,
    render_buss_tree(ExistTree, FitchLines, HypMap),
    render_buss_tree(GoalTree, FitchLines, HypMap),
    write('\\RightLabel{$\\scriptsize{\\exists E}'),
    ( is_vacuous_discharge(WitNum, GoalTree, FitchLines) -> write('$}'), nl ; write('\\ '), write(WitNum), write('$}'), nl ),
    write('\\BinaryInfC{$'),
    render_formula_for_buss(Result),
    write('$}'), nl.

render_buss_tree(unknown_node(Just, _LineNum, Formula), _FitchLines, _HypMap) :-
    !,
    write('\\AxiomC{['), write(Just), write(']}'), nl,
    write('\\UnaryInfC{$'),
    render_formula_for_buss(Formula),
    write('$}'), nl.

% =========================================================================
% HELPERS POUR TREE RENDERING
% =========================================================================

hypothesis_is_discharged(HypNum, FitchLines) :-
    member(_-_-Just-_, FitchLines),
    justification_discharges(Just, HypNum).

justification_discharges(rcond(HypNum, _), HypNum) :- !.
justification_discharges(ip(HypNum, _), HypNum) :- !.
justification_discharges(lor(_, HypA, HypB, _, _), HypNum) :- (HypNum = HypA ; HypNum = HypB), !.
justification_discharges(lex(_, WitNum, _), WitNum) :- !.
justification_discharges(_, _) :- fail.

is_vacuous_discharge(HypNum, Tree, FitchLines) :-
    member(HypNum-Formula-assumption-_, FitchLines),
    \+ tree_uses_hypothesis(Tree, HypNum, Formula).

tree_uses_hypothesis(hypothesis(N, F), HypNum, HypFormula) :- N == HypNum, F =@= HypFormula.
tree_uses_hypothesis(unary_node(_, _, SubTree), HypNum, HypFormula) :- tree_uses_hypothesis(SubTree, HypNum, HypFormula).
tree_uses_hypothesis(binary_node(_, _, TreeA, TreeB), HypNum, HypFormula) :-
    ( tree_uses_hypothesis(TreeA, HypNum, HypFormula) ; tree_uses_hypothesis(TreeB, HypNum, HypFormula) ).
tree_uses_hypothesis(ternary_node(_, _, _, _, TreeA, TreeB, TreeC), HypNum, HypFormula) :-
    ( tree_uses_hypothesis(TreeA, HypNum, HypFormula) ; tree_uses_hypothesis(TreeB, HypNum, HypFormula) ; tree_uses_hypothesis(TreeC, HypNum, HypFormula) ).
tree_uses_hypothesis(discharged_node(_, _, _, SubTree), HypNum, HypFormula) :- tree_uses_hypothesis(SubTree, HypNum, HypFormula).
tree_uses_hypothesis(discharged_node(_, _, _, TreeA, TreeB), HypNum, HypFormula) :-
    ( tree_uses_hypothesis(TreeA, HypNum, HypFormula) ; tree_uses_hypothesis(TreeB, HypNum, HypFormula) ).

render_rule_name(ror) :- write('\\lor I').
render_rule_name(lbot) :- write('\\bot E').
render_rule_name(land) :- write('\\land E').
render_rule_name(rand) :- write('\\land I').
render_rule_name(rex) :- write('\\exists I').
render_rule_name(lall) :- write('\\forall E').
render_rule_name(rall) :- write('\\forall I').
render_rule_name(l0cond) :- write('\\to E').
render_rule_name(landto) :- write('L\\land\\to').
render_rule_name(lorto) :- write('L\\lor\\to').
render_rule_name(ltoto) :- write('L\\to\\to').
render_rule_name(cq_c) :- write('CQ_{c}').
render_rule_name(cq_m) :- write('CQ_{m}').
% Regles d'egalite -> Leibniz
render_rule_name(eq_subst) :- !, write('Leibniz').
render_rule_name(eq_trans) :- !, write('Leibniz').
render_rule_name(eq_subst_eq) :- !, write('Leibniz').
render_rule_name(eq_sym) :- !, write('Leibniz').
render_rule_name(eq_cong) :- !, write('Leibniz').
render_rule_name(eq_refl) :- !, write('Leibniz').
render_rule_name(eq_trans_chain) :- !, write('Leibniz').
% Fallback
render_rule_name(Rule) :- write(Rule).

% =========================================================================
% LaTeX FORMULA RENDERING
% =========================================================================

render_formula_for_buss(Formula) :-
    catch(
        (rewrite(Formula, 0, _, LatexFormula), render_latex_formula(LatexFormula)),
        _Error,
        (write('???'))
    ).

render_latex_formula((A ' \\to ' B)) :-
    !,
    ( is_atomic_or_negative_formula(A) ->
        render_latex_formula(A)
    ;
        write('('),
        render_latex_formula(A),
        write(')')
    ),
    write(' \\to '),
    ( is_atomic_or_negative_formula(B) ->
        render_latex_formula(B)
    ;
        write('('),
        render_latex_formula(B),
        write(')')
    ).

render_latex_formula((A ' \\land ' B)) :-
    !,
    render_latex_with_parens(A, 'conj_left'),
    write(' \\land '),
    render_latex_with_parens(B, 'conj_right').

render_latex_formula((A ' \\lor ' B)) :-
    !,
    render_latex_with_parens(A, 'disj_left'),
    write(' \\lor '),
    render_latex_with_parens(B, 'disj_right').

render_latex_formula((A ' \\leftrightarrow ' B)) :-
    !,
    write('('),
    render_latex_formula(A),
    write(' \\leftrightarrow '),
    render_latex_formula(B),
    write(')').

render_latex_formula('='(A, B)) :-
    !,
    write('('),
    render_latex_formula(A),
    write('='),
    render_latex_formula(B),
    write(')').

render_latex_formula((' \\lnot ' A)) :-
    !,
    write(' \\lnot '),
    render_latex_with_parens(A, 'neg').

render_latex_formula((' \\forall ' X ' ' A)) :-
    !,
    write(' \\forall '),
    write(X),
    write(' '),
    ( quantifier_body_needs_parens(A) ->
        write('('),
        render_latex_formula(A),
        write(')')
    ;
        render_latex_formula(A)
    ).

render_latex_formula((' \\exists ' X ' ' A)) :-
    !,
    write(' \\exists '),
    write(X),
    write(' '),
    ( quantifier_body_needs_parens(A) ->
        write('('),
        render_latex_formula(A),
        write(')')
    ;
        render_latex_formula(A)
    ).

render_latex_formula('\\bot') :-
    !,
    write('\\bot').

render_latex_formula(Atom) :-
    atomic(Atom),
    !,
    write(Atom).

render_latex_formula(Complex) :-
    write(Complex).

render_latex_with_parens((' \\lnot ' A), _Context) :-
    !,
    render_latex_formula((' \\lnot ' A)).

render_latex_with_parens((A ' \\to ' B), Context) :-
    needs_parens_in_context(' \\to ', Context),
    !,
    write('('),
    render_latex_formula((A ' \\to ' B)),
    write(')').

render_latex_with_parens((A ' \\land ' B), Context) :-
    needs_parens_in_context(' \\land ', Context),
    !,
    write('('),
    render_latex_formula((A ' \\land ' B)),
    write(')').

render_latex_with_parens((A ' \\lor ' B), Context) :-
    needs_parens_in_context(' \\lor ', Context),
    !, write('('),
    render_latex_formula((A ' \\lor ' B)), write(')').

render_latex_with_parens(Formula, _Context) :- render_latex_formula(Formula).

needs_parens_in_context(' \\to ', 'impl_left') :- !.
needs_parens_in_context(' \\to ', 'conj_left') :- !.
needs_parens_in_context(' \\to ', 'conj_right') :- !.
needs_parens_in_context(' \\to ', 'disj_left') :- !.
needs_parens_in_context(' \\to ', 'disj_right') :- !.
needs_parens_in_context(' \\to ', 'neg') :- !.
needs_parens_in_context(' \\land ', 'disj_left') :- !.
needs_parens_in_context(' \\land ', 'disj_right') :- !.
needs_parens_in_context(' \\land ', 'impl_left') :- !.
needs_parens_in_context(' \\land ', 'neg') :- !.
needs_parens_in_context(' \\lor ', 'conj_left') :- !.
needs_parens_in_context(' \\lor ', 'conj_right') :- !.
needs_parens_in_context(' \\lor ', 'impl_left') :- !.
needs_parens_in_context(' \\lor ', 'neg') :- !.
needs_parens_in_context(_, _) :- fail.



% =========================================================================
% END OF FILE
% =========================================================================
