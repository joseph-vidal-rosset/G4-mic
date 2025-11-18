% =========================================================================
% NATURAL DEDUCTION PRINTER IN TREE STYLE  
% =========================================================================
% =========================================================================
% DISPLAY PREMISS FOR TREE STYLE 
% =========================================================================
% render_premise_list_silent/5: Silent version for tree style
render_premise_list_silent([], _, Line, Line, []) :- !.

render_premise_list_silent([LastPremiss], Scope, CurLine, NextLine, [CurLine:LastPremiss]) :-
    !,
    assert_safe_fitch_line(CurLine, LastPremiss, premise, Scope),
    NextLine is CurLine + 1.

render_premise_list_silent([Premiss|Rest], Scope, CurLine, NextLine, [CurLine:Premiss|RestContext]) :-
    assert_safe_fitch_line(CurLine, Premiss, premise, Scope),
    NextCurLine is CurLine + 1,
    render_premise_list_silent(Rest, Scope, NextCurLine, NextLine, RestContext).

% =========================================================================
% INTERFACE TREE STYLE
% =========================================================================
render_nd_tree_proof(Proof) :-
    retractall(fitch_line(_, _, _, _)),
    retractall(abbreviated_line(_)),
    extract_formula_from_proof(Proof, TopFormula),
    detect_and_set_logic_level(TopFormula),
    catch(
        (
            ( premise_list(PremissList), PremissList = [_|_] ->
                render_premise_list_silent(PremissList, 0, 1, NextLine, InitialContext),
                LastPremLine is NextLine - 1,
                % Capture ResLine (6ème argument) qui est la ligne de conclusion
                with_output_to(atom(_), fitch_g4_proof(Proof, InitialContext, 1, LastPremLine, _, ResLine, 0, _))
            ;
                % Pas de prémisses
                with_output_to(atom(_), fitch_g4_proof(Proof, [], 1, 0, _, ResLine, 0, _))
            ),
            % Utilisation de ResLine comme racine de l'arbre
            collect_and_render_tree(ResLine)
        ),
        Error,
        (
            format('% Error rendering ND tree: ~w~n', [Error]),
            write('% Skipping tree visualization'), nl
        )
    ).

% =========================================================================
% COLLECT AND RENDER TREE
% =========================================================================

collect_and_render_tree(RootLineNum) :-
    findall(N-Formula-Just-Scope, 
            (fitch_line(N, Formula, Just, Scope), \+ abbreviated_line(N)), 
            Lines),
    predsort(compare_lines, Lines, SortedLines),
    ( SortedLines = [] ->
        write('% Empty proof tree'), nl
    ;
        % Capture toutes les formules prémisses pour le wrapping conditionnel
        findall(F, fitch_line(_, F, premise, _), AllPremises),

        ( build_buss_tree(RootLineNum, SortedLines, Tree) ->
            
            % Vérifie si la conclusion est simple (premisse/reiteration) ET qu'il y a plusieurs prémisses
            % FIX: Check RootLineNum for justification, not just any line.
            ( is_simple_conclusion(RootLineNum, AllPremises) ->
                % Force la structure pour afficher TOUTES les prémisses comme branches
                wrap_premises_in_tree(RootLineNum, AllPremises, FinalTree)
            ;
                FinalTree = Tree
            ),
            
            write('\\begin{prooftree}'), nl,
            render_buss_tree(FinalTree),
            write('\\end{prooftree}'), nl
        ;
            write('% Warning: missing referenced line(s) or broken tree structure'), nl
        )
    ).

compare_lines(Delta, N1-_-_-_, N2-_-_-_) :-
    compare(Delta, N1, N2).

% Helper pour vérifier si la conclusion est une simple réitération ou une prémisse
% FIX: Ensures the justification check is for the RootLineNum.
is_simple_conclusion(RootLineNum, AllPremises) :-
    length(AllPremises, N),
    N > 1, % Doit avoir plusieurs prémisses
    fitch_line(RootLineNum, _, Just, _), % Check RootLineNum's justification
    ( Just = premise ; Just = reiteration(_) ),
    !.

% Helper pour forcer la création d'un nœud n-aire de prémisses
wrap_premises_in_tree(RootLineNum, AllPremises, FinalTree) :-
    % Crée une liste de premise_node(F) pour toutes les prémisses
    findall(premise_node(F), member(F, AllPremises), PremiseTrees),
    % Obtient la formule de conclusion
    fitch_line(RootLineNum, FinalFormula, _, _),
    
    % Crée le nœud forcé
    FinalTree = n_ary_premise_node(FinalFormula, PremiseTrees).

% =========================================================================
% CONSTRUCTION D'ARBRE BUSSPROOFS
% =========================================================================

build_buss_tree(LineNum, FitchLines, Tree) :-
    ( member(LineNum-Formula-Just-_Scope, FitchLines) ->
        build_tree_from_just(Just, LineNum, Formula, FitchLines, Tree)
    ;
        fail
    ).

% -- Réitération (Règle déplacée pour priorité, corrige P, Q |- P) --
build_tree_from_just(reiteration(SourceLine), _LineNum, Formula, FitchLines, reiteration_node(Formula, SubTree)) :-
    !,
    build_buss_tree(SourceLine, FitchLines, SubTree).

% -- Feuilles --
build_tree_from_just(assumption, LineNum, Formula, _FitchLines, assumption_node(Formula, LineNum)) :- !.
build_tree_from_just(axiom, _LineNum, Formula, _FitchLines, axiom_node(Formula)) :- !.
build_tree_from_just(premise, _LineNum, Formula, _FitchLines, premise_node(Formula)) :- !.

% -- Règles Implication --
% R->
build_tree_from_just(rcond(HypNum, GoalNum), _LineNum, Formula, FitchLines, discharged_node(rcond, HypNum, Formula, SubTree)) :-
    !, build_buss_tree(GoalNum, FitchLines, SubTree).

% L0-> (Modus Ponens)
build_tree_from_just(l0cond(MajLine, MinLine), _LineNum, Formula, FitchLines, binary_node(l0cond, Formula, TreeA, TreeB)) :-
    !, build_buss_tree(MajLine, FitchLines, TreeA), build_buss_tree(MinLine, FitchLines, TreeB).

% L->-> (Règle spéciale G4)
build_tree_from_just(ltoto(Line), _LineNum, Formula, FitchLines, unary_node(ltoto, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

% -- Règles Disjonction --
% R? (Intro Or)
build_tree_from_just(ror(SubLine), _LineNum, Formula, FitchLines, unary_node(ror, Formula, SubTree)) :-
    !, build_buss_tree(SubLine, FitchLines, SubTree).

% L? (Elim Or) - Ternaire
build_tree_from_just(lor(DisjLine, HypA, HypB, GoalA, GoalB), _LineNum, Formula, FitchLines,
                     ternary_node(lor, HypA, HypB, Formula, DisjTree, TreeA, TreeB)) :-
    !, build_buss_tree(DisjLine, FitchLines, DisjTree),
    build_buss_tree(GoalA, FitchLines, TreeA),
    build_buss_tree(GoalB, FitchLines, TreeB).

% L?-> (Disjonction gauche vers flèche)
build_tree_from_just(lorto(Line), _LineNum, Formula, FitchLines, unary_node(lorto, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

% -- Règles Conjonction --
% L? (Elim And)
build_tree_from_just(land(ConjLine, _Which), _LineNum, Formula, FitchLines, unary_node(land, Formula, SubTree)) :-
    !, build_buss_tree(ConjLine, FitchLines, SubTree).
build_tree_from_just(land(ConjLine), _LineNum, Formula, FitchLines, unary_node(land, Formula, SubTree)) :-
    !, build_buss_tree(ConjLine, FitchLines, SubTree).

% R? (Intro And)
build_tree_from_just(rand(LineA, LineB), _LineNum, Formula, FitchLines, binary_node(rand, Formula, TreeA, TreeB)) :-
    !, build_buss_tree(LineA, FitchLines, TreeA), build_buss_tree(LineB, FitchLines, TreeB).

% L?-> (Conjonction gauche vers flèche)
build_tree_from_just(landto(Line), _LineNum, Formula, FitchLines, unary_node(landto, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

% -- Règles Falsum / Négation --
% L? (Bot Elim)
build_tree_from_just(lbot(BotLine), _LineNum, Formula, FitchLines, unary_node(lbot, Formula, SubTree)) :-
    !, build_buss_tree(BotLine, FitchLines, SubTree).

% IP (Preuve indirecte / Classique)
build_tree_from_just(ip(HypNum, BotNum), _LineNum, Formula, FitchLines, discharged_node(ip, HypNum, Formula, SubTree)) :-
    !, build_buss_tree(BotNum, FitchLines, SubTree).

% -- Règles Quantificateurs --
% L? (Exist Elim)
build_tree_from_just(lex(ExistLine, WitNum, GoalNum), _LineNum, Formula, FitchLines, 
                     discharged_node(lex, WitNum, Formula, ExistTree, GoalTree)) :-
    !,
    build_buss_tree(ExistLine, FitchLines, ExistTree), build_buss_tree(GoalNum, FitchLines, GoalTree).

% R? (Exist Intro)
build_tree_from_just(rex(WitLine), _LineNum, Formula, FitchLines, unary_node(rex, Formula, SubTree)) :-
    !, build_buss_tree(WitLine, FitchLines, SubTree).

% L? (Forall Elim)
build_tree_from_just(lall(UnivLine), _LineNum, Formula, FitchLines, unary_node(lall, Formula, SubTree)) :-
    !, build_buss_tree(UnivLine, FitchLines, SubTree).

% R? (Forall Intro)
build_tree_from_just(rall(BodyLine), _LineNum, Formula, FitchLines, unary_node(rall, Formula, SubTree)) :-
    !, build_buss_tree(BodyLine, FitchLines, SubTree).

% Conversions Quantificateurs
build_tree_from_just(cq_c(Line), _LineNum, Formula, FitchLines, unary_node(cq_c, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

build_tree_from_just(cq_m(Line), _LineNum, Formula, FitchLines, unary_node(cq_m, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

% -- Règles d'Égalité --
build_tree_from_just(eq_refl, _LineNum, Formula, _FitchLines, axiom_node(Formula)) :- !.

build_tree_from_just(eq_sym(SourceLine), _LineNum, Formula, FitchLines, 
                     unary_node(eq_sym, Formula, SubTree)) :-
    !, build_buss_tree(SourceLine, FitchLines, SubTree).

build_tree_from_just(eq_trans(Line1, Line2), _LineNum, Formula, FitchLines, 
                     binary_node(eq_trans, Formula, Tree1, Tree2)) :-
    !, build_buss_tree(Line1, FitchLines, Tree1), build_buss_tree(Line2, FitchLines, Tree2).

build_tree_from_just(eq_subst(Line1, Line2), _LineNum, Formula, FitchLines,
                     binary_node(eq_subst, Formula, Tree1, Tree2)) :-
    !, build_buss_tree(Line1, FitchLines, Tree1), build_buss_tree(Line2, FitchLines, Tree2).

build_tree_from_just(eq_cong(SourceLine), _LineNum, Formula, FitchLines, 
                     unary_node(eq_cong, Formula, SubTree)) :-
    !, build_buss_tree(SourceLine, FitchLines, SubTree).

build_tree_from_just(eq_subst_eq(Line1, Line2), _LineNum, Formula, FitchLines,
                     binary_node(eq_subst_eq, Formula, Tree1, Tree2)) :-
    !, build_buss_tree(Line1, FitchLines, Tree1), build_buss_tree(Line2, FitchLines, Tree2).

build_tree_from_just(eq_trans_chain, _LineNum, Formula, _FitchLines, 
                     axiom_node(Formula)) :- !.

% Fallback
build_tree_from_just(Just, LineNum, Formula, _FitchLines, unknown_node(Just, LineNum, Formula)) :-
    format('% WARNING: Unknown justification type: ~w~n', [Just]).

% =========================================================================
% RENDU RECURSIF DE L'ARBRE (Latex Bussproofs)
% =========================================================================

% render_buss_tree(+Tree)
% Genere les commandes LaTeX pour l'arbre

% -- Feuilles --
render_buss_tree(axiom_node(F)) :-
    write('\\AxiomC{$'), render_formula_for_buss(F), write('$}'), nl.

render_buss_tree(premise_node(F)) :-
    write('\\AxiomC{$'), render_formula_for_buss(F), write('$}'), nl.

% -- Hypothèses (STYLE CORRIGÉ: Numéro en petite taille, noLine, Formule) --
render_buss_tree(assumption_node(F, HypNum)) :-
    format('\\AxiomC{\\scriptsize{~w}}', [HypNum]), nl, % Ajout de \scriptsize
    write('\\noLine'), nl,
    write('\\UnaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% -- Réitération --
render_buss_tree(reiteration_node(F, SubTree)) :-
    render_buss_tree(SubTree),
    % Correction: Utilisation de write/nl pour s'assurer que l'inférence est rendue
    write('\\RightLabel{\\scriptsize{R}}'), nl,
    write('\\UnaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% -- Noeuds N-aires FORCÉS pour l'affichage de toutes les prémisses (cas simple conclusion) --
render_buss_tree(n_ary_premise_node(F, Trees)) :-
    % 1. Rendu de tous les sous-arbres (prémisses)
    maplist(render_buss_tree, Trees),
    
    % 2. Ajout de l'étiquette Wk (Weakening)
    write('\\RightLabel{\\scriptsize{Wk}}'), nl,
    
    % 3. Utilisation de BinaryInfC si N=2 (P et Q)
    length(Trees, N),
    ( N = 2 ->
        % La commande BinayInfC prend les deux dernières AxiomC, correspondant exactement à la demande P, Q |- P
        write('\\BinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl
    ;
        % Pour N > 2, nous utilisons TrinaryInfC si possible, sinon un message
        ( N = 3 ->
            write('\\TrinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl
        ;
            % Si N>3 (peu probable pour une preuve simple), on se rabat sur BinaryInfC pour garder le document compilable
            format('% Warning: Simplified N=~w inference to BinaryInfC for display.', [N]), nl,
            write('\\BinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl
        )
    ).

% -- Noeuds Unaires --
render_buss_tree(unary_node(Rule, F, SubTree)) :-
    render_buss_tree(SubTree),
    format_rule_label(Rule, Label),
    format('\\RightLabel{\\scriptsize{~w}}~n', [Label]),
    write('\\UnaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% -- Noeuds Binaires --
render_buss_tree(binary_node(Rule, F, TreeA, TreeB)) :-
    render_buss_tree(TreeA),
    render_buss_tree(TreeB),
    format_rule_label(Rule, Label),
    format('\\RightLabel{\\scriptsize{~w}}~n', [Label]),
    write('\\BinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% -- Noeuds Ternaires --
render_buss_tree(ternary_node(Rule, _HypA, _HypB, F, TreeA, TreeB, TreeC)) :-
    render_buss_tree(TreeA),
    render_buss_tree(TreeB),
    render_buss_tree(TreeC),
    format_rule_label(Rule, Label),
    format('\\RightLabel{\\scriptsize{~w}}~n', [Label]),
    write('\\TrinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% -- Noeuds avec Déchargement (Hypothèses) --
render_buss_tree(discharged_node(Rule, HypNum, F, SubTree)) :-
    render_buss_tree(SubTree),
    format_rule_label(Rule, BaseLabel),
    % Indique l'indice de l'hypothèse déchargée à côté de la règle
    format('\\RightLabel{\\scriptsize{~w}~w}', [BaseLabel, HypNum]), nl,
    write('\\UnaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% Cas spécial pour exists elimination
render_buss_tree(discharged_node(lex, WitNum, F, ExistTree, GoalTree)) :-
    render_buss_tree(ExistTree),
    render_buss_tree(GoalTree),
    format('\\RightLabel{\\scriptsize{$\\exists E$}~w}', [WitNum]), nl,
    write('\\BinaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% Fallback
render_buss_tree(unknown_node(Just, _, F)) :-
    write('\\AxiomC{?'), write(Just), write('?}'), nl,
    write('\\UnaryInfC{$'), render_formula_for_buss(F), write('$}'), nl.

% =========================================================================
% HELPER: LABELS DES REGLES
% =========================================================================
format_rule_label(rcond, '$\\to I$').
format_rule_label(l0cond, '$\\to E$').
format_rule_label(ror, '$\\lor I$').
format_rule_label(lor, '$\\lor E$').
format_rule_label(land, '$\\land E$').
format_rule_label(rand, '$\\land I$').
format_rule_label(lbot, '$\\bot E$').
format_rule_label(ip, 'IP').
format_rule_label(lex, '$\\exists E$').
format_rule_label(rex, '$\\exists I$').
format_rule_label(lall, '$\\forall E$').
format_rule_label(rall, '$\\forall I$').
format_rule_label(ltoto, '$L\\to\\to$').
format_rule_label(landto, '$L\\land\\to$').
format_rule_label(lorto, '$L\\lor\\to$').
format_rule_label(cq_c, '$CQ_c$').
format_rule_label(cq_m, '$CQ_m$').
format_rule_label(eq_refl, 'Refl').
format_rule_label(eq_sym, 'Sym').
format_rule_label(eq_trans, 'Trans').
format_rule_label(eq_subst, 'Subst').
format_rule_label(eq_cong, 'Cong').
format_rule_label(eq_subst_eq, 'SubstEq').
format_rule_label(X, X). % Fallback

% =========================================================================
% HELPER: WRAPPER POUR REWRITE
% =========================================================================
render_formula_for_buss(F) :-
    rewrite(F, 0, _, Latex),
    write(Latex).
