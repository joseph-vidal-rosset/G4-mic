% =========================================================================
% NATURAL DEDUCTION PRINTER IN FLAG STYLE  
% =========================================================================
:- dynamic fitch_line/4.
:- dynamic abbreviated_line/1.
% =========================================================================
% FROM G4 Sequent Calculus To Natural Deduction in Fitch Style 
% =========================================================================
g4_to_fitch_sequent(Proof, OriginalSequent) :-
    !,
    retractall(fitch_line(_, _, _, _)),
    retractall(abbreviated_line(_)),
    
    OriginalSequent = (_G > [Conclusion]),
    
    ( premiss_list(PremList), PremList \= [] ->
        render_premiss_list(PremList, 0, 1, NextLine, InitialContext),
        LastPremLine is NextLine - 1  % ✅ CORRECTION : dernière ligne de prémisse
    ;
        _NextLine = 1,
        LastPremLine = 0,             % ✅ CORRECTION : pas de prémisses
        InitialContext = []
    ),
    
    % ✅ CORRECTION : Scope=1 (indentation), CurLine=LastPremLine (numérotation)
    fitch_g4_proof(Proof, InitialContext, 1, LastPremLine, LastLine, ResLine, 0, _),
    
    % DÉTECTER : Est-ce qu'une règle a été appliquée ?
    ( LastLine = LastPremLine ->
        % Aucune ligne ajoutée → axiome pur → afficher réitération
        write('\\fa '),
        rewrite(Conclusion, 0, _, LatexConclusion),
        write(LatexConclusion),
        format(' &  R ~w\\\\', [ResLine]), nl
    ;
        % Une règle a déjà affiché la conclusion → ne rien faire
        true
    ).

% g4_to_fitch_theorem/1 : Pour théorèmes (comportement original)
g4_to_fitch_theorem(Proof) :-
    retractall(fitch_line(_, _, _, _)),
    retractall(abbreviated_line(_)),
    fitch_g4_proof(Proof, [], 1, 0, _, _, 0, _).
% =========================================================================
% AFFICHAGE DES PRÉMISSES
% =========================================================================
% render_premiss_list/5: Affiche une liste de prémisses en Fitch
render_premiss_list([], _, Line, Line, []) :- !.

render_premiss_list([LastPremiss], Scope, CurLine, NextLine, [CurLine:LastPremiss]) :-
    !,
    render_fitch_indent(Scope),
    write(' \\fj '),
    rewrite(LastPremiss, 0, _, LatexFormula),
    write(LatexFormula),
    write(' &  PR\\\\'), nl,
    assert_safe_fitch_line(CurLine, LastPremiss, premise, Scope),
    NextLine is CurLine + 1.
    
render_premiss_list([Premiss|Rest], Scope, CurLine, NextLine, [CurLine:Premiss|RestContext]) :-
    render_fitch_indent(Scope),
    write(' \\fa '),
    rewrite(Premiss, 0, _, LatexFormula),
    write(LatexFormula),
    write(' &  PR\\\\'), nl,
    assert_safe_fitch_line(CurLine, Premiss, premise, Scope),
    NextCurLine is CurLine + 1,
    render_premiss_list(Rest, Scope, NextCurLine, NextLine, RestContext).
% =========================================================================
% ASSERTION SÉCURISÉE
% =========================================================================
assert_safe_fitch_line(N, Formula, Just, Scope) :-
    catch(
        (
            ( acyclic_term(Formula) ->
                Safe = Formula
            ;
                make_acyclic_term(Formula, Safe)
            ),
            assertz(fitch_line(N, Safe, Just, Scope))
        ),
        Error,
        (
            format('% Warning: Could not assert line ~w: ~w~n', [N, Error]),
            assertz(fitch_line(N, error_term(Formula), Just, Scope))
        )
    ).
% =========================================================================
% GESTION DES TERMES CYCLIQUES
% =========================================================================
/*
make_acyclic_term(Term, Safe) :-
    catch(
        make_acyclic_term(Term, [], _MapOut, Safe),
        _,
        Safe = cyc(Term)
    ).

make_acyclic_term(Term, MapIn, MapOut, Safe) :-
    ( var(Term) ->
        Safe = Term, MapOut = MapIn
    ; atomic(Term) ->
        Safe = Term, MapOut = MapIn
    ; find_pair(Term, MapIn, Value) ->
        Safe = Value, MapOut = MapIn
    ;
        gensym(cyc, Patom),
        Placeholder = cyc(Patom),
        MapMid = [pair(Term, Placeholder)|MapIn],
        Term =.. [F|Args],
        make_acyclic_args(Args, MapMid, MapAfterArgs, SafeArgs),
        SafeTermBuilt =.. [F|SafeArgs],
        replace_pair(Term, Placeholder, SafeTermBuilt, MapAfterArgs, MapOut),
        Safe = SafeTermBuilt
    ).

make_acyclic_args([], Map, Map, []).
make_acyclic_args([A|As], MapIn, MapOut, [SA|SAs]) :-
    make_acyclic_term(A, MapIn, MapMid, SA),
    make_acyclic_args(As, MapMid, MapOut, SAs).

find_pair(Term, [pair(Orig,Val)|_], Val) :- Orig == Term, !.
find_pair(Term, [_|Rest], Val) :- find_pair(Term, Rest, Val).

replace_pair(Term, OldVal, NewVal, [pair(Orig,OldVal)|Rest], [pair(Orig,NewVal)|Rest]) :- 
    Orig == Term, !.
replace_pair(Term, OldVal, NewVal, [H|T], [H|T2]) :- 
    replace_pair(Term, OldVal, NewVal, T, T2).
replace_pair(_, _, _, [], []).
*/
% =========================================================================
% GESTION DES SUBSTITUTIONS @
% =========================================================================

fitch_g4_proof(@(ProofTerm, _), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    fitch_g4_proof(ProofTerm, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut).

% =========================================================================
% AXIOME
% =========================================================================

fitch_g4_proof(ax((Premisses > [Goal]), _Tag), Context, _Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    member(Goal, Premisses),
    find_context_line(Goal, Context, GoalLine),
    NextLine = CurLine,
    ResLine = GoalLine,
    VarOut = VarIn.

fitch_g4_proof(ax((Premisses > [Goal])), Context, _Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    member(Goal, Premisses),
    find_context_line(Goal, Context, GoalLine),
    NextLine = CurLine,
    ResLine = GoalLine,
    VarOut = VarIn.

% =========================================================================
% PROPOSITIONAL RULES 
% =========================================================================
% L0→ 
fitch_g4_proof(l0cond((Premisss > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    select((Ant => Cons), Premisss, Remaining),
    member(Ant, Remaining),
    find_context_line((Ant => Cons), Context, MajLine),
    find_context_line(Ant, Context, MinLine),
    DerLine is CurLine + 1,
    format(atom(Just), '$ \\to E $ ~w,~w', [MajLine, MinLine]),
    render_have(Scope, Cons, Just, CurLine, DerLine, VarIn, V1),
    assert_safe_fitch_line(DerLine, Cons, l0cond(MajLine, MinLine), Scope),
    fitch_g4_proof(SubProof, [DerLine:Cons|Context], Scope, DerLine, NextLine, ResLine, V1, VarOut).

% L∧→ 
fitch_g4_proof(landto((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    extract_new_formula(Premisses, SubProof, NewFormula),
    select(((A & B) => C), Premisses, _),
    once(member(ImpLine:((A & B) => C), Context)),
    derive_and_continue(Scope, NewFormula, 'L$ \\land \\to $ ~w', [ImpLine],
                       landto(ImpLine), SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut).

% L∨→ : Disjunction to implications
fitch_g4_proof(lorto((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    SubProof =.. [_Rule|[(SubPremisses > _SubGoal)|_]],
    findall(F, (member(F, SubPremisses), \+ member(F, Premisses)), NewFormulas),
    select(((A | B) => C), Premisses, _),
    find_context_line(((A | B) => C), Context, ImpLine),
    ( NewFormulas = [F1, F2] ->
        Line1 is CurLine + 1,
        Line2 is CurLine + 2,
        assert_safe_fitch_line(Line1, F1, lorto(ImpLine), Scope),
        assert_safe_fitch_line(Line2, F2, lorto(ImpLine), Scope),
        format(atom(Just), 'L$ \\lor \\to $ ~w', [ImpLine]),
        render_have(Scope, F1, Just, CurLine, Line1, VarIn, V1),
        render_have(Scope, F2, Just, Line1, Line2, V1, V2),
        fitch_g4_proof(SubProof, [Line2:F2, Line1:F1|Context], Scope, Line2, NextLine, ResLine, V2, VarOut)
    ; NewFormulas = [F1] ->
        derive_and_continue(Scope, F1, 'L$ \\lor \\to $ ~w', [ImpLine],
                           lorto(ImpLine), SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut)
    ;
        fitch_g4_proof(SubProof, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut)
    ).

% L∧ : Conjunction elimination
fitch_g4_proof(land((Premisses > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    select((A & B), Premisses, _),
   % member(ConjLine:(A & B), Context), ligne corrigée par la suivante
    find_context_line((A & B), Context, ConjLine),
    ( is_direct_conjunct(Goal, (A & B)) ->
        derive_formula(Scope, Goal, '$ \\land E $ ~w', [ConjLine], land(ConjLine),
                      CurLine, NextLine, ResLine, VarIn, VarOut)
    ;
        extract_conjuncts((A & B), ConjLine, Scope, CurLine, ExtCtx, LastLine, VarIn, V1),
        append(ExtCtx, Context, NewCtx),
        fitch_g4_proof(SubProof, NewCtx, Scope, LastLine, NextLine, ResLine, V1, VarOut)
    ).

% L⊥ : Explosion
fitch_g4_proof(lbot((Premisss > [Goal]), _), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    member(#, Premisss),
    member(FalseLine: #, Context),
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, Goal, lbot(FalseLine), Scope),
    format(atom(Just), '$ \\bot E $ ~w', [FalseLine]),
    render_have(Scope, Goal, Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% R∨ : Disjunction introduction
fitch_g4_proof(ror((_ > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    ( Goal = (_ | _), try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) ->
        true
    ; fitch_g4_proof(SubProof, Context, Scope, CurLine, SubEnd, DisjunctLine, VarIn, V1),
      OrLine is SubEnd + 1,
      assert_safe_fitch_line(OrLine, Goal, ror(DisjunctLine), Scope),
      format(atom(Just), '$ \\lor I $ ~w', [DisjunctLine]),
      render_have(Scope, Goal, Just, SubEnd, OrLine, V1, VarOut),
      NextLine = OrLine,
      ResLine = OrLine
    ).

% =========================================================================
% RÈGLES AVEC HYPOTHÈSES (ASSUME-DISCHARGE)
% =========================================================================

% R→ : Implication introduction
fitch_g4_proof(rcond((_ > [A => B]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    HypLine is CurLine + 1,
    assert_safe_fitch_line(HypLine, A, assumption, Scope),
    render_hypo(Scope, A, 'AS', CurLine, HypLine, VarIn, V1),
    NewScope is Scope + 1,
    fitch_g4_proof(SubProof, [HypLine:A|Context], NewScope, HypLine, SubEnd, GoalLine, V1, V2),
    ImplLine is SubEnd + 1,
    assert_safe_fitch_line(ImplLine, (A => B), rcond(HypLine, GoalLine), Scope),
    format(atom(Just), '$ \\to I $ ~w-~w', [HypLine, GoalLine]),
    render_have(Scope, (A => B), Just, SubEnd, ImplLine, V2, VarOut),
    NextLine = ImplLine,
    ResLine = ImplLine.

% TNE : Triple negation elimination
fitch_g4_proof(tne((_ > [(A => B)]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    HypLine is CurLine + 1,
    assert_safe_fitch_line(HypLine, A, assumption, Scope),
    render_hypo(Scope, A, 'AS', CurLine, HypLine, VarIn, V1),
    NewScope is Scope + 1,
    fitch_g4_proof(SubProof, [HypLine:A|Context], NewScope, HypLine, SubEnd, GoalLine, V1, V2),
    ImplLine is SubEnd + 1,
    assert_safe_fitch_line(ImplLine, (A => B), rcond(HypLine, GoalLine), Scope),
    format(atom(Just), '$ \\to I $ ~w-~w', [HypLine, GoalLine]),
    render_have(Scope, (A => B), Just, SubEnd, ImplLine, V2, VarOut),
    NextLine = ImplLine,
    ResLine = ImplLine.

% IP : Indirect proof / Classical
fitch_g4_proof(ip((_ > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    ( Goal = (A => #) ->
        Assumption = ((A => #) => #),
        Rule = 'DNE_m'
    ;
        Assumption = (Goal => #),
        Rule = 'IP'
    ),
    HypLine is CurLine + 1,
    assert_safe_fitch_line(HypLine, Assumption, assumption, Scope),
    render_hypo(Scope, Assumption, 'AS', CurLine, HypLine, VarIn, V1),
    NewScope is Scope + 1,
    fitch_g4_proof(SubProof, [HypLine:Assumption|Context], NewScope, HypLine, SubEnd, BotLine, V1, V2),
    IPLine is SubEnd + 1,
    assert_safe_fitch_line(IPLine, Goal, ip(HypLine, BotLine), Scope),
    format(atom(Just), '~w ~w-~w', [Rule, HypLine, BotLine]),
    render_have(Scope, Goal, Just, SubEnd, IPLine, V2, VarOut),
    NextLine = IPLine,
    ResLine = IPLine.

% L∨ : Disjunction elimination
fitch_g4_proof(lor((Premisss > [Goal]), SP1, SP2), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    ( try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) ->
       true
    ; 
      select((A | B), Premisss, _),
      find_disj_context(A, B, Context, DisjLine),
      AssLineA is CurLine + 1,
      assert_safe_fitch_line(AssLineA, A, assumption, Scope),
      render_hypo(Scope, A, 'AS', CurLine, AssLineA, VarIn, V1),
      NewScope is Scope + 1,
      fitch_g4_proof(SP1, [AssLineA:A|Context], NewScope, AssLineA, EndA, GoalA, V1, V2),
      AssLineB is EndA + 1,
      assert_safe_fitch_line(AssLineB, B, assumption, Scope),
      render_hypo(Scope, B, 'AS', EndA, AssLineB, V2, V3),
      fitch_g4_proof(SP2, [AssLineB:B|Context], NewScope, AssLineB, EndB, GoalB, V3, V4),
      ElimLine is EndB + 1,
      assert_safe_fitch_line(ElimLine, Goal, lor(DisjLine, AssLineA, AssLineB, GoalA, GoalB), Scope),
      format(atom(Just), '$ \\lor E $ ~w,~w-~w,~w-~w', [DisjLine, AssLineA, GoalA, AssLineB, GoalB]),
      render_have(Scope, Goal, Just, EndB, ElimLine, V4, VarOut),
      NextLine = ElimLine,
      ResLine = ElimLine
    ).

% =========================================================================
% RÈGLES BINAIRES
% =========================================================================

% R∧ : Conjunction introduction
fitch_g4_proof(rand((_ > [Goal]), SP1, SP2), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    Goal = (L & _R),
    ( try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) -> true
    ; fitch_g4_proof(SP1, Context, Scope, CurLine, End1, LeftLine, VarIn, V1),
      fitch_g4_proof(SP2, [LeftLine:L|Context], Scope, End1, End2, RightLine, V1, V2),
      derive_formula(Scope, Goal, '$ \\land I $ ~w,~w', [LeftLine, RightLine], rand(LeftLine, RightLine),
                    End2, NextLine, ResLine, V2, VarOut)
    ).

% L→→ : Special G4 rule
fitch_g4_proof(ltoto((Premisses > _), SP1, SP2), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    select(((Ant => Inter) => Cons), Premisses, _),
    find_context_line(((Ant => Inter) => Cons), Context, ComplexLine),
    
    % ÉTAPE 1 : Dériver (Inter => Cons) par L→→
    ExtractLine is CurLine + 1,
    format(atom(ExtractJust), 'L$ \\to \\to $ ~w', [ComplexLine]),
    render_have(Scope, (Inter => Cons), ExtractJust, CurLine, ExtractLine, VarIn, V1),
    assert_safe_fitch_line(ExtractLine, (Inter => Cons), ltoto(ComplexLine), Scope),
    
    % ÉTAPE 2 : Assumer Ant
    AssLine is ExtractLine + 1,
    assert_safe_fitch_line(AssLine, Ant, assumption, Scope),
    render_hypo(Scope, Ant, 'AS', ExtractLine, AssLine, V1, V2),
    NewScope is Scope + 1,
    
    % ÉTAPE 3 : Prouver Inter avec [Ant, (Inter=>Cons) | Context]
    fitch_g4_proof(SP1, [AssLine:Ant, ExtractLine:(Inter => Cons)|Context],
                  NewScope, AssLine, SubEnd, InterLine, V2, V3),
    
    % ÉTAPE 4 : Dériver (Ant => Inter) par →I
    ImpLine is SubEnd + 1,
    assert_safe_fitch_line(ImpLine, (Ant => Inter), rcond(AssLine, InterLine), Scope),
    format(atom(Just1), '$ \\to I $ ~w-~w', [AssLine, InterLine]),
    render_have(Scope, (Ant => Inter), Just1, SubEnd, ImpLine, V3, V4),
    
    % ÉTAPE 5 : Dériver Cons par →E
    MPLine is ImpLine + 1,
    assert_safe_fitch_line(MPLine, Cons, l0cond(ComplexLine, ImpLine), Scope),
    format(atom(Just2), '$ \\to E $ ~w,~w', [ComplexLine, ImpLine]),
    render_have(Scope, Cons, Just2, ImpLine, MPLine, V4, V5),
    
    % ÉTAPE 6 : Continuer avec SP2
    fitch_g4_proof(SP2, [MPLine:Cons, ImpLine:(Ant => Inter), ExtractLine:(Inter => Cons)|Context],
                  Scope, MPLine, NextLine, ResLine, V5, VarOut).
% =========================================================================
% RÈGLES DE QUANTIFICATION
% =========================================================================
% R∀
fitch_g4_proof(rall((_ > [(![Z-X]:A)]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    fitch_g4_proof(SubProof, Context, Scope, CurLine, SubEnd, BodyLine, VarIn, V1),
    derive_formula(Scope, (![Z-X]:A), '$ \\forall I $ ~w', [BodyLine], rall(BodyLine),
                  SubEnd, NextLine, ResLine, V1, VarOut).
% L∀ : Élimination Universelle
fitch_g4_proof(lall((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    extract_new_formula(Premisses > _, SubProof, NewFormula),
    
    % Trouver le quantificateur universel qui génère NewFormula
    (
        % Cas 1: NewFormula est une instance directe d'un universel dans Premisses
        (
            member((![Z-X]:Body), Premisses),
            % Vérifier si Body (avec substitution) donne NewFormula
            strip_annotations_deep(Body, StrippedBody),
            strip_annotations_deep(NewFormula, StrippedNew),
            unifiable(StrippedBody, StrippedNew, _),
            UniversalFormula = (![Z-X]:Body)
        ;
            % Cas 2: Chercher par structure équivalente
            member((![Z-X]:Body), Premisses),
            formulas_equivalent(Body, NewFormula),
            UniversalFormula = (![Z-X]:Body)
        ;
            % Cas 3: Fallback - prendre le premier (comportement actuel)
            select((![Z-X]:Body), Premisses, _),
            UniversalFormula = (![Z-X]:Body)
        )
    ),
    
    find_context_line(UniversalFormula, Context, UnivLine),
    derive_and_continue(Scope, NewFormula, '$ \\forall E $ ~w', [UnivLine], lall(UnivLine),
                       SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut).

% R∃
fitch_g4_proof(rex((_ > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    fitch_g4_proof(SubProof, Context, Scope, CurLine, SubEnd, _WitnessLine, VarIn, V1),
    % ✅ CORRECTION : Référencer SubEnd (la ligne du témoin), pas WitnessLine
    derive_formula(Scope, Goal, '$ \\exists I $ ~w', [SubEnd], rex(SubEnd),
                  SubEnd, NextLine, ResLine, V1, VarOut).
% L∃
fitch_g4_proof(lex((Premisses > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    select((?[Z-X]:Body), Premisses, _),
    find_context_line(?[Z-X]:Body, Context, ExistLine),
    extract_witness(SubProof, Witness),
    ( member(_:Witness, Context) ->
        fitch_g4_proof(SubProof, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut)
    ; WitLine is CurLine + 1,
      NewScope is Scope + 1,
      assert_safe_fitch_line(WitLine, Witness, assumption, NewScope),
      render_hypo(Scope, Witness, 'AS', CurLine, WitLine, VarIn, V1),
      fitch_g4_proof(SubProof, [WitLine:Witness|Context], NewScope, WitLine, SubEnd, _GoalLine, V1, V2),
      ElimLine is SubEnd + 1,
      assert_safe_fitch_line(ElimLine, Goal, lex(ExistLine, WitLine, SubEnd), Scope),
      % ✅ CORRECTION : Référencer SubEnd (dernière ligne de la sous-preuve)
      format(atom(Just), '$ \\exists E $ ~w,~w-~w', [ExistLine, WitLine, SubEnd]),
      render_have(Scope, Goal, Just, SubEnd, ElimLine, V2, VarOut),
      NextLine = ElimLine, ResLine = ElimLine
    ).
% L∃∨ : Combined existential-disjunction 
fitch_g4_proof(lex_lor((_ > [Goal]), SP1, SP2), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    SP1 =.. [_, (Prem1 > _)|_],
    SP2 =.. [_, (Prem2 > _)|_],
    member(WitA, Prem1), contains_skolem(WitA), \+ is_quantified(WitA),
    member(WitB, Prem2), contains_skolem(WitB), \+ is_quantified(WitB),
    WitLine is CurLine + 1,
    render_hypo(Scope, (WitA | WitB), 'AS', CurLine, WitLine, VarIn, V1),
    NewScope is Scope + 1,
    assume_in_scope(WitA, Goal, SP1, [WitLine:(WitA | WitB)|Context],
                   NewScope, WitLine, EndA, GoalA, V1, V2),
    assume_in_scope(WitB, Goal, SP2, [WitLine:(WitA | WitB)|Context],
                   NewScope, EndA, EndB, GoalB, V2, V3),
    DisjElim is EndB + 1,
    CaseAStart is WitLine + 1,
    CaseBStart is EndA + 1,
    format(atom(DisjJust), '$ \\lor E $ ~w,~w-~w,~w-~w',
           [WitLine, CaseAStart, GoalA, CaseBStart, GoalB]),
    render_have(NewScope, Goal, DisjJust, EndB, DisjElim, V3, V4),
    ElimLine is DisjElim + 1,
    format(atom(ExistJust), '$ \\exists E $ ~w-~w', [WitLine, DisjElim]),
    render_have(Scope, Goal, ExistJust, DisjElim, ElimLine, V4, VarOut),
    NextLine = ElimLine, ResLine = ElimLine.

% CQ_c : Classical quantifier conversion
fitch_g4_proof(cq_c((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    extract_new_formula(Premisses, SubProof, NewFormula),
    select((![Z-X]:A) => B, Premisses, _),
    find_context_line((![Z-X]:A) => B, Context, Line),  % ← CORRECTION
    derive_and_continue(Scope, NewFormula, '$ CQ_{c} $ ~w', [Line], cq_c(Line),
                       SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut).

% CQ_m : Minimal quantifier conversion
fitch_g4_proof(cq_m((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    extract_new_formula(Premisses, SubProof, NewFormula),
    select((?[Z-X]:A)=>B, Premisses, _),
    find_context_line((?[Z-X]:A)=>B, Context, Line),  % ← CORRECTION : cherche la bonne ligne
    derive_and_continue(Scope, NewFormula, '$ CQ_{m} $ ~w', [Line], cq_m(Line),
                       SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut).

% =========================================================================
% RÈGLES D'ÉGALITÉ (EQUALITY RULES)
% =========================================================================
% =========================================================================
% RÈGLES D'ÉGALITÉ (EQUALITY RULES) - VERSION CORRIGÉE
% =========================================================================

% Réflexivité
fitch_g4_proof(eq_refl(D), _Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    D = [Goal],
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, Goal, eq_refl, Scope),
    render_have(Scope, Goal, 'Leibniz', CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Symétrie
fitch_g4_proof(eq_sym(_G>D), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    D = [A = B],
    find_context_line(B = A, Context, EqLine),
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, (A = B), eq_sym(EqLine), Scope),
    format(atom(Just), 'Leibniz ~w', [EqLine]),
    render_have(Scope, (A = B), Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Transitivité
fitch_g4_proof(eq_trans(G>D), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    D = [A = C],
    G = [A = B, B = C | _Rest],  % Pattern matching direct
    find_context_line(A = B, Context, Line1),
    find_context_line(B = C, Context, Line2),
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, (A = C), eq_trans(Line1, Line2), Scope),
    format(atom(Just), 'Leibniz ~w,~w', [Line1, Line2]),
    render_have(Scope, (A = C), Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Substitution (Leibniz) - CAS PRINCIPAL
fitch_g4_proof(eq_subst(G>D), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    D = [Goal],
    Goal \= (_ = _),  % Pas une égalité
    
    % Extraire l'égalité et le prédicat de G
    member(A = B, G),
    member(Pred, G),
    Pred \= (_ = _),
    Pred \= (A = B),
    
    % Vérifier que Goal est Pred avec A remplacé par B
    Pred =.. [PredName|Args],
    Goal =.. [PredName|GoalArgs],
    
    % Trouver la position où la substitution a lieu
    nth0(Pos, Args, A),
    nth0(Pos, GoalArgs, B),
    
    % Trouver les numéros de ligne dans le contexte
    find_context_line(A = B, Context, EqLine),
    find_context_line(Pred, Context, PredLine),
    
    !,
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, Goal, eq_subst(EqLine, PredLine), Scope),
    format(atom(Just), 'Leibniz ~w,~w', [EqLine, PredLine]),
    render_have(Scope, Goal, Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Congruence
fitch_g4_proof(eq_cong(_G>D), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    D = [LHS = RHS],
    LHS =.. [F|ArgsL],
    RHS =.. [F|ArgsR],
    find_diff_pos(ArgsL, ArgsR, _Pos, TermL, TermR),
    find_context_line(TermL = TermR, Context, EqLine),
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, (LHS = RHS), eq_cong(EqLine), Scope),
    format(atom(Just), 'Leibniz ~w', [EqLine]),
    render_have(Scope, (LHS = RHS), Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Substitution dans égalité
fitch_g4_proof(eq_subst_eq(G>D), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    D = [Goal_LHS = Goal_RHS],
    member(X = Y, G),
    member(Ctx_LHS = Ctx_RHS, G),
    find_context_line(X = Y, Context, XY_Line),
    find_context_line(Ctx_LHS = Ctx_RHS, Context, Ctx_Line),
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, (Goal_LHS = Goal_RHS), eq_subst_eq(XY_Line, Ctx_Line), Scope),
    format(atom(Just), 'Leibniz ~w,~w', [XY_Line, Ctx_Line]),
    render_have(Scope, (Goal_LHS = Goal_RHS), Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Transitivité en chaîne
fitch_g4_proof(eq_trans_chain(_G>D), _Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    D = [A = C],
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, (A = C), eq_trans_chain, Scope),
    render_have(Scope, (A = C), 'Leibniz', CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.
% =========================================================================
% FALLBACK
% =========================================================================
fitch_g4_proof(UnknownRule, _Context, _Scope, CurLine, CurLine, CurLine, VarIn, VarIn) :-
    format('% WARNING: Unknown rule ~w~n', [UnknownRule]).

/*
% =========================================================================
% HELPERS COMBINATORS
% =========================================================================
% Helper : Enlever TOUTES les annotations (pas juste les quantificateurs)
strip_annotations_deep(@(Term, _), Stripped) :- !, strip_annotations_deep(Term, Stripped).
strip_annotations_deep(![_-X]:Body, ![X]:StrippedBody) :- !, strip_annotations_deep(Body, StrippedBody).
strip_annotations_deep(?[_-X]:Body, ?[X]:StrippedBody) :- !, strip_annotations_deep(Body, StrippedBody).
strip_annotations_deep(A & B, SA & SB) :- !, strip_annotations_deep(A, SA), strip_annotations_deep(B, SB).
strip_annotations_deep(A | B, SA | SB) :- !, strip_annotations_deep(A, SA), strip_annotations_deep(B, SB).
strip_annotations_deep(A => B, SA => SB) :- !, strip_annotations_deep(A, SA), strip_annotations_deep(B, SB).
strip_annotations_deep(A <=> B, SA <=> SB) :- !, strip_annotations_deep(A, SA), strip_annotations_deep(B, SB).
strip_annotations_deep(Term, Term).
% =========================================================================
% HELPERS COMBINATORS
% =========================================================================
derive_and_continue(Scope, Formula, RuleTemplate, Refs, RuleTerm, SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    derive_formula(Scope, Formula, RuleTemplate, Refs, RuleTerm, CurLine, DerivLine, _, VarIn, V1),
    fitch_g4_proof(SubProof, [DerivLine:Formula|Context], Scope, DerivLine, NextLine, ResLine, V1, VarOut).

derive_formula(Scope, Formula, RuleTemplate, Refs, RuleTerm, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    NextLine is CurLine + 1,
    assert_safe_fitch_line(NextLine, Formula, RuleTerm, Scope),
    format(atom(Just), RuleTemplate, Refs),
    render_have(Scope, Formula, Just, CurLine, NextLine, VarIn, VarOut),
    ResLine = NextLine.

assume_in_scope(Assumption, _Goal, SubProof, Context, ParentScope, StartLine, EndLine, GoalLine, VarIn, VarOut) :-
    AssLine is StartLine + 1,
    assert_safe_fitch_line(AssLine, Assumption, assumption, ParentScope),
    render_hypo(ParentScope, Assumption, 'AS', StartLine, AssLine, VarIn, V1),
    NewScope is ParentScope + 1,
    fitch_g4_proof(SubProof, [AssLine:Assumption|Context], NewScope, AssLine, EndLine, GoalLine, V1, VarOut).
% =========================================================================
% EXTRACTION & HELPERS
% =========================================================================
extract_new_formula(CurrentPremisses, SubProof, NewFormula) :-
    SubProof =.. [_Rule|[(SubPremisses > _SubGoal)|_]],
    member(NewFormula, SubPremisses),
    \+ member(NewFormula, CurrentPremisses),
    !.
extract_new_formula(_CurrentPremisses, SubProof, NewFormula) :-
    SubProof =.. [_Rule|[(SubPremisses > _SubGoal)|_]],
    member(NewFormula, SubPremisses),
    \+ is_quantified(NewFormula),
    !.
extract_new_formula(CurrentPremisses, SubProof, _) :-
    format('% ERROR extract_new_formula: No suitable formula found~n', []),
    format('%   CurrentPremisses: ~w~n', [CurrentPremisses]),
    SubProof =.. [Rule|[(SubPremisses > _)|_]],
    format('%   SubProof rule: ~w~n', [Rule]),
    format('%   SubPremisses: ~w~n', [SubPremisses]),
    fail.
% =========================================================================
% FIND_CONTEXT_LINE : Matcher formules dans le contexte
% =========================================================================
% =========================================================================
% PRIORITÉ ABSOLUE : PRÉMISSES (lignes 1-N où N = nombre de prémisses)
% =========================================================================

find_context_line(Formula, Context, LineNumber) :-
    premiss_list(PremList),
    length(PremList, NumPremises),
    % Chercher UNIQUEMENT dans les N premières lignes
    member(LineNumber:ContextFormula, Context),
    LineNumber =< NumPremises,
    % Matcher avec les différentes variantes possibles
    ( ContextFormula = Formula
    ; strip_annotations_match(Formula, ContextFormula)
    ; formulas_equivalent(Formula, ContextFormula)
    ),
    !.  % Couper dès qu'on trouve dans les prémisses

% =========================================================================
% PRIORITÉ -1 : NÉGATION DE QUANTIFICATEUR (forme originale ~)
% =========================================================================

% Cherche (![x-x]:Body) => # mais contexte a ~![x]:Body (forme originale)
find_context_line((![_Z-_X]:Body) => #, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        % Forme originale avec ~
        ContextFormula = (~ ![_]:Body)
    ;
        % Forme transformée
        ContextFormula = ((![_]:Body) => #)
    ;
        % Forme transformée avec annotation
        ContextFormula = ((![_-_]:Body) => #)
    ),
    !.

% Même chose pour l'existentiel
find_context_line((?[_Z-_X]:Body) => #, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        ContextFormula = (~ ?[_]:Body)
    ;
        ContextFormula = ((?[_]:Body) => #)
    ;
        ContextFormula = ((?[_-_]:Body) => #)
    ),
    !.
% =========================================================================
% PRIORITÉ 0 : QUANTIFICATEURS - MATCHER STRUCTURE INTERNE COMPLEXE
% =========================================================================
% Universel : matcher structure interne indépendamment de la transformation
find_context_line(![Z-_]:SearchBody, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        % Cas 1: Contexte sans annotation
        ContextFormula = (![Z]:ContextBody),
        formulas_equivalent(SearchBody, ContextBody)
    ;
        % Cas 2: Contexte avec annotation
        ContextFormula = (![Z-_]:ContextBody),
        formulas_equivalent(SearchBody, ContextBody)
    ),
    !.

% Existentiel : matcher structure interne
find_context_line(?[Z-_]:SearchBody, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        ContextFormula = (?[Z]:ContextBody),
        formulas_equivalent(SearchBody, ContextBody)
    ;
        ContextFormula = (?[Z-_]:ContextBody),
        formulas_equivalent(SearchBody, ContextBody)
    ),
    !.

% ─────────────────────────────────────────────────────────────────────────
% PRIORITÉ 1 : NÉGATIONS (notation originale ~ vs transformée => #)
% ─────────────────────────────────────────────────────────────────────────

% Cas 1: Cherche ?[x]:A => # mais contexte a ~ ?[x]:A
find_context_line((?[Z-_]:A) => #, Context, LineNumber) :-
    member(LineNumber:(~ ?[Z]:A), Context), !.

% Cas 2: Cherche ![x]:(A => #) mais contexte a ![x]: ~A
find_context_line(![Z-_]:(A => #), Context, LineNumber) :-
    member(LineNumber:(![Z]: ~A), Context), !.

% Cas 3: Cherche A => # mais contexte a ~A (formule simple)
find_context_line(A => #, Context, LineNumber) :-
    A \= (?[_]:_),
    A \= (![_]:_),
    member(LineNumber:(~A), Context), !.

% ─────────────────────────────────────────────────────────────────────────
% PRIORITÉ 2 : QUANTIFICATEURS (avec/sans annotations de variables)
% ─────────────────────────────────────────────────────────────────────────

% Universel : cherche ![x-x]:Body mais contexte a ![x]:Body
find_context_line(![Z-_]:Body, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        ContextFormula = (![Z]:Body)      % Sans annotation
    ;
        ContextFormula = (![Z-_]:Body)    % Avec annotation différente
    ),
    !.

% Existentiel : cherche ?[x-x]:Body mais contexte a ?[x]:Body
find_context_line(?[Z-_]:Body, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        ContextFormula = (?[Z]:Body)      % Sans annotation
    ;
        ContextFormula = (?[Z-_]:Body)    % Avec annotation différente
    ),
    !.

% ─────────────────────────────────────────────────────────────────────────
% PRIORITÉ 3 : BICONDITIONNELLES (décomposées)
% ─────────────────────────────────────────────────────────────────────────

find_context_line((A => B) & (B => A), Context, LineNumber) :-
    member(LineNumber:(A <=> B), Context), !.

find_context_line((B => A) & (A => B), Context, LineNumber) :-
    member(LineNumber:(A <=> B), Context), !.

% ─────────────────────────────────────────────────────────────────────────
% PRIORITÉ 4 : MATCH EXACT
% ─────────────────────────────────────────────────────────────────────────

find_context_line(Formula, Context, LineNumber) :-
    member(LineNumber:Formula, Context), !.

% ─────────────────────────────────────────────────────────────────────────
% PRIORITÉ 5 : UNIFICATION
% ─────────────────────────────────────────────────────────────────────────

find_context_line(Formula, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    unify_with_occurs_check(Formula, ContextFormula), !.

% ─────────────────────────────────────────────────────────────────────────
% PRIORITÉ 6 : STRUCTURE MATCHING
% ─────────────────────────────────────────────────────────────────────────

find_context_line(Formula, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    match_formula_structure(Formula, ContextFormula), !.

% ─────────────────────────────────────────────────────────────────────────
% FALLBACK : WARNING si aucune correspondance
% ─────────────────────────────────────────────────────────────────────────

find_context_line(Formula, _Context, 0) :-
    format('% WARNING: Formula ~w not found in context~n', [Formula]).

% =========================================================================
% HELPER : Équivalence de formules (comparaison structurelle pure)
% =========================================================================

% Helper : matcher en enlevant les annotations
strip_annotations_match(![_-X]:Body, ![X]:Body) :- !.
strip_annotations_match(![X]:Body, ![_-X]:Body) :- !.
strip_annotations_match(?[_-X]:Body, ?[X]:Body) :- !.
strip_annotations_match(?[X]:Body, ?[_-X]:Body) :- !.
strip_annotations_match(A, B) :- A = B.


% Biconditionnelle : matcher structure sans regarder l'ordre
formulas_equivalent((A1 => B1) & (B2 => A2), C <=> D) :- 
    !,
    (
        (formulas_equivalent(A1, C), formulas_equivalent(A2, C),
         formulas_equivalent(B1, D), formulas_equivalent(B2, D))
    ;
        (formulas_equivalent(A1, D), formulas_equivalent(A2, D),
         formulas_equivalent(B1, C), formulas_equivalent(B2, C))
    ).

formulas_equivalent(A <=> B, (C => D) & (D2 => C2)) :- 
    !,
    (
        (formulas_equivalent(A, C), formulas_equivalent(A, C2),
         formulas_equivalent(B, D), formulas_equivalent(B, D2))
    ;
        (formulas_equivalent(A, D), formulas_equivalent(A, D2),
         formulas_equivalent(B, C), formulas_equivalent(B, C2))
    ).

formulas_equivalent((A <=> B), (C <=> D)) :- 
    !,
    (
        (formulas_equivalent(A, C), formulas_equivalent(B, D))
    ;
        (formulas_equivalent(A, D), formulas_equivalent(B, C))
    ).

% Négation transformée
formulas_equivalent(A => #, ~ B) :- !, formulas_equivalent(A, B).
formulas_equivalent(~ A, B => #) :- !, formulas_equivalent(A, B).

% Quantificateurs : comparer corps uniquement (ignorer variable)
formulas_equivalent(![_]:Body1, ![_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(![_-_]:Body1, ![_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(![_]:Body1, ![_-_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(![_-_]:Body1, ![_-_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).

formulas_equivalent(?[_]:Body1, ?[_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(?[_-_]:Body1, ?[_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(?[_]:Body1, ?[_-_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).
formulas_equivalent(?[_-_]:Body1, ?[_-_]:Body2) :- 
    !, formulas_equivalent(Body1, Body2).

% Connecteurs binaires
formulas_equivalent(A & B, C & D) :- 
    !, formulas_equivalent(A, C), formulas_equivalent(B, D).
formulas_equivalent(A | B, C | D) :- 
    !, formulas_equivalent(A, C), formulas_equivalent(B, D).
formulas_equivalent(A => B, C => D) :- 
    !, formulas_equivalent(A, C), formulas_equivalent(B, D).

% Faux
formulas_equivalent(#, #) :- !.

% Prédicats/Termes : comparer structure (ignorer variables)
formulas_equivalent(Term1, Term2) :-
    compound(Term1),
    compound(Term2),
    !,
    Term1 =.. [Functor|_Args1],
    Term2 =.. [Functor|_Args2],
    % Même foncteur suffit (on ignore les arguments qui sont des variables)
    !.

% Identité stricte
formulas_equivalent(A, B) :- A == B, !.

% Fallback : termes atomiques avec même nom
formulas_equivalent(A, B) :- 
    atomic(A), atomic(B),
    !.

% Helper : matcher deux formules par structure (module renommage de variables)
% Négations
match_formula_structure(A => #, B => #) :- 
    !, match_formula_structure(A, B).
match_formula_structure(~A, B => #) :- 
    !, match_formula_structure(A, B).
match_formula_structure(A => #, ~ B) :- 
    !, match_formula_structure(A, B).
match_formula_structure(~ A, ~ B) :- 
    !, match_formula_structure(A, B).

% Quantificateurs
match_formula_structure(![_-_]:Body1, ![_-_]:Body2) :-
    !, match_formula_structure(Body1, Body2).
match_formula_structure(?[_-_]:Body1, ?[_-_]:Body2) :-
    !, match_formula_structure(Body1, Body2).

% Connecteurs binaires
match_formula_structure(A & B, C & D) :-
    !, match_formula_structure(A, C), match_formula_structure(B, D).
match_formula_structure(A | B, C | D) :-
    !, match_formula_structure(A, C), match_formula_structure(B, D).
match_formula_structure(A => B, C => D) :-
    !, match_formula_structure(A, C), match_formula_structure(B, D).
match_formula_structure(A <=> B, C <=> D) :-
    !, match_formula_structure(A, C), match_formula_structure(B, D).

% Faux
match_formula_structure(#, #) :- !.

% Égalité stricte
match_formula_structure(A, B) :-
    A == B, !.

% Subsomption
match_formula_structure(A, B) :-
    subsumes_term(A, B) ; subsumes_term(B, A).


find_disj_context(L, R, Context, Line) :-
    ( member(Line:(CL | CR), Context), subsumes_term((L | R), (CL | CR)) -> true
    ; member(Line:(CL | CR), Context), \+ \+ ((L = CL, R = CR))
    ).

extract_witness(SubProof, Witness) :-
    SubProof =.. [Rule|Args],
    Args = [(Prem > _)|_],
    ( member(Witness, Prem), contains_skolem(Witness), ( Rule = rall ; Rule = lall ; \+ is_quantified(Witness) ) ), !.
extract_witness(SubProof, Witness) :-
    SubProof =.. [_, (_ > _), SubSP|_],
    extract_witness(SubSP, Witness).

is_quantified(![_-_]:_) :- !.
is_quantified(?[_-_]:_) :- !.

contains_skolem(Formula) :-
    Formula =.. [_|Args],
    member(Arg, Args),
    (Arg = f_sk(_,_) ; compound(Arg), contains_skolem(Arg)).

is_direct_conjunct(G, (A & B)) :- (G = A ; G = B), !.
is_direct_conjunct(G, (A & R)) :- (G = A ; is_direct_conjunct(G, R)).

extract_conjuncts((A & B), CLine, Scope, CurLine, [L1:A, L2:B], L2, VarIn, VarOut) :-
    L1 is CurLine + 1,
    L2 is CurLine + 2,
    assert_safe_fitch_line(L1, A, land(CLine), Scope),
    assert_safe_fitch_line(L2, B, land(CLine), Scope),
    format(atom(Just1), '$ \\land E $ ~w', [CLine]),
    format(atom(Just2), '$ \\land E $ ~w', [CLine]),
    render_have(Scope, A, Just1, CurLine, L1, VarIn, V1),
    render_have(Scope, B, Just2, L1, L2, V1, VarOut).
% =========================================================================
% LOGIQUE DE DÉRIVATION IMMÉDIATE
% =========================================================================
derive_immediate(Scope, Formula, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, Formula, RuleTerm, Scope),
    format(atom(Just), JustFormat, JustArgs),
    render_have(Scope, Formula, Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

try_derive_immediately(Goal, Context, _Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    member(ResLine:Goal, Context),
    !,
    NextLine = CurLine,
    VarOut = VarIn.

try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    member(MajLine:(Ant => Goal), Context),
    member(MinLine:Ant, Context),
    !,
    RuleTerm = l0cond(MajLine, MinLine),
    JustFormat = '$ \\to E $ ~w,~w',
    JustArgs = [MajLine, MinLine],
    derive_immediate(Scope, Goal, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut).

try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    member(ConjLine:(A & B), Context),
    (Goal = A ; Goal = B),
    !,
    RuleTerm = land(ConjLine),
    JustFormat = '$ \\land E $ ~w',
    JustArgs = [ConjLine],
    derive_immediate(Scope, Goal, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut).

try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    member(FLine: #, Context),
    !,
    RuleTerm = lbot(FLine),
    JustFormat = '$ \\bot E $ ~w',
    JustArgs = [FLine],
    derive_immediate(Scope, Goal, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut).

try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    Goal = (L | R),
    ( member(SLine:L, Context) -> true ; member(SLine:R, Context) ),
    !,
    RuleTerm = ror(SLine),
    JustFormat = '$ \\lor I $ ~w',
    JustArgs = [SLine],
    derive_immediate(Scope, Goal, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut).

try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    Goal = (L & R),
    member(LLine:L, Context),
    member(RLine:R, Context),
    !,
    RuleTerm = rand(LLine, RLine),
    JustFormat = '$ \\land I $ ~w,~w',
    JustArgs = [LLine, RLine],
    derive_immediate(Scope, Goal, RuleTerm, JustFormat, JustArgs, CurLine, NextLine, ResLine, VarIn, VarOut).

% =========================================================================
% CONSTRUCTION DE LA MAP DES HYPOTHÈSES PARTAGÉES
% =========================================================================

build_hypothesis_map([], Map, Map).
build_hypothesis_map([N-Formula-assumption-Scope|Rest], AccMap, FinalMap) :-
    !,
    ( member(M-Formula-assumption-Scope, Rest), M > N ->
        build_hypothesis_map(Rest, [M-N|AccMap], FinalMap)
    ;
        build_hypothesis_map(Rest, AccMap, FinalMap)
    ).
build_hypothesis_map([_|Rest], AccMap, FinalMap) :-
    build_hypothesis_map(Rest, AccMap, FinalMap).

% =========================================================================
% FIN
% =========================================================================
*/
