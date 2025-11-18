% =========================================================================
% GESTION DES TERMES CYCLIQUES
% =========================================================================
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
% PRIORITE ABSOLUE : PREMISSES (lignes 1-N ou N = nombre de premisses)
% =========================================================================

find_context_line(Formula, Context, LineNumber) :-
    premise_list(PremList),
    length(PremList, NumPremises),
    % Chercher UNIQUEMENT dans les N premieres lignes
    member(LineNumber:ContextFormula, Context),
    LineNumber =< NumPremises,
    % Matcher avec les differentes variantes possibles
    ( ContextFormula = Formula
    ; strip_annotations_match(Formula, ContextFormula)
    ; formulas_equivalent(Formula, ContextFormula)
    ),
    !.  % Couper des qu'on trouve dans les premisses

% =========================================================================
% PRIORITE -1 : NEGATION DE QUANTIFICATEUR (forme originale ~)
% =========================================================================

% Cherche (![x-x]:Body) => # mais contexte a ~![x]:Body (forme originale)
find_context_line((![_Z-_X]:Body) => #, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        % Forme originale avec ~
        ContextFormula = (~ ![_]:Body)
    ;
        % Forme transformee
        ContextFormula = ((![_]:Body) => #)
    ;
        % Forme transformee avec annotation
        ContextFormula = ((![_-_]:Body) => #)
    ),
    !.

% Meme chose pour l'existentiel
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
% PRIORITE 0 : QUANTIFICATEURS - MATCHER STRUCTURE INTERNE COMPLEXE
% =========================================================================
% Universel : matcher structure interne independamment de la transformation
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

% -------------------------------------------------------------------------
% PRIORITE 1 : NEGATIONS (notation originale ~ vs transformee => #)
% -------------------------------------------------------------------------

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

% -------------------------------------------------------------------------
% PRIORITE 2 : QUANTIFICATEURS (avec/sans annotations de variables)
% -------------------------------------------------------------------------

% Universel : cherche ![x-x]:Body mais contexte a ![x]:Body
find_context_line(![Z-_]:Body, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        ContextFormula = (![Z]:Body)      % Sans annotation
    ;
        ContextFormula = (![Z-_]:Body)    % Avec annotation differente
    ),
    !.

% Existentiel : cherche ?[x-x]:Body mais contexte a ?[x]:Body
find_context_line(?[Z-_]:Body, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    (
        ContextFormula = (?[Z]:Body)      % Sans annotation
    ;
        ContextFormula = (?[Z-_]:Body)    % Avec annotation differente
    ),
    !.

% -------------------------------------------------------------------------
% PRIORITE 3 : BICONDITIONNELLES (decomposees)
% -------------------------------------------------------------------------

find_context_line((A => B) & (B => A), Context, LineNumber) :-
    member(LineNumber:(A <=> B), Context), !.

find_context_line((B => A) & (A => B), Context, LineNumber) :-
    member(LineNumber:(A <=> B), Context), !.

% -------------------------------------------------------------------------
% PRIORITE 4 : MATCH EXACT
% -------------------------------------------------------------------------

find_context_line(Formula, Context, LineNumber) :-
    member(LineNumber:Formula, Context), !.

% -------------------------------------------------------------------------
% PRIORITE 5 : UNIFICATION
% -------------------------------------------------------------------------

find_context_line(Formula, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    unify_with_occurs_check(Formula, ContextFormula), !.

% -------------------------------------------------------------------------
% PRIORITE 6 : STRUCTURE MATCHING
% -------------------------------------------------------------------------

find_context_line(Formula, Context, LineNumber) :-
    member(LineNumber:ContextFormula, Context),
    match_formula_structure(Formula, ContextFormula), !.

% -------------------------------------------------------------------------
% FALLBACK : WARNING si aucune correspondance
% -------------------------------------------------------------------------

find_context_line(Formula, _Context, 0) :-
    format('% WARNING: Formula ~w not found in context~n', [Formula]).

% =========================================================================
% HELPER : Equivalence de formules (comparaison structurelle pure)
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

% Negation transformee
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

% Predicats/Termes : comparer structure (ignorer variables)
formulas_equivalent(Term1, Term2) :-
    compound(Term1),
    compound(Term2),
    !,
    Term1 =.. [Functor|_Args1],
    Term2 =.. [Functor|_Args2],
    % Meme foncteur suffit (on ignore les arguments qui sont des variables)
    !.

% Identite stricte
formulas_equivalent(A, B) :- A == B, !.

% Fallback : termes atomiques avec meme nom
formulas_equivalent(A, B) :- 
    atomic(A), atomic(B),
    !.

% Helper : matcher deux formules par structure (module renommage de variables)
% Negations
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

% Egalite stricte
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
% LOGIQUE DE DERIVATION IMMEDIATE
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
% CONSTRUCTION DE LA MAP DES HYPOTHESES PARTAGEES
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
% End of common ND PRINTING
% =========================================================================
