% =========================================================================
% G4 FOL Prover with equality
% TPTP-version
% =========================================================================
% =========================================================================
% EIGENVARIABLE REGISTRY (using b_setval for BACKTRACKABLE global state)
% =========================================================================
% Initialize eigenvariable registry (call before each proof attempt)
% Using b_setval for BACKTRACKABLE global variable
init_eigenvars :- b_setval(g4_eigenvars, []).

% member_check(Term, List): check if Term is structurally equivalent (=@=) to any member
member_check(Term, List) :-
    member(Elem, List),
    Term =@= Elem,
    !.

%==========================================================================
% AXIOM - SEPARATE PREDICATE (NOT TABLED)
%==========================================================================
% Must be tested BEFORE any tabled rules to avoid caching non-axiomatic proofs
g4mic_ax(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, ax(Gamma>Delta, ax)) :-
    member(A, Gamma),
    A\=(_&_),
    A\=(_|_),
    A\=(_=>_),
    A\=(!_),
    A\=(?_),
    Delta = [B],
    unify_with_occurs_check(A, B).

% TABLING: Memoization to avoid redundant computations
:- table g4mic_proves/7.

% g4mic_proves/7 -
% g4mic_proves(Sequent, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, Proof)
% LogicLevel: minimal | intuitionistic | classical
%==========================================================================
% Entry point: test axiom FIRST (non-tabled), then other rules (tabled)
%==========================================================================
g4mic_proves(Seq, FV, Th, SI, SO, LL, Proof) :-
    g4mic_ax(Seq, FV, Th, SI, SO, LL, Proof), !.

% 0.1 L-bot
g4mic_proves(Gamma>Delta, _, _, SkolemIn, SkolemIn, LogicLevel, lbot(Gamma>Delta, #)) :-
    member(LogicLevel, [intuitionistic, classical]),
    member(#, Gamma), !.
% =========================================================================
%  PROPOSITIONAL RULES
% =========================================================================
% 1. L&
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, land(Gamma>Delta,P)) :-
    select((A&B),Gamma,G1), !,
    g4mic_proves([A,B|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).
% 2. L0->
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, l0cond(Gamma>Delta,P)) :-
    select((A=>B),Gamma,G1),
    member(A,G1), !,
    g4mic_proves([B|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).

% 2. L&->
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, landto(Gamma>Delta,P)) :-
    select(((A&B)=>C),Gamma,G1), !,
    g4mic_proves([(A=>(B => C))|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).
% 3. TNE : Odd Negation Elimination
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, tne(Gamma>Delta, P)) :-
    Delta = [(A => B)],  % Goal: not-A
    % Search in Gamma for a formula with more negations
    member(LongNeg, Gamma),
    % Verify that LongNeg = not^n(not-A) with n >= 2 (so total >= 3)
    is_nested_negation(LongNeg, A => B, Depth),
    Depth >= 2,  % At least 2 more negations than the goal
    !,
    g4mic_proves([A|Gamma]>[B], FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).
% 7. IP (Indirect Proof - THE classical law).
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, classical, ip(Gamma>Delta, P)) :-
    Delta = [A],  % Any goal A (not just bottom)
    A \= #,   % Not already bottom
    \+ member((A => #), Gamma),  % not-A not already in context
    Threshold > 0,
    g4mic_proves([(A => #)|Gamma]>[#], FreeVars, Threshold, SkolemIn, SkolemOut, classical, P).
% 4. Lv-> (OPTIMIZED)
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, lorto(Gamma>Delta,P)) :-
    select(((A|B)=>C),Gamma,G1), !,
    % Check which disjuncts are present
    ( member(A, G1), member(B, G1) ->
        % Both present: keep both (rare case)
        g4mic_proves([A=>C,B=>C|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ; member(A, G1) ->
        % Only A present: keep only A=>C
        g4mic_proves([A=>C|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ; member(B, G1) ->
        % Only B present: keep only B=>C
        g4mic_proves([B=>C|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ;
        % Neither present: keep both (default behavior)
        g4mic_proves([A=>C,B=>C|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ).
% 5. Lv (fallback for all logics including minimal)
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, lor(Gamma>Delta, P1,P2)) :-
    select((A|B),Gamma,G1), !,
    g4mic_proves([A|G1]>Delta, FreeVars, Threshold, SkolemIn, J1, LogicLevel, P1),
    g4mic_proves([B|G1]>Delta, FreeVars, Threshold, J1, SkolemOut, LogicLevel, P2).
% 13. R-forall - with BACKTRACKABLE global eigenvariable registry
g4mic_proves(Gamma > Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, rall(Gamma>Delta, P)) :-
    select((![_Z-X]:A), Delta, D1), !,
    copy_term((X:A,FreeVars), (f_sk(SkolemIn,FreeVars):A1,FreeVars)),
    % CHECK: f_sk must not be identical to any previously used eigenvariable
    % Using b_getval for backtrackable global variable
    (catch(b_getval(g4_eigenvars, UsedVars), _, UsedVars = [])),
    \+ member_check(f_sk(SkolemIn,FreeVars), UsedVars),
    % Register this eigenvariable (backtrackable)
    b_setval(g4_eigenvars, [f_sk(SkolemIn,FreeVars)|UsedVars]),
    J1 is SkolemIn+1,
    g4mic_proves(Gamma > [A1|D1], FreeVars, Threshold, J1, SkolemOut, LogicLevel, P).
% 14. L-forall - WITH OTTEN's LIMITATION
g4mic_proves(Gamma > Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, lall(Gamma>Delta, P)) :-
    member((![_Z-X]:A), Gamma),
    % OTTEN's CHECK: prevent infinite instantiation when threshold is reached
    % \+ length(FreeVars, Threshold),
    length(FreeVars, Len), Len =< Threshold,
    copy_term((X:A,FreeVars), (Y:A1,FreeVars)),
    g4mic_proves([A1|Gamma] > Delta, [Y|FreeVars], Threshold, SkolemIn, SkolemOut, LogicLevel, P), !.
% 8. R->
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, rcond(Gamma>Delta,P)) :-
    Delta = [A=>B], !,
    g4mic_proves([A|Gamma]>[B], FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).
% 6. L->->
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, ltoto(Gamma>Delta,P1,P2)) :-
    select(((A=>B)=>C),Gamma,G1), !,
    g4mic_proves([A,(B=>C)|G1]>[B], FreeVars, Threshold, SkolemIn, J1, LogicLevel, P1),
    g4mic_proves([C|G1]> Delta, FreeVars, Threshold, J1, SkolemOut, LogicLevel, P2).

% 9 LvExists  (Quantification Rule Exception: must be *before* Rv)
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, lex_lor(Gamma>Delta, P1, P2)) :-
    select((?[_Z-X]:(A|B)), Gamma, G1), !,
    copy_term((X:(A|B),FreeVars), (f_sk(SkolemIn,FreeVars):(A1|B1),FreeVars)),
    J1 is SkolemIn+1,
    g4mic_proves([A1|G1]>Delta, FreeVars, Threshold, J1, J2, LogicLevel, P1),
    g4mic_proves([B1|G1]>Delta, FreeVars, Threshold, J2, SkolemOut, LogicLevel, P2).
% 10. R?
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, ror(Gamma>Delta, P)) :-
    Delta = [(A|B)], !,
    (   g4mic_proves(Gamma>[A], FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ;   g4mic_proves(Gamma>[B], FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ).
% 11. R-and : Right conjunction
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, rand(Gamma>Delta,P1,P2)) :-
    Delta = [(A&B)], !,
    g4mic_proves(Gamma>[A], FreeVars, Threshold, SkolemIn, J1, LogicLevel, P1),
    g4mic_proves(Gamma>[B], FreeVars, Threshold, J1, SkolemOut, LogicLevel, P2).
 % 12. L-exists - with BACKTRACKABLE global eigenvariable registry
g4mic_proves(Gamma > Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, lex(Gamma>Delta, P)) :-
    select((?[_Z-X]:A), Gamma, G1), !,
    % Auto-initialize on first call (check with catch for backtrackable variable)
  %  (SkolemIn =:= 1, catch(b_getval(g4_eigenvars, _), _, true) -> init_eigenvars ; true),
    copy_term((X:A,FreeVars), (f_sk(SkolemIn,FreeVars):A1,FreeVars)),
    % CHECK: f_sk must not be identical to any previously used eigenvariable
    % Using b_getval for backtrackable global variable
    (catch(b_getval(g4_eigenvars, UsedVars), _, UsedVars = [])),
    \+ member_check(f_sk(SkolemIn,FreeVars), UsedVars),
    % Register this eigenvariable (backtrackable)
    b_setval(g4_eigenvars, [f_sk(SkolemIn,FreeVars)|UsedVars]),
    J1 is SkolemIn+1,
    g4mic_proves([A1|G1] > Delta, FreeVars, Threshold, J1, SkolemOut, LogicLevel, P).
% 15. R-exists
g4mic_proves(Gamma > Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, rex(Gamma>Delta, P)) :-
    select((?[_Z-X]:A), Delta, D1), !,
    length(FreeVars, Len), Len < Threshold,
    copy_term((X:A,FreeVars), (Y:A1,FreeVars)),
    g4mic_proves(Gamma > [A1|D1], [Y|FreeVars], Threshold, SkolemIn, SkolemOut, LogicLevel, P), !.
% 16. CQ_c - Classical rule
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, classical, cq_c(Gamma>Delta,P)) :-
    select((![Z-X]:A) => B, Gamma, G1),

    % Search for (exists?:?) => B in G1
    ( member((?[ZTarget-YTarget]:ATarget) => B, G1),
      % Compare (A => B) with ATarget
      \+ \+ ((A => B) = ATarget) ->
        % Unifiable: use YTarget
        g4mic_proves([?[ZTarget-YTarget]:ATarget|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, classical, P)
    ;
        % Otherwise: normal case with X
        g4mic_proves([?[Z-X]:(A => B)|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, classical, P)
    ).
% 17. CQ_m - Quantifier conversion (VALID IN ALL LOGICS)
% Critical rule: (?[X]:A => B) → ![X]:(A => B)
g4mic_proves(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, cq_m(Gamma>Delta,P)) :-
    select((?[Z-X]:A)=>B, Gamma, G1),
    g4mic_proves([![Z-X]:(A=>B)|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).
% =========================================================================
% EQUALITY RULES
% =========================================================================
% REFLEXIVITY: ⊢ t = t (NO GROUND RESTRICTION)
g4mic_proves(_Gamma > Delta, _, _, SkolemIn, SkolemIn, _, eq_refl(Delta)) :-
    Delta = [T = T],
    !.

% SYMMETRY: t = u ⊢ u = t
g4mic_proves(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, eq_sym(Gamma>Delta)) :-
    Delta = [A = B],
    member(B = A, Gamma),
    !.

% TRANSITIVITY: t = u, u = v ⊢ t = v
g4mic_proves(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, eq_trans(Gamma>Delta)) :-
    Delta = [A = C],
    member(A = B, Gamma),
    member(B = C, Gamma),
    !.

% SUBSTITUTION IN PREDICATE (arity 1): t1 = t2, P(t1) ⊢ P(t2)
g4mic_proves(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, eq_subst_pred_1(Gamma>Delta)) :-
    Delta = [Goal],
    Goal \= (_ = _),
    Goal =.. [P, T2],
    P \= (=),
    member(T1 = T2, Gamma),
    Premise =.. [P, T1],
    member(Premise, Gamma),
    !.

% SUBSTITUTION IN PREDICATE (arity 2): P(a1,b1), a1=a2, b1=b2 ⊢ P(a2,b2)
g4mic_proves(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, eq_subst_pred_2(Gamma>Delta)) :-
    Delta = [Goal],
    Goal \= (_ = _),
    Goal =.. [P, A2, B2],
    P \= (=),
    args_equal_in_context([A2, B2], [A1, B1], Gamma),
    Premise =.. [P, A1, B1],
    member(Premise, Gamma),
    !.

% SUBSTITUTION IN PREDICATE (arity 3): P(a1,b1,c1), equalities ⊢ P(a2,b2,c2)
g4mic_proves(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, eq_subst_pred_3(Gamma>Delta)) :-
    Delta = [Goal],
    Goal \= (_ = _),
    Goal =.. [P, A2, B2, C2],
    P \= (=),
    args_equal_in_context([A2, B2, C2], [A1, B1, C1], Gamma),
    Premise =.. [P, A1, B1, C1],
    member(Premise, Gamma),
    !.

% SUBSTITUTION IN FUNCTION (arity 1): arg1 = arg2 ⊢ f(arg1) = f(arg2)
g4mic_proves(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, eq_subst_func_1(Gamma>Delta)) :-
    Delta = [F1 = F2],
    F1 =.. [Func, Arg1],
    F2 =.. [Func, Arg2],
    Func \= (=),
    (member(Arg1 = Arg2, Gamma) ; member(Arg2 = Arg1, Gamma)),
    !.

% SUBSTITUTION IN FUNCTION (arity 2): a1=a2, b1=b2 ⊢ f(a1,b1) = f(a2,b2)
g4mic_proves(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, eq_subst_func_2(Gamma>Delta)) :-
    Delta = [F1 = F2],
    F1 =.. [Func, A1, B1],
    F2 =.. [Func, A2, B2],
    Func \= (=),
    args_equal_in_context([A1, B1], [A2, B2], Gamma),
    !.

% =========================================================================
% HELPER: Verify argument equality in context
% =========================================================================
args_equal_in_context([], [], _).
args_equal_in_context([A|As], [A|Bs], G) :- 
    !, 
    args_equal_in_context(As, Bs, G).
args_equal_in_context([A|As], [B|Bs], G) :-
    (member(A = B, G) ; member(B = A, G)),
    args_equal_in_context(As, Bs, G).

% =========================================================================
% ANTISEQUENT - Only when explicitly enabled by driver (PASS 2)
% =========================================================================
% This clause is ONLY activated after normal proof search fails
% It represents a counter-model when no atom in Gamma is in Delta
% Antisequent with empty Gamma: ⊬ B
g4mic_proves([] > Delta, _, Threshold, SkolemIn, SkolemIn, classical, asq([] < Delta, _)) :-
    nb_current(asq_enabled, true),
    Threshold >= 4,   % DO NOT CHANGE THIS VALUE !
    Delta = [B],
    B \= asq,
    B \= asq(_,_),
    % No restriction on B's form - any invalid formula can generate an antisequent
    !.

% Antisequent with non-empty Gamma: Γ ⊬ B
g4mic_proves(Gamma > Delta, _, Threshold, SkolemIn, SkolemIn, classical, asq(Gamma < Delta, _)) :-
    nb_current(asq_enabled, true),
    Threshold >= 4,         % DO NOT CHANGE THIS VALUE !
    Gamma \= [],  % Gamma non-empty
    Delta = [B],
    B \= asq,
    B \= asq(_,_),
    member(A, Gamma),
    A \= asq,
    A \= asq(_,_),
    % No restriction on A's form - any atom or formula can be in Gamma
    \+ member(A, Delta),
    !.
% =========================================================================
% HELPERS
% =========================================================================
% Helper: verify if Formula = not^n(Target) and return n
is_nested_negation(Target, Target, 0) :- !.
is_nested_negation((Inner => #), Target, N) :-
    is_nested_negation(Inner, Target, N1),
    N is N1 + 1.

% =========================================================================
% END of Prover
% =========================================================================
