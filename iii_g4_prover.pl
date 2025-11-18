% =========================================================================
% G4 FOL Prover with equality 
% TPTP-version
% =========================================================================
% prove/7 - 
% prove(Sequent, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, Proof)
% LogicLevel: minimal | intuitionistic | classical
%==========================================================================
% AXIOMS
%=========================================================================
% O.0 Ax 
prove(G > D, _, _, J, J, _, ax(G>D, ax)) :-
    member(A, G),
    A\=(_&_),
    A\=(_|_),
    A\=(_=>_),
    A\=(!_),
    A\=(?_),
    D = [B],
    unify_with_occurs_check(A, B).
% 0.1 L-bot
prove(G>D, _, _, J, J, LogicLevel, lbot(G>D, #)) :-
    member(LogicLevel, [intuitionistic, classical]),
    member(#, G), !.
% =========================================================================
%  PROPOSITIONAL RULES
% =========================================================================
% 1. L&
prove(G>D, FV, I, J, K, LogicLevel, land(G>D,P)) :-
    select((A&B),G,G1), !,
    prove([A,B|G1]>D, FV, I, J, K, LogicLevel, P).
% 2. L0->  
prove(G>D, FV, I, J, K, LogicLevel, l0cond(G>D,P)) :-
    select((A=>B),G,G1),
    member(A,G1), !,
    prove([B|G1]>D, FV, I, J, K, LogicLevel, P).
% 2. L&->
prove(G>D, FV, I, J, K, LogicLevel, landto(G>D,P)) :-
    select(((A&B)=>C),G,G1), !,
    prove([(A=>(B => C))|G1]>D, FV, I, J, K, LogicLevel, P).
% 3. TNE : Odd Negation Elimination
prove(G>D, FV, I, J, K, LogicLevel, tne(G>D, P)) :-
    D = [(A => B)],  % Goal: not-A
    % Search in G for a formula with more negations
    member(LongNeg, G),
    % Verify that LongNeg = not^n(not-A) with n >= 2 (so total >= 3)
    is_nested_negation(LongNeg, A => B, Depth),
    Depth >= 2,  % At least 2 more negations than the goal
    !,
    prove([A|G]>[B], FV, I, J, K, LogicLevel, P).
% 7. IP (Indirect Proof - THE classical law). 
prove(G>D, FV, I, J, K, classical, ip(G>D, P)) :-
    D = [A],  % Any goal A (not just bottom)
    A \= #,   % Not already bottom
    \+ member((A => #), G),  % not-A not already in context
    I > 0,
    prove([(A => #)|G]>[#], FV, I, J, K, classical, P).
% 4. Lv-> (OPTIMIZED)
prove(G>D, FV, I, J, K, LogicLevel, lorto(G>D,P)) :-
    select(((A|B)=>C),G,G1), !,
    % Check which disjuncts are present
    ( member(A, G1), member(B, G1) ->
        % Both present: keep both (rare case)
        prove([A=>C,B=>C|G1]>D, FV, I, J, K, LogicLevel, P)
    ; member(A, G1) ->
        % Only A present: keep only A=>C
        prove([A=>C|G1]>D, FV, I, J, K, LogicLevel, P)
    ; member(B, G1) ->
        % Only B present: keep only B=>C
        prove([B=>C|G1]>D, FV, I, J, K, LogicLevel, P)
    ;
        % Neither present: keep both (default behavior)
        prove([A=>C,B=>C|G1]>D, FV, I, J, K, LogicLevel, P)
    ).
% 5. Lv (fallback for all logics including minimal)
prove(G>D, FV, I, J, K, LogicLevel, lor(G>D, P1,P2)) :-
    select((A|B),G,G1), !,
    prove([A|G1]>D, FV, I, J, J1, LogicLevel, P1),
    prove([B|G1]>D, FV, I, J1, K, LogicLevel, P2).
% 13. R-forall 
prove(G > D, FV, I, J, K, LogicLevel, rall(G>D, P)) :-
    select((![_Z-X]:A), D, D1), !,
    copy_term((X:A,FV), (f_sk(J,FV):A1,FV)),
    J1 is J+1,
    prove(G > [A1|D1], FV, I, J1, K, LogicLevel, P).
% 14. L-forall 
prove(G > D, FV, I, J, K, LogicLevel, lall(G>D, P)) :-
    member((![_Z-X]:A), G),
    length(FV, Len), Len < I,  
    copy_term((X:A,FV), (Y:A1,FV)),
    prove([A1|G] > D, [Y|FV], I, J, K, LogicLevel, P), !.
% 8. R-> 
prove(G>D, FV, I, J, K, LogicLevel, rcond(G>D,P)) :-
    D = [A=>B], !,
    prove([A|G]>[B], FV, I, J, K, LogicLevel, P).
% 6. L->-> 
prove(G>D, FV, I, J, K, LogicLevel, ltoto(G>D,P1,P2)) :-
    select(((A=>B)=>C),G,G1), !,
    prove([A,(B=>C)|G1]>[B], FV, I, J, _J1, LogicLevel, P1),
    prove([C|G1]> D, FV, I, _K1, K, LogicLevel, P2).
% 9 LvExists  (Quantification Rule Exception: must be *before* Rv)
prove(G>D, FV, I, J, K, LogicLevel, lex_lor(G>D, P1, P2)) :-
    select((?[_Z-X]:(A|B)), G, G1), !,
    copy_term((X:(A|B),FV), (f_sk(J,FV):(A1|B1),FV)),
    J1 is J+1,
    prove([A1|G1]>D, FV, I, J1, J2, LogicLevel, P1),
    prove([B1|G1]>D, FV, I, J2, K, LogicLevel, P2).
% 10. R? 
prove(G>D, FV, I, J, K, LogicLevel, ror(G>D, P)) :-
    D = [(A|B)], !,
    (   prove(G>[A], FV, I, J, K, LogicLevel, P)
    ;   prove(G>[B], FV, I, J, K, LogicLevel, P)
    ).
% 11. R-and : Right conjunction
prove(G>D, FV, I, J, K, LogicLevel, rand(G>D,P1,P2)) :-
    D = [(A&B)], !,
    prove(G>[A], FV, I, J, J1, LogicLevel, P1),
    prove(G>[B], FV, I, J1, K, LogicLevel, P2).
 % 12. L-exists 
prove(G > D, FV, I, J, K, LogicLevel, lex(G>D, P)) :-
    select((?[_Z-X]:A), G, G1), !,
    copy_term((X:A,FV), (f_sk(J,FV):A1,FV)),
    J1 is J+1,
    prove([A1|G1] > D, FV, I, J1, K, LogicLevel, P).
% 15. R-exists 
prove(G > D, FV, I, J, K, LogicLevel, rex(G>D, P)) :-
    select((?[_Z-X]:A), D, D1), !,
    length(FV, Len), Len < I,  
    copy_term((X:A,FV), (Y:A1,FV)),
    prove(G > [A1|D1], [Y|FV], I, J, K, LogicLevel, P), !.
% 16. CQ_c - Classical rule
prove(G>D, FV, I, J, K, classical, cq_c(G>D,P)) :-
    select((![Z-X]:A) => B, G, G1),
    
    % Search for (exists?:?) => B in G1
    ( member((?[ZTarget-YTarget]:ATarget) => B, G1),
      % Compare (A => B) with ATarget
      \+ \+ ((A => B) = ATarget) ->
        % Unifiable: use YTarget
        prove([?[ZTarget-YTarget]:ATarget|G1]>D, FV, I, J, K, classical, P)
    ;
        % Otherwise: normal case with X
        prove([?[Z-X]:(A => B)|G1]>D, FV, I, J, K, classical, P)
    ).
% 17. CQ_m - Minimal rule (minimal and intuitionistic ONLY, last resort)
% IMPORTANT: EXCLUDED from classical logic (IP + standard rules suffice)
prove(G>D, FV, I, J, K, LogicLevel, cq_m(G>D,P)) :-
    member(LogicLevel, [minimal, intuitionistic]),
    select((?[Z-X]:A)=>B, G, G1),
    prove([![Z-X]:(A=>B)|G1]>D, FV, I, J, K, LogicLevel, P).
% =========================================================================
% EQUALITY RULES
% =========================================================================
% REFLEXIVITY: |- t = t
prove(_G > D, _, _, J, J, _, eq_refl(D)) :-
    D = [T = T],
    ground(T),  % <- Ajouter cette ligne
    !.
% SYMMETRY: t = u |- u = t  
prove(G > D, _, _, J, J, _, eq_sym(G>D)) :-
    D = [A = B],
    member(B = A, G),
    !.
% SIMPLE TRANSITIVITY: t = u, u = v |- t = v
prove(G > D, _, _, J, J, _, eq_trans(G>D)) :-
    D = [A = C],
    A \== C,
    (   (member(A = B, G), member(B = C, G))
    ;   (member(B = A, G), member(B = C, G))
    ;   (member(A = B, G), member(C = B, G))
    ;   (member(B = A, G), member(C = B, G))
    ),
    !.
% CHAINED TRANSITIVITY: a=b, b=c, c=d |- a=d
prove(G > D, _, _, J, J, _, eq_trans_chain(G>D)) :-
    D = [A = C],
    A \== C,
    \+ member(A = C, G),
    \+ member(C = A, G),
    find_equality_path(A, C, G, [A], _Path),
    !.
% CONGRUENCE: t = u |- f(t) = f(u)
prove(G > D, _, _, J, J, _, eq_cong(G>D)) :-
    D = [LHS = RHS],
    LHS =.. [F|ArgsL],
    RHS =.. [F|ArgsR],
    length(ArgsL, N),
    length(ArgsR, N),
    N > 0,
    find_diff_pos(ArgsL, ArgsR, _Pos, TermL, TermR),
    (member(TermL = TermR, G) ; member(TermR = TermL, G)),
    !.
% SUBSTITUTION IN EQUALITY: x=y, f(x)=z |- f(y)=z
prove(G > D, _, _, J, J, _, eq_subst_eq(G>D)) :-
    D = [Goal_LHS = Goal_RHS],
    member(Ctx_LHS = Ctx_RHS, G),
    Ctx_LHS \== Goal_LHS,
    member(X = Y, G),
    X \== Y,
    (
        (substitute_in_term(X, Y, Ctx_LHS, Goal_LHS), Ctx_RHS == Goal_RHS)
    ;   (substitute_in_term(Y, X, Ctx_LHS, Goal_LHS), Ctx_RHS == Goal_RHS)
    ;   (substitute_in_term(X, Y, Ctx_RHS, Goal_RHS), Ctx_LHS == Goal_LHS)
    ;   (substitute_in_term(Y, X, Ctx_RHS, Goal_RHS), Ctx_LHS == Goal_LHS)
    ),
    !.
% SUBSTITUTION (Leibniz): t = u, P(t) |- P(u)
prove(G > D, _, _, J, J, _, eq_subst(G>D)) :-
    D = [Goal],
    Goal \= (_ = _),
    Goal \= (_ => _),
    Goal \= (_ & _),
    Goal \= (_ | _),
    Goal \= (!_),
    Goal \= (?_),
    member(A = B, G),
    member(Pred, G),
    Pred \= (_ = _),
    Pred \= (_ => _),
    Pred \= (_ & _),
    Pred \= (_ | _),
    Pred =.. [PredName|Args],
    Goal =.. [PredName|GoalArgs],
    member_pos(A, Args, Pos),
    nth0(Pos, GoalArgs, B),
    !.
% =========================================================================
% HELPERS
% =========================================================================
% Helper: find position of an element
member_pos(X, [X|_], 0) :- !.
member_pos(X, [_|T], N) :-
    member_pos(X, T, N1),
    N is N1 + 1.

% Helper: substitute Old with New in Term
substitute_in_term(Old, New, Old, New) :- !.
substitute_in_term(Old, New, Term, Result) :-
    compound(Term),
    !,
    Term =.. [F|Args],
    maplist(substitute_in_term(Old, New), Args, NewArgs),
    Result =.. [F|NewArgs].
substitute_in_term(_, _, Term, Term).

% Helper: find position where two lists differ
find_diff_pos([X|_], [Y|_], 0, X, Y) :- X \= Y, !.
find_diff_pos([X|RestL], [X|RestR], Pos, TermL, TermR) :-
    find_diff_pos(RestL, RestR, Pos1, TermL, TermR),
    Pos is Pos1 + 1.

% Helper: find a path (with cycle detection)
find_equality_path(X, X, _, _, [X]) :- !.
find_equality_path(X, Z, Context, Visited, [X|Path]) :-
    (member(X = Y, Context) ; member(Y = X, Context)),
    Y \== X,
    \+ member(Y, Visited),
    find_equality_path(Y, Z, Context, [Y|Visited], Path).

% Helper: verify if Formula = not^n(Target) and return n
is_nested_negation(Target, Target, 0) :- !.
is_nested_negation((Inner => #), Target, N) :-
    is_nested_negation(Inner, Target, N1),
    N is N1 + 1.
% =========================================================================
% END of Prover
% =========================================================================
