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
prove(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, ax(Gamma>Delta, ax)) :-
    member(A, Gamma),
    A\=(_&_),
    A\=(_|_),
    A\=(_=>_),
    A\=(!_),
    A\=(?_),
    Delta = [B],
    unify_with_occurs_check(A, B).
% 0.1 L-bot
prove(Gamma>Delta, _, _, SkolemIn, SkolemIn, LogicLevel, lbot(Gamma>Delta, #)) :-
    member(LogicLevel, [intuitionistic, classical]),
    member(#, Gamma), !.
% =========================================================================
%  PROPOSITIONAL RULES
% =========================================================================
% 1. L&
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, land(Gamma>Delta,P)) :-
    select((A&B),Gamma,G1), !,
    prove([A,B|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).
% 2. L0->  
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, l0cond(Gamma>Delta,P)) :-
    select((A=>B),Gamma,G1),
    member(A,G1), !,
    prove([B|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).
% 2. L&->
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, landto(Gamma>Delta,P)) :-
    select(((A&B)=>C),Gamma,G1), !,
    prove([(A=>(B => C))|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).
% 3. TNE : Odd Negation Elimination
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, tne(Gamma>Delta, P)) :-
    Delta = [(A => B)],  % Goal: not-A
    % Search in Gamma for a formula with more negations
    member(LongNeg, Gamma),
    % Verify that LongNeg = not^n(not-A) with n >= 2 (so total >= 3)
    is_nested_negation(LongNeg, A => B, Depth),
    Depth >= 2,  % At least 2 more negations than the goal
    !,
    prove([A|Gamma]>[B], FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).
% 7. IP (Indirect Proof - THE classical law). 
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, classical, ip(Gamma>Delta, P)) :-
    Delta = [A],  % Any goal A (not just bottom)
    A \= #,   % Not already bottom
    \+ member((A => #), Gamma),  % not-A not already in context
    Threshold > 0,
    prove([(A => #)|Gamma]>[#], FreeVars, Threshold, SkolemIn, SkolemOut, classical, P).
% 4. Lv-> (OPTIMIZED)
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, lorto(Gamma>Delta,P)) :-
    select(((A|B)=>C),Gamma,G1), !,
    % Check which disjuncts are present
    ( member(A, G1), member(B, G1) ->
        % Both present: keep both (rare case)
        prove([A=>C,B=>C|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ; member(A, G1) ->
        % Only A present: keep only A=>C
        prove([A=>C|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ; member(B, G1) ->
        % Only B present: keep only B=>C
        prove([B=>C|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ;
        % Neither present: keep both (default behavior)
        prove([A=>C,B=>C|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ).
% 5. Lv (fallback for all logics including minimal)
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, lor(Gamma>Delta, P1,P2)) :-
    select((A|B),Gamma,G1), !,
    prove([A|G1]>Delta, FreeVars, Threshold, SkolemIn, J1, LogicLevel, P1),
    prove([B|G1]>Delta, FreeVars, Threshold, J1, SkolemOut, LogicLevel, P2).
% 13. R-forall - with global eigenvariable registry
prove(Gamma > Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, rall(Gamma>Delta, P)) :-
    select((![_Z-X]:A), Delta, D1), !,
    copy_term((X:A,FreeVars), (f_sk(SkolemIn,FreeVars):A1,FreeVars)),
    % CHECK: f_sk must not be identical to any previously used eigenvariable
    (nb_current(g4_eigenvars, UsedVars) -> true ; UsedVars = []),
    \+ member_check(f_sk(SkolemIn,FreeVars), UsedVars),
    % Register this eigenvariable
    nb_setval(g4_eigenvars, [f_sk(SkolemIn,FreeVars)|UsedVars]),
    J1 is SkolemIn+1,
    prove(Gamma > [A1|D1], FreeVars, Threshold, J1, SkolemOut, LogicLevel, P).
% 14. L-forall - WITH OTTEN's LIMITATION
prove(Gamma > Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, lall(Gamma>Delta, P)) :-
    member((![_Z-X]:A), Gamma),
    % OTTEN's CHECK: prevent infinite instantiation when threshold is reached
    \+ length(FreeVars, Threshold),
    copy_term((X:A,FreeVars), (Y:A1,FreeVars)),
    prove([A1|Gamma] > Delta, [Y|FreeVars], Threshold, SkolemIn, SkolemOut, LogicLevel, P), !.
% 8. R-> 
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, rcond(Gamma>Delta,P)) :-
    Delta = [A=>B], !,
    prove([A|Gamma]>[B], FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).
% 6. L->-> 
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, ltoto(Gamma>Delta,P1,P2)) :-
    select(((A=>B)=>C),Gamma,G1), !,
    prove([A,(B=>C)|G1]>[B], FreeVars, Threshold, SkolemIn, _J1, LogicLevel, P1),
    prove([C|G1]> Delta, FreeVars, Threshold, _K1, SkolemOut, LogicLevel, P2).
% 9 LvExists  (Quantification Rule Exception: must be *before* Rv)
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, lex_lor(Gamma>Delta, P1, P2)) :-
    select((?[_Z-X]:(A|B)), Gamma, G1), !,
    copy_term((X:(A|B),FreeVars), (f_sk(SkolemIn,FreeVars):(A1|B1),FreeVars)),
    J1 is SkolemIn+1,
    prove([A1|G1]>Delta, FreeVars, Threshold, J1, J2, LogicLevel, P1),
    prove([B1|G1]>Delta, FreeVars, Threshold, J2, SkolemOut, LogicLevel, P2).
% 10. R? 
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, ror(Gamma>Delta, P)) :-
    Delta = [(A|B)], !,
    (   prove(Gamma>[A], FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ;   prove(Gamma>[B], FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P)
    ).
% 11. R-and : Right conjunction
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, rand(Gamma>Delta,P1,P2)) :-
    Delta = [(A&B)], !,
    prove(Gamma>[A], FreeVars, Threshold, SkolemIn, J1, LogicLevel, P1),
    prove(Gamma>[B], FreeVars, Threshold, J1, SkolemOut, LogicLevel, P2).
 % 12. L-exists - with global eigenvariable registry
prove(Gamma > Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, lex(Gamma>Delta, P)) :-
    select((?[_Z-X]:A), Gamma, G1), !,
    % Auto-initialize on first call
    (SkolemIn =:= 1, \+ nb_current(g4_eigenvars, _) -> init_eigenvars ; true),
    copy_term((X:A,FreeVars), (f_sk(SkolemIn,FreeVars):A1,FreeVars)),
    % CHECK: f_sk must not be identical to any previously used eigenvariable
    (nb_current(g4_eigenvars, UsedVars) -> true ; UsedVars = []),
    \+ member_check(f_sk(SkolemIn,FreeVars), UsedVars),
    % Register this eigenvariable
    nb_setval(g4_eigenvars, [f_sk(SkolemIn,FreeVars)|UsedVars]),
    J1 is SkolemIn+1,
    prove([A1|G1] > Delta, FreeVars, Threshold, J1, SkolemOut, LogicLevel, P).
% 15. R-exists 
prove(Gamma > Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, rex(Gamma>Delta, P)) :-
    select((?[_Z-X]:A), Delta, D1), !,
    length(FreeVars, Len), Len < Threshold,  
    copy_term((X:A,FreeVars), (Y:A1,FreeVars)),
    prove(Gamma > [A1|D1], [Y|FreeVars], Threshold, SkolemIn, SkolemOut, LogicLevel, P), !.
% 16. CQ_c - Classical rule
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, classical, cq_c(Gamma>Delta,P)) :-
    select((![Z-X]:A) => B, Gamma, G1),
    
    % Search for (exists?:?) => B in G1
    ( member((?[ZTarget-YTarget]:ATarget) => B, G1),
      % Compare (A => B) with ATarget
      \+ \+ ((A => B) = ATarget) ->
        % Unifiable: use YTarget
        prove([?[ZTarget-YTarget]:ATarget|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, classical, P)
    ;
        % Otherwise: normal case with X
        prove([?[Z-X]:(A => B)|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, classical, P)
    ).
% 17. CQ_m - Minimal rule (minimal and intuitionistic ONLY, last resort)
% IMPORTANT: EXCLUDED from classical logic (IP + standard rules suffice)
prove(Gamma>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, cq_m(Gamma>Delta,P)) :-
    member(LogicLevel, [minimal, intuitionistic]),
    select((?[Z-X]:A)=>B, Gamma, G1),
    prove([![Z-X]:(A=>B)|G1]>Delta, FreeVars, Threshold, SkolemIn, SkolemOut, LogicLevel, P).
% =========================================================================
% EQUALITY RULES
% =========================================================================
% REFLEXIVITY: |- t = t
prove(_Gamma > Delta, _, _, SkolemIn, SkolemIn, _, eq_refl(Delta)) :-
    Delta = [T = T],
    ground(T),
    !.

% SYMMETRY: t = u |- u = t  
prove(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, eq_sym(Gamma>Delta)) :-
    Delta = [A = B],
    member(B = A, Gamma),
    !.

% SIMPLE TRANSITIVITY: t = u, u = v |- t = v
prove(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, eq_trans(Gamma>Delta)) :-
    Delta = [A = C],
    A \== C,
    (   (member(A = B, Gamma), member(B = C, Gamma))
    ;   (member(B = A, Gamma), member(B = C, Gamma))
    ;   (member(A = B, Gamma), member(C = B, Gamma))
    ;   (member(B = A, Gamma), member(C = B, Gamma))
    ),
    !.

% CHAINED TRANSITIVITY: a=b, b=c, c=d |- a=d
prove(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, eq_trans_chain(Gamma>Delta)) :-
    Delta = [A = C],
    A \== C,
    \+ member(A = C, Gamma),
    \+ member(C = A, Gamma),
    find_equality_path(A, C, Gamma, [A], _Path),
    !.

% CONGRUENCE: t = u |- f(t) = f(u)
prove(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, eq_cong(Gamma>Delta)) :-
    Delta = [LHS = RHS],
    LHS =.. [F|ArgsL],
    RHS =.. [F|ArgsR],
    length(ArgsL, N),
    length(ArgsR, N),
    N > 0,
    find_diff_pos(ArgsL, ArgsR, _Pos, TermL, TermR),
    (member(TermL = TermR, Gamma) ; member(TermR = TermL, Gamma)),
    !.

% SUBSTITUTION IN EQUALITY: x=y, f(x)=z |- f(y)=z
prove(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, eq_subst_eq(Gamma>Delta)) :-
    Delta = [Goal_LHS = Goal_RHS],
    member(Ctx_LHS = Ctx_RHS, Gamma),
    Ctx_LHS \== Goal_LHS,
    member(X = Y, Gamma),
    X \== Y,
    (
        (substitute_in_term(X, Y, Ctx_LHS, Goal_LHS), Ctx_RHS == Goal_RHS)
    ;   (substitute_in_term(Y, X, Ctx_LHS, Goal_LHS), Ctx_RHS == Goal_RHS)
    ;   (substitute_in_term(X, Y, Ctx_RHS, Goal_RHS), Ctx_LHS == Goal_LHS)
    ;   (substitute_in_term(Y, X, Ctx_RHS, Goal_RHS), Ctx_LHS == Goal_LHS)
    ),
    !.

% SUBSTITUTION (Leibniz): t = u, P(t) |- P(u)
prove(Gamma > Delta, _, _, SkolemIn, SkolemIn, _, eq_subst(Gamma>Delta)) :-
    Delta = [Goal],
    Goal \= (_ = _),
    Goal \= (_ => _),
    Goal \= (_ & _),
    Goal \= (_ | _),
    Goal \= (!_),
    Goal \= (?_),
    member(A = B, Gamma),
    member(Pred, Gamma),
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
% EIGENVARIABLE REGISTRY (using nb_setval)
% =========================================================================
% Initialize eigenvariable registry (call before each proof attempt)
init_eigenvars :- nb_setval(g4_eigenvars, []).

% member_check(Term, List): check if Term is structurally equivalent (=@=) to any member
member_check(Term, List) :-
    member(Elem, List),
    Term =@= Elem,
    !.

% =========================================================================
% END of Prover
% =========================================================================
