% =========================================================================
% TEST FILE: Simple FOF problems with axioms + conjecture
% =========================================================================

% -------------------------------------------------------------------------
% Problem 1: Socrates syllogism (classic first-order reasoning)
% -------------------------------------------------------------------------
fof(humans_are_mortal, axiom, ![X]: (human(X) => mortal(X))).
fof(socrates_is_human, axiom, human(socrates)).
fof(socrates_is_mortal, conjecture, mortal(socrates)).

% -------------------------------------------------------------------------
% Problem 2: Transitivity (simple relational reasoning)
% -------------------------------------------------------------------------
fof(transitivity, axiom, ![X,Y,Z]: ((r(X,Y) & r(Y,Z)) => r(X,Z))).
fof(r_ab, axiom, r(a,b)).
fof(r_bc, axiom, r(b,c)).
fof(r_ac, conjecture, r(a,c)).

% -------------------------------------------------------------------------
% Problem 3: Function composition
% -------------------------------------------------------------------------
fof(f_preserves_p, axiom, ![X]: (p(X) => p(f(X)))).
fof(p_a, axiom, p(a)).
fof(p_f_f_a, conjecture, p(f(f(a)))).
