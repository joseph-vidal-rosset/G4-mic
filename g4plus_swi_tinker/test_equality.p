% TPTP test file for equality
% Testing equality axioms and basic properties

% Reflexivity of equality
fof(reflexivity, conjecture, ![X]: (X = X)).

% Symmetry of equality
fof(symmetry, conjecture, ![X, Y]: ((X = Y) => (Y = X))).

% Transitivity of equality
fof(transitivity, conjecture, ![X, Y, Z]: (((X = Y) & (Y = Z)) => (X = Z))).

% Function congruence
fof(function_cong, conjecture, ![X, Y]: ((X = Y) => (f(X) = f(Y)))).

% Simple equality with constant
fof(simple_constant, conjecture, a = a).
