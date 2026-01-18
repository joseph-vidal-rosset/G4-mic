% Example TPTP file for G4-mic
% Note: G4-mic uses lowercase-only syntax, so uppercase variables are converted

% Simple propositional test
fof(test_prop, conjecture, p => p).

% First-order with quantifiers (TPTP uppercase vars → G4-mic lowercase)
fof(test_forall, conjecture, ![X]: (p(X) => p(X))).

% Existential quantifier
fof(test_exists, conjecture, p(a) => ?[X]: p(X)).

% Function symbols
fof(test_function, conjecture, ![X]: (p(f(X)) => p(f(X)))).

% Classical logic
fof(test_classical, conjecture, ((p => q) => p) => p).

% More complex FOL
fof(test_complex, conjecture, 
    (![X]: (p(X) => q(X))) & p(a) => q(a)).
