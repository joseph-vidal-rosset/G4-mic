% Example TPTP problem file for G4+ testing
% Simple example with equality

% Axiom: There exists a unique object satisfying g
fof(axiom1, axiom,
    ?[X]: ![Y]: ((Y = X) <=> g(Y))
).

% Conjecture: If everything is f, then there exists something that is both g and f
fof(conjecture1, conjecture,
    (![X]: f(X)) => (?[X]: (g(X) & f(X)))
).
