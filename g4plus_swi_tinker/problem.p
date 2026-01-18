% Axiom: There exists an X such that for all Y, Y=X iff g(Y)
   fof(axiom1, axiom,
       ?[X]: ![Y]: ((Y = X) <=> g(Y))
       ).

   % Conjecture: If everything is f, then there exists something that is both g and f
      fof(conjecture1, conjecture,
          (![X]: f(X)) => (?[X]: (g(X) & f(X)))
          ).
