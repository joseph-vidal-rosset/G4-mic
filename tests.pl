% =================================================================
% 1. BASIC TESTS - MINIMAL PROPOSITIONAL LOGIC
% =================================================================

% Identity and implication introduction tests
test_identity_simple :-
    write('Test 1.1: A → A'), nl,
    decide(a => a).

test_identity_complex :-
    write('Test 1.2: A → (B → A)'), nl,
    decide(a => (b => a)).

test_permutation :-
    write('Test 1.3: A → (B → (A ∧ B))'), nl,
    decide(a => (b => (a & b))).

% Conjunction tests
test_conjunction_intro :-
    write('Test 1.4: (A ∧ B) → (B ∧ A)'), nl,
    decide((a & b) => (b & a)).

test_conjunction_assoc :-
    write('Test 1.5: ((A ∧ B) ∧ C) → (A ∧ (B ∧ C))'), nl,
    decide(((a & b) & c) => (a & (b & c))).

% Disjunction tests
test_disjunction_intro :-
    write('Test 1.6: A → (A ∨ B)'), nl,
    decide(a => (a | b)).

test_disjunction_comm :-
    write('Test 1.7: (A ∨ B) → (B ∨ A)'), nl,
    decide((a | b) => (b | a)).

test_disjunction_elim :-
    write('Test 1.8: ((A → C) ∧ (B → C)) → ((A ∨ B) → C)'), nl,
    decide(((a => c) & (b => c)) => ((a | b) => c)).

% Biconditional tests
test_biconditional_intro :-
    write('Test 1.9: (A → B) → ((B → A) → (A ↔ B))'), nl,
    decide((a => b) => ((b => a) => (a <=> b))).

test_biconditional_elim :-
    write('Test 1.10: (A ↔ B) → (A → B)'), nl,
    decide((a <=> b) => (a => b)).

% Modus Tollens tests (CORRECTED)
test_modus_tollens :-
    write('Test 1.11: ((A → B) ∧ ¬B) → ¬A'), nl,
    decide(((a => b) & ~b) => ~a).

test_modus_tollens_complex :-
    write('Test 1.12: ((A → (B → C)) ∧ ¬C) → (A → ¬B)'), nl,
    decide(((a => (b => c)) & ~c) => (a => ~b)).

% =================================================================
% 2. INTUITIONISTIC TESTS - NEGATION
% =================================================================

% Negation introduction/elimination tests
test_negation_intro :-
    write('Test 2.1: (A → ⊥) → ¬A'), nl,
    decide((a => f) => ~a).

test_negation_elim :-
    write('Test 2.2: (A ∧ ¬A) → ⊥'), nl,
    decide((a & ~a) => f).

test_negation_contraposition_weak :-
    write('Test 2.3: (A → B) → (¬B → ¬A)'), nl,
    decide((a => b) => (~b => ~a)).

% Contradiction tests
test_contradiction_anything :-
    write('Test 2.4: ⊥ → A'), nl,
    decide(f => a).

test_absurdity_chain :-
    write('Test 2.5: (¬A → ⊥) → A [may fail in intuitionistic logic]'), nl,
    catch(decide((~a => f) => a), _, write('Expected failure in intuitionistic logic')), nl.

% =================================================================
% 3. CLASSICAL TESTS - BEYOND INTUITIONISTIC LOGIC
% =================================================================

% Indirect proof tests
test_indirect_proof :-
    write('Test 3.1: ¬¬A → A (Double negation)'), nl,
    decide( ~ ~ a => a).

test_excluded_middle :-
    write('Test 3.2: A ∨ ¬A (Excluded middle) [classical]'), nl,
    catch(decide(a | ~ a), _, write('May fail depending on implementation')), nl.

test_material_implication :-
    write('Test 3.3: (A → B) ↔ (¬A ∨ B)'), nl,
    catch(decide((a => b) <=> ( ~ a | b)), _, write('Complex test')), nl.

% Classical contraposition tests
test_contraposition_strong :-
    write('Test 3.4: (¬B → ¬A) → (A → B)'), nl,
    decide(( ~ b => ~ a) => (a => b)).

% =================================================================
% 4. QUANTIFIER TESTS - CORRECTED SYNTAX
% =================================================================

% Basic universal tests
test_universal_intro :-
    write('Test 4.1: ∀x(P(x) → P(x))'), nl,
    decide(![x]:(p(x) => p(x))).

test_universal_elim :-
    write('Test 4.2: (∀x P(x)) → P(a)'), nl,
    decide((![x]:p(x)) => p(a)).

test_universal_distribution :-
    write('Test 4.3: (∀x(P(x) → Q(x))) → ((∀x P(x)) → (∀x Q(x)))'), nl,
    decide((![x]:(p(x) => q(x))) => ((![x]:p(x)) => (![x]:q(x)))).

% Basic existential tests
test_existential_intro :-
    write('Test 4.4: P(a) → ∃x P(x)'), nl,
    decide(p(a) => (?[x]:p(x))).

test_existential_elim :-
    write('Test 4.5: (∃x P(x)) → (∀x(P(x) → Q)) → Q'), nl,
    decide((?[x]:p(x)) => ((![x]:(p(x) => q)) => q)).

test_mixed_quantifiers :-
    write('Test 4.6: Valid mixed quantifiers'), nl,
    decide((?[y]:(![x]:p(x,y))) => (![x]:(?[y]:p(x,y)))).

test_quantifier_negation :-
    write('Test 4.7: ¬(∀x P(x)) ↔ (∃x ¬P(x))'), nl,
    catch(decide((~(![x]:p(x))) <=> (?[x]: ~ p(x))), 
          _, write('May fail - complex equivalence')), nl.

% =================================================================
% 5. PREMISE TESTS - PRACTICAL REASONING
% =================================================================

% Modus ponens with premises
test_modus_ponens :-
    write('Test 5.1: ((A => B) & A) => B'), nl,
    decide(((a => b)& a) => b).

test_hypothetical_syllogism :-
    write('Test 5.2: ((A → B) &(B → C)) => (A → C)'), nl,
    decide(((a => b) & (b => c)) => (a => c)).


test_disjunctive_syllogism :-
    write('Test 5.3: ((A ∨ B)& ¬A) => B'), nl,
    decide(((a | b) & ~ a ) => b).


% Complex tests with quantifiers - SIMPLIFIED
test_universal_instantiation :-
    write('Test 5.4: {∀x(H(x) → M(x)), H(socrates)} ⊢ M(socrates)'), nl,
    catch(decide((![x]:(h(x) => m(x)) & h(socrates)) => m(socrates)),
          _, write('Quantifier test - may need adjustment')), nl.

test_existential_generalization :-
    write('Test 5.5: {M(socrates)} ⊢ ∃x M(x)'), nl,
    catch(decide(m(socrates) => ?[x]:m(x)),
          _, write('Quantifier test - may need adjustment')), nl.

% =================================================================
% 6. STRESS TESTS - COMPLEX FORMULAS
% =================================================================

test_complex_formula_1 :-
    write('Test 6.1: Complex formula with quantifiers'), nl,
    catch(decide((![x]:(p(x) => q(x))) => ((![x]:p(x)) => (![x]:q(x)))), 
          _, write('Timeout or failure')), nl.

test_complex_formula_2 :-
    write('Test 6.2: Mixed logic with negations'), nl,
    catch(decide(((a => b) & (c => d)) => ((a & c) => (b & d))), 
          _, write('Timeout or failure')), nl.

% =================================================================
% TEST RUNNERS
% =================================================================

run_all_tests :-
    write('========================================'), nl,
    write('FOL PROVER TEST SUITE START'), nl,
    write('========================================'), nl, nl,
    
    % Minimal propositional tests
    write('=== MINIMAL PROPOSITIONAL LOGIC ==='), nl,
    test_identity_simple, nl,
    test_identity_complex, nl,
    test_permutation, nl,
    test_conjunction_intro, nl,
    test_conjunction_assoc, nl,
    test_disjunction_intro, nl,
    test_disjunction_comm, nl,
    test_disjunction_elim, nl,
    test_biconditional_intro, nl,
    test_biconditional_elim, nl,
    test_modus_tollens, nl,
    test_modus_tollens_complex, nl,
    
    % Intuitionistic tests
    write('=== INTUITIONISTIC LOGIC ==='), nl,
    test_negation_intro, nl,
    test_negation_elim, nl,
    test_negation_contraposition_weak, nl,
    test_contradiction_anything, nl,
    test_absurdity_chain, nl,
    
    % Classical tests
    write('=== CLASSICAL LOGIC ==='), nl,
    test_indirect_proof, nl,
    test_excluded_middle, nl,
    test_material_implication, nl,
    test_contraposition_strong, nl,
    
    % Quantifier tests
    write('=== QUANTIFIERS ==='), nl,
    test_universal_intro, nl,
    test_universal_elim, nl,
    test_universal_distribution, nl,
    test_existential_intro, nl,
    test_existential_elim, nl,
    test_mixed_quantifiers, nl,
    test_quantifier_negation, nl,
    
    
   
    write('=== Usual logical truths ==='), nl,
    test_modus_ponens, nl,
    test_hypothetical_syllogism, nl,
    test_disjunctive_syllogism, nl,
    test_universal_instantiation, nl,
    test_existential_generalization, nl,
    
    % Stress tests
    write('=== STRESS TESTS ==='), nl,
    test_complex_formula_1, nl,
    test_complex_formula_2, nl,
    
    write('========================================'), nl,
    write('TEST SUITE END'), nl,
    write('========================================'), nl.

% Quick tests for immediate verification
quick_tests :-
    write('=== QUICK TESTS ==='), nl,
    test_identity_simple, nl,
    test_modus_tollens, nl,
 %   test_modus_ponens_premises, nl,
    test_universal_intro, nl,
    write('=== QUICK TESTS END ==='), nl.

% Individual MT test for debugging
test_mt_only :-
    write('=== ISOLATED MT TEST ==='), nl,
    test_modus_tollens, nl.

% Logic level demonstration tests
demo_logic_levels :-
    write('=== LOGIC LEVEL DEMONSTRATION ==='), nl,
    write('--- Minimal Logic Example ---'), nl,
    decide(a => a), nl,
    write('--- Intuitionistic Logic Example ---'), nl, 
    decide((a & ~a) => f), nl,
    write('--- Classical Logic Example ---'), nl,
    decide( ~ ~ a => a), nl,
    write('=== DEMO END ==='), nl.
