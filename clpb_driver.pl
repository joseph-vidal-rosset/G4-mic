%% File: clpb_nanocop_driver.pl  -  Version: 1.0
%%
%% Purpose: Minimal interface for nanoCoP using CLPB operators
%% Usage:   show(Formula).  % where Formula uses CLPB syntax
%%
%% Examples:
%%   show(~ ~ a =< a).           % Double negation elimination
%%   show((a =< b) * a =< b).    % Modus ponens
%%   show(a + ~ a).              % Excluded middle
%%   show(~ (a * ~ a)).          % Non-contradiction
%%
%% Author: Interface for nanoCoP with CLPB operators

% =========================================================================
% LOADING REQUIRED MODULES
% =========================================================================

% Load nanoCoP core
:- catch([nanocop20_swi], _, 
    catch([nanocop20], _, 
        format('WARNING: nanoCoP core not found!~n'))).

% =========================================================================
% INTERFACE MINIMALE show/1
% =========================================================================

%% show(+Formula) - Interface minimaliste avec statistiques uniquement
show(Formula) :-
    translate_clpb_to_nanocop(Formula, InternalFormula),
    time(prove(InternalFormula, _Proof)),
    !.

% =========================================================================
% TRADUCTION CLPB → nanoCoP
% =========================================================================

%% translate_clpb_to_nanocop(+CLPB, -nanoCoP)
% Traduit de la syntaxe CLPB vers la syntaxe interne de nanoCoP

% Implication CLPB
translate_clpb_to_nanocop(A =< B, (A1 => B1)) :- 
    !, 
    translate_clpb_to_nanocop(A, A1), 
    translate_clpb_to_nanocop(B, B1).

% Biconditional CLPB
translate_clpb_to_nanocop(A =:= B, (A1 <=> B1)) :- 
    !, 
    translate_clpb_to_nanocop(A, A1), 
    translate_clpb_to_nanocop(B, B1).

% Conjonction CLPB
translate_clpb_to_nanocop(A * B, (A1 , B1)) :- 
    !, 
    translate_clpb_to_nanocop(A, A1), 
    translate_clpb_to_nanocop(B, B1).

% Disjonction CLPB
translate_clpb_to_nanocop(A + B, (A1 ; B1)) :- 
    !, 
    translate_clpb_to_nanocop(A, A1), 
    translate_clpb_to_nanocop(B, B1).

% Négation CLPB
translate_clpb_to_nanocop(~ A, (~ A1)) :- 
    !, 
    translate_clpb_to_nanocop(A, A1).

% Falsum (bot)
translate_clpb_to_nanocop(0, (~(p0 => p0))) :- !.

% Atomes et variables (cas de base)
translate_clpb_to_nanocop(F, F).

% =========================================================================
% EXAMPLES
% =========================================================================

%% run_clpb_examples - Execute examples with CLPB syntax
%% run_clpb_examples - Execute examples with CLPB syntax
%% run_clpb_examples - Execute examples with CLPB syntax
run_clpb_examples :-
    format('~n=== nanoCoP with CLPB operators ===~n'),
    
    format('~n1. Double negation: ~~ ~~ a =< a~n'),
    show((~ (~ a)) =< a),
    
    format('~n2. Excluded middle: a + ~~ a~n'),
    show(a + (~ a)),
    
    format('~n3. Modus ponens: (a =< b) * a =< b~n'),
    show(((a =< b) * a) =< b),
    
    format('~n4. De Morgan: ~~ (a * b) =:= (~~ a + ~~ b)~n'),
    show((~ (a * b)) =:= ((~ a) + (~ b))),
    
    format('~n5. Peirce: ((a =< b) =< a) =< a~n'),
    show(((a =< b) =< a) =< a).
% =========================================================================
% HELP
% =========================================================================

help_clpb :-
    format('~n=== nanoCoP with CLPB operators ===~n'),
    format('~nMain command:~n'),
    format('  show(Formula).  - Prove a formula with CLPB syntax~n'),
    format('~nCLPB operators:~n'),
    format('  =<              - implication~n'),
    format('  =:=             - biconditional~n'),
    format('  *               - conjunction (and)~n'),
    format('  +               - disjunction (or)~n'),
    format('  ~               - negation (not)~n'),
    format('  0               - falsum (bot, ⊥)~n'),
    format('~nExamples:~n'),
    format('  show(~ ~ a =< a).~n'),
    format('  show(a + ~ a).~n'),
    format('  show((a =< b) * a =< b).~n'),
    format('  run_clpb_examples.~n'),
    format('~n').

% =========================================================================
% INITIALIZATION
% =========================================================================

:- format('nanoCoP CLPB Interface loaded.~n').
:- format('Type help_clpb. for help.~n').
:- format('Type run_clpb_examples. to run examples.~n').
