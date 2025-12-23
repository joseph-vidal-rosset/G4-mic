% =========================================================================
% OPÉRATEURS COMMUNS - Module centralisé
% À inclure dans tous les modules du prouveur
% =========================================================================
:- use_module(library(lists)).
:- use_module(library(statistics)).
% =========================================================================
% OPÉRATEURS TPTP (syntaxe d'entrée)
% =========================================================================
:- op( 500, fy, ~).             % negation
:- op(1000, xfy, &).            % conjunction
:- op(1100, xfy, '|').          % disjunction
:- op(1110, xfy, =>).           % conditional
:- op(1120, xfy, <=>).          % biconditional
:- op( 500, fy, !).             % universal quantifier:  ![X]:
:- op( 500, fy, ?).             % existential quantifier:  ?[X]:
:- op( 500, xfy, :).            % quantifier separator
% :- op(400, fx, f).             % falsity (⊥)

% =========================================================================
% OPÉRATEURS LATEX (sortie formatée)
% ATTENTION : Respecter exactement les espaces !
% =========================================================================
:- op( 500, fy, ' \\lnot ').     % negation
:- op(1000, xfy, ' \\land ').    % conjunction
:- op(1100, xfy, ' \\lor ').     % disjunction
:- op(1110, xfx, ' \\to ').      % conditional
:- op(1120, xfx, ' \\leftrightarrow ').  % biconditional
:- op( 500, fy, ' \\forall ').   % universal quantifier
:- op( 500, fy, ' \\exists ').   % existential quantifier
:- op( 500, xfy, ' ').           % espace pour quantificateurs
:- op(400, fx, ' \\bot ').      % falsity (⊥)

% =========================================================================
% DOCUMENTATION DES OPÉRATEURS
% =========================================================================

% Priorités (ordre croissant) :
% 500  : ~, !, ?, :
% 1000 : &
% 1100 : |
% 1110 : =>
% 1120 : <=>
% 1200 : f (⊥)

% Associativité :
% fy  : préfixe, associatif à droite (ex: ~ ~p)
% xfy : infixe, associatif à droite (ex: p & q & r)
% xfx : infixe, non associatif (ex: p <=> q)
% fx  : préfixe, non associatif (ex: f)

% Usage dans les modules :
% :- [operators].  % Inclure en début de fichier
