%% test_loading.pl - Diagnostique du chargement nanoCoP

test_loading :-
    format('=== DIAGNOSTIQUE nanoCoP ===~n'),

    % Vérifier les fichiers
    format('1. Vérification des fichiers:~n'),
    Files = ['operators.pl', 'nanocop20_swi.pl', 'nanocop20.pl', 'nanocop_proof.pl'],
    forall(member(F, Files),
           (exists_file(F) ->
              format('  ✓ ~w trouvé~n', [F]) ;
              format('  ✗ ~w MANQUANT~n', [F]))),

    % Tenter le chargement manuel
    format('~nanoCop_deciden2. Tentative de chargement manuel:~n'),
    (exists_file('nanocop20_swi.pl') ->
        (format('  Chargement de nanocop20_swi.pl...~n'),
         catch([nanocop20_swi], E, (format('  ERREUR: ~w~n', [E]), fail))) ;
     exists_file('nanocop20.pl') ->
        (format('  Chargement de nanocop20.pl...~n'),
         catch([nanocop20], E, (format('  ERREUR: ~w~n', [E]), fail))) ;
        format('  Aucun fichier nanoCoP trouvé!~n')
    ),

    % Vérifier les prédicats
    format('~n3. Vérification des prédicats:~n'),
    Preds = [prove/2, prove2/3, bmatrix/3],
    forall(member(P, Preds),
           (current_predicate(P) ->
              format('  ✓ ~w disponible~n', [P]) ;
              format('  ✗ ~w MANQUANT~n', [P]))),

    % Test simple si possible
    format('~n4. Test simple:~n'),
    (current_predicate(prove/2) ->
        (format('  Test de prove(p, Proof)...~n'),
         (prove(p, _) ->
            format('  ✓ Test réussi~n') ;
            format('  ✗ Test échoué (normal pour ~p)~n', [p]))) ;
        format('  Impossible: prove/2 non disponible~n')
    ),

    format('~n=== FIN DIAGNOSTIQUE ===~n').

% Test rapide
quick_test :-
    [operators],
    format('Operators chargé~n'),
    (exists_file('nanocop20_swi.pl') ->
        ([nanocop20_swi], format('nanocop20_swi chargé~n')) ;
        format('nanocop20_swi non trouvé~n')),
    (current_predicate(prove/2) ->
        format('prove/2 disponible~n') ;
        format('prove/2 NON disponible~n')).
