%*******************************************************************************
%                                    AETOILE
%*******************************************************************************

/*
Rappels sur l'algorithme

- structures de donnees principales = 2 ensembles : P (etat pendants) et Q (etats clos)
- P est dedouble en 2 arbres binaires de recherche equilibres (AVL) : Pf et Pu

   Pf est l'ensemble des etats pendants (pending states), ordonnes selon
   f croissante (h croissante en cas d'egalite de f). Il permet de trouver
   rapidement le prochain etat a developper (celui qui a f(U) minimum).

   Pu est le meme ensemble mais ordonne lexicographiquement (selon la donnee de
   l'etat). Il permet de retrouver facilement n'importe quel etat pendant

   On gere les 2 ensembles de fa�on synchronisee : chaque fois qu'on modifie
   (ajout ou retrait d'un etat dans Pf) on fait la meme chose dans Pu.

   Q est l'ensemble des etats deja developpes. Comme Pu, il permet de retrouver
   facilement un etat par la donnee de sa situation.
   Q est modelise par un seul arbre binaire de recherche equilibre.

Predicat principal de l'algorithme :

   aetoile(Pf,Pu,Q)

   - reussit si Pf est vide ou bien contient un etat minimum terminal
   - sinon on prend un etat minimum U, on genere chaque successeur S et les valeurs g(S) et h(S)
	 et pour chacun
		si S appartient a Q, on l'oublie
		si S appartient a Ps (etat deja rencontre), on compare
			g(S)+h(S) avec la valeur deja calculee pour f(S)
			si g(S)+h(S) < f(S) on reclasse S dans Pf avec les nouvelles valeurs
				g et f
			sinon on ne touche pas a Pf
		si S est entierement nouveau on l'insere dans Pf et dans Ps
	- appelle recursivement etoile avec les nouvelles valeurs NewPF, NewPs, NewQs

*/

%*******************************************************************************

:- ['avl.pl'].       % predicats pour gerer des arbres bin. de recherche
:- ['taquin.pl'].    % predicats definissant le systeme a etudier

%*******************************************************************************

main :-
	writeln("main"),
	% initialisations Pf, Pu et Q
	initial_state(S0),
	% lancement de Aetoile
	% H(S0) = H0
	heuristique(S0, H0),
	% G0 = 0, F0 = G0 + H0 = H0.
	empty(Pf),
	empty(Pu),
	empty(Q),
	insert([[H0, H0, 0], S0], Pf, NewPf),
	insert([S0, [H0, H0, 0], nil, nil], Pu, NewPu),
	writeln("Debut de A*."),
	aetoile(NewPf, NewPu, Q).


%*******************************************************************************
aetoile([], [], _) :- writeln("Pas de solution : l'etat final n'est pas atteignable !").

aetoile(_, _, Q) :-
	% Si le noeud de valeur f min est la situation terminale, alors on a trouvé la solution et on l'affiche.
	final_state(Sf),
	belongs([Sf, _, _, _], Q),
	affiche_solution(Q, Sf).

aetoile(Pf, Pu, Q) :-
	% On enlève le noeud de Pf correspondant à l'état U à développer (celui de f min)
	suppress_min([[F, H, G], U], Pf, NewPf),
	final_state(Sf),

	not(belongs([Sf, _, _, _], Q)),

	% On enlève aussi le noeud frère associé dans Pu
	suppress([U, [F, H, G], Pere, A], Pu, NewPu),

	% Développement de U
	% % Déterminer tous les noeuds contenant un état successeur S de U
	% % Et calculer Fs, Hs, Gs connaissant G(U) et le coût pour passer de U à S
	expand([[F, H, G], U], NoeudsPotentiels),
	% % Traiter chaque noeud successeur
	loop_successors(NoeudsPotentiels, NewPf, NewPu, Q, FinalPf, FinalPu),

	% U désormais traité, on l'insère à Q
	insert([U, [F, H, G], Pere, A], Q, FinalQ),

	% Appel récursif
	aetoile(FinalPf, FinalPu, FinalQ).

%*******************************************************************************

affiche_solution(_, S0) :-
	initial_state(S0).

affiche_solution(Q, S) :-
	belongs([S, Val, Pere, A], Q),
	affiche_solution(Q, Pere),
	writeln([Pere, A, S, Val]).

expand([[_, _, G], U], NoeudsPotentiels) :-
	% Déterminer tous les noeuds contenant un état successeur S de U
	% Et calculer Fs, Hs, Gs connaissant G(U) et le coût pour passer de U à S
	% Renvoyer les noeuds sous la forme de Pu
	findall([S, [Fs, Hs, Gs], U, A], (rule(A, Cost, U, S), heuristique(S, Hs), Gs is G+Cost, Fs is Hs+Gs), NoeudsPotentiels).


loop_successors([], Pf, Pu, _, Pf, Pu).

loop_successors([S|Suite], Pf, Pu, Q, NewPf, NewPu) :-
	% Si S est connu dans Q, alors on oublie ce successeur
	loop_successor(S, Pf, Pu, Q, NPf, NPu),
	loop_successors(Suite, NPf, NPu, Q, NewPf, NewPu).

loop_successor(S, Pf, Pu, Q, Pf, Pu) :-
		% Si S est connu dans Q, alors on oublie ce successeur
		belongs(S, Q).

	% Si S est connu dans Pu, alors on garle le terme associé à la meilleur évaluation (idem dans Pf)
	% % Le nouveau noeud a une meilleur évaluation, on modifie P
loop_successor([S, ValS, Pere, A], Pf, Pu, _, FinalPf, FinalPu) :-
	belongs([S, Val, _, _], Pu),
	((ValS @< Val) ->
		suppress([S, Val, _, _], Pu, NewPu),
		suppress([Val, S], Pf, NewPf),
		insert([S, ValS, Pere, A], NewPu, FinalPu),
		insert([ValS, S], NewPf, FinalPf)
		;
		FinalPf = Pf,
		FinalPu = Pu).

	% % Sinon, on crée un nouveau terme à insérer dans Pu et Pf
loop_successor([S, ValS, Pere, A], Pf, Pu, _, NextPf, NextPu) :-
	insert([S, ValS, Pere, A], Pu, NextPu),
	insert([ValS, S], Pf, NextPf).

	%*******************************************************************************
