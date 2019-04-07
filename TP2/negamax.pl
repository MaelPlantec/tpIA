	/*
	Ce programme met en oeuvre l'algorithme Minmax (avec convention
	negamax) et l'illustre sur le jeu du TicTacToe (morpion 3x3)
	*/

:- [tictactoe].

	/****************************************************
  	ALGORITHME MINMAX avec convention NEGAMAX : negamax/5
  	*****************************************************/

	/*
	negamax(+J, +Etat, +P, +Pmax, [?Coup, ?Val])

	SPECIFICATIONS :

	Retourne pour un joueur J donn�, devant jouer dans
	une situation donn�e Etat, de profondeur donnee P,
	le meilleur couple [Coup, Valeur] apres une analyse
	pouvant aller jusqu'a la profondeur Pmax.

	Il y a 3 cas a decrire (donc 3 clauses pour negamax/5)

1/ La profondeur maximale est atteinte : on ne peut pas
developper cet Etat. Il n'y a donc pas de coup possible a jouer (Coup = rien)
et l'evaluation de Etat est faite par l'heuristique. */
negamax(J, Etat, Pmax, Pmax, [nil, Val]) :-
	heuristique(J, Etat, NewVal),
	Val is -NewVal.

/* 2/ la profondeur maximale n'est pas  atteinte mais J ne
peut pas jouer ; au TicTacToe un joueur ne peut pas jouer
quand le tableau est complet (totalement instancie). Il n'y a pas de coup a jouer (Coup = rien)
et l'evaluation de Etat est faite par l'heuristique.  */
negamax(J, Etat, _, _, [nil, Val]) :-
	situation_terminale(J, Etat),
	heuristique(J, Etat, NewVal),
	Val is -NewVal.

/* 3/ la profondeur maxi n'est pas atteinte et J peut encore
jouer. Il faut evaluer le sous-arbre complet issu de Etat ;

- on determine d'abord la liste de tous les couples
[Coup_possible, Situation_suivante] via le predicat
 successeurs/3 (deja fourni, voir plus bas).

- cette liste est passee a un predicat intermediaire :
loop_negamax/5, charge d'appliquer negamax sur chaque
Situation_suivante ; loop_negamax/5 retourne une liste de
couples [Coup_possible, Valeur]

- parmi cette liste, on garde le meilleur couple, c-a-d celui
qui a la plus petite valeur (cf. predicat meilleur/2);
soit [C1,V1] ce couple optimal. Le predicat meilleur/2
effectue cette selection.

- finalement le couple retourné par negamax est [Coup, V2]
avec : V2 is -V1 (cf. convention negamax vue en cours).  */
negamax(J, Etat, P, Pmax, [Coup, Val]) :-
	P < Pmax,
	successeurs(J, Etat, Succ),
	loop_negamax(J, P, Pmax, Succ, ListeCouples),
	meilleur(ListeCouples, [Coup, MVal]),
	Val is -MVal.

	/*******************************************
	 DEVELOPPEMENT D'UNE SITUATION NON TERMINALE
	 successeurs/3
	 *******************************************/

	 /*
   	 successeurs(+J,+Etat, ?Succ)

   	 retourne la liste des couples [Coup, Etat_Suivant]
 	 pour un joueur donne dans une situation donnee
	 */

successeurs(J,Etat,Succ) :-
	copy_term(Etat, Etat_Suiv),
	findall([Coup,Etat_Suiv],
		    successeur(J,Etat_Suiv,Coup),
		    Succ).

	/*************************************
         Boucle permettant d'appliquer negamax
         a chaque situation suivante :
	*************************************/

	/*
	loop_negamax(+J,+P,+Pmax,+Successeurs,?Liste_Couples)
	retourne la liste des couples [Coup, Valeur_Situation_Suivante]
	a partir de la liste des couples [Coup, Situation_Suivante]
	*/

loop_negamax(_,_, _  ,[], []).
loop_negamax(J,P,Pmax,[[Coup,Suiv]|Succ],[[Coup,Vsuiv]|Reste_Couples]) :-
	loop_negamax(J,P,Pmax,Succ,Reste_Couples),
	adversaire(J,A),
	Pnew is P+1,
	negamax(A,Suiv,Pnew,Pmax, [_,Vsuiv]).

	/*

A FAIRE : commenter chaque litteral de la 2eme clause de loop_negamax/5,
	en particulier la forme du terme [_,Vsuiv] dans le dernier
	litteral ?
	*/

	/*********************************
	 Selection du couple qui a la plus
	 petite valeur V
	 *********************************/

	/* meilleur(+Liste_de_Couples, ?Meilleur_Couple)

	SPECIFICATIONS :
	On suppose que chaque element de la liste est du type [C,V]
	- le meilleur dans une liste a un seul element est cet element
	- le meilleur dans une liste [X|L] avec L \= [], est obtenu en comparant
	  X et Y,le meilleur couple de L
	  Entre X et Y on garde celui qui a la petite valeur de V.	*/

meilleur([X],X).
meilleur([[C,V]|Reste], [MC, MV]) :-
	Reste \= [],
	meilleur(Reste, [IC, IV]),
	(IV > V
	-> MV = IV, MC = IC ; MV = V, MC = C).

liste([[[1,2],-3],[[1,3],-21],[[1,4],-1],[[1,4],-1]]).


	/******************
  	PROGRAMME PRINCIPAL
  	*******************/

main(Coup, Val, Pmax) :-
	joueur_initial(J),
	situation_initiale(S),
	negamax(J, S, 0, Pmax, [Coup, Val]).

% Doit placer x au centre
test_coin(Coup, Val, Pmax) :-
	Pmax >= 1,
	negamax(x, [[o,_,_],[_,_,_],[_,_,_]], 1, Pmax, [Coup, Val]).

test_centre(Coup, Val, Pmax) :-
	Pmax >= 1,
	negamax(x, [[_,_,_],[_,o,_],[_,_,_]], 1, Pmax, [Coup, Val]).

test_1(Coup, Val, Pmax) :-
	Pmax >= 2,
	negamax(o, [[x,_,_],[_,o,_],[_,_,_]], 2, Pmax, [Coup, Val]).

test_2(Coup, Val, Pmax) :-
	Pmax >= 2,
	negamax(o, [[_,x,_],[_,o,_],[_,_,_]], 2, Pmax, [Coup, Val]).

test_diag(Coup, Val, Pmax) :-
	Pmax >= 3,
	negamax(x, [[x,_,o],[_,o,_],[_,_,_]], 3, Pmax, [Coup, Val]).
