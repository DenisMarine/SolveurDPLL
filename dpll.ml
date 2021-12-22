open List

(* fonctions utilitaires *********************************************)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []
;;

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"
;;

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [[1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];[19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];[-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];[-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];[-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];[-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];[-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];[-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];[-14;-17];[-15;-18]]

(*********************************euuu***********************************)

(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral i à vrai *)

(*renvoie la liste l sans la negation de x*)
let rec mnegation x l lpre=
  match l with
  | [] -> lpre
  | e::reste -> if -x=e then lpre@reste else mnegation x reste (e::lpre)
;;

let simplifie i clauses =
	(*filtr est notre filtre utilisé pour filter_map*)
	let filtr l =
		if mem i l then None 
		else Some (mnegation i l [])
	in rev (filter_map filtr clauses)
;;

(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* un clause vide est insatisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche
;;

(* tests *)
(*print_string "tests solveur_split :\n";;
print_string "censé etre unsat : \n";;
let () = print_modele (solveur_split systeme []);;
print_string "censé etre sat coloriage: \n";;
let () = print_modele (solveur_split coloriage []);;
print_string "censé etre sat : \n";;
let () = print_modele (solveur_split exemple_7_2 []);;*)



(* solveur dpll récursif *)
    
(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)

exception Not_found;;

let rec unitaire clauses =
	match clauses with 
	| [] -> raise Not_found
	| e :: l -> if (length e) = 1 then (hd e)
	else unitaire l
;;
    
(* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' *)

exception Failure of string;;


(*cette fonction nous permet d'enlever un litéral et sa négation dans la liste des propositions d'une formule*)
let rec enleve_p_et_non_p x l lpre=
  match l with
  | [] -> lpre
  | e::reste -> if (x=e || -x=e) then enleve_p_et_non_p x reste lpre else enleve_p_et_non_p x reste (e::lpre);;
 
let rec pur clauses = 
  let rec aux liste =
    match liste with 
    [] -> raise (Failure "pas de littéral pur")
    | e::reste -> if not(mem (-e) reste) then e else aux (enleve_p_et_non_p e reste []) 
  in aux (flatten clauses);;
  


let rec solveur_dpll_rec clauses interpretation =
  if clauses = [] then Some interpretation
	else if mem [] clauses then None else
    match (try Some (unitaire clauses) 
  with Not_found -> None)
with 
| Some u -> solveur_dpll_rec (simplifie u clauses) (u::interpretation)
| None -> match (try Some (pur clauses) 
    with Failure "pas de littéral pur" -> None)
  with 
  | Some p -> solveur_dpll_rec (simplifie p clauses) (p::interpretation)
  | None -> let e = hd (hd clauses) in 
  let branche = solveur_dpll_rec (simplifie e clauses) (e::interpretation) in
  match branche with
  | None -> solveur_dpll_rec (simplifie (-e) clauses) ((-e)::interpretation)
  | _ -> branche
;;

	
(* tests *)
(*print_string "tests solveur_dpll_rec :\n";;
print_string "censé etre unsat : \n";;
let () = print_modele (solveur_dpll_rec systeme []);;
print_string "censé etre sat coloriage: \n";;
let () = print_modele (solveur_dpll_rec coloriage []);;
print_string "censé etre sat : \n";;
let () = print_modele (solveur_dpll_rec exemple_7_2 []);;	*)

let () = 
	let clauses = Dimacs.parse Sys.argv.(1) in
	print_modele (solveur_dpll_rec clauses [])

  (*let () = 
	let clauses = Dimacs.parse Sys.argv.(1) in
	print_modele (solveur_split clauses [])*)

  (* temps d'execution pour sudoku-9x9-expert.cnf en solveur_dpll_rec : 0,334s *)
  (* temps d'execution pour sudoku-9x9-expert.cnf en solveur_split : infini *)

  (* temps d'execution pour sudoku-9x9-hard.cnf en solveur_dpll_rec : 0,284s *)
  (* temps d'execution pour sudoku-9x9-hard.cnf en solveur_split : 29,033s *)
