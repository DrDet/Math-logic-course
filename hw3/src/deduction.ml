open Printf;;
open Tree;;
open Buffer;;
open Str;;
open Utils;;

let ax1 a b = Binop(Impl, a, Binop(Impl, b, a));;
let ax2 a b c = Binop(Impl, Binop(Impl, a, b), Binop(Impl, Binop(Impl, a, Binop(Impl, b, c)), Binop(Impl, a, c)));;

let prove_alpha alpha = 
	[	
		(ax1 alpha alpha); 
		(ax2 alpha (Binop(Impl, alpha, alpha)) alpha); 
		(ax1 alpha (Binop(Impl, alpha, alpha))); 
		(Binop(Impl, Binop(Impl, alpha, Binop(Impl, Binop(Impl, alpha, alpha), alpha)), Binop(Impl, alpha, alpha))); 
		(Binop(Impl, alpha, alpha))	
	]
;;

let prove_ax_hyp exp alpha = 
	[
		(ax1 exp alpha);
		exp;
		(Binop(Impl, alpha, exp))
	]
;;

let prove_mp exp impl left alpha =
	let t = ax2 alpha left exp in
	let mp1 = begin 
				  match t with 
				  | Binop(Impl, a, b) -> b
				  | _ -> t
			  end in
	let mp2 = begin 
				  match mp1 with 
				  | Binop(Impl, a, b) -> b
				  | _ -> t
			  end in
	[
		t;
		mp1;
		mp2
	]
;;

let apply_deduction hyps main_expr proof = (*hyps == Array<Tree>*)
	let _len = Array.length hyps in
	let _hyps = let t = Hashtbl.create _len in
				Array.iteri (fun idx x -> Hashtbl.add t x (idx + 1)) hyps;
				t
	in
	let _alpha = Array.get hyps ((Array.length hyps) - 1) in
	let _proved_mp = Hashtbl.create 20000 in 	(*Tree -> (int, int)*)
	let _impls = Hashtbl.create 20000 in 		(*Tree->(Tree,int)*)
	let _exps = Hashtbl.create 20000 in		(*Tree->int*)
	let process_case idx expr' = 
		let s = tree_to_string expr' in
		let s' = Annotator.annotate s (idx + 1) _proved_mp _impls _exps _hyps in
		let start = (search_forward (regexp_string "#") s' 0) + 1 in
		let expr = string_to_tree (string_before s' (start - 1)) in
		let s'' = string_after s' start in
		let case' = split (regexp "[ \010\013\009\026\012]+") s'' in
		let case = List.map (fun x -> int_of_string x) case' in
		match case with
			| head :: rest when (head = 0 && (List.nth case 1) = (_len - 1)) -> (prove_alpha _alpha)
			| head :: rest when (head = 0 || head = 1) -> (prove_ax_hyp expr _alpha)
			| head :: rest when head = 2 -> let impl = List.nth proof (List.nth case 1) in
											let left = List.nth proof (List.nth case 2) in
											(prove_mp expr impl left _alpha)
			| _ -> []
	in
	let rec tail_rec l idx = match l with
	| head :: tail -> let tmp = (process_case idx head) in
					  tmp @ (tail_rec tail (idx + 1))
	| [] -> []
	in 
	tail_rec proof 0
;;