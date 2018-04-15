open Printf;;
open Tree;;
open Buffer;;
open Annotator;;
open Str;;

let rec tree_to_string t = 
	let buf = Buffer.create 1000 in
	let s_op op = match op with Conj -> "&" | Disj -> "|" | Impl -> "->" in
	begin
		match t with
			| Binop(op, a, b) -> add_char buf '('; add_string buf (tree_to_string a); add_string buf (s_op op); add_string buf (tree_to_string b); add_char buf ')'
			| Neg(t) -> add_char buf '('; add_char buf '!'; add_string buf (tree_to_string t); add_char buf ')'
			| Var(s) -> add_string buf s 
	end;
	contents buf
;;

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
let hypothesis = Array.make (Hashtbl.length hpts) (Var(""));;
Hashtbl.iter (fun expr idx -> Array.set hypothesis (idx - 1) expr) hpts;;
let len = Array.length hypothesis;;

Array.iteri (fun i x -> 
				if i <> (len - 1) then begin
					fprintf oc "%s" (tree_to_string x);
					if i <> (len - 2) then fprintf oc ","
				end
				else
					fprintf oc "|-%s->%s\n" (tree_to_string x) (conclusion.contents)
			)
			hypothesis
;;

let alpha = Array.get hypothesis ((Array.length hypothesis) - 1);;

let ax1 a b = Binop(Impl, a, Binop(Impl, b, a));;
let ax2 a b c = Binop(Impl, Binop(Impl, a, b), Binop(Impl, Binop(Impl, a, Binop(Impl, b, c)), Binop(Impl, a, c)));;

let prove_alpha = 
	let buf = create 1000 in
	add_string buf (tree_to_string (ax1 alpha alpha));
	add_char buf '\n';
	add_string buf (tree_to_string (ax2 alpha (Binop(Impl, alpha, alpha)) alpha));
	add_char buf '\n';
	add_string buf (tree_to_string (ax1 alpha (Binop(Impl, alpha, alpha))));
	add_char buf '\n';
	add_string buf (tree_to_string (Binop(Impl, Binop(Impl, alpha, Binop(Impl, Binop(Impl, alpha, alpha), alpha)), Binop(Impl, alpha, alpha))));
	add_char buf '\n';
	add_string buf (tree_to_string (Binop(Impl, alpha, alpha)));
	add_char buf '\n';
	contents buf
;;

let prove_ax_hyp exp = 
	let buf = create 1000 in
	add_string buf (tree_to_string (ax1 exp alpha));
	add_char buf '\n';
	add_string buf (tree_to_string exp);
	add_char buf '\n';
	add_string buf (tree_to_string (Binop(Impl, alpha, exp)));
	add_char buf '\n';
	contents buf
;;

let prove_mp exp impl left =
	let buf = create 1000 in
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
	add_string buf (tree_to_string t);
	add_char buf '\n';
	add_string buf (tree_to_string mp1);
	add_char buf '\n';
	add_string buf (tree_to_string mp2);
	add_char buf '\n';
	contents buf
;;

let l = read_in_list [] in
List.iteri
	begin
		fun idx s -> 
		let s' = annotate s (idx + 1) in
		let start = (search_forward (regexp_string "#") s' 0) + 1 in
		let expr = string_to_tree (string_before s' (start - 1)) in
		let s'' = string_after s' start in
		let case' = split (regexp "[ \010\013\009\026\012]+") s'' in
		let case = List.map (fun x -> int_of_string x) case' in
		match case with
			| head :: rest when (head = 0 && (List.nth case 1) = (len - 1)) -> fprintf oc "%s" prove_alpha 
			| head :: rest when (head = 0 || head = 1) -> fprintf oc "%s" (prove_ax_hyp expr)
			| head :: rest when head = 2 -> let impl = string_to_tree (List.nth l (List.nth case 1)) in
											let left = string_to_tree (List.nth l (List.nth case 2)) in
											fprintf oc "%s" (prove_mp expr impl left)
			| _ -> ()
	end
	l
;;