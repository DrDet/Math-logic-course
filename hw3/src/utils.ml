open Tree;;
open Buffer;;
open Str;;
open Printf;;

let my_append a b =
	let a' = List.rev a in
	let rec add_all dst src = match src with
		| head :: tail -> add_all (head :: dst) tail 
		| [] -> dst
	in
	List.rev (add_all a' b)
;;

let string_to_tree s = 
	let (>>) x f = f x in
	s >> Lexing.from_string >> Parser.main Lexer.main
;;

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

let remove_whitespaces s = global_replace (regexp "[ \010\013\009\026\012]+") "" s;;

let rec read_in_list ic l =
	try
		let s' = input_line ic in
		let s = remove_whitespaces s' in
		if s <> "" then
			read_in_list ic (s :: l)
		else 
			read_in_list ic l
	with eof -> 
		close_in ic;
		List.rev l
;;

let rec print_proof oc proof = match proof with
	| head :: tail -> fprintf oc "%s\n" (tree_to_string head); print_proof oc tail
	| [] -> ()
;;

let get_bool_value mask n =
	let fit = (1 lsl (n + 1)) - 1 in
	let t = mask land fit in
	let bit = t lsr n in
	bit = 1
;;

let calc_op op x y = match op with
	| Conj -> x && y 
	| Disj -> x || y
	| Impl -> (not x) || y
;;