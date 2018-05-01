open Tree;;
open Buffer;;
open Printf;;
open Utils;;
open Str;;

exception Not_provable of int;;
let empty_tree = Var("");;

let (ic, oc) = (open_in "input.txt", open_out "output.txt");;
let main_string = remove_whitespaces (input_line ic);;

let main_hyps = 
	let end_idx = search_forward (regexp_string "|=") main_string 0 in
	let s = string_before main_string end_idx in
	let l' = Str.split (regexp_string ",") s in
	List.map (fun x -> string_to_tree x) l'
;;

let conclusion = 
	let start_idx = (search_forward (regexp_string "|=") main_string 0) + 2 in
	let s = string_after main_string start_idx in
	string_to_tree s
;;

let main_expr = let main_expr_string = if (List.length main_hyps) > 0 then 
								("(" ^ (global_replace (regexp ((quote "|=") ^ "\\|" ^ (quote ","))) ")->(" main_string) ^ ")")
						else 
							""
				in
				if main_expr_string = "" then 
					conclusion 
				else
					string_to_tree main_expr_string
;;
(*get vars and fix order of them*)
let vars_si = Hashtbl.create 5;;	(*string->idx(0)*)
let vars_is = Hashtbl.create 5;;	(*idx(0)->string*)
let add_s s = 
	if (Hashtbl.mem vars_si s) = false then 
		Hashtbl.add vars_si s (Hashtbl.length vars_si);
;;
let rec fill_vars_si t = match t with 
	| Var(s) -> add_s s
	| Binop(op, a, b) -> (fill_vars_si a); fill_vars_si b
	| Neg(a) -> fill_vars_si a
;;
fill_vars_si main_expr;;
Hashtbl.iter (fun s i -> Hashtbl.add vars_is i s) vars_si;;
let vars_cnt = Hashtbl.length vars_si;;
(*get vars and fix order of them*)

let files = Hashtbl.create 16;;

let get_proof file _A _B = 
	if ((Hashtbl.mem files file) = false) then begin
		let ic = open_in file in
		let l = read_in_list ic [] in
		let rec map_to_tree l = match l with
		| head :: tail -> (string_to_tree head) :: (map_to_tree tail)
		| [] -> []
		in
		Hashtbl.add files file (map_to_tree l)
	end;
	let l = Hashtbl.find files file in
	let rec make_substitution t _A _B = match t with 
		| Binop(op, a, b) -> Binop(op, make_substitution a _A _B, make_substitution b _A _B) 
		| Neg(a) -> Neg(make_substitution a _A _B)
		| Var(s) -> if s = "A" then _A else _B
	in
	let rec map_to_sbst l = match l with 
	| head :: tail -> (make_substitution head _A _B) :: (map_to_sbst tail)
	| [] -> [] in
	map_to_sbst l 
;;

let rec fixed_prove t hyp_mask = match t with
	| Var(s) -> let idx = Hashtbl.find vars_si s in
				let value = get_bool_value hyp_mask idx in
				(value, [])
	| Binop(op, a, b) -> let proof_a' = fixed_prove a hyp_mask in
						 let proof_b' = fixed_prove b hyp_mask in
						 let proof_a = snd proof_a' in
						 let proof_b = snd proof_b' in
						 let a_val = fst proof_a' in
						 let b_val = fst proof_b' in
						 let s = (function Conj -> "conj_" | Disj -> "disj_" | Impl -> "impl_") op in
						 let buf = Buffer.create 30 in
						 let _none_ = 	 add_string buf "proofs/";
										 add_string buf s;
										 add_string buf (string_of_bool a_val);
										 add_string buf (string_of_bool b_val);
										 add_string buf ".txt" in
						 let file_name = contents buf in
						 let proof_op = get_proof file_name a b in
						(calc_op op a_val b_val, my_append (my_append proof_a proof_b) proof_op)
	| Neg(a) -> let proof_a' = fixed_prove a hyp_mask in
				let a_val = fst proof_a' in
				let proof_a = snd proof_a' in
				let buf = Buffer.create 30 in
				let _none_ = 
					add_string buf "proofs/not_";
					add_string buf (string_of_bool a_val);
					add_string buf ".txt" in
				let file_name = contents buf in
				let proof_not = get_proof file_name a empty_tree in
				(not a_val, my_append proof_a proof_not)
;;

let get_hyps hyp_cnt hyp_mask = 
	let res = Array.make hyp_cnt empty_tree in
	Hashtbl.iter (fun s idx -> 
					if idx < hyp_cnt then begin
						let value = get_bool_value hyp_mask idx in
						if value then
							Array.set res idx (Var(s))
						else
							Array.set res idx (Neg(Var(s)))
					end
				)					
				vars_si;
	res
;;

let rec main_prove hyp_cnt hyp_mask = 
	if hyp_cnt = vars_cnt then begin
		let tmp = fixed_prove main_expr hyp_mask in
		snd tmp
	end else begin
			let mask_0 = hyp_mask in
			let mask_1 = (hyp_mask lor (1 lsl hyp_cnt)) in
			let proof_0' = main_prove (hyp_cnt + 1) mask_0 in
			let proof_1' = main_prove (hyp_cnt + 1) mask_1 in
			let proof_0 = Deduction.apply_deduction (get_hyps (hyp_cnt + 1) mask_0) main_expr proof_0' in
			let proof_1 = Deduction.apply_deduction (get_hyps (hyp_cnt + 1) mask_1) main_expr proof_1' in
			let excluded = Var(Hashtbl.find vars_is hyp_cnt) in
			let hyp_exluding_proof = get_proof "proofs/_excluded.txt" main_expr excluded in
			(my_append (my_append proof_0 proof_1) hyp_exluding_proof)
	end
;;

let check () =
	let rec calc_expr expr mask = match expr with
		| Var(s) -> get_bool_value mask (Hashtbl.find vars_si s)
		| Binop(op, a, b) -> let a_val = calc_expr a mask in
							 let b_val = calc_expr b mask in
							 calc_op op a_val b_val
		| Neg(a) -> let a_val = calc_expr a mask in
								not a_val
	in
	for mask = 0 to ((1 lsl vars_cnt) - 1) do
		let value = calc_expr main_expr mask in
		if value = false then
			raise (Not_provable(mask))
	done
in
try
	check ();
	let proof = main_prove 0 0 in
	let header = global_replace (regexp_string "|=") "|-" main_string in
	fprintf oc "%s\n" header;
	let rec get_mps t depth = match t with 
		| Binop(Impl, a, b) when depth < (List.length main_hyps) -> (Binop(Impl, a, b)) :: (get_mps b (depth + 1)) 
		| _ -> [t]
	in
	let suf_proof = my_append main_hyps (List.tl (get_mps main_expr 0)) in
	print_proof oc (my_append proof suf_proof)
with Not_provable(mask) ->
	fprintf oc "%s " "Высказывание ложно при ";
	for i = 0 to (vars_cnt - 1) do
		let str_var = Hashtbl.find vars_is i in
		let str_val =  if (get_bool_value mask i) then "И" else "Л" in
		let suf = if i = (vars_cnt - 1) then "" else ", " in
		fprintf oc "%s=%s%s " str_var str_val suf
	done