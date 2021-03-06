(*
  Cours "Typage et Analyse Statique"
  Université Pierre et Marie Curie
  Antoine Miné 2015
*)

(* 
   The constant domain
 *)

open Abstract_syntax_tree
open Value_domain

  
module Intervals = (struct
  
  (* types *)
  (* ***** *)


  (* type of abstract values *)
  type borne =
   	| Cst of Z.t
   	| POS_INF
  	| NEG_INF

  type intervalle =
	| INTERVALLE of borne * borne
	| BOT

  type t = intervalle

  (* utilities *)
  let gt_zero a = match a with
	| Cst c -> c > Z.zero
	| _ -> false
  let min borneA borneB =
        match borneA, borneB with
        | NEG_INF, _ | _, NEG_INF -> NEG_INF
        | POS_INF, x | x, POS_INF -> x
        | Cst x, Cst y ->
                if x < y then Cst x else Cst y

  let max borneA borneB =
        match borneA, borneB with
        | POS_INF, _ | _, POS_INF -> POS_INF
        | NEG_INF, x | x, NEG_INF -> x
        | Cst x, Cst y ->
                if x > y then Cst x else Cst y

  let neg_born a = match a with
	| Cst x -> Cst (Z.neg x)
	| POS_INF -> POS_INF
	| NEG_INF -> NEG_INF

  let add_born a b  = match a, b with
	| Cst x, Cst y -> Cst (Z.add x y)
	| POS_INF,NEG_INF | NEG_INF,POS_INF -> invalid_arg "bound_add" (* (+∞) + (−∞) *)
	| POS_INF,_ | _,POS_INF -> POS_INF
	| NEG_INF,_ | _,NEG_INF -> NEG_INF

  let sub_born a b = match a,b  with
	| Cst x, Cst y -> Cst (Z.sub x y)
	| POS_INF,NEG_INF | NEG_INF,POS_INF -> invalid_arg "bound_sub" (* (+∞) + (−∞) *)
	| NEG_INF,_ | _,NEG_INF -> NEG_INF
	| POS_INF,_ | _,POS_INF -> POS_INF

  let mul_born a b = match a,b  with
	| Cst x, Cst y -> Cst (Z.mul x y)
	| NEG_INF,NEG_INF -> POS_INF 
	| POS_INF,POS_INF -> POS_INF 
	| NEG_INF, POS_INF | POS_INF,NEG_INF -> NEG_INF
	| NEG_INF, Cst x | Cst x,NEG_INF ->
		if x = Z.zero then
			Cst Z.zero
		else 
			if x < Z.zero then
				POS_INF
			else
				NEG_INF
	| POS_INF, Cst x | Cst x,POS_INF ->
		if x = Z.zero then
			Cst Z.zero
		else 
			if x < Z.zero then
				NEG_INF
			else
				POS_INF

  let div_born a b = match a,b  with
	| Cst x, Cst y -> Cst (Z.div x y)
	| x,NEG_INF | x,POS_INF -> Cst Z.zero
	| POS_INF, Cst x -> if x > Z.zero then
				POS_INF
			    else
				NEG_INF				
	| NEG_INF, Cst x -> if x > Z.zero then
				NEG_INF
			    else
				POS_INF	
		

  (* ********* *)
     
  (* interface implementation *)
  (* ************************ *)


  (* unrestricted value *)
  let top = INTERVALLE(NEG_INF, POS_INF)  (* Intervalle [-8; +8] *)

  (* bottom value *)
  let bottom = BOT

  (* constant *)
  let const c = INTERVALLE(Cst c, Cst c)

  (* interval *)
  let rand x y =
    if x=y then const x (* [x,x] *)
    else if x<y then INTERVALLE(Cst x, Cst y) (* [x ,y]*)
    else BOT (* Intervalle non possible *)


  (* arithmetic operations *)

  let neg a = match a with
	| INTERVALLE(x,y) -> INTERVALLE (neg_born y, neg_born x)
	| x -> x

  let add x y = match x,y with
	| INTERVALLE(a,b),INTERVALLE(c,d) -> INTERVALLE(add_born a d, add_born b c)
	| _, BOT | BOT,_ -> BOT

  let sub x y = match x,y with
	| INTERVALLE(a,b),INTERVALLE(c,d) -> INTERVALLE(sub_born a c, sub_born b d)
	| _, BOT | BOT,_ -> BOT

  let mul x y = match x,y with
	| BOT,_ | _, BOT -> BOT
        | INTERVALLE(a, b), INTERVALLE(c, d) ->
                let ac = mul_born a c in
                let ad = mul_born a d in
                let bc = mul_born b c in
                let bd = mul_born b d in
                let borne_inf = min (min ac ad) (min bc bd) in
                let borne_max = max (max ac ad) (max bc bd) in
                INTERVALLE(borne_inf, borne_max)

  let div x y = match x,y with
	| BOT,_ | _,BOT -> BOT
        | INTERVALLE (_, _), INTERVALLE(Cst x, _)
        | INTERVALLE (_, _), INTERVALLE(_, Cst x) when x = Z.zero -> BOT
	| INTERVALLE(a,b), INTERVALLE(c,d) -> 
			let ac = div_born a c in
			let ad = div_born a d in
			let bc = div_born b c in
			let bd = div_born b d in
			let borne_inf = if gt_zero c then
				 min ac ad else min bc bd in
			let borne_sup = if gt_zero c then
				 min bc bd else max ac ad in
			INTERVALLE(borne_inf,borne_sup)


  (* set-theoretic operations *)
  
  let join a b = match a,b with
  | BOT,x | x,BOT -> x
  | _ -> top

  let meet a b = match a,b with
  | _ -> BOT


  (* no need for a widening as the domain has finite height; we use the join *)
  let widen = join


  (* comparison operations (filters) *)

  let eq a b =
    (* this is not very precise, how can we improve it ? *)
    a, b

  let neq a b =
    a, b
      
  let geq a b =
    a, b
      
  let gt a b =
    a, b


  (* subset inclusion of concretizations *)
  let subset a b = match a,b with
  | BOT,_ -> true
  | _ -> false

  (* check the emptyness of the concretization *)
  let is_bottom a =
    a=BOT

  (* prints abstract element *)
  let print fmt x = match x with
  | BOT -> Format.fprintf fmt "bottom"
  | INTERVALLE(Cst x,Cst y) -> Format.fprintf fmt "[%s,%s]" (Z.to_string x) (Z.to_string y)
  | INTERVALLE(NEG_INF, Cst y) -> Format.fprintf fmt "[-∞,%s]" (Z.to_string y)
  | INTERVALLE(Cst x, POS_INF) -> Format.fprintf fmt "[%s,+∞]" (Z.to_string x)
  | INTERVALLE(NEG_INF, POS_INF) -> Format.fprintf fmt "[-∞,+∞]"
  | _ -> invalid_arg "We should not be here"
(* operator dispatch *)
        
  let unary x op = match op with
  | AST_UNARY_PLUS  -> x
  | AST_UNARY_MINUS -> neg x

  let binary x y op = match op with
  | AST_PLUS     -> add x y
  | AST_MINUS    -> sub x y
  | AST_MULTIPLY -> mul x y
  | AST_DIVIDE   -> div x y

  let compare x y op = match op with
  | AST_EQUAL         -> eq x y
  | AST_NOT_EQUAL     -> neq x y
  | AST_GREATER_EQUAL -> geq x y
  | AST_GREATER       -> gt x y
  | AST_LESS_EQUAL    -> let y',x' = geq y x in x',y'
  | AST_LESS          -> let y',x' = gt y x in x',y'
        


  let bwd_unary x op r = match op with
  | AST_UNARY_PLUS  -> meet x r
  | AST_UNARY_MINUS -> meet x (neg r)

        
  let bwd_binary x y op r = match op with

  | AST_PLUS ->
      (* r=x+y => x=r-y and y=r-x *)      
      meet x (sub r y), meet y (sub r x)

  | AST_MINUS ->
      (* r=x-y => x=y+r and y=x-r *)
      meet x (add y r), meet y (sub y r)
        
  | AST_MULTIPLY ->
      (* r=x*y => (x=r/y or y=r=0) and (y=r/x or x=r=0)  *)
      let contains_zero o = subset (const Z.zero) o in
      (if contains_zero y && contains_zero r then x else meet x (div r y)),
      (if contains_zero x && contains_zero r then y else meet y (div r x))
        
  | AST_DIVIDE ->
      (* this is sound, but not precise *)
      x, y
        
      
end : VALUE_DOMAIN)

    
