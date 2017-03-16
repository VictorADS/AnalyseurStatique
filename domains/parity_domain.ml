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

  
module Parity = (struct
  
  (* types *)
  (* ***** *)


  (* type of abstract values *)
  type parite =
	| PAIR
	| IMPAIR
	| TOP
	| BOT

  type t = parite

  (* utilities *)


  (* ********* *)
     
  (* interface implementation *)
  (* ************************ *)


  (* unrestricted value *)
  let top = TOP

  (* bottom value *)
  let bottom = BOT

  (* constant *)
  let const c = 
	let remainder = Z.rem c (Z.of_int 2) in
		if (remainder = Z.zero) then
			PAIR
		else
			IMPAIR

  (* interval *)
  let rand x y =
    if x=y then
	let remainder = Z.rem x (Z.of_int 2) in
		if(remainder = Z.zero) then
			PAIR
		else
			IMPAIR
    else if x<y then TOP
    else BOT


  (* arithmetic operations *)

  let neg a = a

  let add x y = match x,y with 
	| BOT, x | x, BOT -> BOT
	| TOP, x | x, TOP -> TOP
	| PAIR, PAIR -> PAIR
	| IMPAIR, IMPAIR -> PAIR
	| PAIR, IMPAIR | IMPAIR, PAIR -> IMPAIR

  let sub x y = match x,y with 
	| BOT, x | x, BOT -> BOT
	| TOP, x | x, TOP -> TOP
	| PAIR, PAIR -> PAIR
	| IMPAIR, IMPAIR -> PAIR
	| PAIR, IMPAIR | IMPAIR, PAIR -> IMPAIR

  let mul x y = match x,y with 
	| BOT, x | x, BOT -> BOT
	| TOP, x | x, TOP -> TOP
	| PAIR, PAIR -> PAIR
	| IMPAIR, IMPAIR -> PAIR
	| PAIR, IMPAIR | IMPAIR, PAIR -> IMPAIR

  let div x y = x


  (* set-theoretic operations *)

  (* union *)
  let join a b = a

  (* intersec *)
  let meet a b = a


  (* no need for a widening as the domain has finite height; we use the join *)
  let widen a b = a

  (* comparison operations (filters) *)

  let eq a b = a,b

  let neq interA interB = interA,interB


  let geq interA interB = interA, interB
      
  let gt interA interB = interA, interB



  (* subset inclusion of concretizations *)
  let subset a b = true

  (* check the emptyness of the concretization *)
  let is_bottom a =
    a=BOT

  (* prints abstract element *)
  let print fmt x = match x with
  | BOT -> Format.fprintf fmt "bottom"
  | TOP -> Format.fprintf fmt "Top"
  | PAIR -> Format.fprintf fmt "Pair"
  | IMPAIR -> Format.fprintf fmt "Impair"
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
      let contains_zero o = subset Z.zero o in
      (if contains_zero y && contains_zero r then x else meet x (div r y)),
      (if contains_zero x && contains_zero r then y else meet y (div r x))
        
  | AST_DIVIDE ->
      (* this is sound, but not precise *)
      x, y
        
      
end : VALUE_DOMAIN)

    
