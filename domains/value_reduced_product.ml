open Value_reduction
open Abstract_syntax_tree
open Value_domain

module ReducedProduct(R : VALUE_REDUCTION) =
(struct
module A = R.A
module B = R.B
  type t = R.t (* A.t * B.t *)
  
  let top = ((A.top),(B.top))

  let bottom= ((A.bottom),(B.bottom))

  let const c = R.reduce ((A.const c),(B.const c))

  let rand x y =R.reduce ((A.rand x y),(B.rand x y))
	
  let join x y = R.reduce ((A.join (fst x) (fst y)),(B.join (snd x) (snd y)))

  let meet x y =  R.reduce ((A.meet (fst x) (fst y)),(B.meet (snd x) (snd y)))
 
  let widen x y= R.reduce ((A.widen (fst x) (fst y)),(B.widen (snd x) (snd y)))

  let subset x y =  ((A.subset (fst x) (fst y)) && (B.subset (snd x) (snd y))) 

  let is_bottom a= A.is_bottom (fst a) && B.is_bottom (snd a) 
 
  let unary ((a,b):t) (op:int_unary_op) : t =R.reduce ((A.unary a op),(B.unary b op))

  let binary x y op =R.reduce ((A.binary (fst x) (fst y) op),(B.binary (snd x) (snd y) op))

  let bwd_unary x op r =R.reduce ((A.bwd_unary (fst x) op (fst r) ),(B.bwd_unary (snd x) op (snd r)))

  let bwd_binary x y op r =match ((A.bwd_binary (fst x) (fst y) op (fst r) ),(B.bwd_binary (snd x) (snd y) op (snd r))) with 
    |(a,b),(v,w)-> (R.reduce (a,v),R.reduce (b,w))

  let print fmt x =let _=let _=Format.fprintf fmt "(" in
	(A.print fmt (fst x)) in 
		let _=Format.fprintf fmt "," in
	 	    let _=(B.print fmt (snd x)) in 
				Format.fprintf fmt ")" 
    
  let compare x y op =match (A.compare (fst x) (fst y) op),(B.compare (snd x) (snd y) op) with 
    |(a,b),(v,w)-> (R.reduce (a,v),R.reduce (b,w))

  let is_pair a = invalid_arg "Concrete reducedproduct"
  let left_born a = invalid_arg "left born reducedproduct"
  let right_born a = invalid_arg "right born reducedproduct"
end : VALUE_DOMAIN)
