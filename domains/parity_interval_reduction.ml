open Parity_domain
open Interval_domain
open Value_reduction

module ParityIntervalsReduction =
(struct
module A = Parity
module B = Intervals
type t = A.t * B.t
type bt = B.t

  let pair x = (Z.rem x (Z.of_int 2)) = Z.zero

let reduce ((par,itv):t) : t = 
  let a = B.left_born itv and b = B.right_born itv in
   let a2 = Z.add a (Z.of_int 1) and b2 = Z.sub b (Z.of_int 1) in
    match A.is_pair par, pair a, pair b with
      | true, true, true   | false, false, false-> par, itv
      | true, true, false  | false, false, true -> if (Z.gt a b2)  then A.bottom,B.bottom else par, (B.rand a b2)
      | true, false, false | false, true, true  -> if (Z.gt a2 b2) then A.bottom,B.bottom else par, (B.rand a2 b2)
      | true, false, true  | false, true, false -> if (Z.gt a2 b)  then A.bottom,B.bottom else par, (B.rand a2 b)

end : VALUE_REDUCTION)
