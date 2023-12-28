(* module Float_u_array = Stdlib__Float_u_array
module Float_u = Stdlib__Float_u

let of_int = Float_u.of_int
let (=) = Float_u.equal

let () =
  let[@inline never][@warning "-8"] f [| b |] = b in
  assert (f [| of_int 1 |] = of_int 1) *)

module M : sig
  type ('a : float64) t = 'a
  val f : 'a -> 'a t
end = struct
  type ('a : float64) t = 'a

  let f = fun (x : float#) -> x
  (* let g x = f x
  let h x = g x
  let i x = h x *)
  (* let test () = i #1. *)
end
