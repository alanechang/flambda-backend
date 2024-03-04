(* TEST
   readonly_files = "float_u_array.ml"
   modules = "${readonly_files}"
   * flambda2
   ** expect
     flags = "-extension comprehensions -extension layouts_alpha"
   ** expect
     flags = "-extension comprehensions -extension layouts_beta"
*)

module Float_u = Stdlib__Float_u

let of_int = Float_u.of_int
let (=) = Float_u.equal

(* array comprehension *)
(* CR layouts v4: add array comprehension support *)
(* let () =
  let check_i = Float_u_array.iteri (fun i x -> assert (x = of_int i)) in
  (* fixed size *)
  let a = [|Float_u.of_int e for e = 0 to 9|] in
  check_i a;
  (* call to length a *)
  let b = [| x for x in a |] in
  check_i b;
  (* dynamic size *)
  let c = [| Float_u.(add (mul (of_int 10) x) y) for x in a for y in b |] in
  check_i c;
  (* mix types *)
  let d = [| Float_u.(add (mul (of_int 10) x) (of_int y)) for x in a for y = 0 to 9 |] in
  check_i d;
  let e = [| Float_u.(add (of_int (10 * x)) y) for x = 0 to 9 for y in a |] in
  check_i e;
  () *)

let f () = [|Float_u.of_int e for e = 0 to 9|]

[%%expect{|
module Float_u = Stdlib__Float_u
val of_int : int -> float# = <fun>
val ( = ) : Float_u.t -> Float_u.t -> bool = <fun>
Line 26, characters 13-29:
26 | let f () = [|Float_u.of_int e for e = 0 to 9|]
                  ^^^^^^^^^^^^^^^^
Error: This expression has type float# but an expression was expected of type
         ('a : value)
       The layout of float# is float64, because
         it is the primitive float64 type float#.
       But the layout of float# must be a sublayout of value, because
         it's the element type of array comprehension.
|}];;
