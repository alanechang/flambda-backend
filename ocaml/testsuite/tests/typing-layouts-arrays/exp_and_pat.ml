(* TEST
 readonly_files = "float_u_array.ml"
 modules = "${readonly_files}"
 * flambda2
 ** native
   flags = "-extension comprehensions -extension layouts_alpha"
 ** bytecode
   flags = "-extension comprehensions -extension layouts_alpha"
 ** native
   flags = "-extension comprehensions -extension layouts_beta"
 ** bytecode
   flags = "-extension comprehensions -extension layouts_beta"
*)

module Float_u = Stdlib__Float_u

let of_int = Float_u.of_int
let (=) = Float_u.equal

(* match statement *)
let () =
  let d = [| of_int 1; of_int 2 |] in
  match d with
    | [| a; b |] ->
      assert (a = of_int 1);
      assert (b = of_int 2)
    | _ -> assert false

(* let statement pattern *)
let () =
  let a = [||] in
  let b = [| of_int 1 |] in
  let c = Float_u_array.append a b in
  let[@warning "-8"] [| d |] = c in
  assert (d = of_int 1)

(* function argument pattern *)
let () =
  let[@warning "-8"] f [| b |] = b in
  assert (f [| of_int 1 |] = of_int 1)
