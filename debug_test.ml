(* module type S0 = sig
  type t : any
  val add : t -> t -> t
end

module type S = sig
  include S0
  val double : t -> t
end

(* let g (type a : any) (module M0 : S0 with type t = a) =
  let module M = struct
    include M0
    let double x = add x x
  end in
  (module M : S with type t = a) *)
let g: ('a : any). (module S0 with type t = 'a) -> (module S with type t = 'a) = fun (module S0) ->
  let module M = struct
    include M0
    let double x = add x x
  end in
  (module M : S with type t = a)
module Float_u = Stdlib__Float_u
let () =
  let module M = struct
    type t = float#
    let add = Float_u.add
  end in
  let O = g (module M) in
  O.double #1. *)


let open_out_bin name =
  open_out_gen [Open_wronly; Open_creat; Open_trunc; Open_binary] 0o666 name

let f filename flags =
  let oc = open_out_bin filename in
  let i = Int64.of_string "123456789123456" in
  Marshal.to_channel oc (i,i) flags;
  ()

let () = Printf.printf "hello world"
