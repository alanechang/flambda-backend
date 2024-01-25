(* TEST
 readonly_files = "gen_u_array.ml test_gen_u_array.ml"
 modules = "${readonly_files}"
 * flambda2
 ** bytecode
   flags = "-extension layouts"
 ** bytecode
   flags = "-extension layouts_beta"
 ** native
   flags = "-extension layouts"
 ** native
   flags = "-extension layouts_beta"
*)


module Int32_I = struct
  include Int32
  let max_val = max_int
  let min_val = min_int
  let rand = Random.int32
  let print = Format.printf "%ld"
end

module Int32_array : Test_gen_u_array.S = struct
  include Stdlib.Array
  type element_t = int32
  type t = element_t array
  let map_to_array f a = map f a
  let map_from_array f a = map f a
  let max_length = Sys.max_array_length
  let equal = for_all2 (fun x y -> x = y)
  module I = Int32_I
end
module _ = Test_gen_u_array.Test (Int32_array)

module Int32_u_array0 :
  Gen_u_array.S0
  with type element_t = int32#
  and type ('a : any) array_t = 'a array = struct
  type element_t = int32#
  type ('a : any) array_t = 'a array
  type element_arg = unit -> element_t
  type t = element_t array
  external length : ('a : bits32). 'a array -> int = "%array_length"
  external get: ('a : bits32). 'a array -> int -> 'a = "%array_safe_get"
  let get t i = let a = get t i in fun () -> a
  external set: ('a : bits32). 'a array -> int -> 'a -> unit = "%array_safe_set"
  let set t i e = set t i (e ())
  external unsafe_get: ('a : bits32). 'a array -> int -> 'a = "%array_unsafe_get"
  let unsafe_get t i = let a = unsafe_get t i in fun () -> a
  external unsafe_set: ('a : bits32). 'a array -> int -> 'a -> unit = "%array_unsafe_set"
  let unsafe_set t i e = unsafe_set t i (e ())

  external unsafe_create : ('a : bits32). int -> 'a array =
    "caml_make_unboxed_int32_vect_bytecode" "caml_make_unboxed_int32_vect"
  external unsafe_blit : ('a : bits32).
    'a array -> int -> 'a array -> int -> int -> unit =
    "caml_array_blit" "caml_unboxed_int32_vect_blit"
  let empty () = [||]
  external to_boxed : ('a : bits32) -> (int32[@local_opt]) = "%box_int32"
  let compare_element x y = Int32.compare (to_boxed (x ())) (to_boxed (y ()))
end

module Int32_u_array = Gen_u_array.Make (Int32_u_array0)
module Int32_u_array_boxed = Test_gen_u_array.Make_boxed (struct
  module M = Int32_u_array
  module I = Int32_I
  module E = struct
    open Stdlib__Int32_u
    let to_boxed x = to_int32 (x ())
    let of_boxed x () = of_int32 x
  end
end)
module _ = Test_gen_u_array.Test (Int32_u_array_boxed)


(* Extra tests for functions not covered above *)
(* module Int32_u = Stdlib__Int32_u
let () =
  let open Int32_u_array in
  let module I = Int32 in
  let to_boxed = Int32_u.to_int32 in
  let u_of_int = Int32_u.of_int in
  let (+.) x y = I.add x y in
  let rec check_i_upto a i =
    if i >= 0 then begin
      assert (to_boxed (get a i) = I.of_int i);
      check_i_upto a (i - 1);
    end
  in

  let check_i a = check_i_upto a (length a - 1) in
  let check_inval f arg =
    match f arg with
    | _ -> assert false
    | exception (Invalid_argument _) -> ()
    | exception _ -> assert false
  in



  (* static blocks *)
  let r = [| #0l; #1l; #2l; #3l; #4l; #5l;
             #6l; #7l; #8l; #9l; #10l; #11l;
             #12l; #13l; #14l; #15l; #16l; #17l;
             #18l; #19l; #20l; #21l; #22l; #23l;
             #24l; #25l; #26l; #27l; #28l; #29l;
             #30l; #31l; #32l; #33l; #34l; #35l;
             #36l; #37l; #38l; #39l; #40l; #41l;
             #42l; #43l; #44l; #45l; #46l; #47l;
             #48l; #49l; #50l; #51l; #52l; #53l;
             #54l; #55l; #56l; #57l; #58l; #59l;
             #60l; #61l; #62l; #63l; #64l; #65l;
             #66l; #67l; #68l; #69l; #70l; #71l;
             #72l; #73l; #74l; #75l; #76l; #77l;
             #78l; #79l; #80l; #81l; #82l; #83l;
             #84l; #85l; #86l; #87l; #88l; #89l;
             #90l; #91l; #92l; #93l; #94l; #95l;
             #96l; #97l; #98l; #99l; #100l; #101l;
             #102l; #103l; #104l; #105l; #106l; #107l;
             #108l; #109l; #110l; #111l; #112l; #113l;
             #114l; #115l; #116l; #117l; #118l; #119l;
             #120l; #121l; #122l; #123l; #124l; #125l;
             #126l; #127l; #128l; #129l; #130l; #131l;
             #132l; #133l; #134l; #135l; #136l; #137l;
             #138l; #139l; #140l; #141l; #142l; #143l;
             #144l; #145l; #146l; #147l; #148l; #149l;
             #150l; #151l; #152l; #153l; #154l; #155l;
             #156l; #157l; #158l; #159l; #160l; #161l;
             #162l; #163l; #164l; #165l; #166l; #167l;
             #168l; #169l; #170l; #171l; #172l; #173l;
             #174l; #175l; #176l; #177l; #178l; #179l;
             #180l; #181l; #182l; #183l; #184l; #185l;
             #186l; #187l; #188l; #189l; #190l; #191l;
             #192l; #193l; #194l; #195l; #196l; #197l;
             #198l; #199l |]
  in
  check_i r;
  let r = [| #0l; #1l; #2l; #3l; #4l; #5l;
             #6l; #7l; #8l; #9l; #10l; #11l;
             #12l; #13l; #14l; #15l; #16l; #17l;
             #18l; #19l; #20l; #21l; #22l; #23l;
             #24l; #25l; #26l; #27l; #28l; #29l;
             #30l; #31l; #32l; #33l; #34l; #35l;
             #36l; #37l; #38l; #39l; #40l; #41l;
             #42l; #43l; #44l; #45l; #46l; #47l;
             #48l; #49l; #50l; #51l; #52l; #53l;
             #54l; #55l; #56l; #57l; #58l; #59l;
             #60l; #61l; #62l; #63l; #64l; #65l;
             #66l; #67l; #68l; #69l; #70l; #71l;
             #72l; #73l; #74l; #75l; #76l; #77l;
             #78l; #79l; #80l; #81l; #82l; #83l;
             #84l; #85l; #86l; #87l; #88l; #89l;
             #90l; #91l; #92l; #93l; #94l; #95l;
             #96l; #97l; #98l; #99l; #100l; #101l;
             #102l; #103l; #104l; #105l; #106l; #107l;
             #108l; #109l; #110l; #111l; #112l; #113l;
             #114l; #115l; #116l; #117l; #118l; #119l;
             #120l; #121l; #122l; #123l; #124l; #125l;
             #126l; #127l; #128l; #129l; #130l; #131l;
             #132l; #133l; #134l; #135l; #136l; #137l;
             #138l; #139l; #140l; #141l; #142l; #143l;
             #144l; #145l; #146l; #147l; #148l; #149l;
             #150l; #151l; #152l; #153l; #154l; #155l;
             #156l; #157l; #158l; #159l; #160l; #161l;
             #162l; #163l; #164l; #165l; #166l; #167l;
             #168l; #169l; #170l; #171l; #172l; #173l;
             #174l; #175l; #176l; #177l; #178l; #179l;
             #180l; #181l; #182l; #183l; #184l; #185l;
             #186l; #187l; #188l; #189l; #190l; #191l;
             #192l; #193l; #194l; #195l; #196l; #197l;
             #198l; #199l; #200l |]
  in
  check_i r;
  (* dynamic blocks *)
  let[@inline never] f x = x in
  let r = [| f #0l; f #1l; f #2l; f #3l; f #4l; f #5l;
             f #6l; f #7l; f #8l; f #9l; f #10l; f #11l;
             f #12l; f #13l; f #14l; f #15l; f #16l; f #17l;
             f #18l; f #19l; f #20l; f #21l; f #22l; f #23l;
             f #24l; f #25l; f #26l; f #27l; f #28l; f #29l;
             f #30l; f #31l; f #32l; f #33l; f #34l; f #35l;
             f #36l; f #37l; f #38l; f #39l; f #40l; f #41l;
             f #42l; f #43l; f #44l; f #45l; f #46l; f #47l;
             f #48l; f #49l; f #50l; f #51l; f #52l; f #53l;
             f #54l; f #55l; f #56l; f #57l; f #58l; f #59l;
             f #60l; f #61l; f #62l; f #63l; f #64l; f #65l;
             f #66l; f #67l; f #68l; f #69l; f #70l; f #71l;
             f #72l; f #73l; f #74l; f #75l; f #76l; f #77l;
             f #78l; f #79l; f #80l; f #81l; f #82l; f #83l;
             f #84l; f #85l; f #86l; f #87l; f #88l; f #89l;
             f #90l; f #91l; f #92l; f #93l; f #94l; f #95l;
             f #96l; f #97l; f #98l; f #99l; f #100l; f #101l;
             f #102l; f #103l; f #104l; f #105l; f #106l; f #107l;
             f #108l; f #109l; f #110l; f #111l; f #112l; f #113l;
             f #114l; f #115l; f #116l; f #117l; f #118l; f #119l;
             f #120l; f #121l; f #122l; f #123l; f #124l; f #125l;
             f #126l; f #127l; f #128l; f #129l; f #130l; f #131l;
             f #132l; f #133l; f #134l; f #135l; f #136l; f #137l;
             f #138l; f #139l; f #140l; f #141l; f #142l; f #143l;
             f #144l; f #145l; f #146l; f #147l; f #148l; f #149l;
             f #150l; f #151l; f #152l; f #153l; f #154l; f #155l;
             f #156l; f #157l; f #158l; f #159l; f #160l; f #161l;
             f #162l; f #163l; f #164l; f #165l; f #166l; f #167l;
             f #168l; f #169l; f #170l; f #171l; f #172l; f #173l;
             f #174l; f #175l; f #176l; f #177l; f #178l; f #179l;
             f #180l; f #181l; f #182l; f #183l; f #184l; f #185l;
             f #186l; f #187l; f #188l; f #189l; f #190l; f #191l;
             f #192l; f #193l; f #194l; f #195l; f #196l; f #197l;
             f #198l; f #199l |]
  in
  check_i r;
  let r = [| f #0l; f #1l; f #2l; f #3l; f #4l; f #5l;
             f #6l; f #7l; f #8l; f #9l; f #10l; f #11l;
             f #12l; f #13l; f #14l; f #15l; f #16l; f #17l;
             f #18l; f #19l; f #20l; f #21l; f #22l; f #23l;
             f #24l; f #25l; f #26l; f #27l; f #28l; f #29l;
             f #30l; f #31l; f #32l; f #33l; f #34l; f #35l;
             f #36l; f #37l; f #38l; f #39l; f #40l; f #41l;
             f #42l; f #43l; f #44l; f #45l; f #46l; f #47l;
             f #48l; f #49l; f #50l; f #51l; f #52l; f #53l;
             f #54l; f #55l; f #56l; f #57l; f #58l; f #59l;
             f #60l; f #61l; f #62l; f #63l; f #64l; f #65l;
             f #66l; f #67l; f #68l; f #69l; f #70l; f #71l;
             f #72l; f #73l; f #74l; f #75l; f #76l; f #77l;
             f #78l; f #79l; f #80l; f #81l; f #82l; f #83l;
             f #84l; f #85l; f #86l; f #87l; f #88l; f #89l;
             f #90l; f #91l; f #92l; f #93l; f #94l; f #95l;
             f #96l; f #97l; f #98l; f #99l; f #100l; f #101l;
             f #102l; f #103l; f #104l; f #105l; f #106l; f #107l;
             f #108l; f #109l; f #110l; f #111l; f #112l; f #113l;
             f #114l; f #115l; f #116l; f #117l; f #118l; f #119l;
             f #120l; f #121l; f #122l; f #123l; f #124l; f #125l;
             f #126l; f #127l; f #128l; f #129l; f #130l; f #131l;
             f #132l; f #133l; f #134l; f #135l; f #136l; f #137l;
             f #138l; f #139l; f #140l; f #141l; f #142l; f #143l;
             f #144l; f #145l; f #146l; f #147l; f #148l; f #149l;
             f #150l; f #151l; f #152l; f #153l; f #154l; f #155l;
             f #156l; f #157l; f #158l; f #159l; f #160l; f #161l;
             f #162l; f #163l; f #164l; f #165l; f #166l; f #167l;
             f #168l; f #169l; f #170l; f #171l; f #172l; f #173l;
             f #174l; f #175l; f #176l; f #177l; f #178l; f #179l;
             f #180l; f #181l; f #182l; f #183l; f #184l; f #185l;
             f #186l; f #187l; f #188l; f #189l; f #190l; f #191l;
             f #192l; f #193l; f #194l; f #195l; f #196l; f #197l;
             f #198l; f #199l; f #200l |]
  in
  check_i r;
  check_i [| #0l; ((fun x -> x) #1l)|];
  check_i [| #0l; ((fun x -> x) #1l); #2l|];
  () *)


(* expression and patterns *)
let () =
  let module M = Int32_u_array in
  let (=) = Stdlib__Int32_u.equal in
  (* match statement *)
  let d = [| #1l; #2l |] in
  (match d with
    | [| a; b |] ->
      assert (a = #1l);
      assert (b = #2l)
    | _ -> assert false);

  (* let statement pattern *)
  let a = [||] in
  let b = [| #1l |] in
  let c = M.append a b in
  let[@warning "-8"] [| d |] = c in
  assert (d = #1l);

  (* function argument pattern *)
  let[@warning "-8"] f [| b |] = b in
  assert (f [| #1l |] = #1l);
  ()
