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

module Int64_I = struct
  include Int64
  let max_val = max_int
  let min_val = min_int
  let rand = Random.int64
  let print = Format.printf "%Ld"
end

module Int64_array : Test_gen_u_array.S = struct
  include Stdlib.Array
  type element_t = int64
  type t = element_t array
  let map_to_array f a = map f a
  let map_from_array f a = map f a
  let max_length = Sys.max_array_length
  let equal = for_all2 (fun x y -> x = y)
  module I = Int64_I
end
module _ = Test_gen_u_array.Test (Int64_array)

module Int64_u_array0 :
  Gen_u_array.S0
  with type element_t = int64#
  and type ('a : any) array_t = 'a array = struct
  type element_t = int64#
  type ('a : any) array_t = 'a array
  type element_arg = unit -> element_t
  type t = element_t array
  external length : ('a : bits64). 'a array -> int = "%array_length"
  external get: ('a : bits64). 'a array -> int -> 'a = "%array_safe_get"
  let get t i = let a = get t i in fun () -> a
  external set: ('a : bits64). 'a array -> int -> 'a -> unit = "%array_safe_set"
  let set t i e = set t i (e ())
  external unsafe_get: ('a : bits64). 'a array -> int -> 'a = "%array_unsafe_get"
  let unsafe_get t i = let a = unsafe_get t i in fun () -> a
  external unsafe_set: ('a : bits64). 'a array -> int -> 'a -> unit = "%array_unsafe_set"
  let unsafe_set t i e = unsafe_set t i (e ())

  external unsafe_create : ('a : bits64). int -> 'a array =
    "caml_make_unboxed_int64_vect_bytecode" "caml_make_unboxed_int64_vect"
  external unsafe_blit : ('a : bits64).
    'a array -> int -> 'a array -> int -> int -> unit =
    "caml_array_blit" "caml_unboxed_int64_vect_blit"
  let empty () = [||]
  external to_boxed : ('a : bits64) -> (int64[@local_opt]) = "%box_int64"
  let compare_element x y = Int64.compare (to_boxed (x ())) (to_boxed (y ()))
end

module Int64_u_array = Gen_u_array.Make (Int64_u_array0)
module Int64_u_array_boxed = Test_gen_u_array.Make_boxed (struct
  module M = Int64_u_array
  module I = Int64_I
  module E = struct
    open Stdlib__Int64_u
    let to_boxed x = to_int64 (x ())
    let of_boxed x () = of_int64 x
  end
end)
module _ = Test_gen_u_array.Test (Int64_u_array_boxed)



(* Extra tests for functions not covered above *)
(* module Int64_u = Stdlib__Int64_u
let () =
  let open Std_Int64_u_array in
  let module I = Int64 in
  let to_boxed = Int64_u.to_int64 in
  let u_of_int = Int64_u.of_int in
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
  let r = [| #0L; #1L; #2L; #3L; #4L; #5L;
             #6L; #7L; #8L; #9L; #10L; #11L;
             #12L; #13L; #14L; #15L; #16L; #17L;
             #18L; #19L; #20L; #21L; #22L; #23L;
             #24L; #25L; #26L; #27L; #28L; #29L;
             #30L; #31L; #32L; #33L; #34L; #35L;
             #36L; #37L; #38L; #39L; #40L; #41L;
             #42L; #43L; #44L; #45L; #46L; #47L;
             #48L; #49L; #50L; #51L; #52L; #53L;
             #54L; #55L; #56L; #57L; #58L; #59L;
             #60L; #61L; #62L; #63L; #64L; #65L;
             #66L; #67L; #68L; #69L; #70L; #71L;
             #72L; #73L; #74L; #75L; #76L; #77L;
             #78L; #79L; #80L; #81L; #82L; #83L;
             #84L; #85L; #86L; #87L; #88L; #89L;
             #90L; #91L; #92L; #93L; #94L; #95L;
             #96L; #97L; #98L; #99L; #100L; #101L;
             #102L; #103L; #104L; #105L; #106L; #107L;
             #108L; #109L; #110L; #111L; #112L; #113L;
             #114L; #115L; #116L; #117L; #118L; #119L;
             #120L; #121L; #122L; #123L; #124L; #125L;
             #126L; #127L; #128L; #129L; #130L; #131L;
             #132L; #133L; #134L; #135L; #136L; #137L;
             #138L; #139L; #140L; #141L; #142L; #143L;
             #144L; #145L; #146L; #147L; #148L; #149L;
             #150L; #151L; #152L; #153L; #154L; #155L;
             #156L; #157L; #158L; #159L; #160L; #161L;
             #162L; #163L; #164L; #165L; #166L; #167L;
             #168L; #169L; #170L; #171L; #172L; #173L;
             #174L; #175L; #176L; #177L; #178L; #179L;
             #180L; #181L; #182L; #183L; #184L; #185L;
             #186L; #187L; #188L; #189L; #190L; #191L;
             #192L; #193L; #194L; #195L; #196L; #197L;
             #198L; #199L |]
  in
  check_i r;
  let r = [| #0L; #1L; #2L; #3L; #4L; #5L;
             #6L; #7L; #8L; #9L; #10L; #11L;
             #12L; #13L; #14L; #15L; #16L; #17L;
             #18L; #19L; #20L; #21L; #22L; #23L;
             #24L; #25L; #26L; #27L; #28L; #29L;
             #30L; #31L; #32L; #33L; #34L; #35L;
             #36L; #37L; #38L; #39L; #40L; #41L;
             #42L; #43L; #44L; #45L; #46L; #47L;
             #48L; #49L; #50L; #51L; #52L; #53L;
             #54L; #55L; #56L; #57L; #58L; #59L;
             #60L; #61L; #62L; #63L; #64L; #65L;
             #66L; #67L; #68L; #69L; #70L; #71L;
             #72L; #73L; #74L; #75L; #76L; #77L;
             #78L; #79L; #80L; #81L; #82L; #83L;
             #84L; #85L; #86L; #87L; #88L; #89L;
             #90L; #91L; #92L; #93L; #94L; #95L;
             #96L; #97L; #98L; #99L; #100L; #101L;
             #102L; #103L; #104L; #105L; #106L; #107L;
             #108L; #109L; #110L; #111L; #112L; #113L;
             #114L; #115L; #116L; #117L; #118L; #119L;
             #120L; #121L; #122L; #123L; #124L; #125L;
             #126L; #127L; #128L; #129L; #130L; #131L;
             #132L; #133L; #134L; #135L; #136L; #137L;
             #138L; #139L; #140L; #141L; #142L; #143L;
             #144L; #145L; #146L; #147L; #148L; #149L;
             #150L; #151L; #152L; #153L; #154L; #155L;
             #156L; #157L; #158L; #159L; #160L; #161L;
             #162L; #163L; #164L; #165L; #166L; #167L;
             #168L; #169L; #170L; #171L; #172L; #173L;
             #174L; #175L; #176L; #177L; #178L; #179L;
             #180L; #181L; #182L; #183L; #184L; #185L;
             #186L; #187L; #188L; #189L; #190L; #191L;
             #192L; #193L; #194L; #195L; #196L; #197L;
             #198L; #199L; #200L |]
  in
  check_i r;
  (* dynamic blocks *)
  let[@inline never] f x = x in
  let r = [| f #0L; f #1L; f #2L; f #3L; f #4L; f #5L;
             f #6L; f #7L; f #8L; f #9L; f #10L; f #11L;
             f #12L; f #13L; f #14L; f #15L; f #16L; f #17L;
             f #18L; f #19L; f #20L; f #21L; f #22L; f #23L;
             f #24L; f #25L; f #26L; f #27L; f #28L; f #29L;
             f #30L; f #31L; f #32L; f #33L; f #34L; f #35L;
             f #36L; f #37L; f #38L; f #39L; f #40L; f #41L;
             f #42L; f #43L; f #44L; f #45L; f #46L; f #47L;
             f #48L; f #49L; f #50L; f #51L; f #52L; f #53L;
             f #54L; f #55L; f #56L; f #57L; f #58L; f #59L;
             f #60L; f #61L; f #62L; f #63L; f #64L; f #65L;
             f #66L; f #67L; f #68L; f #69L; f #70L; f #71L;
             f #72L; f #73L; f #74L; f #75L; f #76L; f #77L;
             f #78L; f #79L; f #80L; f #81L; f #82L; f #83L;
             f #84L; f #85L; f #86L; f #87L; f #88L; f #89L;
             f #90L; f #91L; f #92L; f #93L; f #94L; f #95L;
             f #96L; f #97L; f #98L; f #99L; f #100L; f #101L;
             f #102L; f #103L; f #104L; f #105L; f #106L; f #107L;
             f #108L; f #109L; f #110L; f #111L; f #112L; f #113L;
             f #114L; f #115L; f #116L; f #117L; f #118L; f #119L;
             f #120L; f #121L; f #122L; f #123L; f #124L; f #125L;
             f #126L; f #127L; f #128L; f #129L; f #130L; f #131L;
             f #132L; f #133L; f #134L; f #135L; f #136L; f #137L;
             f #138L; f #139L; f #140L; f #141L; f #142L; f #143L;
             f #144L; f #145L; f #146L; f #147L; f #148L; f #149L;
             f #150L; f #151L; f #152L; f #153L; f #154L; f #155L;
             f #156L; f #157L; f #158L; f #159L; f #160L; f #161L;
             f #162L; f #163L; f #164L; f #165L; f #166L; f #167L;
             f #168L; f #169L; f #170L; f #171L; f #172L; f #173L;
             f #174L; f #175L; f #176L; f #177L; f #178L; f #179L;
             f #180L; f #181L; f #182L; f #183L; f #184L; f #185L;
             f #186L; f #187L; f #188L; f #189L; f #190L; f #191L;
             f #192L; f #193L; f #194L; f #195L; f #196L; f #197L;
             f #198L; f #199L |]
  in
  check_i r;
  let r = [| f #0L; f #1L; f #2L; f #3L; f #4L; f #5L;
             f #6L; f #7L; f #8L; f #9L; f #10L; f #11L;
             f #12L; f #13L; f #14L; f #15L; f #16L; f #17L;
             f #18L; f #19L; f #20L; f #21L; f #22L; f #23L;
             f #24L; f #25L; f #26L; f #27L; f #28L; f #29L;
             f #30L; f #31L; f #32L; f #33L; f #34L; f #35L;
             f #36L; f #37L; f #38L; f #39L; f #40L; f #41L;
             f #42L; f #43L; f #44L; f #45L; f #46L; f #47L;
             f #48L; f #49L; f #50L; f #51L; f #52L; f #53L;
             f #54L; f #55L; f #56L; f #57L; f #58L; f #59L;
             f #60L; f #61L; f #62L; f #63L; f #64L; f #65L;
             f #66L; f #67L; f #68L; f #69L; f #70L; f #71L;
             f #72L; f #73L; f #74L; f #75L; f #76L; f #77L;
             f #78L; f #79L; f #80L; f #81L; f #82L; f #83L;
             f #84L; f #85L; f #86L; f #87L; f #88L; f #89L;
             f #90L; f #91L; f #92L; f #93L; f #94L; f #95L;
             f #96L; f #97L; f #98L; f #99L; f #100L; f #101L;
             f #102L; f #103L; f #104L; f #105L; f #106L; f #107L;
             f #108L; f #109L; f #110L; f #111L; f #112L; f #113L;
             f #114L; f #115L; f #116L; f #117L; f #118L; f #119L;
             f #120L; f #121L; f #122L; f #123L; f #124L; f #125L;
             f #126L; f #127L; f #128L; f #129L; f #130L; f #131L;
             f #132L; f #133L; f #134L; f #135L; f #136L; f #137L;
             f #138L; f #139L; f #140L; f #141L; f #142L; f #143L;
             f #144L; f #145L; f #146L; f #147L; f #148L; f #149L;
             f #150L; f #151L; f #152L; f #153L; f #154L; f #155L;
             f #156L; f #157L; f #158L; f #159L; f #160L; f #161L;
             f #162L; f #163L; f #164L; f #165L; f #166L; f #167L;
             f #168L; f #169L; f #170L; f #171L; f #172L; f #173L;
             f #174L; f #175L; f #176L; f #177L; f #178L; f #179L;
             f #180L; f #181L; f #182L; f #183L; f #184L; f #185L;
             f #186L; f #187L; f #188L; f #189L; f #190L; f #191L;
             f #192L; f #193L; f #194L; f #195L; f #196L; f #197L;
             f #198L; f #199L; f #200L |]
  in
  check_i r;
  check_i [| #0L; ((fun x -> x) #1L)|];
  check_i [| #0L; ((fun x -> x) #1L); #2L|]; *)


(* expression and patterns *)
let () =
  let module M = Int64_u_array in
  let (=) = Stdlib__Int64_u.equal in
  (* match statement *)
  let d = [| #1L; #2L |] in
  (match d with
    | [| a; b |] ->
      assert (a = #1L);
      assert (b = #2L)
    | _ -> assert false);

  (* let statement pattern *)
  let a = [||] in
  let b = [| #1L |] in
  let c = M.append a b in
  let[@warning "-8"] [| d |] = c in
  assert (d = #1L);

  (* function argument pattern *)
  let[@warning "-8"] f [| b |] = b in
  assert (f [| #1L |] = #1L);
  ()
