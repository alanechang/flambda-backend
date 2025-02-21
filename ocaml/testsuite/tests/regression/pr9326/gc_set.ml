(* TEST
*)

module OCaml_5 = struct
open Gc

let min_heap_sz = 524288 (* 512k *)
let space_overhead = 70
let stack_limit = 4194304 (* 4M *)
let custom_major_ratio = 40
let custom_minor_ratio = 99
let custom_minor_max_size = 4096

let run () =
  let g1 = Gc.get() in
  (* Do not use { g1 with ... }, so that the code will break if more fields
     are added to the Gc.control record type *)
  Gc.set { minor_heap_size = min_heap_sz;
           major_heap_increment = g1.major_heap_increment;
           space_overhead = space_overhead;
           verbose = g1.verbose;
           max_overhead = g1.max_overhead;
           stack_limit = stack_limit;
           allocation_policy = g1.allocation_policy;
           window_size = g1.window_size;
           custom_major_ratio = custom_major_ratio;
           custom_minor_ratio = custom_minor_ratio;
           custom_minor_max_size = custom_minor_max_size };
  let g2 = Gc.get() in
  assert (g2.minor_heap_size = min_heap_sz);
  assert (g2.space_overhead = space_overhead);
  assert (g2.verbose = g1.verbose);
  assert (g2.max_overhead = g1.max_overhead);
  assert (g2.stack_limit = stack_limit);
  assert (g2.allocation_policy = g1.allocation_policy);
  assert (g2.window_size = g1.window_size);
  assert (g2.custom_major_ratio = custom_major_ratio);
  assert (g2.custom_minor_ratio = custom_minor_ratio);
  assert (g2.custom_minor_max_size = custom_minor_max_size)
end

(* OCaml 4 and 5's runtime differ in what fields are controllable via [Gc.set],
   e.g. [stack_limit] can be changed in OCaml 5 native code but not in OCaml 4
   native code.
 *)

module OCaml_4 = struct
open Gc

let min_heap_sz = 524288 (* 512k *)
let maj_heap_inc = 4194304 (* 4M *)

let run () =
  let g1 = Gc.get() in
  (* Do not use { g1 with ... }, so that the code will break if more fields
     are added to the Gc.control record type *)
  Gc.set { minor_heap_size = min_heap_sz;
           major_heap_increment = maj_heap_inc;
           space_overhead = g1.space_overhead;
           verbose = g1.verbose;
           max_overhead = g1.max_overhead;
           stack_limit = g1.stack_limit;
           allocation_policy = g1.allocation_policy;
           window_size = g1.window_size;
           custom_major_ratio = g1.custom_major_ratio;
           custom_minor_ratio = g1.custom_minor_ratio;
           custom_minor_max_size = g1.custom_minor_max_size };
  let g2 = Gc.get() in
  assert (g2.minor_heap_size = min_heap_sz);
  assert (g2.major_heap_increment = maj_heap_inc);
  assert (g2.space_overhead = g1.space_overhead);
  assert (g2.verbose = g1.verbose);
  assert (g2.max_overhead = g1.max_overhead);
  assert (g2.stack_limit = g1.stack_limit);
  assert (g2.allocation_policy = g1.allocation_policy);
  assert (g2.window_size = g1.window_size);
  assert (g2.custom_major_ratio = g1.custom_major_ratio);
  assert (g2.custom_minor_ratio = g1.custom_minor_ratio);
  assert (g2.custom_minor_max_size = g1.custom_minor_max_size)

end

external runtime5 : unit -> bool = "%runtime5"
let () = if runtime5 () then OCaml_5.run () else OCaml_4.run ()
