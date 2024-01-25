(* TEST
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

module type Array0_gen = sig
  (* An alias for the type of arrays. *)
  type element_t: any
  type ('a : any) array_t
  type element_arg = unit -> element_t
  type t = element_t array_t

  (* Array operations *)

  val length : t -> int
  val get: t -> int -> element_arg
  val set: t -> int -> element_arg -> unit
  val unsafe_get: t -> int -> element_arg
  val unsafe_set: t -> int -> element_arg -> unit
  val unsafe_create : int -> t
  val unsafe_blit :
    t -> int -> t -> int -> int -> unit
  val empty : unit -> t
  val compare_element: element_arg -> element_arg -> int
end


module type Array_gen = sig
include Array0_gen

val make : int -> element_arg -> t
(** [make n x] returns a fresh array of length [n],
   initialized with [x].
   All the elements of this new array are initially
   physically equal to [x] (in the sense of the [==] predicate).
   Consequently, if [x] is mutable, it is shared among all elements
   of the array, and modifying [x] through one of the array entries
   will modify all other entries at the same time.

   @raise Invalid_argument if [n < 0] or [n > Sys.max_array_length].
   If the value of [x] is a floating-point number, then the maximum
   size is only [Sys.max_array_length / 2].*)

val create : int -> element_arg -> t
  [@@ocaml.deprecated "Use Array.make/ArrayLabels.make instead."]
(** @deprecated [create] is an alias for {!make}. *)

(* external create_float: int -> float array = "caml_make_float_vect"
 * (** [create_float n] returns a fresh float array of length [n],
 *     with uninitialized data.
 *     @since 4.03 *)
 *
 * val make_float: int -> float array
 *   [@@ocaml.deprecated
 *     "Use Array.create_float/ArrayLabels.create_float instead."]
 * (** @deprecated [make_float] is an alias for {!create_float}. *) *)


val init : int -> (int -> element_arg) -> t
(** [init n f] returns a fresh array of length [n],
   with element number [i] initialized to the result of [f i].
   In other terms, [init n f] tabulates the results of [f]
   applied to the integers [0] to [n-1].

   @raise Invalid_argument if [n < 0] or [n > Sys.max_array_length].
   If the return type of [f] is [float], then the maximum
   size is only [Sys.max_array_length / 2].*)

val make_matrix : int -> int -> element_arg -> t array
(** [make_matrix dimx dimy e] returns a two-dimensional array
   (an array of arrays) with first dimension [dimx] and
   second dimension [dimy]. All the elements of this new matrix
   are initially physically equal to [e].
   The element ([x,y]) of a matrix [m] is accessed
   with the notation [m.(x).(y)].

   @raise Invalid_argument if [dimx] or [dimy] is negative or
   greater than {!Sys.max_array_length}.
   If the value of [e] is a floating-point number, then the maximum
   size is only [Sys.max_array_length / 2]. *)

val create_matrix : int -> int -> element_arg -> t array
  [@@ocaml.deprecated
    "Use Array.make_matrix/ArrayLabels.make_matrix instead."]
(** @deprecated [create_matrix] is an alias for {!make_matrix}. *)

val append : t -> t -> t
(** [append v1 v2] returns a fresh array containing the
   concatenation of the arrays [v1] and [v2].
   @raise Invalid_argument if
   [length v1 + length v2 > Sys.max_array_length]. *)

val concat : t list -> t
(** Same as {!append}, but concatenates a list of arrays. *)

val sub : t -> int -> int -> t
(** [sub a pos len] returns a fresh array of length [len],
   containing the elements number [pos] to [pos + len - 1]
   of array [a].

   @raise Invalid_argument if [pos] and [len] do not
   designate a valid subarray of [a]; that is, if
   [pos < 0], or [len < 0], or [pos + len > length a]. *)

val copy : t -> t
(** [copy a] returns a copy of [a], that is, a fresh array
   containing the same elements as [a]. *)

val fill : t -> int -> int -> element_arg -> unit
(** [fill a pos len x] modifies the array [a] in place,
   storing [x] in elements number [pos] to [pos + len - 1].

   @raise Invalid_argument if [pos] and [len] do not
   designate a valid subarray of [a]. *)

val blit :
  t -> int -> t -> int -> int ->
    unit
(** [blit src src_pos dst dst_pos len] copies [len] elements
   from array [src], starting at element number [src_pos], to array [dst],
   starting at element number [dst_pos]. It works correctly even if
   [src] and [dst] are the same array, and the source and
   destination chunks overlap.

   @raise Invalid_argument if [src_pos] and [len] do not
   designate a valid subarray of [src], or if [dst_pos] and [len] do not
   designate a valid subarray of [dst]. *)

(* val to_list : t -> element_arg list
 * (** [to_list a] returns the list of all the elements of [a]. *)
 *
 * val of_list : element_arg list -> t
 * (** [of_list l] returns a fresh array containing the elements
 *    of [l].
 *
 *    @raise Invalid_argument if the length of [l] is greater than
 *    [Sys.max_array_length]. *) *)
(* CR layouts v5: Unboxed values can't be in list yet *)

(** {1 Iterators} *)

val iter : (element_arg -> unit) -> t -> unit
(** [iter f a] applies function [f] in turn to all
   the elements of [a].  It is equivalent to
   [f a.(0); f a.(1); ...; f a.(length a - 1); ()]. *)

val iteri : (int -> element_arg -> unit) -> t -> unit
(** Same as {!iter}, but the
   function is applied to the index of the element as first argument,
   and the element itself as second argument. *)

val map : (element_arg -> element_arg) -> t -> t
(** [map f a] applies function [f] to all the elements of [a],
   and builds an array with the results returned by [f]:
   [[| f a.(0); f a.(1); ...; f a.(length a - 1) |]]. *)

val mapi : (int -> element_arg -> element_arg) -> t -> t
(** Same as {!map}, but the
   function is applied to the index of the element as first argument,
   and the element itself as second argument. *)

val fold_left : ('a -> element_arg -> 'a) -> 'a -> t -> 'a
(** [fold_left f init a] computes
   [f (... (f (f init a.(0)) a.(1)) ...) a.(n-1)],
   where [n] is the length of the array [a]. *)

(* val fold_left_map :
 *   (element_arg -> 'b -> element_arg * 'c) -> element_arg -> 'b array -> element_arg * 'c array
 * (** [fold_left_map] is a combination of {!fold_left} and {!map} that threads an
 *     accumulator through calls to [f].
 *     @since 4.13.0 *) *)
(* CR layouts v5: Unboxed values can't be in tuples yet *)

val fold_right : (element_arg -> 'a -> 'a) -> t -> 'a -> 'a
(** [fold_right f a init] computes
   [f a.(0) (f a.(1) ( ... (f a.(n-1) init) ...))],
   where [n] is the length of the array [a]. *)


(** {1 Iterators on two arrays} *)


val iter2 : (element_arg -> element_arg -> unit) -> t -> t -> unit
(** [iter2 f a b] applies function [f] to all the elements of [a]
   and [b].
   @raise Invalid_argument if the arrays are not the same size.
   @since 4.03.0 (4.05.0 in ArrayLabels)
   *)

val map2 : (element_arg -> element_arg -> element_arg) -> t -> t -> t
(** [map2 f a b] applies function [f] to all the elements of [a]
   and [b], and builds an array with the results returned by [f]:
   [[| f a.(0) b.(0); ...; f a.(length a - 1) b.(length b - 1)|]].
   @raise Invalid_argument if the arrays are not the same size.
   @since 4.03.0 (4.05.0 in ArrayLabels) *)


(** {1 Array scanning} *)

val for_all : (element_arg -> bool) -> t -> bool
(** [for_all f [|a1; ...; an|]] checks if all elements
   of the array satisfy the predicate [f]. That is, it returns
   [(f a1) && (f a2) && ... && (f an)].
   @since 4.03.0 *)

val exists : (element_arg -> bool) -> t -> bool
(** [exists f [|a1; ...; an|]] checks if at least one element of
    the array satisfies the predicate [f]. That is, it returns
    [(f a1) || (f a2) || ... || (f an)].
    @since 4.03.0 *)

val for_all2 : (element_arg -> element_arg -> bool) -> t -> t -> bool
(** Same as {!for_all}, but for a two-argument predicate.
   @raise Invalid_argument if the two arrays have different lengths.
   @since 4.11.0 *)

val exists2 : (element_arg -> element_arg -> bool) -> t -> t -> bool
(** Same as {!exists}, but for a two-argument predicate.
   @raise Invalid_argument if the two arrays have different lengths.
   @since 4.11.0 *)

val mem : element_arg -> t -> bool
(** [mem a set] is true if and only if [a] is structurally equal
    to an element of [l] (i.e. there is an [x] in [l] such that
    [compare_element a x = 0]).
    @since 4.03.0 *)

(* val memq : element_arg -> t -> bool
 * (** Same as {!mem}, but uses physical equality
 *    instead of structural equality to compare list elements.
 *    @since 4.03.0 *) *)

(* val find_opt : (element_arg -> bool) -> t -> element_arg option
 * (** [find_opt f a] returns the first element of the array [a] that satisfies
 *     the predicate [f], or [None] if there is no value that satisfies [f] in the
 *     array [a].
 *
 *     @since 4.13.0 *)
 *
 * val find_map : (element_arg -> 'b option) -> t -> 'b option
 * (** [find_map f a] applies [f] to the elements of [a] in order, and returns the
 *     first result of the form [Some v], or [None] if none exist.
 *
 *     @since 4.13.0 *) *)
(* CR layouts v5: Unboxed values can't be in option yet *)

(** {1 Arrays of pairs} *)

(* val split : (element_arg * 'b) array -> t * 'b array
 * (** [split [|(a1,b1); ...; (an,bn)|]] is [([|a1; ...; an|], [|b1; ...; bn|])].
 *
 *     @since 4.13.0 *)
 *
 * val combine : t -> 'b array -> (element_arg * 'b) array
 * (** [combine [|a1; ...; an|] [|b1; ...; bn|]] is [[|(a1,b1); ...; (an,bn)|]].
 *     Raise [Invalid_argument] if the two arrays have different lengths.
 *
 *     @since 4.13.0 *) *)
(* CR layouts v5: Unboxed values can't be in tuples yet *)

(** {1 Sorting} *)

val sort : (element_arg -> element_arg -> int) -> t -> unit
(** Sort an array in increasing order according to a comparison
   function.  The comparison function must return 0 if its arguments
   compare as equal, a positive integer if the first is greater,
   and a negative integer if the first is smaller (see below for a
   complete specification).  For example, {!Stdlib.compare} is
   a suitable comparison function. After calling [sort], the
   array is sorted in place in increasing order.
   [sort] is guaranteed to run in constant heap space
   and (at most) logarithmic stack space.

   The current implementation uses Heap Sort.  It runs in constant
   stack space.

   Specification of the comparison function:
   Let [a] be the array and [cmp] the comparison function.  The following
   must be true for all [x], [y], [z] in [a] :
-   [cmp x y] > 0 if and only if [cmp y x] < 0
-   if [cmp x y] >= 0 and [cmp y z] >= 0 then [cmp x z] >= 0

   When [sort] returns, [a] contains the same elements as before,
   reordered in such a way that for all i and j valid indices of [a] :
-   [cmp a.(i) a.(j)] >= 0 if and only if i >= j
*)

val stable_sort : (element_arg -> element_arg -> int) -> t -> unit
(** Same as {!sort}, but the sorting algorithm is stable (i.e.
   elements that compare equal are kept in their original order) and
   not guaranteed to run in constant heap space.

   The current implementation uses Merge Sort. It uses a temporary array of
   length [n/2], where [n] is the length of the array.  It is usually faster
   than the current implementation of {!sort}.
*)

val fast_sort : (element_arg -> element_arg -> int) -> t -> unit
(** Same as {!sort} or {!stable_sort}, whichever is
    faster on typical input. *)


(** {1 Arrays and Sequences} *)

(* val to_seq : t -> element_arg Seq.t
 * (** Iterate on the array, in increasing order. Modifications of the
 *     array during iteration will be reflected in the sequence.
 *     @since 4.07 *)
 *
 * val to_seqi : t -> (int * element_arg) Seq.t
 * (** Iterate on the array, in increasing order, yielding indices along elements.
 *     Modifications of the array during iteration will be reflected in the
 *     sequence.
 *     @since 4.07 *)
 *
 * val of_seq : element_arg Seq.t -> t
 * (** Create an array from the generator
 *     @since 4.07 *) *)
(* CR layouts v5: Unboxed [Seq.t] not yet supported *)
(**/**)

end

module Int32_u_array0 : Array0_gen with type element_t = int32# and type ('a : any) array_t = 'a array = struct
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

module Int64_u_array0 : Array0_gen with type element_t = int64# and type ('a : any) array_t = 'a array = struct
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

module Nativeint_u_array0 : Array0_gen with type element_t = nativeint# and type ('a : any) array_t = 'a array = struct
  type element_t = nativeint#
  type ('a : any) array_t = 'a array
  type element_arg = unit -> element_t
  type t = element_t array
  external length : ('a : word). 'a array -> int = "%array_length"
  external get: ('a : word). 'a array -> int -> 'a = "%array_safe_get"
  let get t i = let a = get t i in fun () -> a
  external set: ('a : word). 'a array -> int -> 'a -> unit = "%array_safe_set"
  let set t i e = set t i (e ())
  external unsafe_get: ('a : word). 'a array -> int -> 'a = "%array_unsafe_get"
  let unsafe_get t i = let a = unsafe_get t i in fun () -> a
  external unsafe_set: ('a : word). 'a array -> int -> 'a -> unit = "%array_unsafe_set"
  let unsafe_set t i e = unsafe_set t i (e ())

  external unsafe_create : ('a : word). int -> 'a array =
    "caml_make_unboxed_nativeint_vect_bytecode" "caml_make_unboxed_nativeint_vect"
  external unsafe_blit : ('a : word).
    'a array -> int -> 'a array -> int -> int -> unit =
    "caml_array_blit" "caml_unboxed_nativeint_vect_blit"
  let empty () = [||]
  external to_boxed : ('a : word) -> (nativeint[@local_opt]) = "%box_nativeint"
  let compare_element x y = Nativeint.compare (to_boxed (x ())) (to_boxed (y ()))
end

module Make_array (M : Array0_gen)
  : (Array_gen
      with type element_t = M.element_t
      and type ('a : any) array_t = 'a M.array_t) = struct

include M

let unsafe_fill : t -> int -> int -> element_arg -> unit =
  fun a ofs len v ->
    for i = ofs to ofs + len - 1 do unsafe_set a i v done


let make : int -> element_arg -> t = fun n v ->
  let result = unsafe_create n in
  unsafe_fill result 0 n v;
  result

let create = make

let unsafe_sub: t -> int -> int -> t = fun a ofs len ->
  let result = unsafe_create len in
  unsafe_blit a ofs result 0 len;
  result

let append_prim: t -> t -> t = fun a1 a2 ->
  let l1 = length a1 in
  let l2 = length a2 in
  let result = unsafe_create (l1 + l2) in
  unsafe_blit a1 0 result 0 l1;
  unsafe_blit a2 0 result l1 l2;
  result
let ensure_ge (x:int) y =
  if x >= y then x else invalid_arg "Int32_u_array.concat"

let rec sum_lengths acc = function
  | [] -> acc
  | hd :: tl -> sum_lengths (ensure_ge (length hd + acc) acc) tl

let concat: t list -> t = fun l ->
  let len = sum_lengths 0 l in
  let result = unsafe_create len in
  let rec loop l i =
    match l with
    | [] -> assert (i = len)
    | hd :: tl ->
      let hlen = length hd in
      unsafe_blit hd 0 result i hlen;
      loop tl (i + hlen)
  in
  loop l 0;
  result

let init: int -> (int -> element_arg) -> t = fun l f ->
  if l = 0 then (empty ()) else
  if l < 0 then invalid_arg "Int32_u_array.init"
  (* See #6575. We could also check for maximum array size, but this depends
     on whether we create a float array or a regular one... *)
  else
   let res = create l (f 0) in
   for i = 1 to pred l do
     unsafe_set res i (f i)
   done;
   res

let make_matrix sx sy init =
  let res = Array.make sx (empty ()) in
  for x = 0 to pred sx do
    Array.unsafe_set res x (create sy init)
  done;
  res

let create_matrix = make_matrix

let copy a =
  let l = length a in if l = 0 then (empty ()) else unsafe_sub a 0 l

let append a1 a2 =
  let l1 = length a1 in
  if l1 = 0 then copy a2
  else if length a2 = 0 then unsafe_sub a1 0 l1
  else append_prim a1 a2

let sub a ofs len =
  if ofs < 0 || len < 0 || ofs > length a - len
  then invalid_arg "Int32_u_array.sub"
  else unsafe_sub a ofs len

let fill a ofs len v =
  if ofs < 0 || len < 0 || ofs > length a - len
  then invalid_arg "Int32_u_array.fill"
  else unsafe_fill a ofs len v

let blit a1 ofs1 a2 ofs2 len =
  if len < 0 || ofs1 < 0 || ofs1 > length a1 - len
             || ofs2 < 0 || ofs2 > length a2 - len
  then invalid_arg "Int32_u_array.blit"
  else unsafe_blit a1 ofs1 a2 ofs2 len

let iter f a =
  for i = 0 to length a - 1 do f(unsafe_get a i) done

let iter2 f a b =
  if length a <> length b then
    invalid_arg "Int32_u_array.iter2: arrays must have the same length"
  else
    for i = 0 to length a - 1 do f (unsafe_get a i) (unsafe_get b i) done

let map f a =
  let l = length a in
  if l = 0 then (empty ()) else begin
    let r = create l (f(unsafe_get a 0)) in
    for i = 1 to l - 1 do
      unsafe_set r i (f(unsafe_get a i))
    done;
    r
  end

let map2 f a b =
  let la = length a in
  let lb = length b in
  if la <> lb then
    invalid_arg "Int32_u_array.map2: arrays must have the same length"
  else begin
    if la = 0 then (empty ()) else begin
      let r = create la (f (unsafe_get a 0) (unsafe_get b 0)) in
      for i = 1 to la - 1 do
        unsafe_set r i (f (unsafe_get a i) (unsafe_get b i))
      done;
      r
    end
  end

let iteri f a =
  for i = 0 to length a - 1 do f i (unsafe_get a i) done

let mapi f a =
  let l = length a in
  if l = 0 then (empty ()) else begin
    let r = create l (f 0 (unsafe_get a 0)) in
    for i = 1 to l - 1 do
      unsafe_set r i (f i (unsafe_get a i))
    done;
    r
  end

(* let to_list a =
 *   let rec tolist i res =
 *     if i < 0 then res else tolist (i - 1) (unsafe_get a i :: res) in
 *   tolist (length a - 1) []
 *
 * (* Cannot use List.length here because the List module depends on Int32_u_array. *)
 * let rec list_length accu = function
 *   | [] -> accu
 *   | _::t -> list_length (succ accu) t
 *
 * let of_list = function
 *     [] -> (empty ())
 *   | hd::tl as l ->
 *       let a = create (list_length 0 l) hd in
 *       let rec fill i = function
 *           [] -> a
 *         | hd::tl -> unsafe_set a i hd; fill (i+1) tl in
 *       fill 1 tl *)

let fold_left f x a =
  let r = ref x in
  for i = 0 to length a - 1 do
    r := f !r (unsafe_get a i)
  done;
  !r

(* let fold_left_map f acc input_array =
 *   let len = length input_array in
 *   if len = 0 then (acc, (empty ())) else begin
 *     let acc, elt = f acc (unsafe_get input_array 0) in
 *     let output_array = create len elt in
 *     let acc = ref acc in
 *     for i = 1 to len - 1 do
 *       let acc', elt = f !acc (unsafe_get input_array i) in
 *       acc := acc';
 *       unsafe_set output_array i elt;
 *     done;
 *     !acc, output_array
 *   end *)

let fold_right f a x =
  let r = ref x in
  for i = length a - 1 downto 0 do
    r := f (unsafe_get a i) !r
  done;
  !r

let exists p a =
  let n = length a in
  let rec loop i =
    if i = n then false
    else if p (unsafe_get a i) then true
    else loop (succ i) in
  loop 0

let for_all p a =
  (* take [n], [p], and [a] as parameters to avoid a closure allocation *)
  let rec loop n p a i =
    if i = n then true
    else if p (unsafe_get a i) then loop n p a (succ i)
    else false in
  loop (length a) p a 0

let for_all2 p l1 l2 =
  let n1 = length l1
  and n2 = length l2 in
  if n1 <> n2 then invalid_arg "Int32_u_array.for_all2"
  else let rec loop i =
    if i = n1 then true
    else if p (unsafe_get l1 i) (unsafe_get l2 i) then loop (succ i)
    else false in
  loop 0

let exists2 p l1 l2 =
  let n1 = length l1
  and n2 = length l2 in
  if n1 <> n2 then invalid_arg "Int32_u_array.exists2"
  else let rec loop i =
    if i = n1 then false
    else if p (unsafe_get l1 i) (unsafe_get l2 i) then true
    else loop (succ i) in
  loop 0



let mem x a =
  let n = length a in
  let rec loop i =
    if i = n then false
    else if compare_element (unsafe_get a i) x = 0 then true
    else loop (succ i) in
  loop 0

(* let memq x a =
 *   let n = length a in
 *   let rec loop i =
 *     if i = n then false
 *     else if x == (unsafe_get a i) then true
 *     else loop (succ i) in
 *   loop 0 *)

(* let find_opt p a =
 *   let n = length a in
 *   let rec loop i =
 *     if i = n then None
 *     else
 *       let x = unsafe_get a i in
 *       if p x then Some x
 *       else loop (succ i)
 *   in
 *   loop 0
 *
 * let find_map f a =
 *   let n = length a in
 *   let rec loop i =
 *     if i = n then None
 *     else
 *       match f (unsafe_get a i) with
 *       | None -> loop (succ i)
 *       | Some _ as r -> r
 *   in
 *   loop 0
 *
 * let split x =
 *   if x = (empty ()) then (empty ()), (empty ())
 *   else begin
 *     let a0, b0 = unsafe_get x 0 in
 *     let n = length x in
 *     let a = create n a0 in
 *     let b = create n b0 in
 *     for i = 1 to n - 1 do
 *       let ai, bi = unsafe_get x i in
 *       unsafe_set a i ai;
 *       unsafe_set b i bi
 *     done;
 *     a, b
 *   end
 *
 * let combine a b =
 *   let na = length a in
 *   let nb = length b in
 *   if na <> nb then invalid_arg "Int32_u_array.combine";
 *   if na = 0 then (empty ())
 *   else begin
 *     let x = create na (unsafe_get a 0, unsafe_get b 0) in
 *     for i = 1 to na - 1 do
 *       unsafe_set x i (unsafe_get a i, unsafe_get b i)
 *     done;
 *     x
 *   end *)

exception Bottom of int
let sort cmp a =
  let maxson l i =
    let i31 = i+i+i+1 in
    let x = ref i31 in
    if i31+2 < l then begin
      if cmp (get a i31) (get a (i31+1)) < 0 then x := i31+1;
      if cmp (get a !x) (get a (i31+2)) < 0 then x := i31+2;
      !x
    end else
      if i31+1 < l && cmp (get a i31) (get a (i31+1)) < 0
      then i31+1
      else if i31 < l then i31 else raise (Bottom i)
  in
  let rec trickledown l i e =
    let j = maxson l i in
    if cmp (get a j) e > 0 then begin
      set a i (get a j);
      trickledown l j e;
    end else begin
      set a i e;
    end;
  in
  let trickle l i e = try trickledown l i e with Bottom i -> set a i e in
  let rec bubbledown l i =
    let j = maxson l i in
    set a i (get a j);
    bubbledown l j
  in
  let bubble l i = try bubbledown l i with Bottom i -> i in
  let rec trickleup i e =
    let father = (i - 1) / 3 in
    assert (i <> father);
    if cmp (get a father) e < 0 then begin
      set a i (get a father);
      if father > 0 then trickleup father e else set a 0 e;
    end else begin
      set a i e;
    end;
  in
  let l = length a in
  for i = (l + 1) / 3 - 1 downto 0 do trickle l i (get a i); done;
  for i = l - 1 downto 2 do
    let e = (get a i) in
    set a i (get a 0);
    trickleup (bubble i 0) e;
  done;
  if l > 1 then (let e = (get a 1) in set a 1 (get a 0); set a 0 e)


let cutoff = 5
let stable_sort cmp a =
  let merge src1ofs src1len src2 src2ofs src2len dst dstofs =
    let src1r = src1ofs + src1len and src2r = src2ofs + src2len in
    let rec loop i1 s1 i2 s2 d =
      if cmp s1 s2 <= 0 then begin
        set dst d s1;
        let i1 = i1 + 1 in
        if i1 < src1r then
          loop i1 (get a i1) i2 s2 (d + 1)
        else
          blit src2 i2 dst (d + 1) (src2r - i2)
      end else begin
        set dst d s2;
        let i2 = i2 + 1 in
        if i2 < src2r then
          loop i1 s1 i2 (get src2 i2) (d + 1)
        else
          blit a i1 dst (d + 1) (src1r - i1)
      end
    in loop src1ofs (get a src1ofs) src2ofs (get src2 src2ofs) dstofs;
  in
  let isortto srcofs dst dstofs len =
    for i = 0 to len - 1 do
      let e = (get a (srcofs + i)) in
      let j = ref (dstofs + i - 1) in
      while (!j >= dstofs && cmp (get dst !j) e > 0) do
        set dst (!j + 1) (get dst !j);
        decr j;
      done;
      set dst (!j + 1) e;
    done;
  in
  let rec sortto srcofs dst dstofs len =
    if len <= cutoff then isortto srcofs dst dstofs len else begin
      let l1 = len / 2 in
      let l2 = len - l1 in
      sortto (srcofs + l1) dst (dstofs + l1) l2;
      sortto srcofs a (srcofs + l2) l1;
      merge (srcofs + l2) l1 dst (dstofs + l1) l2 dst dstofs;
    end;
  in
  let l = length a in
  if l <= cutoff then isortto 0 a 0 l else begin
    let l1 = l / 2 in
    let l2 = l - l1 in
    let t = make l2 (get a 0) in
    sortto l1 t 0 l2;
    sortto 0 a l2 l1;
    merge l2 l1 t 0 l2 a 0;
  end


let fast_sort = stable_sort

(** {1 Iterators} *)

(* let to_seq a =
 *   let rec aux i () =
 *     if i < length a
 *     then
 *       let x = unsafe_get a i in
 *       Seq.Cons (x, aux (i+1))
 *     else Seq.Nil
 *   in
 *   aux 0
 *
 * let to_seqi a =
 *   let rec aux i () =
 *     if i < length a
 *     then
 *       let x = unsafe_get a i in
 *       Seq.Cons ((i,x), aux (i+1))
 *     else Seq.Nil
 *   in
 *   aux 0
 *
 * let of_rev_list = function
 *     [] -> (empty ())
 *   | hd::tl as l ->
 *       let len = list_length 0 l in
 *       let a = create len hd in
 *       let rec fill i = function
 *           [] -> a
 *         | hd::tl -> unsafe_set a i hd; fill (i-1) tl
 *       in
 *       fill (len-2) tl
 *
 * let of_seq i =
 *   let l = Seq.fold_left (fun acc x -> x::acc) [] i in
 *   of_rev_list l *)

end

module type Array_test_element_interface = sig
  type t
  val of_int : int -> t
  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t
  val neg : t -> t
  val max_val : t
  val min_val : t
  val rand : t -> t
  val compare : t -> t -> int
  val print : t -> unit
end
module type Array_test_interface = sig
  type t
  type element_t
  val length : t -> int
  val get : t -> int -> element_t
  val set : t -> int -> element_t -> unit
  val make : int -> element_t -> t
  val init : int -> (int -> element_t) -> t
  val append : t -> t -> t
  val concat : t list -> t
  val sub : t -> int -> int -> t
  val copy : t -> t
  val fill : t -> int -> int -> element_t -> unit
  val blit : t -> int -> t -> int -> int -> unit
  val to_list : t -> element_t list
  val of_list : element_t list -> t
  val iter : (element_t -> unit) -> t -> unit
  val iteri : (int -> element_t -> unit) -> t -> unit
  val map : (element_t -> element_t) -> t -> t
  val mapi : (int -> element_t -> element_t) -> t -> t
  val fold_left : ('a -> element_t -> 'a) -> 'a -> t -> 'a
  val fold_right : (element_t -> 'a -> 'a) -> t -> 'a -> 'a
  val iter2 : (element_t -> element_t -> unit) -> t -> t -> unit
  val map2 : (element_t -> element_t -> element_t) -> t -> t -> t
  val for_all : (element_t -> bool) -> t -> bool
  val exists : (element_t -> bool) -> t -> bool
  val mem : element_t -> t -> bool
  val sort : (element_t -> element_t -> int) -> t -> unit
  val stable_sort : (element_t -> element_t -> int) -> t -> unit
  val fast_sort : (element_t -> element_t -> int) -> t -> unit
  val to_seq : t -> element_t Seq.t
  val to_seqi : t -> (int * element_t) Seq.t
  val of_seq : element_t Seq.t -> t
  val map_to_array : (element_t -> 'a) -> t -> 'a array
  val map_from_array : ('a -> element_t) -> 'a array -> t
  val unsafe_get : t -> int -> element_t
  val unsafe_set : t -> int -> element_t -> unit
  val equal : t -> t -> bool
  (* From Sys, rather than Float.Array *)
  val max_length : int

  module I : Array_test_element_interface with type t = element_t
end

module Make_boxed_test_module (Arg : sig
  module M : Array_gen
  module I : Array_test_element_interface
  module E : sig
    val to_boxed : M.element_arg -> I.t
    val of_boxed : I.t -> M.element_arg
  end
end) : Array_test_interface = struct
  include Arg.M
  include Arg.E
  module I = Arg.I

  type element_t = I.t

  let empty () = make 0 (of_boxed (I.of_int 0))
  let to_seq a =
    let rec aux i () =
      if i < length a
      then
        let x = unsafe_get a i in
        Seq.Cons (to_boxed x, aux (i+1))
      else Seq.Nil
    in
    aux 0

  let to_seqi a =
    let rec aux i () =
      if i < length a
      then
        let x = unsafe_get a i in
        Seq.Cons ((i,to_boxed x), aux (i+1))
      else Seq.Nil
    in
    aux 0

  let of_rev_list = function
      [] -> empty ()
    | hd::tl as l ->
      let len = List.length l in
      let a = make len (of_boxed hd) in
      let rec fill i = function
          [] -> a
        | hd::tl -> unsafe_set a i (of_boxed hd); fill (i-1) tl
      in
      fill (len-2) tl

  let of_seq i =
    let l = Seq.fold_left (fun acc x -> x::acc) [] i in
    of_rev_list l


  let to_list t = fold_right (fun f l -> (to_boxed f)::l) t []
  (* let res = ref [] in
   * iter (fun f -> res := (to_boxed f) :: !res);
   * List.rev res *)

  let of_list l =
    let len = List.length l in
    let res = make len (of_boxed (I.of_int 0)) in
    List.iteri (fun idx f -> set res idx (of_boxed f)) l;
    res
  let max_length = Sys.max_array_length
  let get t idx = to_boxed (get t idx)
  let set t idx v = set t idx (of_boxed v)

  let make l f = make l (of_boxed f)
  let init l f = init l (fun i -> of_boxed (f i))
  let fill a ofs len v = fill a ofs len (of_boxed v)
  let iter f t = iter (fun v -> f (to_boxed v)) t
  let iteri f t = iteri (fun i v -> f i (to_boxed v)) t
  let map f t = map (fun v -> of_boxed (f (to_boxed v))) t
  let mapi f t = mapi (fun i v -> of_boxed (f i (to_boxed v))) t
  let fold_left f acc t = fold_left (fun acc v -> f acc (to_boxed v)) acc t
  let fold_right f t acc = fold_right (fun v acc -> f (to_boxed v) acc) t acc

  let iter2 f a b = iter2 (fun v1 v2 -> f (to_boxed v1) (to_boxed v2)) a b
  let map2 f a b = map2 (fun v1 v2 -> of_boxed (f (to_boxed v1) (to_boxed v2))) a b
  let for_all f t = for_all (fun v -> f (to_boxed v)) t
  let exists f t = exists (fun v -> f (to_boxed v)) t
  let mem v t = mem (of_boxed v) t
  let sort f t = sort (fun a b -> f (to_boxed a) (to_boxed b)) t
  let stable_sort f t = stable_sort (fun a b -> f (to_boxed a) (to_boxed b)) t
  let fast_sort f t = fast_sort (fun a b -> f (to_boxed a) (to_boxed b)) t

  let map_to_array f t =
    if length t = 0 then [||] else begin
      let res = Array.make (length t) (f (get t 0)) in
      iteri (fun idx v -> if idx > 0 then Array.set res idx (f v)) t;
      res
    end

  let map_from_array f a =
    if Array.length a = 0 then empty () else begin
      let res = make (Array.length a) (f (Array.get a 0)) in
      Array.iteri (fun idx v -> if idx > 0 then set res idx (f v)) a;
      res
    end

  let unsafe_get t idx = to_boxed (unsafe_get t idx)
  let unsafe_set t idx v = unsafe_set t idx (of_boxed v)
  let equal = for_all2 (fun x y -> to_boxed x = to_boxed y)

end

module Test (A : Array_test_interface) : sig end = struct

  (* auxiliary functions *)
  let module I = A.I in
  let rec check_i_upto a i =
    if i >= 0 then begin
      assert (A.get a i = I.of_int i);
      check_i_upto a (i - 1);
    end
  in

  let check_i a = check_i_upto a (A.length a - 1) in

  let check_inval f arg =
    match f arg with
    | _ -> Format.printf "got here\n@?"; assert false
    | exception (Invalid_argument _) -> ()
    | exception _ -> assert false
  in

  (* [make] [set] [get] *)
  let a = A.make 1000 (I.of_int 1) in
  for i = 0 to 499 do A.set a i (I.of_int i) done;
  let rec loop i =
    if i >= 0 then begin
      assert (A.get a i = (if i < 500 then I.of_int i else (I.of_int 1)));
      loop (i - 1);
    end
  in loop 999;
  check_inval (A.get a) (-1);
  check_inval (A.get a) (1000);
  check_inval (fun i -> A.set a i (I.of_int 1)) (-1);
  check_inval (fun i -> A.set a i (I.of_int 1)) 1000;
  check_inval (fun i -> A.make i (I.of_int 1)) (-1);
  check_inval (fun i -> A.make i (I.of_int 1)) (A.max_length + 1);

  let a = A.make 1001 (I.of_int 1) in
  for i = 0 to 499 do A.set a i (I.of_int i) done;
  let rec loop i =
    if i >= 0 then begin
      assert (A.get a i = (if i < 500 then I.of_int i else (I.of_int 1)));
      loop (i - 1);
    end
  in loop 1000;
  check_inval (A.get a) (-1);
  check_inval (A.get a) (1001);
  check_inval (fun i -> A.set a i (I.of_int 1)) (-1);
  check_inval (fun i -> A.set a i (I.of_int 1)) 1001;

  (* [length] *)
  let test_length l = assert (l = (A.length (A.make l (I.of_int 1)))) in
  test_length 0;
  test_length 1;
  test_length 10;
  test_length 25;
  test_length 255;
  test_length 256;
  test_length 1000;
  test_length 1001;
  test_length 123456;

  (* [init] *)
  let a = A.init 1000 I.of_int in
  check_i a;
  let a = A.init 1001 I.of_int in
  check_i a;
  check_inval (fun i -> A.init i I.of_int) (-1);
  check_inval (fun i -> A.init i I.of_int) (A.max_length + 1);

  (* [append] *)
  let check m n =
    let a = A.init m I.of_int in
    let b = A.init n (fun x -> I.of_int (x + m)) in
    let c = A.append a b in
    assert (A.length c = (m + n));
    check_i c;
  in
  check 0 0;
  check 0 100;
  check 1 100;
  check 100 0;
  check 100 1;
  check 100 100;
  check 1000 1000;
  check 1000 1001;
  check 1001 1000;
  check 1001 1001;
  (* check_inval omitted *)

  (* [concat] *)
  let check l =
    let f (len, acc) n =
      (len + n, A.init n (fun i -> I.of_int (len + i)) :: acc)
    in
    let (total, ll) = List.fold_left f (0, []) l in
    let b = A.concat (List.rev ll) in
    assert (A.length b = total);
    check_i b;
  in
  check [0; 0; 0];
  check [1; 10; 100];
  check [10; 0];
  check [0];
  check [1000; 1000; 1000];
  check [];
  check [1001; 1000; 1000];
  check [1000; 1001; 1000];
  check [1000; 1000; 1001];
  check [1001; 1001; 1001];
  (* check_inval omitted *)

  (* [sub] *)
  let a = A.init 1000 (fun i -> I.of_int (i - 100)) in
  let b = A.sub a 100 200 in
  check_i b;
  assert (A.length b = 200);
  let b = A.sub a 1000 0 in
  check_i (A.sub a 1000 0);
  assert  (A.length b = 0);
  check_inval (A.sub a (-1)) 0;
  check_inval (A.sub a 0) (-1);
  check_inval (A.sub a 0) 1001;
  check_inval (A.sub a 1000) 1;

  let a = A.init 1001 (fun i -> I.of_int (i - 101)) in
  let b = A.sub a 101 199 in
  check_i b;
  assert (A.length b = 199);
  let b = A.sub a 1001 0 in
  check_i (A.sub a 1001 0);
  assert  (A.length b = 0);
  check_inval (A.sub a (-1)) 0;
  check_inval (A.sub a 0) (-1);
  check_inval (A.sub a 0) 1002;
  check_inval (A.sub a 1001) 1;

  (* [copy] *)
  let check len =
    let a = A.init len I.of_int in
    let b = A.copy a in
    check_i b;
    assert (A.length b = len);
  in
  check 0;
  check 1;
  check 128;
  check 1023;

  (* [blit] [fill] *)
  let test_blit_fill data initval ofs len =
    let a = A.of_list data in
    let b = A.make (List.length data) (I.of_int 1) in
    A.blit a 0 b 0 (A.length b);
    assert (A.equal a b);
    A.fill b ofs len initval;
    let rec check i = function
      | [] -> ()
      | hd :: tl ->
          assert (A.get b i = (if i >= ofs && i < ofs + len
                               then initval else hd));
          check (i + 1) tl;
    in
    check 0 data
  in
  test_blit_fill [I.of_int 1;I.of_int 2;I.of_int 5;I.of_int 8;I.of_int (-100);I.of_int 2120000000] (I.of_int 3) 3 2;
  let a = A.make 100 (I.of_int 0) in
  check_inval (A.fill a (-1) 0) (I.of_int 1);
  check_inval (A.fill a 0 (-1)) (I.of_int 1);
  check_inval (A.fill a 0 101) (I.of_int 1);
  check_inval (A.fill a 100 1) (I.of_int 1);
  check_inval (A.fill a 101 0) (I.of_int 1);
  check_inval (A.blit a (-1) a 0) 0;
  check_inval (A.blit a 0 a 0) (-1);
  check_inval (A.blit a 0 a 0) 101;
  check_inval (A.blit a 100 a 0) 1;
  check_inval (A.blit a 101 a 0) 0;
  check_inval (A.blit a 0 a (-1)) 0;
  check_inval (A.blit a 0 a 100) 1;
  check_inval (A.blit a 0 a 101) 0;
  let a = A.make 101 (I.of_int 0) in
  check_inval (A.fill a (-1) 0) (I.of_int 1);
  check_inval (A.fill a 0 (-1)) (I.of_int 1);
  check_inval (A.fill a 0 102) (I.of_int 1);
  check_inval (A.fill a 101 1) (I.of_int 1);
  check_inval (A.fill a 102 0) (I.of_int 1);
  check_inval (A.blit a (-1) a 0) 0;
  check_inval (A.blit a 0 a 0) (-1);
  check_inval (A.blit a 0 a 0) 102;
  check_inval (A.blit a 101 a 0) 1;
  check_inval (A.blit a 102 a 0) 0;
  check_inval (A.blit a 0 a (-1)) 0;
  check_inval (A.blit a 0 a 101) 1;
  check_inval (A.blit a 0 a 102) 0;
  let test_blit_overlap a ofs1 ofs2 len =
    let a = A.of_list a in
    let b = A.copy a in
    A.blit a ofs1 a ofs2 len;
    for i = 0 to len - 1 do
      assert (A.get b (ofs1 + i) = A.get a (ofs2 + i))
    done
  in
  test_blit_overlap [(I.of_int 1); (I.of_int 2); (I.of_int 3); (I.of_int 4)] 1 2 2;

  (* [to_list] [of_list] *)
  let a = A.init 1000 I.of_int in
  assert (A.equal a (A.of_list (A.to_list a)));
  let a = A.init 1001 I.of_int in
  assert (A.equal a (A.of_list (A.to_list a)));
  let a = A.init 0 I.of_int in
  assert (A.equal a (A.of_list (A.to_list a)));
  (* check_inval omitted *)

  (* [iter] *)
  let a = A.init 300 (I.of_int) in
  let r = ref (I.of_int 0) in
  A.iter (fun x -> assert (x = !r); r := I.add x (I.of_int 1)) a;
  A.iter (fun _ -> assert false) (A.make 0 (I.of_int 0));
  assert (!r = (I.of_int 300));

  let a = A.init 301 (I.of_int) in
  let r = ref (I.of_int 0) in
  A.iter (fun x -> assert (x = !r); r := I.add x (I.of_int 1)) a;
  assert (!r = (I.of_int 301));

  (* [iteri] *)
  let a = A.init 300 I.of_int in
  let r = ref 0 in
  let f i x =
    assert (i = !r);
    assert (x = I.of_int i);
    r := i + 1
  in
  A.iteri f a;
  A.iteri (fun _ _ -> assert false) (A.make 0 (I.of_int 0));
  assert (!r = 300);

  let a = A.init 301 I.of_int in
  let r = ref 0 in
  let f i x =
    assert (i = !r);
    assert (x = I.of_int i);
    r := i + 1
  in
  A.iteri f a;
  A.iteri (fun _ _ -> assert false) (A.make 0 (I.of_int 0));
  assert (!r = 301);

  (* [map], test result and order of evaluation *)
  let a = A.init 500 I.of_int in
  let r = ref (I.of_int 0) in
  let f x =
    assert (x = !r);
    r := I.add !r (I.of_int 1);
    I.sub x (I.of_int 1)
  in
  let b = A.map f a in
  check_i (A.sub b 1 499);

  let a = A.init 501 I.of_int in
  let r = ref (I.of_int 0) in
  let f x =
    assert (x = !r);
    r := I.add !r (I.of_int 1);
    I.sub x (I.of_int 1)
  in
  let b = A.map f a in
  check_i (A.sub b 1 500);

  (* [mapi], test result and order of evaluation *)
  let a = A.init 500 I.of_int in
  let r = ref (I.of_int 0) in
  let f i x =
    assert (x = I.of_int i);
    assert (x = !r);
    r := I.add !r (I.of_int 1);
    I.sub x (I.of_int 1)
  in
  let b = A.mapi f a in
  check_i (A.sub b 1 499);

  let a = A.init 501 I.of_int in
  let r = ref (I.of_int 0) in
  let f i x =
    assert (x = I.of_int i);
    assert (x = !r);
    r := I.add !r (I.of_int 1);
    I.sub x (I.of_int 1)
  in
  let b = A.mapi f a in
  check_i (A.sub b 1 500);

  (* [fold_left], test result and order of evaluation *)
  let a = A.init 500 I.of_int in
  let f acc x =
    assert (acc = x);
    I.add x (I.of_int 1)
  in
  let acc = A.fold_left f (I.of_int 0) a in
  assert (acc = (I.of_int 500));

  let a = A.init 501 I.of_int in
  let acc = A.fold_left f (I.of_int 0) a in
  assert (acc = (I.of_int 501));

  (* [fold_right], test result and order of evaluation *)
  let a = A.init 500 I.of_int in
  let f x acc =
    assert (x = I.sub acc (I.of_int 1));
    x
  in
  let acc = A.fold_right f a (I.of_int 500) in
  assert (acc = (I.of_int 0));

  let a = A.init 501 I.of_int in
  let acc = A.fold_right f a (I.of_int 501) in
  assert (acc = (I.of_int 0));

  (* [iter2], test result and order of evaluation *)
  let a = A.init 123 I.of_int in
  let b = A.init 123 I.of_int in
  let r = ref (I.of_int 0) in
  let f x y =
    assert (x = !r);
    assert (y = !r);
    r := I.add!r (I.of_int 1);
  in
  A.iter2 f a b;
  let c = A.make 456 (I.of_int 0) in
  check_inval (A.iter2 (fun _ _ -> assert false) a) c;
  check_inval (A.iter2 (fun _ _ -> assert false) c) a;

  let a = A.init 124 I.of_int in
  let b = A.init 124 I.of_int in
  let r = ref (I.of_int 0) in
  let f x y =
    assert (x = !r);
    assert (y = !r);
    r := I.add !r (I.of_int 1);
  in
  A.iter2 f a b;

  (* [map2], test result and order of evaluation *)
  let a = A.init 456 I.of_int in
  let b = A.init 456 (fun i -> I.(mul (of_int i) (I.of_int 2))) in
  let r = ref (I.of_int 0) in
  let f x y =
    assert (x = !r);
    assert (y = I.mul !r (I.of_int 2));
    r := I.add !r (I.of_int 1);
    I.(neg (sub x y))
  in
  let c = A.map2 f a b in
  check_i c;
  let d = A.make 455 (I.of_int 0) in
  check_inval (A.map2 (fun _ _ -> assert false) a) d;
  check_inval (A.map2 (fun _ _ -> assert false) d) a;

  let a = A.init 457 I.of_int in
  let b = A.init 457 (fun i -> I.(mul (of_int i) (I.of_int 2))) in
  let r = ref (I.of_int 0) in
  let f x y =
    assert (x = !r);
    assert (y = I.mul !r (I.of_int 2));
    r := I.add !r (I.of_int 1);
    I.(neg (sub x y))
  in
  let c = A.map2 f a b in
  check_i c;

  (* [for_all], test result and order of evaluation *)
  let a = A.init 777 I.of_int in
  let r = ref (I.of_int 0) in
  let f x =
    assert (x = !r);
    r := I.add x (I.of_int 1);
    true
  in
  assert (A.for_all f a);
  let f x = assert (x = (I.of_int 0)); false in
  assert (not (A.for_all f a));

  let a = A.init 778 I.of_int in
  let r = ref (I.of_int 0) in
  let f x =
    assert (x = !r);
    r := I.add x (I.of_int 1);
    true
  in
  assert (A.for_all f a);
  let f x = assert (x = (I.of_int 0)); false in
  assert (not (A.for_all f a));

  (* [exists], test result and order of evaluation *)
  let a = A.init 777 I.of_int in
  let r = ref (I.of_int 0) in
  let f x =
    assert (x = !r);
    r := I.add x (I.of_int 1);
    false
  in
  assert (not (A.exists f a));
  let f x = assert (x = (I.of_int 0)); true in
  assert (A.exists f a);

  let a = A.init 778 I.of_int in
  let r = ref (I.of_int 0) in
  let f x =
    assert (x = !r);
    r := I.add x (I.of_int 1);
    false
  in
  assert (not (A.exists f a));
  let f x = assert (x = (I.of_int 0)); true in
  assert (A.exists f a);

  (* [mem] *)
  let a = A.init 7777 I.of_int in
  assert (A.mem (I.of_int 0) a);
  assert (A.mem (I.of_int 7776) a);
  assert (not (A.mem ((I.of_int (-1))) a));
  assert (not (A.mem (I.of_int 7777) a));
  let check v =
    A.set a 1000 v;
    assert (A.mem v a);
  in
  List.iter check [I.max_val; I.min_val; (I.of_int (-1)); (I.of_int 0)];

  let a = A.init 7778 I.of_int in
  assert (A.mem (I.of_int 0) a);
  assert (A.mem (I.of_int 7777) a);
  assert (not (A.mem ((I.of_int (-1))) a));
  assert (not (A.mem (I.of_int 7778) a));
  let check v =
    A.set a 1001 v;
    assert (A.mem v a);
  in
  List.iter check [I.max_val; I.min_val; (I.of_int (-1)); (I.of_int 0)];

  (* [sort] [fast_sort] [stable_sort] *)
  let check_sort sort cmp a =
    let rec check_sorted a i =
      if i + 1 < A.length a then begin
        assert (cmp (A.get a i) (A.get a (i + 1)) <= 0);
        check_sorted a (i + 1);
      end
    in
    let rec check_permutation a b i =
      let p = Array.make (A.length a) true in
      let rec find lo hi x =
        assert (lo < hi);
        if hi = lo + 1 then begin
          assert (cmp (A.get a lo) x = 0);
          assert (p.(lo));
          p.(lo) <- false;
        end else begin
          let mid = (lo + hi) / 2 in
          assert (lo < mid && mid < hi);
          match cmp (A.get a (mid - 1)) x with
          | 0 when p.(mid - 1) -> find lo mid x
          | 0 -> find mid hi x
          | c when c < 0 -> find mid hi x
          | c when c > 0 -> find lo mid x
          | _ -> assert false
        end
      in
      A.iter (find 0 (A.length a)) b
    in
    let b = A.copy a in
    sort cmp a;
    check_sorted a 0;
    check_permutation a b 0;
  in
  Random.init 123;
  let rand_val _ =
    match Random.int 1000 with
    | n when n < 500 -> I.rand I.max_val
    | _ -> I.neg (I.rand I.max_val)
  in
  let check s =
    let a = A.init 5 I.of_int in
    check_sort s I.compare a; (* already sorted *)
    check_sort s (fun x y -> I.compare y x) a; (* reverse-sorted *)

    let a = A.init 6 I.of_int in
    check_sort s I.compare a; (* already sorted *)
    check_sort s (fun x y -> I.compare y x) a; (* reverse-sorted *)

    let a = A.of_list [I.max_val; I.min_val; (I.of_int (-1)); (I.of_int 0)] in
    check_sort s I.compare a; (* already sorted *)
    check_sort s (fun x y -> I.compare y x) a; (* reverse-sorted *)

    let a = A.init 50000 rand_val in
    check_sort s I.compare a;
    let a = A.init 50001 rand_val in
    check_sort s I.compare a;
    let a = A.make 1000 (I.of_int 1) in
    check_sort s I.compare a;
    let a = A.make 1001 (I.of_int 1) in
    check_sort s I.compare a;
    let a = A.append (A.make 1000 (I.of_int 1)) (A.make 1000 (I.of_int 2)) in
    check_sort s I.compare a;
    let a = A.append (A.make 1001 (I.of_int 1)) (A.make 1001 (I.of_int 2)) in
    check_sort s I.compare a;
  in
  check A.sort;
  check A.stable_sort;
  check A.fast_sort;

  (* [to_seq] *)
  let check_seq a =
    let r = ref 0 in
    let f x =
      assert (A.get a !r = x);
      r := !r + 1;
    in
    let s = A.to_seq a in
    Seq.iter f s;
  in
  check_seq (A.init 999 I.of_int);
  check_seq (A.init 1000 I.of_int);
  check_seq (A.make 0 (I.of_int 0));

  (* [to_seqi] *)
  let check_seqi a =
    let r = ref 0 in
    let f (i, x) =
      assert (i = !r);
      assert (A.get a !r = x);
      r := !r + 1;
    in
    let s = A.to_seqi a in
    Seq.iter f s;
  in
  check_seqi (A.init 999 I.of_int);
  check_seqi (A.init 1000 I.of_int);
  check_seqi (A.make 0 (I.of_int 0));

  (* [of_seq] *)
  let r = ref 0 in
  let rec f () =
    if !r = 100 then Seq.Nil else begin
      let res = Seq.Cons (I.of_int !r, f) in
      r := !r + 1;
      res
    end
  in
  let a = A.of_seq f in
  assert (A.equal a (A.init 100 I.of_int));
  assert (A.equal (A.of_seq Seq.empty) (A.make 0 (I.of_int 0)));

  (* [map_to_array] *)
  let r = ref 0 in
  let f x =
    assert (x = I.of_int !r);
    r := !r + 1;
    I.mul x (I.of_int 2)
  in
  let a = A.init 876 I.of_int in
  let ar1 = A.map_to_array f a in
  let ar2 = Array.init 876 (fun x -> I.of_int (2 * x)) in
  assert (ar1 = ar2);
  let ar = A.map_to_array (fun _ -> assert false) (A.make 0 (I.of_int 0)) in
  assert (ar = [| |]);

  (* [map_from_array] *)
  let r = ref 0 in
  let f x =
    assert (x = I.of_int !r);
    r := !r + 1;
    I.mul x (I.of_int 2)
  in
  let ar = Array.init 876 I.of_int in
  let a1 = A.map_from_array f ar in
  let a2 = A.init 876 (fun x -> I.of_int (2 * x)) in
  assert (A.equal a1 a2);
  let a = A.map_from_array (fun _ -> assert false) [| |] in
  assert (A.equal a (A.make 0 (I.of_int 0)));

  (* comparisons *)
  (* No polymorphic compare yet *)
  (* let normalize_comparison n =
    if n = 0 then 0 else if n < 0 then -1 else 1
  in
  let check c l1 l2 =
    assert (c = (normalize_comparison (compare (A.of_list l1) (A.of_list l2))))
  in
  check 0    [(I.of_int 0); (I.of_int 1); (I.of_int -4); I.max_val; I.min_val]
             [(I.of_int 0); (I.of_int 1); (I.of_int -4); I.max_val; I.min_val];
  check (-1) [(I.of_int 0); (I.of_int 1); (I.of_int -4); I.max_val; I.min_val]
             [(I.of_int 0); (I.of_int 1); (I.of_int -4); I.max_val; I.(add min_val (I.of_int 1))];
  check (-1) [(I.of_int 0); (I.of_int 1); (I.of_int -4); I.max_val; 4509684(I.of_int 3)]
             [(I.of_int 0); (I.of_int 1); (I.of_int -4); I.max_val; 4509684(I.of_int 4)];
  check 1    [(I.of_int 0); (I.of_int 2); (I.of_int -4)]
             [(I.of_int 0); (I.of_int 0); (I.of_int 3)];
  check 1    [(I.of_int 0); (I.of_int 2); (I.of_int -4)]
             [I.min_val; (I.of_int 0); (I.of_int 3)]; *)

  (* [unsafe_get] [unsafe_set] *)
  let a = A.make 3 (I.of_int 0) in
  for i = 0 to 2 do A.unsafe_set a i (I.of_int i) done;
  for i = 0 to 2 do assert (A.unsafe_get a i = I.of_int i) done;

  let a = A.make 4 (I.of_int 0) in
  for i = 0 to 3 do A.unsafe_set a i (I.of_int i) done;
  for i = 0 to 3 do assert (A.unsafe_get a i = I.of_int i) done;

  (* I/O *)
  (* No marshalling yet *)
  (* let test_structured_io value =
    let (tmp, oc) =
      Filename.open_temp_file ~mode:[Open_binary] "int64_array" ".data"
    in
    Marshal.to_channel oc value [];
    close_out oc;
    let ic = open_in_bin tmp in
    let value' = Marshal.from_channel ic in
    close_in ic;
    Sys.remove tmp;
    assert (compare value value' = 0)
  in
  let l = [(I.of_int 0); (I.of_int 1); (I.of_int -4); I.max_val; I.min_val; 3141592(I.of_int 6)] in
  test_structured_io (A.of_list l); *)

end

module Int32_I = struct
  include Int32
  let max_val = max_int
  let min_val = min_int
  let rand = Random.int32
  let print = Format.printf "%ld"
end

module Int64_I = struct
  include Int64
  let max_val = max_int
  let min_val = min_int
  let rand = Random.int64
  let print = Format.printf "%Ld"
end

module Nativeint_I = struct
  include Nativeint
  let max_val = max_int
  let min_val = min_int
  let rand = Random.nativeint
  let print = Format.printf "%nd"
end

module Int32_array : Array_test_interface = struct
  include Stdlib.Array
  type element_t = int32
  type t = element_t array
  let map_to_array f a = map f a
  let map_from_array f a = map f a
  let max_length = Sys.max_array_length
  let equal = for_all2 (fun x y -> x = y)
  module I = Int32_I
end
module _ = Test (Int32_array)

module Int32_u_array = Make_boxed_test_module(struct
  module M = Make_array(Int32_u_array0)
  module I = Int32_I
  module E = struct
    open Stdlib__Int32_u
    let to_boxed x = to_int32 (x ())
    let of_boxed x () = of_int32 x
  end
end)
module _ = Test (Int32_u_array)

module Int64_array : Array_test_interface = struct
  include Stdlib.Array
  type element_t = int64
  type t = element_t array
  let map_to_array f a = map f a
  let map_from_array f a = map f a
  let max_length = Sys.max_array_length
  let equal = for_all2 (fun x y -> x = y)
  module I = Int64_I
end
module _ = Test (Int64_array)

module Int64_u_array = Make_boxed_test_module(struct
  module M = Make_array(Int64_u_array0)
  module I = Int64_I
  module E = struct
    open Stdlib__Int64_u
    let to_boxed x = to_int64 (x ())
    let of_boxed x () = of_int64 x
  end
end)
module _ = Test (Int64_u_array)

module Nativeint_array : Array_test_interface = struct
  include Stdlib.Array
  type element_t = nativeint
  type t = element_t array
  let map_to_array f a = map f a
  let map_from_array f a = map f a
  let max_length = Sys.max_array_length
  let equal = for_all2 (fun x y -> x = y)
  module I = Nativeint_I
end
module _ = Test (Nativeint_array)

module Nativeint_u_array = Make_boxed_test_module(struct
  module M = Make_array(Nativeint_u_array0)
  module I = Nativeint_I
  module E = struct
    open Stdlib__Nativeint_u
    let to_boxed x = to_nativeint (x ())
    let of_boxed x () = of_nativeint x
  end
end)
module _ = Test (Nativeint_u_array)
