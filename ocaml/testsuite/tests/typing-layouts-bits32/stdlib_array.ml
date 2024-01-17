(* TEST
 readonly_files = "int32_u_array.ml"
 modules = "${readonly_files}"

 * bytecode
   flags = "-extension layouts_alpha"
 * bytecode
   flags = "-extension layouts_beta"
 * native
   flags = "-extension layouts_alpha"
 * native
   flags = "-extension layouts_beta"
*)
open Printf

(* This is the module type of [Float.Array] except type [t] is abstract. *)
module type S = sig
  type t
  val length : t -> int
  val get : t -> int -> int32
  val set : t -> int -> int32 -> unit
  val make : int -> int32 -> t
  val init : int -> (int -> int32) -> t
  val append : t -> t -> t
  val concat : t list -> t
  val sub : t -> int -> int -> t
  val copy : t -> t
  val fill : t -> int -> int -> int32 -> unit
  val blit : t -> int -> t -> int -> int -> unit
  val to_list : t -> int32 list
  val of_list : int32 list -> t
  val iter : (int32 -> unit) -> t -> unit
  val iteri : (int -> int32 -> unit) -> t -> unit
  val map : (int32 -> int32) -> t -> t
  val mapi : (int -> int32 -> int32) -> t -> t
  val fold_left : ('a -> int32 -> 'a) -> 'a -> t -> 'a
  val fold_right : (int32 -> 'a -> 'a) -> t -> 'a -> 'a
  val iter2 : (int32 -> int32 -> unit) -> t -> t -> unit
  val map2 : (int32 -> int32 -> int32) -> t -> t -> t
  val for_all : (int32 -> bool) -> t -> bool
  val exists : (int32 -> bool) -> t -> bool
  val mem : int32 -> t -> bool
  val sort : (int32 -> int32 -> int) -> t -> unit
  val stable_sort : (int32 -> int32 -> int) -> t -> unit
  val fast_sort : (int32 -> int32 -> int) -> t -> unit
  val to_seq : t -> int32 Seq.t
  val to_seqi : t -> (int * int32) Seq.t
  val of_seq : int32 Seq.t -> t
  val map_to_array : (int32 -> 'a) -> t -> 'a array
  val map_from_array : ('a -> int32) -> 'a array -> t
  val unsafe_get : t -> int -> int32
  val unsafe_set : t -> int -> int32 -> unit
  val equal : t -> t -> bool
  (* From Sys, rather than Float.Array *)
  val max_length : int
end

(* module [Array] specialized to [float] and with a few changes,
   satisfies signature S *)
module Int32_array : S = struct
  include Stdlib.Array
  let map_to_array f a = map f a
  let map_from_array f a = map f a
  type t = int32 array
  let max_length = Sys.max_array_length
  let equal = for_all2 (fun x y -> x = y)
end

module Std_Int32_u_array = Int32_u_array
module Int32_u_array : S = struct
  include Int32_u_array

  module Int32_u = Stdlib__Int32_u

  let to_int32 = Int32_u.to_int32
  let of_int32 = Int32_u.of_int32

  type t = int32# array

  let empty () = make 0 (of_int32 0l)
  let to_seq a =
    let rec aux i () =
      if i < length a
      then
        let x = unsafe_get a i in
        Seq.Cons (to_int32 x, aux (i+1))
      else Seq.Nil
    in
    aux 0

  let to_seqi a =
    let rec aux i () =
      if i < length a
      then
        let x = unsafe_get a i in
        Seq.Cons ((i,to_int32 x), aux (i+1))
      else Seq.Nil
    in
    aux 0

  let of_rev_list = function
      [] -> empty ()
    | hd::tl as l ->
      let len = List.length l in
      let a = make len (of_int32 hd) in
      let rec fill i = function
          [] -> a
        | hd::tl -> unsafe_set a i (of_int32 hd); fill (i-1) tl
      in
      fill (len-2) tl

  let of_seq i =
    let l = Seq.fold_left (fun acc x -> x::acc) [] i in
    of_rev_list l


  let to_list t = fold_right (fun f l -> (to_int32 f)::l) t []
  (* let res = ref [] in
   * iter (fun f -> res := (Int32_u.to_int32 f) :: !res);
   * List.rev res *)

  let of_list l =
    let len = List.length l in
    let res = create len #0l in
    List.iteri (fun idx f -> set res idx (of_int32 f)) l;
    res
  let max_length = Sys.max_floatarray_length
  let get t idx = to_int32 (get t idx)
  let set t idx v = set t idx (of_int32 v)

  let make l f = make l (of_int32 f)
  let init l f = init l (fun i -> of_int32 (f i))
  let fill a ofs len v = fill a ofs len (of_int32 v)
  let iter f t = iter (fun v -> f (to_int32 v)) t
  let iteri f t = iteri (fun i v -> f i (to_int32 v)) t
  let map f t = map (fun v -> of_int32 (f (to_int32 v))) t
  let mapi f t = mapi (fun i v -> of_int32 (f i (to_int32 v))) t
  let fold_left f acc t = fold_left (fun acc v -> f acc (to_int32 v)) acc t
  let fold_right f t acc = fold_right (fun v acc -> f (to_int32 v) acc) t acc

  let iter2 f a b = iter2 (fun v1 v2 -> f (to_int32 v1) (to_int32 v2)) a b
  let map2 f a b = map2 (fun v1 v2 -> of_int32 (f (to_int32 v1) (to_int32 v2))) a b
  let for_all f t = for_all (fun v -> f (to_int32 v)) t
  let exists f t = exists (fun v -> f (to_int32 v)) t
  let mem v t = mem (of_int32 v) t
  let sort f t = sort (fun a b -> f (to_int32 a) (to_int32 b)) t
  let stable_sort f t = stable_sort (fun a b -> f (to_int32 a) (to_int32 b)) t
  let fast_sort f t = fast_sort (fun a b -> f (to_int32 a) (to_int32 b)) t

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

  let unsafe_get t idx = to_int32 (unsafe_get t idx)
  let unsafe_set t idx v = unsafe_set t idx (of_int32 v)
  let equal = for_all2 (fun x y -> to_int32 x = to_int32 y)
end


module Test (A : S) : sig end = struct

  (* auxiliary functions *)


  let rec check_i_upto a i =
    if i >= 0 then begin
      assert (A.get a i = Int32.of_int i);
      check_i_upto a (i - 1);
    end
  in

  let check_i a = check_i_upto a (A.length a - 1) in

  let check_inval f arg =
    match f arg with
    | _ -> assert false
    | exception (Invalid_argument _) -> ()
    | exception _ -> assert false
  in

  (* [make] [set] [get] *)
  let a = A.make 1000 1l in
  for i = 0 to 499 do A.set a i (Int32.of_int i) done;
  let rec loop i =
    if i >= 0 then begin
      assert (A.get a i = (if i < 500 then Int32.of_int i else 1l));
      loop (i - 1);
    end
  in loop 999;
  check_inval (A.get a) (-1);
  check_inval (A.get a) (1000);
  check_inval (fun i -> A.set a i 1l) (-1);
  check_inval (fun i -> A.set a i 1l) 1000;
  check_inval (fun i -> A.make i 1l) (-1);
  check_inval (fun i -> A.make i 1l) (A.max_length + 1);

  let a = A.make 1001 1l in
  for i = 0 to 499 do A.set a i (Int32.of_int i) done;
  let rec loop i =
    if i >= 0 then begin
      assert (A.get a i = (if i < 500 then Int32.of_int i else 1l));
      loop (i - 1);
    end
  in loop 1000;
  check_inval (A.get a) (-1);
  check_inval (A.get a) (1001);
  check_inval (fun i -> A.set a i 1l) (-1);
  check_inval (fun i -> A.set a i 1l) 1001;

  (* [length] *)
  let test_length l = assert (l = (A.length (A.make l 1l))) in
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
  let a = A.init 1000 Int32.of_int in
  check_i a;
  let a = A.init 1001 Int32.of_int in
  check_i a;
  check_inval (fun i -> A.init i Int32.of_int) (-1);
  check_inval (fun i -> A.init i Int32.of_int) (A.max_length + 1);

  (* [append] *)
  let check m n =
    let a = A.init m Int32.of_int in
    let b = A.init n (fun x -> Int32.of_int (x + m)) in
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
      (len + n, A.init n (fun i -> Int32.of_int (len + i)) :: acc)
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
  let a = A.init 1000 (fun i -> Int32.of_int (i - 100)) in
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

  let a = A.init 1001 (fun i -> Int32.of_int (i - 101)) in
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
    let a = A.init len Int32.of_int in
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
    let b = A.make (List.length data) 1l in
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
  test_blit_fill [1l;2l;5l;8l;-100l;2120000000l] 3l 3 2;
  let a = A.make 100 0l in
  check_inval (A.fill a (-1) 0) 1l;
  check_inval (A.fill a 0 (-1)) 1l;
  check_inval (A.fill a 0 101) 1l;
  check_inval (A.fill a 100 1) 1l;
  check_inval (A.fill a 101 0) 1l;
  check_inval (A.blit a (-1) a 0) 0;
  check_inval (A.blit a 0 a 0) (-1);
  check_inval (A.blit a 0 a 0) 101;
  check_inval (A.blit a 100 a 0) 1;
  check_inval (A.blit a 101 a 0) 0;
  check_inval (A.blit a 0 a (-1)) 0;
  check_inval (A.blit a 0 a 100) 1;
  check_inval (A.blit a 0 a 101) 0;
  let a = A.make 101 0l in
  check_inval (A.fill a (-1) 0) 1l;
  check_inval (A.fill a 0 (-1)) 1l;
  check_inval (A.fill a 0 102) 1l;
  check_inval (A.fill a 101 1) 1l;
  check_inval (A.fill a 102 0) 1l;
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
  test_blit_overlap [1l; 2l; 3l; 4l] 1 2 2;

  (* [to_list] [of_list] *)
  let a = A.init 1000 Int32.of_int in
  assert (A.equal a (A.of_list (A.to_list a)));
  let a = A.init 1001 Int32.of_int in
  assert (A.equal a (A.of_list (A.to_list a)));
  let a = A.init 0 Int32.of_int in
  assert (A.equal a (A.of_list (A.to_list a)));
  (* check_inval omitted *)

  (* [iter] *)
  let a = A.init 300 (Int32.of_int) in
  let r = ref 0l in
  A.iter (fun x -> assert (x = !r); r := Int32.add x 1l) a;
  A.iter (fun _ -> assert false) (A.make 0 0l);
  assert (!r = 300l);

  let a = A.init 301 (Int32.of_int) in
  let r = ref 0l in
  A.iter (fun x -> assert (x = !r); r := Int32.add x 1l) a;
  assert (!r = 301l);

  (* [iteri] *)
  let a = A.init 300 Int32.of_int in
  let r = ref 0 in
  let f i x =
    assert (i = !r);
    assert (x = Int32.of_int i);
    r := i + 1
  in
  A.iteri f a;
  A.iteri (fun _ _ -> assert false) (A.make 0 0l);
  assert (!r = 300);

  let a = A.init 301 Int32.of_int in
  let r = ref 0 in
  let f i x =
    assert (i = !r);
    assert (x = Int32.of_int i);
    r := i + 1
  in
  A.iteri f a;
  A.iteri (fun _ _ -> assert false) (A.make 0 0l);
  assert (!r = 301);

  (* [map], test result and order of evaluation *)
  let a = A.init 500 Int32.of_int in
  let r = ref 0l in
  let f x =
    assert (x = !r);
    r := Int32.add !r 1l;
    Int32.sub x 1l
  in
  let b = A.map f a in
  check_i (A.sub b 1 499);

  let a = A.init 501 Int32.of_int in
  let r = ref 0l in
  let f x =
    assert (x = !r);
    r := Int32.add !r 1l;
    Int32.sub x 1l
  in
  let b = A.map f a in
  check_i (A.sub b 1 500);

  (* [mapi], test result and order of evaluation *)
  let a = A.init 500 Int32.of_int in
  let r = ref 0l in
  let f i x =
    assert (x = Int32.of_int i);
    assert (x = !r);
    r := Int32.add !r 1l;
    Int32.sub x 1l
  in
  let b = A.mapi f a in
  check_i (A.sub b 1 499);

  let a = A.init 501 Int32.of_int in
  let r = ref 0l in
  let f i x =
    assert (x = Int32.of_int i);
    assert (x = !r);
    r := Int32.add !r 1l;
    Int32.sub x 1l
  in
  let b = A.mapi f a in
  check_i (A.sub b 1 500);

  (* [fold_left], test result and order of evaluation *)
  let a = A.init 500 Int32.of_int in
  let f acc x =
    assert (acc = x);
    Int32.add x 1l
  in
  let acc = A.fold_left f 0l a in
  assert (acc = 500l);

  let a = A.init 501 Int32.of_int in
  let acc = A.fold_left f 0l a in
  assert (acc = 501l);

  (* [fold_right], test result and order of evaluation *)
  let a = A.init 500 Int32.of_int in
  let f x acc =
    assert (x = Int32.sub acc 1l);
    x
  in
  let acc = A.fold_right f a 500l in
  assert (acc = 0l);

  let a = A.init 501 Int32.of_int in
  let acc = A.fold_right f a 501l in
  assert (acc = 0l);

  (* [iter2], test result and order of evaluation *)
  let a = A.init 123 Int32.of_int in
  let b = A.init 123 Int32.of_int in
  let r = ref 0l in
  let f x y =
    assert (x = !r);
    assert (y = !r);
    r := Int32.add!r 1l;
  in
  A.iter2 f a b;
  let c = A.make 456 0l in
  check_inval (A.iter2 (fun _ _ -> assert false) a) c;
  check_inval (A.iter2 (fun _ _ -> assert false) c) a;

  let a = A.init 124 Int32.of_int in
  let b = A.init 124 Int32.of_int in
  let r = ref 0l in
  let f x y =
    assert (x = !r);
    assert (y = !r);
    r := Int32.add !r 1l;
  in
  A.iter2 f a b;

  (* [map2], test result and order of evaluation *)
  let a = A.init 456 Int32.of_int in
  let b = A.init 456 (fun i -> Int32.(mul (of_int i) 2l)) in
  let r = ref 0l in
  let f x y =
    assert (x = !r);
    assert (y = Int32.mul !r 2l);
    r := Int32.add !r 1l;
    Int32.(neg (sub x y))
  in
  let c = A.map2 f a b in
  check_i c;
  let d = A.make 455 0l in
  check_inval (A.map2 (fun _ _ -> assert false) a) d;
  check_inval (A.map2 (fun _ _ -> assert false) d) a;

  let a = A.init 457 Int32.of_int in
  let b = A.init 457 (fun i -> Int32.(mul (of_int i) 2l)) in
  let r = ref 0l in
  let f x y =
    assert (x = !r);
    assert (y = Int32.mul !r 2l);
    r := Int32.add !r 1l;
    Int32.(neg (sub x y))
  in
  let c = A.map2 f a b in
  check_i c;

  (* [for_all], test result and order of evaluation *)
  let a = A.init 777 Int32.of_int in
  let r = ref 0l in
  let f x =
    assert (x = !r);
    r := Int32.add x 1l;
    true
  in
  assert (A.for_all f a);
  let f x = assert (x = 0l); false in
  assert (not (A.for_all f a));

  let a = A.init 778 Int32.of_int in
  let r = ref 0l in
  let f x =
    assert (x = !r);
    r := Int32.add x 1l;
    true
  in
  assert (A.for_all f a);
  let f x = assert (x = 0l); false in
  assert (not (A.for_all f a));

  (* [exists], test result and order of evaluation *)
  let a = A.init 777 Int32.of_int in
  let r = ref 0l in
  let f x =
    assert (x = !r);
    r := Int32.add x 1l;
    false
  in
  assert (not (A.exists f a));
  let f x = assert (x = 0l); true in
  assert (A.exists f a);

  let a = A.init 778 Int32.of_int in
  let r = ref 0l in
  let f x =
    assert (x = !r);
    r := Int32.add x 1l;
    false
  in
  assert (not (A.exists f a));
  let f x = assert (x = 0l); true in
  assert (A.exists f a);

  (* [mem] *)
  let a = A.init 7777 Int32.of_int in
  assert (A.mem 0l a);
  assert (A.mem 7776l a);
  assert (not (A.mem (-1l) a));
  assert (not (A.mem 7777l a));
  let check v =
    A.set a 1000 v;
    assert (A.mem v a);
  in
  List.iter check [Int32.max_int; Int32.min_int; -1l; 0l];

  let a = A.init 7778 Int32.of_int in
  assert (A.mem 0l a);
  assert (A.mem 7777l a);
  assert (not (A.mem (-1l) a));
  assert (not (A.mem 7778l a));
  let check v =
    A.set a 1001 v;
    assert (A.mem v a);
  in
  List.iter check [Int32.max_int; Int32.min_int; -1l; 0l];

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
  let rand_int32 _ =
    match Random.int 1000 with
    | n when n < 500 -> Random.int32 Int32.max_int
    | _ -> Int32.neg (Random.int32 Int32.max_int)
  in
  let check s =
    let a = A.init 5 Int32.of_int in
    check_sort s Stdlib.compare a; (* already sorted *)
    check_sort s (fun x y -> Stdlib.compare y x) a; (* reverse-sorted *)

    let a = A.init 6 Int32.of_int in
    check_sort s Stdlib.compare a; (* already sorted *)
    check_sort s (fun x y -> Stdlib.compare y x) a; (* reverse-sorted *)

    let a = A.of_list [Int32.max_int; Int32.min_int; -1l; 0l] in
    check_sort s Stdlib.compare a; (* already sorted *)
    check_sort s (fun x y -> Stdlib.compare y x) a; (* reverse-sorted *)

    let a = A.init 50000 rand_int32 in
    check_sort s Stdlib.compare a;
    let a = A.init 50001 rand_int32 in
    check_sort s Stdlib.compare a;
    let a = A.make 1000 1l in
    check_sort s Stdlib.compare a;
    let a = A.make 1001 1l in
    check_sort s Stdlib.compare a;
    let a = A.append (A.make 1000 1l) (A.make 1000 2l) in
    check_sort s Stdlib.compare a;
    let a = A.append (A.make 1001 1l) (A.make 1001 2l) in
    check_sort s Stdlib.compare a;
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
  check_seq (A.init 999 Int32.of_int);
  check_seq (A.init 1000 Int32.of_int);
  check_seq (A.make 0 0l);

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
  check_seqi (A.init 999 Int32.of_int);
  check_seqi (A.init 1000 Int32.of_int);
  check_seqi (A.make 0 0l);

  (* [of_seq] *)
  let r = ref 0 in
  let rec f () =
    if !r = 100 then Seq.Nil else begin
      let res = Seq.Cons (Int32.of_int !r, f) in
      r := !r + 1;
      res
    end
  in
  let a = A.of_seq f in
  assert (A.equal a (A.init 100 Int32.of_int));
  assert (A.equal (A.of_seq Seq.empty) (A.make 0 0l));

  (* [map_to_array] *)
  let r = ref 0 in
  let f x =
    assert (x = Int32.of_int !r);
    r := !r + 1;
    Int32.mul x 2l
  in
  let a = A.init 876 Int32.of_int in
  let ar1 = A.map_to_array f a in
  let ar2 = Array.init 876 (fun x -> Int32.of_int (2 * x)) in
  assert (ar1 = ar2);
  let ar = A.map_to_array (fun _ -> assert false) (A.make 0 0l) in
  assert (ar = [| |]);

  (* [map_from_array] *)
  let r = ref 0 in
  let f x =
    assert (x = Int32.of_int !r);
    r := !r + 1;
    Int32.mul x 2l
  in
  let ar = Array.init 876 Int32.of_int in
  let a1 = A.map_from_array f ar in
  let a2 = A.init 876 (fun x -> Int32.of_int (2 * x)) in
  assert (A.equal a1 a2);
  let a = A.map_from_array (fun _ -> assert false) [| |] in
  assert (A.equal a (A.make 0 0l));

  (* comparisons *)
  (* No polymorphic compare yet *)
  (* let normalize_comparison n =
    if n = 0 then 0 else if n < 0 then -1 else 1
  in
  let check c l1 l2 =
    assert (c = (normalize_comparison (compare (A.of_list l1) (A.of_list l2))))
  in
  check 0    [0l; 1l; -4l; Int32.max_int; Int32.min_int]
             [0l; 1l; -4l; Int32.max_int; Int32.min_int];
  check (-1) [0l; 1l; -4l; Int32.max_int; Int32.min_int]
             [0l; 1l; -4l; Int32.max_int; Int32.(add min_int 1l)];
  check (-1) [0l; 1l; -4l; Int32.max_int; 45096843l]
             [0l; 1l; -4l; Int32.max_int; 45096844l];
  check 1    [0l; 2l; -4l]
             [0l; 0l; 3l];
  check 1    [0l; 2l; -4l]
             [Int32.min_int; 0l; 3l]; *)

  (* [unsafe_get] [unsafe_set] *)
  let a = A.make 3 0l in
  for i = 0 to 2 do A.unsafe_set a i (Int32.of_int i) done;
  for i = 0 to 2 do assert (A.unsafe_get a i = Int32.of_int i) done;

  let a = A.make 4 0l in
  for i = 0 to 3 do A.unsafe_set a i (Int32.of_int i) done;
  for i = 0 to 3 do assert (A.unsafe_get a i = Int32.of_int i) done;

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
  let l = [0l; 1l; -4l; Int32.max_int; Int32.min_int; 31415926l] in
  test_structured_io (A.of_list l); *)

end

module T = Test (Int32_array)
module T2 = Test (Int32_u_array)

(* Extra tests for functions not covered above *)
module Int32_u = Stdlib__Int32_u
let () =
  let open Std_Int32_u_array in
  let (+.) x y = Int32.add x y in
  let check_inval f arg =
    match f arg with
    | _ -> assert false
    | exception (Invalid_argument _) -> ()
    | exception _ -> assert false
  in

  (* make_matrix *)
  check_inval (make_matrix (-1) 1) (Int32_u.of_int 1);
  check_inval (make_matrix 1 (-1)) (Int32_u.of_int 1);
  let check_matrix a =
    let row_len = Array.length a in
    assert (row_len > 0);
    let col_len = length (a.(0)) in
    for row = 0 to (row_len - 1) do
      assert (length (a.(row)) = col_len);
      for col = 0 to (col_len - 1) do
        assert Int32_u.(equal (get (a.(row)) col) (of_int 1))
      done
    done in
  let a = make_matrix 100 100 (Int32_u.of_int 1) in
  check_matrix a;
  let a = make_matrix 101 100 (Int32_u.of_int 1) in
  check_matrix a;
  let a = make_matrix 101 101 (Int32_u.of_int 1) in
  check_matrix a;
  let a = make_matrix 100 101 (Int32_u.of_int 1) in
  check_matrix a;

  (* for_all2 *)
  let test a =
    let r = ref 0l in
    let f x y =
      let x = Int32_u.to_int32 x in
      let y = Int32_u.to_int32 y in
      assert (x = !r);
      assert (y = !r);
      r := x +. 1l;
      true
    in
    assert (for_all2 f a a);
    let f x y =
      let x = Int32_u.to_int32 x in
      let y = Int32_u.to_int32 y in
      assert (x = 0l); assert (y = 0l); false in
    if length a > 0 then assert (not (for_all2 f a a))

  in
  let a = init 777 Int32_u.of_int in
  test a;
  let a = init 778 Int32_u.of_int in
  test a;
  let a = init 0 Int32_u.of_int in
  test a;
  check_inval (fun x -> for_all2 (fun _ _ -> true) (make 100 x) (make 101 x))
    (Int32_u.of_int 1);

  (* exists2 *)
  let test a =
    let r = ref 0l in
    let f x y =
      let x = Int32_u.to_int32 x in
      let y = Int32_u.to_int32 y in
      assert (x = !r);
      assert (y = !r);
      r := x +. 1l;
      false
    in
    assert (not (exists2 f a a));
    let f x y =
      let x = Int32_u.to_int32 x in
      let y = Int32_u.to_int32 y in
      assert (x = 0l); assert (y = 0l); true in
    if length a > 0 then assert (exists2 f a a)

  in
  let a = init 777 Int32_u.of_int in
  test a;
  let a = init 778 Int32_u.of_int in
  test a;
  let a = init 0 Int32_u.of_int in
  test a;
  check_inval (fun x -> exists2 (fun _ _ -> true) (make 100 x) (make 101 x))
    (Int32_u.of_int 1)
