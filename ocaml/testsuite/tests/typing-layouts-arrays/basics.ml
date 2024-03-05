(* TEST
   * flambda2
   ** expect
     flags = "-extension layouts_alpha"
   ** expect
     flags = "-extension layouts_beta"
   ** expect
*)
(* Tests around type-checking arrays of unboxed types. Tests around
   compilation correctness should go somewhere else. *)

(*******************************************)
(* Test 1: Support unboxed types in arrays *)

type t_any : any

type t1 = float# array
type t2 = int32# array
type t3 = int64# array
type t4 = nativeint# array
type t5 = t_any array

type ('a : float64) t1' = 'a array
type ('a : bits32) t2' = 'a array
type ('a : bits64) t3' = 'a array
type ('a : word) t4' = 'a array
type ('a : any) t5' = 'a array

[%%expect{|
type t_any : any
type t1 = float# array
type t2 = int32# array
type t3 = int64# array
type t4 = nativeint# array
type t5 = t_any array
type ('a : float64) t1' = 'a array
type ('a : bits32) t2' = 'a array
type ('a : bits64) t3' = 'a array
type ('a : word) t4' = 'a array
type ('a : any) t5' = 'a array
|}];;

(*****************************)
(* Test 2: array expressions *)

let v1 = [| #1. |]
[%%expect{|
val v1 : float# array = [|<abstr>|]
|}];;


let v2 = [| #1l |]
[%%expect{|
val v2 : int32# array = [|<abstr>|]
|}];;


let v3 = [| #1L |]
[%%expect{|
val v3 : int64# array = [|<abstr>|]
|}];;


let v4 = [| #1n |]
[%%expect{|
val v4 : nativeint# array = [|<abstr>|]
|}];;

(****************************************)
(* Test 3: Array operations do not work *)

let f (x : float# array) = x.(0)
[%%expect{|
Line 1, characters 27-28:
1 | let f (x : float# array) = x.(0)
                               ^
Error: This expression has type float# array
       but an expression was expected of type 'a array
       The layout of float# is float64, because
         it is the primitive float64 type float#.
       But the layout of float# must be a sublayout of value, because
         of layout requirements from an imported definition.
|}];;

let f (x : float# array) = Array.length x
[%%expect{|
Line 1, characters 40-41:
1 | let f (x : float# array) = Array.length x
                                            ^
Error: This expression has type float# array
       but an expression was expected of type 'a array
       The layout of float# is float64, because
         it is the primitive float64 type float#.
       But the layout of float# must be a sublayout of value, because
         of layout requirements from an imported definition.
|}];;

(*****************************************************************)
(* Test 4: Calling wrong primitives on unboxed array kinds fails *)

external get : float# array -> int -> float = "%floatarray_safe_get"
let d (x : float# array) = get x 0

[%%expect{|
external get : float# array -> int -> float = "%floatarray_safe_get"
Line 2, characters 27-34:
2 | let d (x : float# array) = get x 0
                               ^^^^^^^
Error: Array of unboxed types can't be operated on by primitives
       for arrays of boxed types.
|}];;


(* Doesn't prevent the use of [Obj.magic] *)
external get : floatarray -> int -> float = "%floatarray_safe_get"
let d (x : float# array) = get (Obj.magic x : floatarray) 0

[%%expect{|
external get : floatarray -> int -> float = "%floatarray_safe_get"
val d : float# array -> float = <fun>
|}];;

external get : ('a : any). 'a array -> int -> float = "%floatarray_safe_get"
let d (x : 'a array) = get x 0

[%%expect{|
external get : ('a : any). 'a array -> int -> float = "%floatarray_safe_get"
Line 2, characters 23-30:
2 | let d (x : 'a array) = get x 0
                           ^^^^^^^
Error: A representable layout is required here.
       The layout of 'a is any, because
         of the definition of d at line 2, characters 6-30.
       But the layout of 'a must be representable, because
         it's the type of an array element.
|}];;

external get : int32# array -> int -> float = "%floatarray_safe_get"
let d (x : int32# array) = get x 0

[%%expect{|
external get : int32# array -> int -> float = "%floatarray_safe_get"
Line 2, characters 27-34:
2 | let d (x : int32# array) = get x 0
                               ^^^^^^^
Error: Array of unboxed types can't be operated on by primitives
       for arrays of boxed types.
|}];;

external get : int64# array -> int -> float = "%floatarray_safe_get"
let d (x : int64# array) = get x 0

[%%expect{|
external get : int64# array -> int -> float = "%floatarray_safe_get"
Line 2, characters 27-34:
2 | let d (x : int64# array) = get x 0
                               ^^^^^^^
Error: Array of unboxed types can't be operated on by primitives
       for arrays of boxed types.
|}];;

external get : nativeint# array -> int -> float = "%floatarray_safe_get"
let d (x : nativeint# array) = get x 0

[%%expect{|
external get : nativeint# array -> int -> float = "%floatarray_safe_get"
Line 2, characters 31-38:
2 | let d (x : nativeint# array) = get x 0
                                   ^^^^^^^
Error: Array of unboxed types can't be operated on by primitives
       for arrays of boxed types.
|}];;

(**************************)
(* Test 5: [@layout_poly] *)

external[@layout_poly] get : ('a : any). 'a array -> int -> 'a = "%array_safe_get"
let f1 (x : float# array) = get x 0
let f2 (x : int32# array) = get x 0
let f3 (x : int64# array) = get x 0
let f4 (x : nativeint# array) = get x 0

[%%expect{|
external get : ('a : any). 'a array -> int -> 'a = "%array_safe_get"
  [@@layout_poly]
val f1 : float# array -> float# = <fun>
val f2 : int32# array -> int32# = <fun>
val f3 : int64# array -> int64# = <fun>
val f4 : nativeint# array -> nativeint# = <fun>
|}];;

external[@layout_poly] set : ('a : any). 'a array -> int -> 'a -> unit = "%array_safe_set"
let f1 (x : float# array) v = set x 0 v
let f2 (x : int32# array) v = set x 0 v
let f3 (x : int64# array) v = set x 0 v
let f4 (x : nativeint# array) v = set x 0 v

[%%expect{|
external set : ('a : any). 'a array -> int -> 'a -> unit = "%array_safe_set"
  [@@layout_poly]
val f1 : float# array -> float# -> unit = <fun>
val f2 : int32# array -> int32# -> unit = <fun>
val f3 : int64# array -> int64# -> unit = <fun>
val f4 : nativeint# array -> nativeint# -> unit = <fun>
|}]
