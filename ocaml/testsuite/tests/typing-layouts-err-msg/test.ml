(* TEST

readonly_files = "a.ml"
flags = "-extension layouts_alpha"
* setup-ocamlc.byte-build-env
** ocamlc.byte
module = "a.ml"
*** expect
*)

#directory "ocamlc.byte";;
#load "a.cmo";;

type t_void : void
let f (x : t_void): 'a A.t = x

[%%expect{|
type t_void : void
Line 2, characters 29-30:
2 | let f (x : t_void): 'a A.t = x
                                 ^
Error: This expression has type t_void but an expression was expected of type
         'a A.t = ('a : value)
       The layout of t_void is void, because
         of the annotation on the declaration of the type t_void.
       But the layout of t_void must be a sublayout of value, because
         the type argument of imported type A.t has layout value.
|}]

type t_void : void
type t = t_void A.t

[%%expect{|
type t_void : void
Line 2, characters 9-15:
2 | type t = t_void A.t
             ^^^^^^
Error: This type t_void should be an instance of type ('a : value)
       The layout of t_void is void, because
         of the annotation on the declaration of the type t_void.
       But the layout of t_void must be a sublayout of value, because
         the type argument of imported type A.t has layout value.
|}]


type t_void : void
let f (x : t_void): ('a, 'b) A.t2 = x

[%%expect{|
type t_void : void
Line 2, characters 36-37:
2 | let f (x : t_void): ('a, 'b) A.t2 = x
                                        ^
Error: This expression has type t_void but an expression was expected of type
         ('a, 'b) A.t2 = ('a : value)
       The layout of t_void is void, because
         of the annotation on the declaration of the type t_void.
       But the layout of t_void must be a sublayout of value, because
         the type argument of imported type A.t2 has layout value.
|}]

type t_void : void
type t = (t_void, t_void) A.t2

[%%expect{|
type t_void : void
Line 2, characters 10-16:
2 | type t = (t_void, t_void) A.t2
              ^^^^^^
Error: This type t_void should be an instance of type ('a : value)
       The layout of t_void is void, because
         of the annotation on the declaration of the type t_void.
       But the layout of t_void must be a sublayout of value, because
         the type argument of imported type A.t2 has layout value.
|}]
