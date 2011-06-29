(* identifiers *)
type ide = Ide of string

(* pointer expression *)
type pexp =
	  BaseDeref of ide (* ^p *)
	| PtrDeref of pexp (* ^..^p *)

(* arithmetical expressions *)
type aexp  =
	  N of int
	| R of float
	| Ident of ide
	| Vec of ide * aexp
	| Sum of aexp * aexp
	| Sub of aexp * aexp
	| Mul  of  aexp * aexp
	| Div  of  aexp * aexp
	| IdDeref of pexp (* ^..^ide *)
	| IdRef of ide (* @ide *)
	| Nil (* NULL *)

(* boolean expressions *)
type bexp =
	  B of bool
	| Equ of aexp * aexp
	| LE of  aexp * aexp
	| LT of  aexp * aexp
	| Not of bexp
	| And of bexp * bexp
	| Or of bexp * bexp

(* left expressions *)
type lexp =
	  LVar of ide
	| LVec of ide * aexp
	| LPointer of pexp

(* declarations *)
type bType = Int | Float

type pType = 
	  Ptr of bType	(* ^int *)
	| PPtr of pType (* ^(^..^int) *)

type gType =
	  Basic of bType
	| Const of bType * aexp
	| Vector of bType * int * int
	| Pointer of pType

type dec = Dec of ide * gType

(* commands *)
type cmd =
	  Ass of lexp * aexp
	| Blk of cmd list
	| Ite of bexp * cmd * cmd
	| While of bexp * cmd
	| For of ide * aexp * aexp * cmd
	| Repeat of cmd * bexp
	| Write of aexp
	| Alloc of ide
	| Free of ide
	| PCall of ide * aexp list

(* procedures *)
type param = Par of ide * bType

type sub_prog = Proc of ide * param list * dec list * cmd

(* programs *)
type program = Program of dec list * sub_prog list * cmd | Null
