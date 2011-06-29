(* (2003)Originale ML(Marco Pistore & Floriano Zini) *)
(*	(2004)Estensione OCAML(Fabrizio Lazzarotto)	*)
(*		  (2007)Revisione (Stefano Schivo)		 *)
(*			(2011) Revision (Nataliia Bielova)   *)

(*				(2011) Project Pointer-Heap (Walter Da Col) *)

open Syntaxtree;;
(*** INTERPRETER DOMAINS ***)

(* memory *)
type loc = 
	  Loc of int
	| HLoc of int (* Heap pointer *)
	| NULL (* Null location *)
	
type value =
	  ValueInt of int
	| ValueFloat of float
	| ValueLoc of loc (* Pointers have a loc for value *)

type store = loc -> value

type env_entry =  
	  Var of loc
	| Val of value
	| Descr_Vector of loc * int * int
	| Descr_Pointer of loc * int * bType (* loc, depth and type *)
	| Descr_Procedure of param list * dec list * cmd


type env = ide -> env_entry

(* heap *)
type heap_entry = int * value (* reference counter * value *)

type free_loc = loc list (* list of free location *)

type heap_store = loc -> heap_entry

type heap = free_loc * heap_store

(* exception *)
exception NO_MEM
exception NO_IDE
exception SYNTAX
exception INDEX_OUT_OF_BOUNDS
exception INDEX_IS_FLOAT
exception DIFFERENT_TYPE_OPERATION
exception DIFFERENT_TYPE_ASSIGNATION
exception PARAMETERS_DO_NOT_MATCH
(* pointer *)
exception PTR_NULL_POINTER of string
exception PTR_ASSIGN of string
exception PTR_DEREF of string
(* heap *)
exception NO_HEAP
exception HEAP_OUT_OF_MEM
exception STATIC_DEALLOC
(* warning suppressor - for impossible match case *)
exception WARNING_SUPPRESSOR
(* Debug exception *)
exception DEBUG of string

(******************************)

(* THE INTERPRETER *)

(* utility functions *)
let initenv (x:ide):env_entry = raise NO_IDE
let initmem (x:loc):value = raise NO_MEM

let updatemem ((s:store), addr, (v:value)) :store = function
	x -> if (x = addr) then v else s(x)

let updateenv ((e:env),id, (v:env_entry)) :env = function
	y -> if (y = id) then v else e(y)

let newmem (s: store) : int =   
	let rec aux n =
		try (let _=s(Loc(n)) in aux(n+1)) with NO_MEM -> n (* s(Loc(n)) is used only to read the memory at the location n, so to see whether that location is non-valid (which means free), and so we don't consider it's value *)
	in aux 0

let rec updatemem_vector((s:store), addr, length, (v:value)) :store =
	match length with
		  1 ->  updatemem(s,addr,v)
		| n ->  let s' = updatemem(s,addr,v)
				in
					updatemem_vector(s',Loc(newmem s'),n-1,v)

(* HEAP MEMORY *)

(* Init heap store *)
let init_heap_store (x:loc):heap_entry = raise NO_HEAP

(* Initialize a list of free location with given size *)
(* starting from 1000 to visually recognize a loc from an hloc *)
let rec init_free_loc (size:int):free_loc =
	match size with
		  0 -> []
		| n -> (init_free_loc(size -1))@[HLoc(n+999)]  

(* Get first free location and update list of free location *)
let new_heaploc (fl:free_loc):(free_loc * loc) =
	match fl with
		  [] -> raise HEAP_OUT_OF_MEM (* here can be a good point for gc *)
		| x::y -> y,x

(* Allocate a new space in heap, set by default to (0,NULL) *)
let new_heapentry ((hs:heap_store),(addr:loc)):heap_store = function
	x -> if (x = addr) then (0,ValueLoc(NULL)) else hs(x)

(* Init heap formed by list of location and a store *)
let initheap (size:int):heap = (init_free_loc(size),init_heap_store)

(* Alloc some space in heap and return modified heap and location of the space *)
let new_heapmem (h:heap):(heap * loc) =
	match h with
		  hlf,hhs -> (
				let hlf',newloc = (new_heaploc(hlf))
				in
				let hhs' = (new_heapentry(hhs,newloc))
				in
				((hlf',hhs'),newloc)
				)

(* put a location in free_loc *)
let remove_mem ((h:heap),(x:loc)):heap =
	match h with
		hfl,hhs -> ((hfl@[x]),hhs)

(* update value in heap_store *)
let update_heapentry ((hs:heap_store),(addr:loc),(v:value)):heap_store = function
	x -> (
		let rc = (
			match hs(addr) with
				r,_ -> r
			)
		in
		if (x = addr) then (rc,v) else hs(x)
		)

(* update ref counter in heap_store *)
let update_heapentry_ref ((hs:heap_store),(addr:loc),(r:int)):heap_store = function
	x -> (
		let v = (
			match hs(addr) with
				_,y -> y
			)
		in
		if (x = addr) then (r,v) else hs(x)
		)

(* HEAP UTILITY *)

(* read reference counter of loc *)
let href ((h:heap),(x:loc)):int =
	match h with
		hfl,hhs -> (
			match hhs(x) with
				r,_ -> r
			)

(* increase ref counter of loc  *)
let href_up ((h:heap),(x:loc)):heap =
	match h with
		hfl,hhs -> (
			let r,_ = hhs(x) (* Location test *)
			in
			(hfl,(update_heapentry_ref(hhs,x,(r+1))))
			)

(* decrease ref counter of loc  *)
let rec href_down ((h:heap),(x:loc)):heap =
	match h with
		hfl,hhs -> (
			let r,l = hhs(x) (* Location test *)
			in
			match r with
				  1 -> ( (* if ref drop to zero, poited HLoc loses one reference *)
						let h' = (
							match l with
								  ValueLoc(HLoc(y)) -> (href_down(h,HLoc(y)))
								| _ -> h
							)
						in
						let h'' = (
							match h' with
								hfl',hhs' -> (hfl',(update_heapentry_ref(hhs',x,(r-1))))
							)
						in (remove_mem(h'',x)) (* Ref = 0, remove allocation *)
					)						
				| n -> (hfl,(update_heapentry_ref(hhs,x,(r-1))))
			)

(* HEAP READ/WRITE *)

(* read value at loc in heap *)
let hread ((h:heap),(x:loc)):value =
	match h with
		hfl,hhs -> (
			match hhs(x) with 
				r,v -> if r == 0 then raise NO_HEAP else v 
			)

(* write value in heap *)
let hwrite ((h:heap),(x:loc),(v:value)):heap =
	match h with
		hfl,hhs -> (
			let r,_ = hhs(x) (* Location test *)
			in (
				if r == 0 then 
					raise NO_HEAP (* if ref is 0 mem is not accessible *)
				else 
					(hfl,(update_heapentry(hhs,x,v)))
				)
			)

(* PEXP EVALUATION - UTILITY *)

(* evaluate depth of a pexp *)
let rec get_pexp_dep (e:pexp)(r:env):int = match e with
	  BaseDeref(i) -> (
			match r(i) with
				  Descr_Pointer(_,d,_) -> (d - 1) (* with p:^int, if we evaluate ^p we have a depth of 0 because ^p is a ValueInt *)
				| _ -> raise SYNTAX
			)
	| PtrDeref(x) -> (get_pexp_dep x r) - 1

let rec get_pexp_id (e:pexp):ide = match e with
	  BaseDeref(y) -> y
	| PtrDeref(x) -> (get_pexp_id x)

(* utility for scroll location chain , p -> loc -> loc -> .... -> int *)
let get_pvalue_at_depth (i:ide)(r:env)(s:store)(h:heap)(d:int):value = (
	let rec inception (s:store)(h:heap)(start:value)(lvl:int):value = (
		match lvl with
			  0 -> start
			| n -> (
				match start with
					  ValueLoc(x) -> (
							match x with
								  NULL -> raise (PTR_NULL_POINTER("Cannot dereference a nil location"))
								| Loc(y) -> inception s h (s(Loc(y))) (n-1)
								| HLoc(y) -> inception s h (hread(h,HLoc(y))) (n-1)
							)
					| _ -> raise WARNING_SUPPRESSOR
				)
		)
	in
	match r(i) with
		Descr_Pointer(ploc,pdep,_) -> (
			if d < 0 then raise (PTR_DEREF("Too many dereference"));
				inception s h (s(ploc)) (pdep - d)
				)
		| _ ->  raise SYNTAX (* DEREF of a non-pointer *)
	)
				

(* EXPRESSION EVALUATION *)

(* evaluation of pointer expression *)
let rec eval_pexp (e:pexp) (r:env) (s:store) (h:heap): value = (
	let pid = (get_pexp_id e)
	in (get_pvalue_at_depth pid r s h (get_pexp_dep e r))
	)
	  
(* evaluation of arithmetical expressions *)
let rec eval_aexp (e:aexp) (r:env) (s:store) (h:heap) : value = match e with
	  N(n)	  ->  ValueInt(n)
	| R(n)	  ->  ValueFloat(n)
	| Ident(i)  ->  (
					 match r(i) with
						  Var(l) -> s(l)
						| Val(v) -> v
						| Descr_Pointer(p,_,_) -> s(p) (* evaluating pointer result in pointed address *)
						| _ -> raise SYNTAX
					)
	| Vec(v,i)  ->  (
					 match r(v) with
						  Descr_Vector(Loc(vo),lb,ub) ->
								let res =  (eval_aexp i r s h) in (
								match res with 
									  ValueFloat(_) -> raise INDEX_IS_FLOAT
									| ValueInt(pos) ->							 
												if (pos >= lb && pos <= ub) then
													s(Loc(vo+pos))
												else
													raise INDEX_OUT_OF_BOUNDS
									| _ -> raise SYNTAX
								)
						| _ -> raise SYNTAX
					)
	
	| Sum (a,b) ->  aexp_op_fun a b r s h (+) (+.)
	
	| Sub (a,b) ->  aexp_op_fun a b r s h (-) (-.)
	
	| Mul (a,b) ->  let mi a b = a*b
					in 
						let mf a b = a*.b
						in aexp_op_fun a b r s h mi mf
	
	| Div (a,b) -> aexp_op_fun a b r s h (/) (/.)
	(* Pointer *)
	| IdRef(i) -> ( (* @ide *)
				match r(i) with
					  Var(l) -> ValueLoc(l)
					| Descr_Pointer(p,_,_) -> ValueLoc(p)
					| _ -> raise SYNTAX
				)
	| IdDeref(exp) -> (eval_pexp exp r s h) (* ^..^ide *)
	| Nil -> ValueLoc(NULL)


and aexp_op_fun  (a:aexp) (b:aexp) (r:env) (s:store) (h:heap) fi fr = 
	let aValue = (eval_aexp a r s h)
		and bValue = (eval_aexp b r s h)
	in (
		 match aValue with 
			 ValueInt(op1)	  -> (
									 match bValue with
										  ValueInt(op2) -> ValueInt(fi op1 op2)
										| _ -> raise DIFFERENT_TYPE_OPERATION
									)
			| ValueFloat(op1)   -> (
									 match bValue with
										  ValueFloat(op2) -> ValueFloat(fr op1 op2)
										| _ -> raise DIFFERENT_TYPE_OPERATION
									)
			| ValueLoc(_) -> raise SYNTAX
		)


let rec eval_bexp (e:bexp) (r:env) (s:store) (h:heap) = match e with
	  B(b)	  ->  b
	| And (a,b) ->  ((eval_bexp a r s h) && (eval_bexp b r s h))
	| Or  (a,b) ->  ((eval_bexp a r s h) || (eval_bexp b r s h))
	| Equ (a,b) ->  ((eval_aexp a r s h)  = (eval_aexp b r s h))
	| LE  (a,b) ->  ((eval_aexp a r s h) <= (eval_aexp b r s h))
	| LT  (a,b) ->  ((eval_aexp a r s h)  < (eval_aexp b r s h))
	| Not (a)   ->  (not(eval_bexp a r s h))

(* Obtain depth for a generic expression, for assigning to a pointer *)
let rec get_aexp_dep (e:aexp)(r:env)(s:store)(h:heap): int = match e with
	  IdDeref(x) -> (
				let id = (get_pexp_id x)
				in
				match r(id) with
					  Descr_Pointer(_,_,_) ->(get_pexp_dep x r)
					| _ -> raise WARNING_SUPPRESSOR (* we can't arrive here with a non-pointer *)
				)
	| _ -> ( (* any aexp but IdDeref *)
			let ret = (eval_aexp e r s h)
			in
			match ret with
				  ValueLoc(x) -> ( match e with (* any aexp that return a location *)
									  IdRef(y) -> ( match r(y) with
													  Var(_) -> 1
													| Descr_Pointer(_,z,_) -> (z+1)
													| _ -> raise WARNING_SUPPRESSOR
												)
									| Ident(y) -> ( match r(y) with
													  Descr_Pointer(_,z,_) -> z
													| _ -> raise WARNING_SUPPRESSOR
												)
									| _ -> raise WARNING_SUPPRESSOR (* already catched *)
								)
							
				| _ -> 0 (* If not location is a Basic Type so depth is 0 *)
		)


(* PTYPE UTILITY *)

(* get pointer depth from its ptype *)
let rec get_ptype_dep (p:pType): int = match p with
	  Ptr(_) -> 1 (* ^btype *)
	| PPtr(e) -> 1 + (get_ptype_dep e) (* ^..(^btype) *)
	
(* get pointer btype from its ptype *)
let rec get_ptype_btype (p:pType): bType = match p with
	  Ptr(b) -> b
	| PPtr(e) -> (get_ptype_btype e)

(* DECLARATIONS *)

(* evaluation of declarations *)
let rec eval_decs (d:dec list) (r:env) (s:store) = match d with
	  []						->  (r,s)
	| Dec(x,Basic(bType))::decls ->  let newaddr = newmem s in
					 let r' =  (updateenv(r,x,Var(Loc(newaddr)))) 	
									in (
										 match bType with
											  Int   -> eval_decs decls r' (updatemem(s,Loc(newaddr),ValueInt(0)))
											| Float -> eval_decs decls r' (updatemem(s,Loc(newaddr),ValueFloat(0.0)))
										)
	| Dec(x,Const(bType,value_exp))::decls  
								->  let value = eval_aexp value_exp r s (initheap 0) (* at declaration time we cannot have heap *)
									in 
									(
									  match bType with
										   Int  -> 
											(
											 match value with
												  ValueInt(v) -> eval_decs decls (updateenv(r,x,Val(ValueInt(v)))) s
												| ValueFloat(v) -> raise DIFFERENT_TYPE_ASSIGNATION
												| ValueLoc(_) -> raise SYNTAX
											)
										 | Float->
											(
											 match value with
												  ValueFloat(v) -> eval_decs decls (updateenv(r,x,Val(ValueFloat(v)))) s
												| ValueInt(v) -> raise DIFFERENT_TYPE_ASSIGNATION
												| ValueLoc(_) -> raise SYNTAX
											)
									)
								  
	| Dec(x,Vector(bType,lb,ub))::decls
								->  let newaddr = newmem s
									and dim = ub - lb + 1
									in
									let vo = Loc(newaddr - lb) in
					let r' =  (updateenv(r,x,Descr_Vector(vo,lb,ub))) 
									in
									(
									  match bType with
										  Int -> eval_decs decls r' (updatemem_vector(s,Loc(newaddr),dim,ValueInt(0)))
										| Float -> eval_decs decls r' (updatemem_vector(s,Loc(newaddr),dim,ValueFloat(0.0)))
									)
	| Dec(x,Pointer(pType))::decls (* Pointer points to NULL after declaration *)
								->	let newaddr = (newmem s) (* entry in store *)
									in
									let pdepth = (get_ptype_dep pType)
									in
									let pbtype = (get_ptype_btype pType)
									in
									let r' = (updateenv(r,x,Descr_Pointer(Loc(newaddr),pdepth,pbtype)))
									in eval_decs decls r' (updatemem(s,Loc(newaddr),ValueLoc(NULL)))

(* evaluation of declarations of subprograms *)
let rec eval_sub_prog_decs (d: sub_prog list) ((r:env),(s:store)) = match d with
      [] -> (r,s)
    | Proc(id,params,locals,cmds)::decls ->
	let v = (Descr_Procedure(params,locals,cmds)) in
        eval_sub_prog_decs decls ((updateenv(r,id,v)),s)


(* evaluation of actual parameter list *) (* heap used to evaluate parameters *)
let rec eval_actual_params (e:aexp list) (r:env) (s:store) (h:heap) = match e with
      []        ->  [] 
    | esp::vl   ->  (eval_aexp esp r s h)::(eval_actual_params vl r s h)



(* prepare for execution of subprograms *) 

let type_checking (input_values:value list) (parameters:param list) = 

	let rec check_types (actuals:value list) (formals:param list) :bool =
		match (actuals,formals) with
			  [],[] -> true
			| (v)::acts,Par(id,bType)::forms ->
				(
				 match v with
					  ValueInt(x) ->
						if (bType=Int) then
							(check_types acts forms)
						else false
					| ValueFloat(x) ->
						if (bType=Float) then
							(check_types acts forms)
						else false
					| ValueLoc(_) -> false (* parameters do not support location for input *)
				)
			| _ -> raise SYNTAX
	in
		if (List.length(input_values)!= List.length(parameters))
			then false
		else
			(check_types input_values parameters)

let rec assign_values (formals:param list) (actuals:value list) ((r:env), (s: store)) =
    match (formals,actuals) with
          [],[] -> (r,s)
        | Par(id,bType)::forms,v::acts ->
            let (r',s') =
                assign_values forms acts (eval_decs[Dec(id,Basic(bType))] r s)
            in
                (
                 match r'(id) with
                      Var(l) -> (r',updatemem(s',l,v))
                    | _ -> raise SYNTAX
                )
        | _ -> raise SYNTAX

(* Utility for Type checking *)
let rec get_btype (s:store)(e:env)(h:heap)(a:aexp):bType = (
	match a with
		  Ident(i) -> (
				match e(i) with
					  Var(l) -> ( (* in this version of CC var type is defined by its value in store *)
							match s(l) with
								  ValueInt(_) -> Int
								| ValueFloat(_) -> Float
								| _ -> raise WARNING_SUPPRESSOR
							)
					| Val(v) -> (
							match v with
								  ValueInt(_) -> Int
								| ValueFloat(_) -> Float
								| _ -> raise WARNING_SUPPRESSOR
							)
					| Descr_Pointer(_,_,t) -> t
					| _ -> raise WARNING_SUPPRESSOR
				)
		| IdRef(y) -> (get_btype s e h (Ident(y)))
		| IdDeref(y) -> (get_btype s e h (Ident(get_pexp_id y)))
		| N(_) -> Int
		| R(_) -> Float
		| Nil -> raise (DEBUG("get_btype Nil"))
		| _ -> (
			let ret = (eval_aexp a e s h)
			in
			match ret with
				  ValueInt(_) -> Int
				| ValueFloat(_) -> Float
				| _ -> raise WARNING_SUPPRESSOR
			)
	)

(* EXECUTION *)

(* execution of commands *)
let rec exec (c: cmd) (r: env)(s: store)(h:heap) = match c with
	Ass(i,e)		->  let ret = eval_aexp e r s h
						in 
						(
						 match i with
							  LVar(id)  -> (
											match r(id) with
											  Var(l)	-> ( (* fixed type checking (missing) *)
													let idType = (get_btype s r h (Ident(id)))
													in
													match ret with
														  ValueLoc(_) -> raise DIFFERENT_TYPE_ASSIGNATION
														| ValueInt(_) -> if idType = Int then (updatemem(s,l,ret)),h else raise DIFFERENT_TYPE_ASSIGNATION
														| ValueFloat(_) -> if idType = Float then (updatemem(s,l,ret)),h else raise DIFFERENT_TYPE_ASSIGNATION
													)
											| Descr_Pointer(ploc,pdep,ptype) -> ( (* a pointer is a variables that accept only loc *)
													let (depOK,typeOK,toWrite) = (
														match e with
															  Nil -> (true,true,ValueLoc(NULL)) (* NULL has always the right type and depth *)
															| _ -> ((if pdep != (get_aexp_dep e r s h) then false else true),(ptype == (get_btype s r h e)),ret)
														)
													in
													let h' = ( (* used for adding a reference to an HLoc if assigned to a pointer *)
														match ret with
															  ValueLoc(x) -> (
																	match x with
																		  HLoc(y) -> href_up(h,x)
																		| _ -> h
																	)
															| _ -> h
														)
													in
													if depOK then (
														if typeOK then (
															match s(ploc) with (* @p is always a location in store *)
																  ValueLoc(x) -> (
																		match x with
																			  HLoc(y) -> ( (* overwriting an HLoc means removing a ref *)
																					(updatemem(s,ploc,toWrite)),href_down(h',x)
																					)
																			| _ -> (updatemem(s,ploc,toWrite)),h'
																		)
																				
																| _ -> raise WARNING_SUPPRESSOR (* a pointer first store location can't contain a non-loc *)
															)
														else raise (PTR_ASSIGN("Different type (btype)"))
														)
													else raise (PTR_ASSIGN("Different type (depth)"))
													)
											| _		 -> raise SYNTAX
										   )
							| LVec(v,idx) -> (
											  match r(v) with
												  Descr_Vector(Loc(vo),lb,ub) ->
														let res = (eval_aexp idx r s h) in (
														match res with 
														| ValueFloat(_) -> raise INDEX_IS_FLOAT
														| ValueInt(pos) ->												
																	if (pos >= lb && pos <= ub) then
																		(updatemem(s,Loc(vo+pos),ret)),h
																	else
																		(
																		 raise INDEX_OUT_OF_BOUNDS
																		)
														| ValueLoc(_) -> raise SYNTAX
														)
												| _ -> raise SYNTAX
											 )
							| LPointer(exp) -> ( 
										let pexpId = (get_pexp_id exp)
										and pexpDep = (get_pexp_dep exp r)
										in (
											match r(pexpId) with
												 Descr_Pointer(ploc,pdep,ptype) -> (
													let depOK = (
														match e with 
															  Nil -> true
															| _ -> if pexpDep != (get_aexp_dep e r s h) then false else true
														)
													and destValue = (eval_pexp exp r s h) (* check if pointed destination is reachable too *)
													and locToDest = (get_pvalue_at_depth pexpId r s h (pexpDep+1)) (* LPointer has minimun 1 ^ *)
													in 
													let typeOK = ( (* type checking *)
														match destValue with
															  ValueInt(_) -> (
																	match ret with
																		  ValueInt(_) -> true
																		| _ -> false
																	)
															| ValueFloat(_) -> (
																	match ret with
																		  ValueFloat(_) -> true
																		| _ -> false
																	)
															| ValueLoc(y) -> (
																	match ret with
																		  ValueLoc(z) -> ( (* a location came only from something with btype (or Nil)*)
																				match e with
																					  Nil -> true
																					| _ -> ((get_btype s r h (Ident(pexpId))) == (get_btype s r h e))
																				)
																		| _ -> false
																	)
														)
													in (
														if not depOK then raise (PTR_ASSIGN("Different type (depth)"));
														if not typeOK then raise (PTR_ASSIGN("Different type"));
														let h' = ( (* overwriting an HLoc means removing a ref *)
															match destValue with
																  ValueLoc(HLoc(y)) -> href_down(h,HLoc(y))
																| _ -> h
															)
														in
														let h'' = ( (* used for adding a reference to an HLoc if assigned to a pointer *)
														match ret with
															  ValueLoc(x) -> (
																	match x with
																		  HLoc(y) -> href_up(h',x)
																		| _ -> h'
																	)
															| _ -> h'
														)
														in (
															match locToDest with (* If I'm in store or heap *)
																  ValueLoc(HLoc(x)) -> s,(hwrite(h'',HLoc(x),ret))																			
																| ValueLoc(Loc(x)) -> (updatemem(s,Loc(x),ret)),h''
																| _ -> raise WARNING_SUPPRESSOR (* can't happend *)
															)
														)
													)																
												 | _ -> raise SYNTAX (* ^ide with ide not pointer *)
												)
											) (* end LPointer *)							
						)
	| Blk([])	   ->  s,h
	| Blk(x::y)	 ->  let es,eh = (exec x r s h) in  (exec (Blk(y)) r es eh)
	| Ite(b,c1,c2)  ->  if (eval_bexp b r s h) then (exec c1 r s h)
						else (exec c2 r s h)
	| While(b,c)	->  if (not(eval_bexp b r s h)) then s,h
						else
							let s'',h'' = exec c r s h
							in (exec (While(b,c)) r s'' h'')
	| Repeat(c, b)  -> let s'',h'' = exec c r s h in
			if (eval_bexp b r s h) then s'',h''
			else (exec (Repeat(c,b)) r s'' h'') 
	| For(i,valmin_exp,valmax_exp,c) (* heap can be modified only with cmd c *)
					->  let valmin = eval_aexp valmin_exp r s h
						and update_counter l s =
							match s(l) with
							  ValueInt(n) -> updatemem(s, l, ValueInt(n + 1))
							| ValueFloat(f) -> updatemem(s, l, ValueFloat(f +. 1.0))
							| ValueLoc(_) -> raise SYNTAX
						in 
						(
						 match r(i) with
							  Var(l) -> 
								(
								let s0 = updatemem(s, l, valmin)
								in
									let rec exec_for s h =
										let s',h' = exec c r s h (* here *)
										in
											let ret = eval_bexp (LT(Ident(i), valmax_exp)) r s' h'
											in
												if (ret) then exec_for (update_counter l s') h'
												else s',h'
									in exec_for s0 h
								)
							| _ -> raise SYNTAX
						)
	| Write(e)	  ->  let ret = (eval_aexp e r s h)
						in
						(
						 match ret with
							  ValueInt(op1) -> print_int(op1); print_string "\n";s,h
							| ValueFloat(op1) -> print_float(op1); print_string "\n";s,h
							| ValueLoc(l) -> (
										match l with
											  NULL -> print_string "nil\n";s,h
											| Loc(x) -> print_int(x); print_string "\n";s,h
											| HLoc(x) -> print_int(x); print_string "\n";s,h
										)
						)
	| PCall(id,input_exprs)
					->  let input_values = (eval_actual_params input_exprs r s h)
						in
						(
						 match (r(id)) with
							  Descr_Procedure(params,locals,cmds) ->
								if ((type_checking input_values params)) then
									exec_proc (r(id)) input_values r s h
								else
									raise PARAMETERS_DO_NOT_MATCH
							| _ -> raise SYNTAX
						)
	| Free(i) -> ( (* free a pointer can be done only if it points to heap *)
			match r(i) with
				  Descr_Pointer(ploc,pdep,ptype) -> (
						match s(ploc) with (* free means removing a reference *)
							  ValueLoc(HLoc(x)) -> (updatemem(s,ploc,ValueLoc(NULL))),(href_down(h,HLoc(x)))
							| _ -> raise STATIC_DEALLOC
						)
				| _ -> raise SYNTAX
			)
	| Alloc(i) -> (
			match r(i) with
				  Descr_Pointer(ploc,pdep,ptype) -> (
						let rec createMem (h:heap)(dep:int):(heap*value) = (
							match dep with
								  0 -> (
										match ptype with
											  Int -> h,ValueInt(0)
											| Float -> h,ValueFloat(0.0)
									)
								| n -> (
										let h',l' = new_heapmem(h) (* creates new memory *)
										in
										let h' = href_up(h',l') (* adding 1 ref to new location *)
										in 
										let h'',v = (createMem h' (n-1)) (* create another new memory that will be assigned to current *)
										in (hwrite(h'',l',v)),ValueLoc(l')
									)
							)
						in 
						let h' = ( (* overwriting an HLoc means removing a referencce *)
							match s(ploc) with
								  ValueLoc(HLoc(x)) -> href_down(h,HLoc(x))
								| _ -> h
							)
						in
						let h'',v = (createMem h' pdep)
						in ((updatemem(s,ploc,v)),h'')
					)
				| _ -> raise SYNTAX
			)

(* execution of subprograms *)
and exec_proc (ee:env_entry) (input_values:value list) (r: env) (s: store) (h:heap) :store*heap =

	let do_exec (formal_params: param list ) (local_decs: dec list) (com: cmd) (values:value list) (r: env) (s: store) (h:heap): store*heap =
		let (r',s') = assign_values formal_params values (r,s)
		in
			let (r'',s'') = eval_decs local_decs r' s'
			in
				exec com r'' s'' h
	in
		match ee with
			  Descr_Procedure(params,locals,com) ->
				do_exec params locals com input_values r s h
			| _ -> raise SYNTAX

(* evaluation of programs *)
let run prog = 
	match prog with
		Program(vars,sub_progs,com) ->   let (r,s) = (eval_decs vars initenv initmem)
								in 
								let (r',s') = (eval_sub_prog_decs sub_progs (r,s))
								in (exec com r' s' (initheap 256 ))
	  | Null -> initmem,(initheap 0)
