(*
 * SNU 4541.664A Program Analysis 2017 Spring
 * K- Interpreter Solution
 * DongKwon Lee (dklee@ropas.snu.ac.kr)
 *)


(*
 * K- Interpreter
 *)

module type KMINUS =
sig
  exception Error of string
  type id = string
  type exp =
      | NUM of int
      | VAR of id
	  | DEREF of id
	  | AT of id
      | ADD of exp * exp
	  | MINUS of exp
	  | TRUE
	  | FALSE
	  | NOT of exp
	  | ANDALSO of exp * exp
	  | ORELSE of exp * exp
	  | LESS of exp * exp
  
  type cmd =
      | SKIP
      | SEQ of cmd * cmd        (* sequence *)
      | IF of exp * cmd * cmd   (* if-then-else *)
	  | WHILE of exp * cmd      (* while *)
      | ASSIGN of id * exp      (* assgin to variable *)
	  | PTRASSIGN of id * exp   (* assign using ptr *)

  type program = cmd
  type memory
  type value

  val botMemory : memory
  val eval : memory * exp -> value  (* exp eval *)
  val assume : memory * exp -> memory (* memory filtering *)
  val assumeNot : memory * exp -> memory (* memory filtering *)
  val analyzer : memory * program -> memory
  val used_varlist : program -> id list
  val pp_memory : memory -> id list -> unit
end

module K : KMINUS =
struct
  exception Error of string
  type id = string
  type exp =
      | NUM of int
      | VAR of id
	  | DEREF of id
	  | AT of id
      | ADD of exp * exp
	  | MINUS of exp
	  | TRUE
	  | FALSE
	  | NOT of exp
	  | ANDALSO of exp * exp
	  | ORELSE of exp * exp
	  | LESS of exp * exp
  
  type cmd =
      | SKIP
      | SEQ of cmd * cmd        (* sequence *)
      | IF of exp * cmd * cmd   (* if-then-else *)
	  | WHILE of exp * cmd      (* while *)
      | ASSIGN of id * exp      (* assgin to variable *)
	  | PTRASSIGN of id * exp   (* assign using ptr *)


  type program = cmd
  
  (* abstract domain type : "do not" change here *)
  type z_hat = BOT_Z | CONST of int | TOP_Z
  type bool_hat = TOP_BOOL | T | F | BOT_BOOL
  type loc_hat = LSET of string list

 
  (* abstract memory, value type : "do not" change here *)
  type value = z_hat * bool_hat * loc_hat
  type memory = id -> value
 
  (* bottom values *)
  let botValue = (BOT_Z, BOT_BOOL, LSET [])
  let botMemory = fun x -> botValue
  
  (* memory operation *)
  let store mem id v = fun x -> if (x = id) then v else mem(x)
  
  let rec compare_mem m1 m2 varlist =
    match varlist with
	| [] -> true
	| hd::tl -> (m1(hd) = m2(hd)) && (compare_mem m1 m2 tl)
 
  (* memory pretty print : "do not" change here *)
  let rec pp_zhat : z_hat -> unit = fun z ->	
	match z with
	| TOP_Z -> print_string("TOP")
	| BOT_Z -> print_string("BOTTOM")
    | CONST i -> let _ = print_string("CONST") in print_int(i)

 let rec pp_lochat : loc_hat -> unit = fun loc ->
    match loc with
	| LSET [] -> ()
	| LSET (hd::tl) -> let _ = print_string(hd ^ ", ") in (pp_lochat (LSET tl))


  let pp_bool : bool_hat -> unit = fun b ->
    match b with
	| BOT_BOOL -> print_string("bottom") 
	| T -> print_string("T")
	| F -> print_string("F")
	| TOP_BOOL -> print_string("T, F")

  let rec pp_memory : memory -> id list -> unit = fun mem -> (fun varlist ->
    match varlist with
	| [] -> ()
	| hd::tl ->
	  let (zhat, b, lochat) = mem(hd) in
	  let _ = print_string(hd ^ " -> Z : ") in
	  let _ = pp_zhat(zhat) in
	  let _ = print_string(" bool : ") in
	  let _ = pp_bool(b) in
	  let _ = print_string(" loc : [ ") in
	  let _ = pp_lochat(lochat) in
	  let _ = print_string("]") in
	  let _ = print_newline() in
	  pp_memory mem tl
	  )
	 
  (* var list gathering : "do not" change here *)
  let rec list_trim l =
    match l with
	| [] -> []
	| hd::tl -> if (List.mem hd tl) then list_trim tl else hd::(list_trim tl)

  let rec used_vars_exp exp =
      (match exp with
      | NUM i -> []
      | VAR id | DEREF id | AT id -> id::[]
      | ADD (e1, e2) -> (used_vars_exp e1) @ (used_vars_exp e2)
	  | MINUS e -> used_vars_exp e
	  | TRUE -> []
	  | FALSE -> []
	  | NOT e -> used_vars_exp e
	  | ANDALSO (e1, e2) -> (used_vars_exp e1) @ (used_vars_exp e2)
	  | ORELSE (e1, e2) -> (used_vars_exp e1) @ (used_vars_exp e2)
	  | LESS (e1, e2) -> (used_vars_exp e1) @ (used_vars_exp e2)
	  )
  
  let rec used_vars cmd =
	match cmd with
	| SKIP -> []
	| SEQ (cmd1, cmd2) -> (used_vars cmd1) @ (used_vars cmd2)
	| IF (e, cmd1, cmd2) -> (used_vars_exp e) @ (used_vars cmd1) @ (used_vars cmd2)
	| WHILE (e, cmd) -> (used_vars_exp e) @ (used_vars cmd)
	| ASSIGN (id, e) -> id::(used_vars_exp e)
	| PTRASSIGN (id, e) -> id::(used_vars_exp e)

  let used_varlist cmd = list_trim (used_vars cmd)
 
  (* join operaters : you may need these operaters *)
  let join_const z1 z2 =
      match (z1, z2) with
      | (BOT_Z, z) -> z
      | (z, BOT_Z) -> z
      | _ -> TOP_Z
  let join_bool b1 b2 =
      match (b1, b2) with
      | (BOT_BOOL, b) -> b
      | (b, BOT_BOOL) -> b
      | _ -> TOP_BOOL
  let join_loc l1 l2 =
      match (l1, l2) with
      | (LSET a, LSET b) -> LSET (a @ b)
  let join_value v1 v2 =
      let ((z1, b1, l1), (z2, b2, l2)) = (v1, v2) in
      (join_const z1 z2, join_bool b1 b2, join_loc l1 l2)
  let rec join_memory m1 m2 varlist =
      match varlist with
      | [] -> botMemory
      | hd::tl -> store (join_memory m1 m2 tl) hd (join_value (m1 hd) (m2 hd))
  
  (* widening operaters : you may need these operaters *)
  let smaller_const z1 z2 =
      match (z1, z2) with
      | (BOT_Z, _) -> true
      | (_, TOP_Z) -> true
      | (z1, z2) -> (z1 = z2)
      | _ -> false
  let smaller_bool b1 b2 =
      match (b1, b2) with
      | (BOT_BOOL, _) -> true
      | (_, TOP_BOOL) -> true
      | (b1, b2) -> (b1 = b2)
      | _ -> false
  let smaller_value v1 v2 =
      match (v1, v2) with
      | ((z1, b1, l1), (z2, b2, l2)) -> (smaller_const z1 z2) && (smaller_bool b1 b2)
  let rec smaller_memory m1 m2 varlist =
      match varlist with
      | [] -> true
      | hd::tl -> (smaller_value (m1 hd) (m2 hd)) && (smaller_memory m1 m2 tl)
  let fix ftn varlist =  
      let x = ref botMemory in
      while not (smaller_memory (ftn !x) !x varlist) do
          x := ftn !x
      done;
      !x
  
  (* narrowing operaters : you may need these operaters *)
 
  (* exp evaluation : TODO you have to implement this *)
  let rec eval : (memory * exp) -> value  = fun (mem, e) ->
    match e with
	| NUM n -> (CONST n, BOT_BOOL, LSET [])
    | TRUE -> (BOT_Z, T, LSET [])
    | FALSE -> (BOT_Z, F, LSET [])
	| VAR x -> mem(x)
	| DEREF x -> let (_, _, LSET ls) = (mem x) in List.fold_left (fun x y -> join_value x (mem y)) botValue ls
    | AT x -> (BOT_Z, BOT_BOOL, LSET [x])
	| ADD (e1, e2) -> (match (eval (mem, e1), eval (mem, e2)) with
                       | ((BOT_Z, _, _), _) -> botValue
                       | (_, (BOT_Z, _, _)) -> botValue
                       | ((TOP_Z, _, _), (_, _, _)) -> (TOP_Z, BOT_BOOL, LSET [])
                       | ((_, _, _), (TOP_Z, _, _)) -> (TOP_Z, BOT_BOOL, LSET [])
                       | ((CONST z1, _, _), (CONST z2, _, _)) -> (CONST (z1+z2), BOT_BOOL, LSET [])
                       | _ -> (TOP_Z, BOT_BOOL, LSET [])
                      )
    | MINUS e -> (match (eval (mem, e)) with
                  | (BOT_Z, _, _) -> botValue
                  | (TOP_Z, _, _) -> (TOP_Z, BOT_BOOL, LSET [])
                  | (CONST z, _, _) -> (CONST (-z), BOT_BOOL, LSET [])
                  | _  -> (TOP_Z, BOT_BOOL, LSET [])
                 )
    | NOT e -> (match (eval (mem, e)) with
                | (_, BOT_BOOL, _) -> botValue
                | (_, T, _) -> (BOT_Z, F, LSET [])
                | (_, F, _) -> (BOT_Z, T, LSET [])
                | (_, TOP_BOOL, _) -> (BOT_Z, TOP_BOOL, LSET [])
                | _  -> (BOT_Z, TOP_BOOL, LSET [])
               )
    | ANDALSO (e1, e2) -> (match (eval (mem, e1), eval (mem, e2)) with
                           | ((_,BOT_BOOL,_), (_,_,_)) -> botValue
                           | ((_,_,_), (_,BOT_BOOL,_)) -> botValue
                           | ((_,F,_), (_,_,_)) -> (BOT_Z, F, LSET []) 
                           | ((_,_,_), (_,F,_)) -> (BOT_Z, F, LSET []) 
                           | ((_,T,_), (_,T,_)) -> (BOT_Z, T, LSET []) 
                           | ((_,TOP_BOOL,_), (_,_,_)) -> (BOT_Z, TOP_BOOL, LSET []) 
                           | ((_,_,_), (_,TOP_BOOL,_)) -> (BOT_Z, TOP_BOOL, LSET []) 
                           | _ -> (BOT_Z, TOP_BOOL, LSET []) 
                          )
    | ORELSE (e1, e2) -> (match (eval (mem, e1), eval (mem, e2)) with
                          | ((_,BOT_BOOL,_), (_,_,_)) -> botValue
                          | ((_,_,_), (_,BOT_BOOL,_)) -> botValue
                          | ((_,T,_), (_,_,_)) -> (BOT_Z, T, LSET []) 
                          | ((_,_,_), (_,T,_)) -> (BOT_Z, T, LSET []) 
                          | ((_,F,_), (_,F,_)) -> (BOT_Z, F, LSET []) 
                          | ((_,TOP_BOOL,_), (_,_,_)) -> (BOT_Z, TOP_BOOL, LSET []) 
                          | ((_,_,_), (_,TOP_BOOL,_)) -> (BOT_Z, TOP_BOOL, LSET []) 
                          | _ -> (BOT_Z, TOP_BOOL, LSET []) 
                         )
	| LESS (e1, e2) -> (match (eval (mem, e1), eval (mem, e2)) with
                        | ((BOT_Z, _, _), _) -> botValue
                        | (_, (BOT_Z, _, _)) -> botValue
                        | ((TOP_Z, _, _), (_, _, _)) -> (BOT_Z, TOP_BOOL, LSET [])
                        | ((_, _, _), (TOP_Z, _, _)) -> (BOT_Z, TOP_BOOL, LSET [])
                        | ((CONST z1, _, _), (CONST z2, _, _)) -> if z1 < z2 then (BOT_Z, T, LSET []) else (BOT_Z, F, LSET [])
                        | _ -> (BOT_Z, TOP_BOOL, LSET []) 
                       )
    | _ -> (TOP_Z, TOP_BOOL, LSET [])
   
  (* memory filtering by boolean expression *)
  let rec assume : (memory * exp) -> memory = fun (mem, e) ->
    match e with
    | TRUE -> mem
    | FALSE -> botMemory 
	| VAR id -> (match mem id with
                 | (_, TOP_BOOL, _) -> mem
                 | (_, T, _) -> mem
                 | (_, _, _) -> botMemory
                )
    | DEREF id -> let (_,_,LSET ls) = (mem id) in
                  let v = List.fold_left (fun v y -> join_value v (mem y)) botValue ls in
                  (match v with
                   | (_,TOP_BOOL,_) -> mem
                   | (_,T,_) -> mem
                   | (_,_,_) -> botMemory
                  )
    | ANDALSO (e1, e2) -> assume(assume(mem, e1), e2) 
    | ORELSE (e1, e2) -> join_memory (assume(mem, e1)) (assume(assumeNot(mem, e1), e2)) (used_vars_exp e) 
    | NOT e -> assumeNot(mem, e)
    | LESS (VAR x, NUM n) -> (match eval(mem, VAR x) with
                              | (BOT_Z,_,_) -> botMemory
                              | (CONST m,_,_) -> if m < n then mem else botMemory
                              | (TOP_Z,_,_) -> mem
                             )
    | LESS (NUM n, VAR x) -> (match eval(mem, VAR x) with
                              | (BOT_Z,_,_) -> botMemory
                              | (CONST m,_,_) -> if n < m then mem else botMemory
                              | (TOP_Z,_,_) -> mem
                             )
    | LESS (_,_) -> (fun x -> (TOP_Z, TOP_BOOL, LSET []))
	| _ -> botMemory

  and assumeNot : (memory * exp) -> memory = fun (mem, e) ->
    match e with
    | TRUE -> botMemory
    | FALSE -> mem
	| VAR id -> (match mem id with
                 | (_, TOP_BOOL, _) -> mem
                 | (_, F, _) -> mem
                 | (_, _, _) -> botMemory
                )
    | DEREF id -> let (_,_,LSET ls) = (mem id) in
                  let v = List.fold_left (fun v y -> join_value v (mem y)) botValue ls in
                  (match v with
                   | (_,TOP_BOOL,_) -> mem
                   | (_,F,_) -> mem
                   | (_,_,_) -> botMemory
                  )
    | ANDALSO (e1, e2) -> join_memory (assumeNot(mem, e1)) (assumeNot(assume(mem, e1), e2)) (used_vars_exp e) 
    | ORELSE (e1, e2) -> assumeNot(assumeNot(mem, e1), e2) 
    | NOT e -> assume(mem, e)
    | LESS (VAR x, NUM n) -> (match eval(mem, VAR x) with
                              | (BOT_Z,_,_) -> botMemory
                              | (CONST m,_,_) -> if m >= n then mem else botMemory
                              | (TOP_Z,_,_) -> mem
                             )
    | LESS (NUM n, VAR x) -> (match eval(mem, VAR x) with
                              | (BOT_Z,_,_) -> botMemory
                              | (CONST m,_,_) -> if n >= m then mem else botMemory
                              | (TOP_Z,_,_) -> mem
                             )
    | LESS (_,_) -> (fun x -> (TOP_Z, TOP_BOOL, LSET []))
	| _ -> botMemory

  (* interval analysis for K- *)
  let rec analyzer : (memory * program) -> memory = fun (mem, pgm) ->
    let varlist = used_varlist pgm in
    match pgm with
    | SKIP -> mem 
    | ASSIGN(id, e) -> store mem id (join_value (mem id) (eval (mem, e)))
    | PTRASSIGN(id, e) -> let (_,_,LSET ls) = (mem id) in
                          let v = eval (mem, e) in
                          List.fold_left (fun m y -> store m y (join_value (m y) v)) mem ls
    | SEQ(cmd1, cmd2) -> let mem1 = analyzer (mem, cmd1) in analyzer (mem1, cmd2) 
    | IF(e, cmd1, cmd2) -> join_memory (analyzer(assume(mem, e), cmd1)) (analyzer(assumeNot(mem, e), cmd2)) varlist
    | WHILE(e, cmd) -> let ftn = (fun x -> join_memory mem (analyzer(assume(x, e), cmd)) varlist) in assumeNot((fix ftn varlist), e)
end
