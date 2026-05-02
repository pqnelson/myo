structure Term = struct
datatype t = Var of string * Sort.t
           | Fun of string * Sort.t * t list;

(* sort : Term.t -> Sort.t *)
fun sort (Var (_, s)) = s
  | sort (Fun (_, s, _)) = s;

(* have_same_sort : Term.t -> Term.t -> bool *)
fun have_same_sort (lhs : t) (rhs : t) =
  (sort lhs) = (sort rhs);

(* is_var : Term.t -> bool *)
fun is_var (Var _) = true
  | is_var _ = false;

(* is_ind : Term.t -> bool *)
fun is_ind (tm : t) = (Sort.IND = sort tm);

(* is_fun : Term.t -> bool *)
fun is_fun (tm : t) = (Sort.FUN = sort tm);

(* is_class : Term.t -> bool *)
fun is_class (tm : t) = (Sort.CLASS = sort tm);

(* fv : Term.t -> Term.t list *)
fun fv (x as (Var _)) = [x]
  | fv (Fun (_, _, args)) = List.foldr (fn (arg, fvs) => (fv arg) @ fvs)
                                       []
                                       args;

(* subst : Term.t -> Term.t -> Term.t -> Term.t *)
fun subst (x : t) (replacement : t) (tm : t) =
  if not (have_same_sort x replacement)
  then raise Sort.Mismatch "Term.subst: variable and replacement have different sorts"
  else if x = tm then replacement
  else (case tm of
         (Var _) => if x = tm then replacement else tm
       | (Fun(f,s,args)) => Fun(f,s,map (subst x replacement) args));

(* compare : Term.t * Term.t -> order *)
fun compare(Var(x1,s1), Var(x2,s2)) =
    (case Sort.compare(s1, s2) of
      EQUAL => String.compare(x1, x2)
    | r => r)
  | compare(Var _, _) = LESS
  | compare(Fun _, Var _) = GREATER
  | compare(Fun(f1,s1,args1), Fun(f2,s2,args2)) =
    (case Sort.compare(s1,s2) of
      EQUAL => (case String.compare(f1, f2) of
                 EQUAL => compare_lists args1 args2
               | r => r)
    | r => r)
(* compare_lists : Term.t list -> Term.t list -> order *)
and compare_lists [] [] = EQUAL
  | compare_lists [] ys = LESS
  | compare_lists xs [] = GREATER
  | compare_lists (x::xs) (y::ys) =
     (case compare(x,y) of
       EQUAL => compare_lists xs ys
     | r => r);

(* eq : Term.t -> Term.t -> bool *)
fun eq (Var(x1,s1)) (Var(x2,s2)) = (s1 = s2) andalso (x1 = x2)
  | eq (Fun(f1,s1,args1)) (Fun(f2,s2,args2)) =
      (s1 = s2) andalso (f1 = f2) andalso (eq_lists args1 args2)
  | eq _ _ = false
(* eq_lists : Term.t list -> Term.t list -> bool *)
and eq_lists [] [] = true
  | eq_lists (x::xs) (y::ys) = (eq x y) andalso (eq_lists xs ys)
  | eq_lists _ _ = false;

(* occurs_in : Term.t -> Term.t -> bool *)
fun occurs_in (subtm : t) (tm : t) : bool =
  (eq subtm tm) orelse
  (case tm of
    (Var _) => false
  | (Fun(_,_,args)) => List.exists (occurs_in subtm) args);

local
  fun fresh_var_iter (x : string) (s : Sort.t) (vars : t list) n = 
    let val var = Var(x ^ (Int.toString n), s)
    in if List.exists (eq var) vars
       then fresh_var_iter x s vars (n + 1)
       else var
    end;
in

fun fresh_var (x : string) (s : Sort.t) (vars : t list) = 
  let val var = Var(x, s)
  in if List.exists (eq var) vars
     then fresh_var_iter x s vars 0
     else var
  end;

end;

fun serialize (Var(x,s)) = "Var("^x^", "^(Sort.to_string s)^")"
  | serialize (Fun(f, s, args)) = "Fun("^f^
                                  ", "^
                                  (Sort.to_string s)^
                                  ", ["^
                                  (String.concatWith ", " (map serialize args))^
                                  "])";

end;
