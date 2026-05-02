structure Unif :> Unif = struct
structure Env :>
            sig
              type t;
              val undefined : unit -> t;
              val apply : t -> Term.t -> Term.t;
              val defined : t -> Term.t -> bool;
              val insert : t -> Term.t -> Term.t -> t;
            end =
struct
type t = (Term.t * Term.t) list;

fun undefined () = [];

fun apply [] _ = raise Fail "apply"
  | apply ((y,tm)::ys) x = if Term.eq x y
                           then tm
                           else apply ys x;

fun defined [] _ = false
  | defined ((y,_)::env) x = (Term.eq x y) orelse
                             defined env x;
local
(* REQUIRES: `x` is not defined in the `env` *)
fun is_cyclic env x tm =
 (case tm of
   (y as (Term.Var _)) => Term.eq x y orelse (* trivial case *)
                          Term.have_same_sort x y andalso
                          defined env y andalso
                          is_cyclic env x (apply env y)
 | (Term.Fun(f,s,args)) => List.exists (is_cyclic env x) args andalso
                           raise Fail "cyclic");
in
fun insert env (x as (Term.Var _)) y = 
      if is_cyclic env x y then env 
      else (x,y)::env
  | insert _ _ _ = raise Fail "Env.insert: trying to insert function as key"
end;
end;



(* Unif.y : Env.t -> (Term.t * Term.t) list -> Env.t

REQUIRES: `env` is cycle-free
REQUIRES: the set `env @ eqns` has exactly the same set of
          unifiers as the original problem. *)
fun y env ([] : (Term.t * Term.t) list) = env
  | y env ((Term.Fun(f,s1,args1),Term.Fun(g,s2,args2))::eqns) = 
      if f = g andalso s1 = s2 andalso length args1 = length args2
      then y env ((ListPair.zip(args1, args2)) @ eqns)
      else raise Fail "impossible unification"
  | y env (((x as (Term.Var _)), t)::eqns) =
      if not(Term.have_same_sort x t)
      then raise Fail "impossible unification: variable has different sort than term"
      else if Env.defined env x (* x already in env *)
      then y env ((Env.apply env x, t)::eqns)
      else y (Env.insert env x t) eqns
  | y env ((t, x as (Term.Var _))::eqns) = y env ((x,t)::eqns);

(* Unif.y_literals : Env.t -> Term.t * Term.t -> Env.t *)
fun y_literals env (lhs,rhs) =
  if Formula.is_not lhs andalso Formula.is_not rhs
  then y_literals env (Formula.dest_not lhs, Formula.dest_not rhs)
  else if Formula.is_falsum lhs andalso Formula.is_falsum rhs
  then env
  else if Formula.is_pred lhs andalso Formula.is_pred rhs
  then let val (p1,args1) = Formula.dest_pred lhs;
           val (p2,args2) = Formula.dest_pred rhs;
       in if p1 = p2 andalso length args1 = length args2
          then y env (ListPair.zip(args1, args2))
          else raise Fail "Unif.y_literals: impossible unification"
       end
  else raise Fail "Unif.y_literals: Cannot unify literals";

fun negate A = if Formula.is_not A
               then Formula.dest_not A
               else Formula.mk_not A;

fun y_complements env (A,B) =
  y_literals env (A, negate B);
end;
