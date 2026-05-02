structure FS0 : FS0 = struct
exception Dest of string;

val zero = Term.Fun("0", Sort.IND, []);

(* pair : Term.t -> Term.t -> Term.t *)
fun pair t1 t2 =
  if not(Term.is_ind t1)
  then raise Sort.Mismatch "FS0.pair: first term expected to be an individual"
  else if not(Term.is_ind t2)
  then raise Sort.Mismatch "FS0.pair: first term expected to be an individual"
  else Term.Fun("cons", Sort.IND, [t1, t2]);

fun dest_pair (Term.Fun("cons", Sort.IND, [t1, t2])) = (t1, t2)
  | dest_pair _ = raise Dest "FS0.dest_pair";

(* FS0.app : Term.t -> Term.t -> Term.t *)
fun app f tm =
  if not(Term.is_fun f)
  then raise Sort.Mismatch "FS0.apply: first argument is not a function"
  else if not(Term.is_ind tm)
  then raise Sort.Mismatch "FS0.apply: second argument is not an individual"
  else Term.Fun("apply", Sort.IND, [f, tm]);

fun dest_app (Term.Fun("apply", Sort.IND, [f, tm])) = (f, tm)
  | dest_app tm = raise Dest "FS0.dest_app";

(* id : Term.t -> Term.t

Just returns the argument (i.e., 'eagerly applies' the
identity function and returns the result). *)
fun id tm = tm;

val id_const = (Term.Fun("id", Sort.FUN, []));

(* mk_id tm : Term.t -> Term.t

Applies the `id_const` to the argument, and returns the
result. *)
fun mk_id tm = app id_const tm;

val if_eq_const = (Term.Fun("if-equal", Sort.FUN, [])); 

(* mk_if_eq : Term.t -> Term.t *)
fun mk_if_eq tm = app if_eq_const tm;

(* if_eq : Term.t -> Term.t *)
local
  fun dest_cons (tm : Term.t) =
   (case tm of
     (Term.Fun("cons", Sort.IND, [t1,t2])) => (t1,t2)
   | _ => raise Match);
in
fun if_eq tm =
  if not(Term.is_ind tm)
  then raise Sort.Mismatch "FS0.if_eq: expects IND"
  else
    let
      val (t1, t234) = dest_cons tm;
      val (t2, t34) = dest_cons t234;
      val (t3, t4) = dest_cons t34;
    in
      if Term.eq t1 t2 then t3
      else mk_if_eq tm
    end
    handle Match => mk_if_eq tm;
end;

(* proj1_const : Term.t *)
val proj1_const = Term.Fun("P1", Sort.FUN, []);

(* mk_proj1 : Term.t -> Term.t

Lazily apply proj1 to a term. *)
fun mk_proj1 tm = app proj1_const tm;

(* proj1 : Term.t -> Term.t

Automatically extracts the first component of a pair,
otherwise just applies the "P1" constant. *)
fun proj1 tm =
 (case tm of
   (Term.Fun("cons", Sort.IND, [tm', _])) => tm'
   | _ => mk_proj1 tm);

(* proj2_const : Term.t *)
val proj2_const = Term.Fun("P2", Sort.FUN, []);

(* mk_proj2 : Term.t -> Term.t

Lazily apply proj2 to a term. *)
fun mk_proj2 tm = app proj2_const tm;

(* proj2 : Term.t -> Term.t

Automatically extracts the second component of a pair,
otherwise just applies the "P2" constant. *)
fun proj2 tm =
 (case tm of
   (Term.Fun("cons", Sort.IND, [_, tm'])) => tm'
   | _ => mk_proj2 tm);

(* const : Term.t -> Term.t *)
fun const tm =
  if not(Term.is_ind tm)
  then raise Sort.Mismatch "FS0.const: expects an individual"
  else Term.Fun("const", Sort.FUN, [tm]);

fun dest_const (Term.Fun("const", Sort.FUN, [tm])) = tm
  | dest_const _ = raise Dest "FS0.dest_const";

(* comp : Term.t -> Term.t -> Term.t

Compose two functions *)
fun comp f g =
  if not(Term.is_fun f)
  then raise Sort.Mismatch "FS0.comp: first argument is not a fun"
  else if not(Term.is_fun g)
  then raise Sort.Mismatch "FS0.comp: second argument is not a fun"
  else Term.Fun("comp", Sort.FUN, [f, g]);

fun dest_comp (Term.Fun("comp", Sort.FUN, [f, g])) = (f,g)
  | dest_comp _ = raise Dest "FS0.dest_comp";

(* juxt : Term.t -> Term.t -> Term.t

Given two functions, applies them componentwise to a `cons`
pair. *)
fun juxt f g =
  if not(Term.is_fun f)
  then raise Sort.Mismatch "FS0.juxt: first argument is not a fun"
  else if not(Term.is_fun g)
  then raise Sort.Mismatch "FS0.juxt: second argument is not a fun"
  else Term.Fun("juxt", Sort.FUN, [f, g]);

fun dest_juxt (Term.Fun("juxt", Sort.FUN, [f, g])) = (f,g)
  | dest_juxt _ = raise Dest "dest_juxt";

(* recur : Term.t -> Term.t -> Term.t

Constructs the recursor given two functions. *)
fun recur f g =
  if not(Term.is_fun f)
  then raise Sort.Mismatch "FS0.recur: first argument is not a fun"
  else if not(Term.is_fun g)
  then raise Sort.Mismatch "FS0.recur: second argument is not a fun"
  else Term.Fun("recur", Sort.FUN, [f, g]);

fun dest_recur (Term.Fun("recur", Sort.FUN, [f, g])) = (f,g)
  | dest_recur _ = raise Dest "FS0.dest_recur";

(* singleton : Term.t -> Term.t *)
fun singleton x =
  if not(Term.is_ind x)
  then raise Sort.Mismatch "FS0.singleton: expects an individual"
  else Term.Fun("singleton", Sort.CLASS, [x]);

fun dest_singleton (Term.Fun("singleton", Sort.CLASS, [x])) = x
  | dest_singleton _ = raise Dest "FS0.dest_singleton";

(* preimage : Term.t -> Term.t -> Term.t *)
fun preimage f S =
  if not(Term.is_fun f)
  then raise Sort.Mismatch "FS0.preimage: first argument is not a fun"
  else if not(Term.is_class S)
  then raise Sort.Mismatch "FS0.preimage: second argument is not a class"
  else Term.Fun("preimage", Sort.CLASS, [f, S]);

fun dest_preimage (Term.Fun("preimage", Sort.CLASS, [f, S])) = (f,S)
  | dest_preimage _ = raise Dest "FS0.dest_preimage";

(* union : Term.t -> Term.t -> Term.t *)
fun union S T =
  if not(Term.is_class S)
  then raise Sort.Mismatch "FS0.union: first argument is not a class"
  else if not(Term.is_class T)
  then raise Sort.Mismatch "FS0.union: second argument is not a class"
  else Term.Fun("union", Sort.CLASS, [S, T]);

fun dest_union (Term.Fun("union", Sort.CLASS, [S, T])) = (S,T)
  | dest_union _ = raise Dest "FS0.dest_union";

(* intersection : Term.t -> Term.t -> Term.t *)
fun intersection S T =
  if not(Term.is_class S)
  then raise Sort.Mismatch "FS0.intersection: first argument is not a class"
  else if not(Term.is_class T)
  then raise Sort.Mismatch "FS0.intersection: second argument is not a class"
  else Term.Fun("intersection", Sort.CLASS, [S, T]);

fun dest_intersection (Term.Fun("intersection", Sort.CLASS, [S, T])) = (S,T)
  | dest_intersection _ = raise Dest "FS0.dest_intersection";

(* induct : Term.t -> Term.t -> Term.t *)
fun induct S T =
  if not(Term.is_class S)
  then raise Sort.Mismatch "FS0.induction: first argument is not a class"
  else if not(Term.is_class T)
  then raise Sort.Mismatch "FS0.induction: second argument is not a class"
  else Term.Fun("induction", Sort.CLASS, [S, T]);

fun dest_induct (Term.Fun("induction", Sort.CLASS, [S, T])) = (S,T)
  | dest_induct _ = raise Dest "FS0.dest_induct";

(* In : Term.t -> Term.t -> Formula.t *)
fun In x C =
  if not(Term.is_ind x)
  then raise Sort.Mismatch "FS0.In: first argument is not an ind"
  else if not(Term.is_class C)
  then raise Sort.Mismatch "FS0.In: second argument is not a class"
  else Formula.mk_pred("in", [x, C]);

fun dest_in fm =
  if not(Formula.is_pred fm)
  then raise Dest "FS0.dest_in"
  else (case Formula.dest_pred fm of
         ("in", [x, C]) => (x, C)
       | _ => raise Dest "FS0.dest_in");

(* equal : Term.t -> Term.t -> Formula.t

TODO: consider 'expanding' this out for functions
 (f = g iff forall x. f x = g x) and for classes
 (S = T iff forall x.(x in S iff x in T)). *)
fun equal lhs rhs =
  if not(Term.have_same_sort lhs rhs)
  then raise Sort.Mismatch "FS0.equal: expects arguments to have same sort"
  else (Formula.mk_pred("=", [lhs, rhs]));

fun dest_equal fm =
  if not(Formula.is_pred fm)
  then raise Dest "FS0.dest_equal"
  else (case Formula.dest_pred fm of
         ("equal", [lhs, rhs]) => (lhs, rhs)
       | _ => raise Dest "FS0.dest_equal");

(* not_equal : Term.t -> Term.t -> Formula.t *)
fun not_equal lhs rhs =
  Formula.mk_not(equal lhs rhs);
end;
