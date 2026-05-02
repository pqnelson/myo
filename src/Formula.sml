structure Formula :> Formula = struct
exception Dest of string;

datatype t = False
           | Pred of string * Term.t list
           | Not of t
           | And of t * t
           | Or of t * t
           | Implies of t * t
           | Iff of t * t
           | Forall of Term.t * t
           | Exists of Term.t * t;

fun is_atom (False) = true
  | is_atom (Pred _) = true
  | is_atom _ = false;

fun mk_falsum () = False;

fun mk_verum () = Not(False);

fun mk_pred args = Pred args;
fun mk_not fm = Not fm;
fun mk_and args = And args;

fun mk_or args = Or args;

fun mk_imp args = Implies args;

fun mk_iff args = Iff args;
fun mk_forall (x, fm) =
  if Term.is_var x then Forall(x, fm)
  else raise Fail "mk_forall: Term must be a variable";

fun mk_exists (x, fm) =
  if Term.is_var x then Exists(x, fm)
  else raise Fail "mk_exists: Term must be a variable";

fun dest_pred (Pred args) = args
  | dest_pred _ = raise Dest "dest_pred";
fun dest_not (Not fm) = fm
  | dest_not _ = raise Dest "dest_not";
fun dest_and (And args) = args
  | dest_and _ = raise Dest "dest_and";

fun dest_or (Or args) = args
  | dest_or _ = raise Dest "dest_or";

fun dest_imp (Implies args) = args
  | dest_imp _ = raise Dest "dest_imp";

fun dest_iff (Iff args) = args
  | dest_iff _ = raise Dest "dest_iff";
fun dest_forall (Forall args) = args
  | dest_forall _ = raise Dest "dest_forall";

fun dest_exists (Exists args) = args
  | dest_exists _ = raise Dest "dest_exists";

fun is_falsum (False) = true
  | is_falsum _ = false;

fun is_verum (Not(False)) = true
  | is_verum _ = false;

fun is_pred (Pred _) = true
  | is_pred _ = false;
fun is_not (Not _) = true
  | is_not _ = false;
fun is_and (And _) = true
  | is_and _ = false;

fun is_or (Or _) = true
  | is_or _ = false;

fun is_imp (Implies _) = true
  | is_imp _ = false;

fun is_iff (Iff _) = true
  | is_iff _ = false;
fun is_forall (Forall _) = true
  | is_forall _ = false;

fun is_exists (Exists _) = true
  | is_exists _ = false;

(* subst : Term.t -> Term.t -> Formula.t -> Formula.t *)
local
fun iter x t fm =
 (case fm of
   (False) => fm
 | (Pred(P,args)) => Pred(P, map (Term.subst x t) args)
 | (Not A) => Not(iter x t A)
 | (And(A,B)) => And(iter x t A, iter x t B)
 | (Or(A,B)) => Or(iter x t A, iter x t B)
 | (Implies(A,B)) => Implies(iter x t A, iter x t B)
 | (Iff(A,B)) => Iff(iter x t A, iter x t B)
 | (Forall(y,A)) => if Term.eq x y then fm
                    else Forall(y, iter x t A)
 | (Exists(y,A)) => if Term.eq x y then fm
                    else Exists(y, iter x t A));
in
fun subst x t fm =
  if not(Term.have_same_sort x t)
  then raise Sort.Mismatch "Formula.subst: variable and replacement have different sorts"
  else iter x t fm
end;

(* foldl : (Formula.t * 'a -> 'a) -> (Term.t * 'a -> 'a) -> 'a * Formula.t -> 'a *)
fun foldl (f : t * 'a -> 'a) (q : Term.t * 'a -> 'a) (init : 'a) (fm : t) : 'a =
  (case fm of
    False => f(fm, init)
  | (Pred _) => f(fm, init)
  | (Not A) => foldl f q init A 
  | (And(A,B)) => foldl f q (foldl f q init A) B
  | (Or(A,B)) => foldl f q (foldl f q init A) B
  | (Implies(A,B)) => foldl f q (foldl f q init A) B
  | (Iff(A,B)) => foldl f q (foldl f q init A) B
  | (Forall(x,A)) => foldl f q (q(x, init)) A
  | (Exists(x,A)) => foldl f q (q(x, init)) A);

(* foldr : (Formula.t * 'a -> 'a) -> (Term.t * 'a -> 'a) -> 'a * Formula.t -> 'a *)
fun foldr f q init fm =
  (case fm of
    False => f(fm, init)
  | (Pred _) => f(fm, init)
  | (Not A) => foldr f q init A 
  | (And(A,B)) => foldr f q (foldr f q init B) A
  | (Or(A,B)) => foldr f q (foldr f q init B) A
  | (Implies(A,B)) => foldr f q (foldr f q init B) A
  | (Iff(A,B)) => foldr f  q(foldr f q init B) A
  | (Forall(x,A)) => foldr f q (q(x, init)) A
  | (Exists(x,A)) => foldr f q (q(x, init)) A);

(* fv : Formula.t -> Term.t list *)
fun fv (False) = []
  | fv (Pred (_, args)) = List.foldl (fn (arg, fvs') => (Term.fv arg) @ fvs')
                                     []
                                     args
  | fv (Not A) = fv A
  | fv (And(A, B)) = (fv A) @ (fv B)
  | fv (Or(A, B)) = (fv A) @ (fv B)
  | fv (Implies(A, B)) = (fv A) @ (fv B)
  | fv (Iff(A, B)) = (fv A) @ (fv B)
  | fv (Forall(x, A)) = List.filter (not o (Term.eq x)) (fv A)
  | fv (Exists(x, A)) = List.filter (not o (Term.eq x)) (fv A);
(* bv : Formula.t -> Term.t list *)
fun bv (False) = []
  | bv (Pred _) = []
  | bv (Not A) = bv A
  | bv (And(A, B)) = (bv A) @ (bv B)
  | bv (Or(A, B)) = (bv A) @ (bv B)
  | bv (Implies(A, B)) = (bv A) @ (bv B)
  | bv (Iff(A, B)) = (bv A) @ (bv B)
  | bv (Forall(x, A)) = x::(bv A)
  | bv (Exists(x, A)) = x::(bv A);

fun contains_var x =
 (fn (False) => false
   | (Pred (_, args)) => List.exists (Term.occurs_in x) args
   | (Not A) => contains_var x A
   | (And(A,B)) => (contains_var x A) orelse (contains_var x B)
   | (Or(A,B)) => (contains_var x A) orelse (contains_var x B)
   | (Implies(A,B)) => (contains_var x A) orelse (contains_var x B)
   | (Iff(A,B)) => (contains_var x A) orelse (contains_var x B)
   | (Forall(y, A)) => (Term.eq x y) orelse (contains_var x A)
   | (Exists(y, A)) => (Term.eq x y) orelse (contains_var x A));

fun precedence (False) (False) = EQUAL
  | precedence (False) _ = GREATER
  | precedence (Pred _) (False) = LESS
  | precedence (Pred _) (Pred _) = EQUAL
  | precedence (Pred _) _ = GREATER
  | precedence (Not _) (False) = LESS
  | precedence (Not _) (Pred _) = LESS
  | precedence (Not _) _ = GREATER
  | precedence (And _) (False) = LESS
  | precedence (And _) (Pred _) = LESS
  | precedence (And _) (Not _) = LESS
  | precedence (And _) (And _) = EQUAL
  | precedence (And _) _ = GREATER
  | precedence (Or _) (False) = LESS
  | precedence (Or _) (Pred _) = LESS
  | precedence (Or _) (Not _) = LESS
  | precedence (Or _) (And _) = LESS
  | precedence (Or _) (Or _) = EQUAL
  | precedence (Or _) _ = GREATER
  | precedence (Implies _) (False) = LESS
  | precedence (Implies _) (Pred _) = LESS
  | precedence (Implies _) (Not _) = LESS
  | precedence (Implies _) (And _) = LESS
  | precedence (Implies _) (Or _) = LESS
  | precedence (Implies _) (Implies _) = EQUAL
  | precedence (Implies _) _ = GREATER
  | precedence (Iff _) (Forall _) = GREATER
  | precedence (Iff _) (Exists _) = GREATER
  | precedence (Iff _) (Iff _) = EQUAL
  | precedence (Iff _) _ = LESS
  | precedence (Forall _) (Exists _) = GREATER
  | precedence (Forall _) (Forall _) = EQUAL
  | precedence (Forall _) _ = LESS
  | precedence (Exists _) (Exists _) = EQUAL
  | precedence (Exists _) _ = LESS

fun compare(lhs, rhs) =
 (case precedence lhs rhs of
   EQUAL => (case (lhs, rhs) of
              (False, False) => EQUAL
            | (Pred(P1,args1),Pred(P2,args2)) =>
              (case String.compare(P1, P2) of
                EQUAL => Term.compare_lists args1 args2
              | r => r)
            | (Not A, Not B) => compare(A, B)
            | (And(A1,B1), And(A2,B2)) => 
                (case compare(A1, A2) of
                  EQUAL => compare(B1,B2)
                | r => r)
            | (Or(A1,B1), Or(A2,B2)) => 
                (case compare(A1, A2) of
                  EQUAL => compare(B1,B2)
                | r => r)
            | (Implies(A1,B1), Implies(A2,B2)) => 
                (case compare(A1, A2) of
                  EQUAL => compare(B1,B2)
                | r => r)
            | (Iff(A1,B1), Iff(A2,B2)) => 
                (case compare(A1, A2) of
                  EQUAL => compare(B1,B2)
                | r => r)
            | (Forall(x, A), Forall(y, B)) =>
                (case Term.compare(x, y) of
                  EQUAL => compare(A, B)
                | r => r)
            | (Exists(x, A), Exists(y, B)) =>
                (case Term.compare(x, y) of
                  EQUAL => compare(A, B)
                | r => r)
            | _ => raise Fail "Formula.compare: I shouldn't be here...")
   | r => r);

fun eq (False) (False) = true
  | eq (Pred(P,args1)) (Pred(Q,args2)) = (P=Q) andalso
                                         (Term.eq_lists args1 args2)
  | eq (Not A) (Not B) = eq A B
  | eq (And(A1,A2)) (And(B1,B2)) = (eq A1 B1) andalso (eq A2 B2)
  | eq (Or(A1,A2)) (Or(B1,B2)) = (eq A1 B1) andalso (eq A2 B2)
  | eq (Implies(A1,A2)) (Implies(B1,B2)) = (eq A1 B1) andalso (eq A2 B2)
  | eq (Iff(A1,A2)) (Iff(B1,B2)) = (eq A1 B1) andalso (eq A2 B2)
  | eq (Forall(x,A)) (Forall(y,B)) = (Term.eq x y) andalso (eq A B)
  | eq (Exists(x,A)) (Exists(y,B)) = (Term.eq x y) andalso (eq A B)
  | eq _ _ = false;

fun member x [] = false
  | member x (y::ys) = (x = y) orelse (member x ys);

fun free_for_iter vars x (fm : t) =
  if is_falsum fm then true
  else if is_pred fm then true
  else if is_not fm
  then let val A = dest_not fm
       in free_for_iter vars x A end
  else if is_and fm
  then let val (A,B) = dest_and fm
       in (free_for_iter vars x A) andalso (free_for_iter vars x B) end
  else if is_or fm
  then let val (A,B) = dest_or fm
       in (free_for_iter vars x A) andalso (free_for_iter vars x B) end
  else if is_imp fm
  then let val (A,B) = dest_imp fm
       in (free_for_iter vars x A) andalso (free_for_iter vars x B) end
  else if is_iff fm
  then let val (A,B) = dest_iff fm
       in (free_for_iter vars x A) andalso (free_for_iter vars x B) end
  else if is_forall fm
  then let val (y,A) = dest_forall fm
       in (Term.eq x y) orelse
          if member y vars
          then not(member x (fv A))
          else free_for_iter vars x A
       end
  else let val (y,A) = dest_exists fm
       in (Term.eq x y) orelse
          if member y vars
          then not(member x (fv A))
          else free_for_iter vars x A
       end;

fun free_for (tm : Term.t) (x : Term.t) fm =
  free_for_iter (Term.fv tm) x fm;

fun is_e_plus (Not(False)) = true
  | is_e_plus (Not(Pred("=",[lhs,rhs]))) = Term.is_ind lhs andalso
                                           Term.is_ind rhs
  | is_e_plus (Pred("=",[lhs,rhs])) = Term.is_ind lhs andalso
                                      Term.is_ind rhs
  | is_e_plus (Pred("in",[lhs,rhs])) = Term.is_ind lhs andalso
                                       Term.is_class rhs
  | is_e_plus (And(A,B)) = is_e_plus A andalso is_e_plus B
  | is_e_plus (Or(A,B)) = is_e_plus A andalso is_e_plus B
  | is_e_plus (Exists(x,A)) = Term.is_ind x andalso is_e_plus A
  | is_e_plus _ = false; 

fun serialize (False) = "False"
  | serialize (Pred(P,args)) = "Pred("^
                               P^
                               "["^
                               (String.concatWith ", " (map Term.serialize
                                                            args))^
                               "])"
  | serialize (Not(A)) = "Not("^(serialize A)^")"
  | serialize (Or(A, B)) = "Or("^(serialize A)^", "^(serialize B)^")"
  | serialize (And(A, B)) = "And("^(serialize A)^", "^(serialize B)^")"
  | serialize (Implies(A, B)) = "Implies("^(serialize A)^", "^(serialize B)^")"
  | serialize (Iff(A, B)) = "Iff("^(serialize A)^", "^(serialize B)^")"
  | serialize (Forall(x, A)) = "Forall("^(Term.serialize x)^", "^(serialize A)^")"
  | serialize (Exists(x, A)) = "Exists("^(Term.serialize x)^", "^(serialize A)^")";

(* atom_union : (t -> 'a list) -> 'a list *)
fun atom_union f =
  (fn (False) => []
    | (fm as (Pred _)) => f fm
    | (Not A) => atom_union f A
    | (And(A,B)) => (atom_union f A) @ (atom_union f B)
    | (Or(A,B)) => (atom_union f A) @ (atom_union f B)
    | (Implies(A,B)) => (atom_union f A) @ (atom_union f B)
    | (Iff(A,B)) => (atom_union f A) @ (atom_union f B)
    | (Forall(_, A)) => atom_union f A
    | (Exists(_, A)) => atom_union f A);
end;
