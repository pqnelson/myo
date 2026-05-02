structure Classical :> Classical = struct
(* nnf : Formula.t -> Formula.t *)
fun nnf fm =
  if Formula.is_and fm
  then let val (A,B) = Formula.dest_and fm
       in Formula.mk_and(nnf A, nnf B) end
  else if Formula.is_or fm
  then let val (A,B) = Formula.dest_or fm
       in Formula.mk_or(nnf A, nnf B) end
  else if Formula.is_imp fm
  then let val (A,B) = Formula.dest_imp fm
       in Formula.mk_or(nnf (Formula.mk_not A),
                        nnf B) end
  else if Formula.is_iff fm
  then let val (A,B) = Formula.dest_iff fm
       in Formula.mk_or(Formula.mk_and(nnf A, nnf B),
                        Formula.mk_and(nnf(Formula.mk_not(A)), nnf(Formula.mk_not(B)))) end
  else if Formula.is_forall fm
  then let val(x,A) = Formula.dest_forall fm
       in Formula.mk_forall(x, nnf A) end
  else if Formula.is_exists fm
  then let val(x,A) = Formula.dest_exists fm
       in Formula.mk_exists(x, nnf A) end
  else if Formula.is_not fm
  then let val fm' = Formula.dest_not fm
       in if Formula.is_not fm'
          then let val A = Formula.dest_not fm'
               in nnf A end
          else if Formula.is_and fm'
          then let val (A,B) = Formula.dest_and fm'
               in Formula.mk_or(nnf(Formula.mk_not(A)),
                                nnf(Formula.mk_not(B))) end
          else if Formula.is_or fm'
          then let val (A,B) = Formula.dest_or fm'
               in Formula.mk_and(nnf(Formula.mk_not(A)),
                                nnf(Formula.mk_not(B))) end
          else if Formula.is_imp fm'
          then let val (A,B) = Formula.dest_imp fm'
               in Formula.mk_and(nnf A,
                                 nnf(Formula.mk_not(B))) end
          else if Formula.is_iff fm'
          then let val (A,B) = Formula.dest_iff fm'
               in Formula.mk_or(Formula.mk_and(nnf A,
                                               nnf(Formula.mk_not(B))),
                                Formula.mk_and(nnf(Formula.mk_not(A)),
                                               nnf B))
               end
          else if Formula.is_exists fm'
          then let val (x,A) = Formula.dest_exists fm'
               in Formula.mk_forall(x, nnf(Formula.mk_not(A))) end
          else if Formula.is_forall fm'
          then let val (x,A) = Formula.dest_forall fm'
               in Formula.mk_exists(x, nnf(Formula.mk_not(A))) end
          else fm
       end
  else fm;


local
  fun simplify1 fm =
    if Formula.is_forall fm
    then let val (x,A) = Formula.dest_forall fm
         in if List.exists (Term.eq x) (Formula.fv A)
            then fm
            else A
         end
    else if Formula.is_exists fm
    then let val (x,A) = Formula.dest_exists fm
         in if List.exists (Term.eq x) (Formula.fv A)
            then fm
            else A
         end
    else if Formula.is_not fm
    then let val A = Formula.dest_not fm
         in if Formula.is_not A
            then Formula.dest_not A
            else fm
         end
    else if Formula.is_and fm
    then let val (A,B) = Formula.dest_and fm
         in if Formula.is_falsum A orelse Formula.is_falsum B
            then Formula.mk_falsum ()
            else if Formula.is_verum A
            then B
            else if Formula.is_verum B
            then A
            else fm
         end
    else if Formula.is_or fm
    then let val (A,B) = Formula.dest_or fm
         in if Formula.is_falsum A orelse Formula.is_verum B
            then B
            else if Formula.is_falsum B orelse Formula.is_verum A
            then A
            else fm
         end
    else if Formula.is_imp fm
    then let val (A,B) = Formula.dest_imp fm
         in if Formula.is_falsum A orelse Formula.is_verum B
            then Formula.mk_verum ()
            else if Formula.is_verum A
            then B
            else fm
         end
    else if Formula.is_iff fm
    then let val (A,B) = Formula.dest_iff fm
         in if Formula.is_verum A
            then B
            else if Formula.is_verum B
            then A
            else if Formula.is_falsum A
            then Formula.mk_not B
            else if Formula.is_falsum B
            then Formula.mk_not A
            else fm
         end
    else fm;
in
fun simplify fm =
  if Formula.is_not fm
  then let val A = Formula.dest_not fm
       in simplify1(Formula.mk_not(simplify A)) end
  else if Formula.is_and fm
  then let val (A,B) = Formula.dest_and fm
       in simplify1(Formula.mk_and(simplify A,simplify B)) end
  else if Formula.is_or fm
  then let val (A,B) = Formula.dest_or fm
       in simplify1(Formula.mk_or(simplify A,simplify B)) end
  else if Formula.is_imp fm
  then let val (A,B) = Formula.dest_imp fm
       in simplify1(Formula.mk_imp(simplify A,simplify B)) end
  else if Formula.is_iff fm
  then let val (A,B) = Formula.dest_iff fm
       in simplify1(Formula.mk_iff(simplify A,simplify B)) end
  else if Formula.is_exists fm
  then let val (x,A) = Formula.dest_exists fm
       in simplify1(Formula.mk_exists(x, simplify A)) end
  else if Formula.is_forall fm
  then let val (x,A) = Formula.dest_forall fm
       in simplify1(Formula.mk_forall(x, simplify A)) end
  else fm (* falsum or predicates are already simplified *)
end;

(* funcs : Term.t -> (string * Sort.t * int) list *)
fun funcs (Term.Var _) = []
  | funcs (Term.Fun(f,s,args)) =
      List.foldr (fn (arg, acc) =>
                   (funcs arg)@acc)
                 [(f,s,length args)]
                 args;

(* functions : Formula.t -> (string * Sort.t * int) list *)
fun functions fm =
  Formula.atom_union
    (fn p => let val (_,args) = Formula.dest_pred p
             in List.foldr (fn (arg, acc) => (funcs arg)@acc)
                           []
                           args
             end)
    fm;

(* variant : string -> Sort.t -> (string * Sort.t * int) list -> string *)
local
  fun iter n name sort funcs =
    if List.exists (fn (x,s,_) =>
                       s = sort andalso
                       (name ^ (Int.toString n)) = x)
                   funcs
    then iter (n + 1) name sort funcs
    else (name ^ (Int.toString n), sort);
in
fun variant name sort funcs : string * Sort.t =
  if List.exists (fn (x,s,_) => s = sort andalso name = x)
                 funcs
  then iter 0 name sort funcs
  else (name, sort);
end;

local
  fun iter [] acc = acc
    | iter (x::xs) acc = if List.exists (Term.eq x) xs
                         then iter xs acc
                         else iter xs (x::acc);
in
fun dedupe vars = iter vars []
end;

(* skolem : Formula.t ->  (string * Sort.t * int) list ->
     Formula.t * (string * Sort.t * int) list

REQUIRES: given formula is in NNF
ENSURES: resulting formula is Skolemized, and produces the
         list of Skolem functions/constants. *)
fun skolem (fm : Formula.t) (fns : (string * Sort.t * int) list)
  : Formula.t * ((string * Sort.t * int) list) =
  if Formula.is_exists fm
  then let val((var as (Term.Var(y,s))), A) = Formula.dest_exists fm;
           val xs = dedupe(Formula.fv fm);
           val (const as (f,s')) = variant (if List.null xs
                                 then ("c_"^y)
                                 else ("f_"^y))
                                s
                                fns;
           val fx = Term.Fun(f,s,xs);
       in skolem (Formula.subst var fx A) ((f,s',length xs)::fns) end
  else if Formula.is_forall fm
  then let val (x, A) = Formula.dest_forall fm;
           val (A', fns') = skolem A fns;
       in (Formula.mk_forall(x, A'), fns') end
  else if Formula.is_and fm
  then let val (A,B) = Formula.dest_and fm
       in skolem2 Formula.mk_and (A,B) fns end
  else if Formula.is_or fm
  then let val (A,B) = Formula.dest_or fm
       in skolem2 Formula.mk_or (A,B) fns end
  else (fm,fns)
and skolem2 conn (A,B) fns =
    let val (A',fns') = skolem A fns;
        val (B',fns'') = skolem B fns';
    in (conn(A', B'), fns'') end;

(* askolemize : Formula.t -> Formula.t

REQUIRES: The given formula is a closed formula.
ENSURES: The resulting formula is in Negation Normal Form with
         all existential quantifiers replaced by Skolem
         functions/constants. *)
fun askolemize fm =
  let val (result, _) = skolem (nnf(simplify(fm))) (functions fm)
  in result end;

fun tryfind f [] = raise Fail "tryfind"
  | tryfind f (x::xs) = (f x
                         handle _ => tryfind f xs);

(* tableau : (Formula.t list * Formula.t list * int) ->
                (Unif.Env.t * int -> 'a) ->
                Unif.Env.t * int -> 'a *)
fun tableau (fms, lits, n) (cont : Unif.Env.t * int -> 'a) (env, k) =
  if n < 0 then raise Fail "no proof at this level"
  else
    (case fms of
      [] => raise Fail "tableau: no proof"
    | (phi::unexp) =>
        if Formula.is_and phi
        then let val (A,B) = Formula.dest_and phi
             in tableau (A::B::unexp,lits,n) cont (env, k) end
        else if Formula.is_or phi
        then let val (A,B) = Formula.dest_or phi
             in tableau (A::unexp,lits,n)
                        (tableau (B::unexp,lits,n) cont)
                        (env, k)
             end
        else if Formula.is_forall phi
        then let val(x,A) = Formula.dest_forall phi;
                 val y = Term.Var("_"^(Int.toString k), Term.sort(x));
                 val A' = Formula.subst x y A;
             in tableau (A'::unexp@[Formula.mk_forall(x,A)],lits,n-1) cont (env, k+1) end
        else
         (tryfind (fn l => cont(Unif.y_complements env (phi,l),k))
                  lits
         handle _ => tableau(unexp,phi::lits,n) cont (env,k)));

fun deepen f n maxiter =
  (print("Searching with depth limit "^
         (Int.toString n)^"\n");
   f n)
  handle (Fail _) => if n < maxiter then deepen f (n + 1) maxiter
                     else raise Fail "maximum iterations encountered";

local
  fun id x = x;
in
fun tabrefute fms maxiter =
  deepen (fn n =>
             (tableau (fms,[],n)
                      id
                      (Unif.Env.undefined (),0);
              n))
         0
         maxiter
end;

(* generalize : Formula.t -> Formula.t *)
fun generalize fm =
  List.foldr Formula.mk_forall fm (dedupe (Formula.fv fm));

fun tab fm maxiter =
  let val fm' = askolemize(Formula.mk_not(generalize fm))
  in if Formula.is_falsum fm' then 0
     else tabrefute [fm'] maxiter
  end;
end;
