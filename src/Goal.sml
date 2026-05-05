structure Goal : Goal = struct
exception Unsolved of string;
exception Mismatch of string;

type t = { goals : ((string * Formula.t) list * Formula.t) list,
           justify : Thm.t list -> Thm.t };

fun subgoals ({goals, ...} : t) = goals;

fun justify ({justify = jfn, ...} : t) = jfn;

local
  fun single (asl, fm) =
    (String.concatWith
       ", "
       (map (fn (label, p) =>
                if "" = label then Formula.serialize p
                else "\""^label^"\": "^(Formula.serialize p))
            asl)) ^
    (if (List.null asl) then "|- "
     else " |- ") ^ 
    (Formula.serialize fm);
  fun iter n acc [] = acc
    | iter n acc ((asl, fm)::gls) =
        iter (n + 1)
             (acc ^
              "Subgoal "^
              (Int.toString n)^
              ": " ^
              (single (asl, fm)) ^"\n")
             gls;
in
fun to_string ({goals, justify}) =
 (case goals of
   [] => "No more goals"
 | [g] => (single g)
 | (gls) => (iter 1 "" gls))
end;

(* setup : Formula.t -> Goal.t *)
fun setup fm =
  let
    fun check [thm] =
      if Formula.eq fm (Thm.concl thm)
      then thm
      else raise Mismatch "Goal.setup: wrong theorem"
  in
    { goals = [([], fm)]
    , justify = check }
  end;

(* extract_thm : Goal.t -> Thm.t *)
fun extract_thm ({goals, justify} : t) = 
  if List.null goals
  then justify []
  else raise Unsolved "Goal.extract_thm: unsolved goals";
end;
