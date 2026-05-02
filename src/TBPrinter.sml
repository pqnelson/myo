structure TBPrinter : Printer = struct
fun term (Term.Var(x,_)) = x
  | term (Term.Fun(f, _, args)) =
      if List.null args
      then f
      else f^"("^(String.concatWith ", "
                                    (map term args))^
           ")";

(* "∀" (* U+2200 *)
   "∃" (* U+2203 *)
"∧" U+2227
"∨"; (* U+2228 *)
"⇔" U+21D4
 *)
fun gather_bvars is_q dest_q acc fm =
  if not(is_q fm) then (acc, fm)
  else let val (var, body) = dest_q fm
       in gather_bvars is_q dest_q (acc^", "^(term var)) body
       end;
fun formula fm =
  if Formula.is_falsum fm
  then "⊥" (* U+22A5 *)
  else if Formula.is_pred fm
  then let val (P,args) = Formula.dest_pred fm
       in P^"["^(String.concatWith ", " (map term args))^"]" end
  else if Formula.is_not fm
  then let val A = Formula.dest_not fm;
           val conn = "¬"; (* U+00AC *)
       in conn ^ (paren_form A fm) end
  else if Formula.is_and fm
  then let val (A, B) = Formula.dest_and fm;
           val conn = "∧"; (* U+2227 *)
       in (paren_form A fm) ^ conn ^ (paren_form B fm) end
  else if Formula.is_or fm
  then let val (A, B) = Formula.dest_or fm;
           val conn = "∨"; (* U+2228 *)
       in (paren_form A fm) ^ conn ^ (paren_form B fm) end
  else if Formula.is_imp fm
  then let val (A, B) = Formula.dest_imp fm;
           val conn = "⟹"; (* U+27F9 for long version, U+21D2 *)
       in (paren_form A fm) ^ conn ^ (paren_form B fm) end
  else if Formula.is_iff fm
  then let val (A, B) = Formula.dest_iff fm;
           val conn = "⟺"; (* U+27FA for long version, U+21D4 *)
       in (paren_form A fm) ^ conn ^ (paren_form B fm) end
  else if Formula.is_forall fm
  then let
    val (var, body) = Formula.dest_forall fm
    val (prefix, A) = gather_bvars Formula.is_forall
                                   Formula.dest_forall
                                   ("∀" ^ (* U+2200 *)
                                    (term var))
                                   body
  in prefix ^ "." ^ (formula body) end
  else if Formula.is_exists fm
  then let
    val (var, body) = Formula.dest_exists fm
    val (prefix, A) = gather_bvars Formula.is_exists
                                   Formula.dest_exists
                                   ("∃" ^ (* U+2203 *)
                                    (term var))
                                   body
  in prefix ^ "." ^ (formula body) end
  else raise Fail("unknown connective: "^(Formula.serialize fm))
and paren_form sub fm =
    (case Formula.precedence sub fm of
      LESS => "("^(formula sub)^")"
    | EQUAL => if (Formula.is_imp fm orelse Formula.is_iff fm) andalso
                  (Formula.is_imp sub orelse Formula.is_iff sub)
               then "("^(formula sub)^")"
               else formula sub
    | _ => formula sub);

(* NB: "⊦" U+22A6 is assertion
 "⊢" U+22A2 is just right tack *)
fun thm th =
  let
    val hyps = Thm.hyps th;
    val concl = Thm.concl th;
    val turnstile = if List.null hyps
                    then "⊢ "
                    else " ⊢ ";
  in
    (String.concatWith ", " (map formula hyps)) ^
    turnstile ^
    (formula concl)
  end;

local
  fun turnstile [] = "⊢ "
    | turnstile _ = " ⊢ ";
  fun single (asl, fm) =
    (String.concatWith
       ", "
       (map (fn (label, p) =>
                if "" = label then formula p
                else "\""^label^"\": "^(formula p))
            asl)) ^
    (turnstile asl) ^ 
    (formula fm);
  fun iter n acc [] = acc
    | iter n acc ((asl, fm)::gls) =
        iter (n + 1)
             (acc ^
              "Subgoal "^
              (Int.toString n)^
              ": " ^
              (single (asl, fm)) ^
              (if List.null gls then "" else "\n"))
             gls;
in
fun goals [] = "No more goals"
  | goals [g] = single g
  | goals gls = iter 1 "" gls
end;

end;
