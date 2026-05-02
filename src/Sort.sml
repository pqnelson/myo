structure Sort = struct
exception Mismatch of string;
datatype t = IND | FUN | CLASS;

(* compare : Sort.t * Sort.t -> order *)
fun compare(IND,IND) = EQUAL
  | compare(IND, _) = LESS
  | compare(FUN,IND) = GREATER
  | compare(FUN,FUN) = EQUAL
  | compare(FUN, _) = LESS
  | compare(CLASS, CLASS) = EQUAL
  | compare(CLASS, _) = GREATER;

(* to_string : Sort.t -> string *)
fun to_string (IND) = "IND"
  | to_string (FUN) = "FUN"
  | to_string (CLASS) = "CLASS";
end;
