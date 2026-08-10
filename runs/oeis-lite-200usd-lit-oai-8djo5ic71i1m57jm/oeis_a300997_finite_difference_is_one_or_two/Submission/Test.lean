import FormalConjectures.Util.ProblemImports
open List Nat Function Set

#check Nat.sInf_mem
#check Nat.sInf_le
#check Nat.sInf_eq_zero
#check Nat.find
#check List.ext_getElem?
#check List.zipWith
#check List.dropWhile
#eval (List.range 3).foldl (fun acc _ => acc+1) 0
