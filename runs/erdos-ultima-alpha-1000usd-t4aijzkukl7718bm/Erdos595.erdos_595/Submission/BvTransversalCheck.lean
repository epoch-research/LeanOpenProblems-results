import FormalConjecturesUtil
example (s : Fin 3 → Bool) (h : s 0 = true) (k : s 0 = false) : False := by
  bv_decide
#print axioms this
