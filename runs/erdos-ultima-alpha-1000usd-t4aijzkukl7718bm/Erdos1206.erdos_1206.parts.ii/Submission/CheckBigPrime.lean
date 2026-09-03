import FormalConjecturesUtil
example : (3 : ZMod 70638151)^70638150 = 1 := by reduce_mod_char
example : (3 : ZMod 70638151)^(70638150/1381) ≠ 1 := by norm_num only [Nat.reduceDiv]; reduce_mod_char
#check mem_list_primes_of_dvd_prod
#check Nat.prime_iff
#check Nat.squarefree_mul
#check Nat.Prime.squarefree
