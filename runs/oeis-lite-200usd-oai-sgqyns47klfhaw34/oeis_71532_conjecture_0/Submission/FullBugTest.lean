import FormalConjectures.Util.ProblemImports

#check Nat.not_full_of_prime_mod_prime_sq
#check Nat.full_of_le_full
#check Nat.Full.zero_left
#check Nat.Full.one_left
#print axioms Nat.not_full_of_prime_mod_prime_sq

#eval decide ((2:ℕ).Full 8)
#eval decide ((3:ℕ).Full 8)
#eval decide ((2:ℕ).Full 12)

example : False := by
  -- criterion: n % p^(k+1)=p => not (k+1)-full. Test n=4,k=1,p=2: 4%4=0 no.
  have h := Nat.not_full_of_prime_mod_prime_sq (n:=2) (k:=0) (p:=2) (by norm_num) (by norm_num)
  have hf : (0+1:ℕ).Full 2 := Nat.Full.one_left 2
  exact h hf
