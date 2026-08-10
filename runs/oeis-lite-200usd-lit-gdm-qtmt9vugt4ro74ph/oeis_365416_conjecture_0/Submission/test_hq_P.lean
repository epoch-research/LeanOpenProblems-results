import FormalConjectures.Util.ProblemImports

lemma hq_P_proof (q : ℕ) (q_mod : q % 252 = 23) (P : ℕ) [Fact (Nat.Prime P)] :
    (q : ZMod P) = ((252 % P : ℕ) : ZMod P) * (((q / 252) % P : ℕ) : ZMod P) + ((23 % P : ℕ) : ZMod P) := by
  have h_eq : q = 252 * (q / 252) + 23 := (Nat.div_add_mod q 252).symm.trans (by omega)
  have h_cast : (q : ZMod P) = (252 : ZMod P) * ((q / 252 : ℕ) : ZMod P) + (23 : ZMod P) := by
    have h_cast_eq := congrArg (Nat.cast : ℕ → ZMod P) h_eq
    push_cast at h_cast_eq
    exact h_cast_eq
  have h_252 : ((252 % P : ℕ) : ZMod P) = (252 : ZMod P) := ZMod.natCast_mod 252 P
  have h_23 : ((23 % P : ℕ) : ZMod P) = (23 : ZMod P) := ZMod.natCast_mod 23 P
  have h_div_cast : ((q / 252 % P : ℕ) : ZMod P) = ((q / 252 : ℕ) : ZMod P) := ZMod.natCast_mod (q / 252) P
  rw [h_cast]
  rw [← h_div_cast, h_252, h_23]
