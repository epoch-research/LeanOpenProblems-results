import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix

lemma choose_p_sub_one_zmod (p k : ℕ) (hp : Nat.Prime p) (hk : k < p) :
    ((Nat.choose (p - 1) k : ℕ) : ZMod p) = (-1 : ZMod p) ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  induction k with
  | zero => simp
  | succ k ih =>
      have hk' : k < p := Nat.lt_trans (Nat.lt_succ_self k) hk
      have hk1_ne : ((k+1 : ℕ) : ZMod p) ≠ 0 := by
        intro hzero
        have hdvd : p ∣ k + 1 := (ZMod.natCast_eq_zero_iff (k+1) p).mp hzero
        have hle := Nat.le_of_dvd (Nat.succ_pos _) hdvd
        omega
      have hnat := Nat.choose_succ_right_eq (p - 1) k
      have hcast : ((Nat.choose (p - 1) (k + 1) : ℕ) : ZMod p) * ((k+1 : ℕ) : ZMod p)
          = ((Nat.choose (p - 1) k : ℕ) : ZMod p) * (((p - 1) - k : ℕ) : ZMod p) := by
        have h := congrArg (fun n : ℕ => (n : ZMod p)) hnat
        simpa [Nat.cast_mul] using h
      have hpk : (((p - 1) - k : ℕ) : ZMod p) = - ((k+1 : ℕ) : ZMod p) := by
        have : (p - 1 - k) + (k + 1) = p := by omega
        apply eq_neg_iff_add_eq_zero.mpr
        rw [← Nat.cast_add, this]
        simp
      apply (mul_right_injective₀ hk1_ne) ?_
      change ((k+1 : ℕ) : ZMod p) * ((Nat.choose (p - 1) (k + 1) : ℕ) : ZMod p)
          = ((k+1 : ℕ) : ZMod p) * ((-1 : ZMod p) ^ (k + 1))
      rw [show ((k+1 : ℕ) : ZMod p) * ((Nat.choose (p - 1) (k + 1) : ℕ) : ZMod p)
            = ((Nat.choose (p - 1) (k + 1) : ℕ) : ZMod p) * ((k+1 : ℕ) : ZMod p) by ring,
          hcast, hpk, ih hk']
      ring
