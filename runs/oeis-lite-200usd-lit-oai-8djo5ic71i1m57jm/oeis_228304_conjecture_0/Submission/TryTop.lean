import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix

def a (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k => ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 4)

def c (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k =>
    ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 2) * (choose (2 * k) k : ℤ) * (choose (2 * (n - k)) (n - k) : ℤ)

def aZ (p n : ℕ) : ZMod p :=
  Finset.sum (range (n + 1)) fun k => ((-1 : ZMod p) ^ k) * ((choose n k : ZMod p) ^ 4)

def cZ (p n : ℕ) : ZMod p :=
  Finset.sum (range (n + 1)) fun k =>
    ((-1 : ZMod p) ^ k) * ((choose n k : ZMod p) ^ 2) * (choose (2 * k) k : ZMod p) * (choose (2 * (n - k)) (n - k) : ZMod p)

lemma cast_a_eq_aZ (p n : ℕ) : ((a n : ℤ) : ZMod p) = aZ p n := by
  simp [a, aZ, map_sum, Nat.cast_sum]

lemma cast_c_eq_cZ (p n : ℕ) : ((c n : ℤ) : ZMod p) = cZ p n := by
  simp [c, cZ, map_sum, Nat.cast_sum]

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

lemma sum_neg_one_range_odd {R : Type*} [Ring R] (m : ℕ) :
    (∑ k ∈ range (2*m+1), (-1 : R)^k) = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2*(m+1)+1 = (2*m+1)+2 by ring]
      rw [Finset.sum_range_add]
      simp [ih, pow_add]

lemma aZ_top (p m : ℕ) (hp : Nat.Prime p) (hp_eq : p = 2*m+1) :
    aZ p (p-1) = 1 := by
  subst p
  unfold aZ
  rw [show 2*m+1 - 1 + 1 = 2*m+1 by omega]
  trans ∑ k ∈ range (2*m+1), (-1 : ZMod (2*m+1)) ^ k
  · apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < 2*m+1 := by simpa using hk
    rw [choose_p_sub_one_zmod (2*m+1) k hp hklt]
    have h4 : (((-1 : ZMod (2*m+1)) ^ k) ^ 4) = 1 := by
      rw [← pow_mul]
      have he : Even (k * 4) := ⟨2*k, by omega⟩
      simpa using (Even.neg_one_pow (α := ZMod (2*m+1)) he)
    simp [h4]
  · exact sum_neg_one_range_odd (R := ZMod (2*m+1)) m
