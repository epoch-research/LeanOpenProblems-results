import FormalConjectures.Util.ProblemImports
open Nat Finset BigOperators

noncomputable def S1z (p : ℕ) : ℤ := ∑ k ∈ range (2 * p + 1), ((p + k - 1).choose k : ℤ)

theorem S1z_eq (p : ℕ) (hp1 : 1 ≤ p) : S1z p = ((3*p).choose p : ℤ) := by
  unfold S1z
  have reindex : ∀ k ∈ range (2*p+1), (p+k-1).choose k = (k+(p-1)).choose (p-1) := by
    intro k _
    have h1 : p+k-1 = k+(p-1) := by omega
    rw [h1]
    have := Nat.choose_symm (Nat.le_add_left (p-1) k)
    rw [show k+(p-1)-(p-1)=k by omega] at this
    exact this
  rw [Finset.sum_congr rfl (fun k hk => by rw [reindex k hk])]
  have hsum := Nat.sum_range_add_choose (2*p) (p-1)
  rw [← Nat.cast_sum, hsum]
  congr 2
  · omega
  · omega

theorem lemA_test (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hcb : ((3*p-1).choose (p-1) : ZMod (p^3)) = 1) :
    S1z p ≡ 3 [ZMOD (p:ℤ)^3] := by
  haveI : NeZero (p^3) := ⟨by positivity⟩
  have hp1 : 1 ≤ p := by omega
  rw [S1z_eq p hp1]
  have hmul := Nat.add_one_mul_choose_eq (3*p-1) (p-1)
  rw [show 3*p-1+1 = 3*p by omega, show p-1+1 = p by omega] at hmul
  have hcancel : 3 * (3*p-1).choose (p-1) = (3*p).choose p := by
    have h2 : p * (3 * (3*p-1).choose (p-1)) = p * ((3*p).choose p) := by
      rw [show p*(3*(3*p-1).choose (p-1)) = 3*p*(3*p-1).choose (p-1) by ring, hmul]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) h2
  have hC1 : (p:ℤ)^3 ∣ ((3*p-1).choose (p-1) : ℤ) - 1 := by
    have hd : ((p^3:ℕ):ℤ) ∣ ((3*p-1).choose (p-1) : ℤ) - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hcb]; ring
    have hpp : ((p^3:ℕ):ℤ) = (p:ℤ)^3 := by push_cast; ring
    rwa [hpp] at hd
  rw [Int.modEq_iff_dvd]
  have hcast : ((3*p).choose p : ℤ) = 3*((3*p-1).choose (p-1):ℤ) := by exact_mod_cast hcancel.symm
  rw [hcast]
  obtain ⟨k, hk⟩ := hC1
  exact ⟨-3*k, by linear_combination -3*hk⟩
