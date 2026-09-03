import FormalConjecturesUtil

/-! Small-coefficient polynomials with high-order zeros at one, by pigeonhole. -/
namespace Erdos773.SmallSignJets
open Polynomial Finset
noncomputable section
set_option maxHeartbeats 1500000

private def word {D : ℕ} (w : Fin D → Bool) : ℤ[X] :=
  ∑ i : Fin D, if w i then X ^ i.val else 0

private lemma word_coeff {D : ℕ} (w : Fin D → Bool) (i : Fin D) :
    (word w).coeff i.val = if w i then 1 else 0 := by
  simp only [word, finset_sum_coeff]
  rw [Finset.sum_eq_single i]
  · split_ifs <;> simp
  · intro j hj hji
    have hn : i.val ≠ j.val := by intro h; exact hji (Fin.ext h.symm)
    split_ifs <;> simp [hn]
  · simp

private lemma word_coeff_high {D : ℕ} (w : Fin D → Bool) {i : ℕ} (hi : D ≤ i) :
    (word w).coeff i = 0 := by
  simp only [word, finset_sum_coeff]
  apply sum_eq_zero
  intro j hj
  have hn : i ≠ j.val := by have := j.isLt; omega
  split_ifs <;> simp [hn]

private lemma word_coeff_cases {D : ℕ} (w : Fin D → Bool) (i : ℕ) :
    (word w).coeff i = 0 ∨ (word w).coeff i = 1 := by
  by_cases hi : i < D
  · have hh := word_coeff w ⟨i, hi⟩
    split_ifs at hh <;> simp [hh]
  · exact Or.inl (word_coeff_high w (by omega))

private lemma word_injective (D : ℕ) : Function.Injective (@word D) := by
  intro w z h
  funext i
  have hh := congrArg (fun P : ℤ[X] => P.coeff i.val) h
  change (word w).coeff i.val = (word z).coeff i.val at hh
  rw [word_coeff, word_coeff] at hh
  cases hw : w i <;> cases hz : z i <;> simp_all

private def jet {D : ℕ} (w : Fin D → Bool) (j : ℕ) : ℕ :=
  ∑ i : Fin D, if w i then i.val.choose j else 0

private lemma jet_bound {D k j : ℕ} (hD : 1 ≤ D) (hj : j < k) (w : Fin D → Bool) :
    jet w j ≤ D ^ k := by
  calc
    _ ≤ ∑ i : Fin D, D ^ j := by
      apply sum_le_sum
      intro i hi
      by_cases hw : w i = true
      · simp only [hw, ↓reduceIte]
        exact (Nat.choose_le_pow _ _).trans
          (Nat.pow_le_pow_left (by have := i.isLt; omega) j)
      · simp [hw]
    _ = D ^ (j + 1) := by simp [pow_succ, mul_comm]
    _ ≤ D ^ k := Nat.pow_le_pow_right hD (by omega)

private lemma jet_coeff {D : ℕ} (w : Fin D → Bool) (j : ℕ) :
    ((word w).comp (X + 1)).coeff j = (jet w j : ℤ) := by
  simp only [word, Polynomial.sum_comp, finset_sum_coeff, jet, Nat.cast_sum]
  apply sum_congr rfl
  intro i hi
  split_ifs <;> simp [coeff_X_add_one_pow]

/-- A direct counting criterion for a nonzero signed polynomial with prescribed
vanishing order and length. -/
theorem exists_signed_jet_of_count (D k : ℕ) (hD : 1 ≤ D)
    (hc : (D ^ k + 1) ^ k < 2 ^ D) :
    ∃ V : ℤ[X], V ≠ 0 ∧ V.natDegree < D ∧ V.leadingCoeff = 1 ∧
      (∀ i, -1 ≤ V.coeff i ∧ V.coeff i ≤ 1) ∧ (X - 1) ^ k ∣ V := by
  let color : (Fin D → Bool) → (Fin k → Fin (D ^ k + 1)) :=
    fun w j => ⟨jet w j.val, Nat.lt_succ_of_le (jet_bound hD j.isLt w)⟩
  have hn : ¬ Function.Injective color := by
    intro hi
    have hh := Fintype.card_le_of_injective color hi
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hh
    omega
  obtain ⟨w,z,hwz,hne⟩ := Function.not_injective_iff.mp hn
  let V := word w - word z
  have hV : V ≠ 0 := by
    intro hh
    exact hne (word_injective D (sub_eq_zero.mp hh))
  have hcoeff (i : ℕ) : -1 ≤ V.coeff i ∧ V.coeff i ≤ 1 := by
    have hw := word_coeff_cases w i
    have hz := word_coeff_cases z i
    simp only [V, coeff_sub]
    rcases hw with hw | hw <;> rcases hz with hz | hz <;> omega
  have hdeg : V.natDegree < D := by
    by_contra! hh
    have hzero : V.coeff V.natDegree = 0 := by
      change (word w - word z).coeff V.natDegree = 0
      rw [coeff_sub, word_coeff_high w hh, word_coeff_high z hh, sub_self]
    exact (leadingCoeff_ne_zero.mpr hV) (by simpa only [coeff_natDegree] using hzero)
  have hj : (X - 1 : ℤ[X]) ^ k ∣ V := by
    rw [← C_1, X_sub_C_pow_dvd_iff, X_pow_dvd_iff]
    intro j hj
    have hh := congrArg (fun c : Fin k → Fin (D ^ k + 1) => (c ⟨j,hj⟩).val) hwz
    change jet w j = jet z j at hh
    simp only [V, sub_comp, coeff_sub, jet_coeff, hh, sub_self, C_1]
  have hl : V.leadingCoeff = -1 ∨ V.leadingCoeff = 1 := by
    have hh := hcoeff V.natDegree
    rw [coeff_natDegree] at hh
    have hh' := leadingCoeff_ne_zero.mpr hV
    omega
  rcases hl with hl | hl
  · refine ⟨-V, neg_ne_zero.mpr hV, ?_, ?_, ?_, dvd_neg.mpr hj⟩
    · simpa only [natDegree_neg] using hdeg
    · simp [hl]
    · intro i
      rw [coeff_neg]
      have hh := hcoeff i
      omega
  · exact ⟨V, hV, hdeg, hl, hcoeff, hj⟩

private lemma cubic_count (k : ℕ) (hk : 1 ≤ k) :
    ((16 * k ^ 3) ^ k + 1) ^ k < 2 ^ (16 * k ^ 3) := by
  let D := 16 * k ^ 3
  have hD : 2 ≤ D := by dsimp [D]; nlinarith [(one_le_pow₀ hk : 1 ≤ k ^ 3)]
  have hsub : D ^ k + 1 ≤ D ^ (k + 1) := by
    rw [pow_succ]
    have hh : 1 ≤ D ^ k := one_le_pow₀ (by omega : 1 ≤ D)
    nlinarith
  have hk2 : k ≤ 2 ^ k := (Nat.lt_two_pow_self (n := k)).le
  have h16 : 16 ≤ 16 ^ k := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 16) hk
  have hDb : D ≤ 2 ^ (7 * k) := by
    calc
      D ≤ 16 ^ k * (2 ^ k) ^ 3 := Nat.mul_le_mul h16 (Nat.pow_le_pow_left hk2 3)
      _ = 2 ^ (7 * k) := by
        rw [← pow_mul, Nat.mul_comm k 3, pow_mul, ← mul_pow]
        norm_num
        rw [show 128 = (2 : ℕ) ^ 7 by norm_num, ← pow_mul]
  calc
    (D ^ k + 1) ^ k ≤ (D ^ (k + 1)) ^ k := Nat.pow_le_pow_left hsub k
    _ = D ^ ((k + 1) * k) := (pow_mul _ _ _).symm
    _ ≤ D ^ (2 * k ^ 2) := Nat.pow_le_pow_right (by omega) (by nlinarith)
    _ ≤ (2 ^ (7 * k)) ^ (2 * k ^ 2) := Nat.pow_le_pow_left hDb _
    _ = 2 ^ (14 * k ^ 3) := by rw [← pow_mul]; congr 1; ring
    _ < 2 ^ (16 * k ^ 3) := by
      apply Nat.pow_lt_pow_right (by decide : 1 < 2)
      have hh : 0 < k ^ 3 := pow_pos (by omega) _
      omega

/-- Polynomial rather than exponential length suffices for arbitrary
vanishing order. The cubic bound is deliberately elementary. -/
theorem exists_signed_jet_cubic (k : ℕ) (hk : 1 ≤ k) :
    ∃ V : ℤ[X], V ≠ 0 ∧ V.natDegree < 16 * k ^ 3 ∧ V.leadingCoeff = 1 ∧
      (∀ i, -1 ≤ V.coeff i ∧ V.coeff i ≤ 1) ∧ (X - 1) ^ k ∣ V := by
  apply exists_signed_jet_of_count (16 * k ^ 3) k
  · have hh : 1 ≤ k ^ 3 := one_le_pow₀ hk
    omega
  · exact cubic_count k hk

private lemma logarithmic_count (k ell : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ ell)
    (hkl : k ≤ 2 ^ ell) :
    ((16 * k ^ 2 * ell) ^ k + 1) ^ k < 2 ^ (16 * k ^ 2 * ell) := by
  let D := 16 * k ^ 2 * ell
  have hk2 : 1 ≤ k ^ 2 := one_le_pow₀ hk
  have hD : 2 ≤ D := by dsimp [D]; nlinarith
  have hsub : D ^ k + 1 ≤ D ^ (k + 1) := by
    rw [pow_succ]
    have hh : 1 ≤ D ^ k := one_le_pow₀ (by omega : 1 ≤ D)
    nlinarith
  have hl2 : ell ≤ 2 ^ ell := (Nat.lt_two_pow_self (n := ell)).le
  have h16 : 16 ≤ (2 : ℕ) ^ (4 * ell) := by
    calc
      16 = (2 : ℕ) ^ 4 := by norm_num
      _ ≤ 2 ^ (4 * ell) := Nat.pow_le_pow_right (by decide) (by omega)
  have hDb : D ≤ 2 ^ (7 * ell) := by
    calc
      D ≤ 2 ^ (4 * ell) * (2 ^ ell) ^ 2 * 2 ^ ell :=
        Nat.mul_le_mul (Nat.mul_le_mul h16 (Nat.pow_le_pow_left hkl 2)) hl2
      _ = 2 ^ (7 * ell) := by
        rw [← pow_mul, ← pow_add, ← pow_add]
        congr 1
        ring
  calc
    (D ^ k + 1) ^ k ≤ (D ^ (k + 1)) ^ k := Nat.pow_le_pow_left hsub k
    _ = D ^ ((k + 1) * k) := (pow_mul _ _ _).symm
    _ ≤ D ^ (2 * k ^ 2) := Nat.pow_le_pow_right (by omega) (by nlinarith)
    _ ≤ (2 ^ (7 * ell)) ^ (2 * k ^ 2) := Nat.pow_le_pow_left hDb _
    _ = 2 ^ (14 * k ^ 2 * ell) := by rw [← pow_mul]; congr 1; ring
    _ < 2 ^ (16 * k ^ 2 * ell) := by
      apply Nat.pow_lt_pow_right (by decide : 1 < 2)
      nlinarith

/-- The same counting argument gives O(k^2 log k) rather than cubic length. -/
theorem exists_signed_jet_quadratic_log (k : ℕ) (hk : 1 ≤ k) :
    ∃ V : ℤ[X], V ≠ 0 ∧ V.natDegree < 16 * k ^ 2 * (k.log2 + 1) ∧
      V.leadingCoeff = 1 ∧ (∀ i, -1 ≤ V.coeff i ∧ V.coeff i ≤ 1) ∧
      (X - 1) ^ k ∣ V := by
  apply exists_signed_jet_of_count (16 * k ^ 2 * (k.log2 + 1)) k
  · have hh : 1 ≤ k ^ 2 := one_le_pow₀ hk
    nlinarith
  · apply logarithmic_count k (k.log2 + 1) hk (by omega)
    exact ((Nat.log2_lt (by omega : k ≠ 0)).mp (by omega)).le

#print axioms exists_signed_jet_quadratic_log

#print axioms exists_signed_jet_cubic
end
end Erdos773.SmallSignJets
