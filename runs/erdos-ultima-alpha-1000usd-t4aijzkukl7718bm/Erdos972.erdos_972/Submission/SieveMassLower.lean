import Submission.SelbergWeights

/-! An elementary logarithmic lower bound for the Selberg normalizing sum. -/
namespace Erdos972SieveMassLower

open Finset ArithmeticFunction Erdos972SelbergWeights
open scoped ArithmeticFunction.Moebius

lemma sum_reciprocal_squares_le_two (R : ℕ) :
    (∑ b ∈ Ioc 0 R, 1 / (b : ℝ)^2) ≤ 2 := by
  have hI : Ioc 0 R = Ioo 0 (R + 1) := by ext b; simp only [mem_Ioc, mem_Ioo]; omega
  rw [hI]
  simpa only [Nat.cast_zero, zero_add, div_one, one_div] using
    (sum_Ioo_inv_sq_le (α := ℝ) 0 (R + 1))

lemma harmonic_le_squarefree_product (R : ℕ) :
    (harmonic R : ℝ) ≤
      (∑ a ∈ Ioc 0 R, if Squarefree a then 1 / (a : ℝ) else 0) *
        (∑ b ∈ Ioc 0 R, 1 / (b : ℝ)^2) := by
  classical
  choose a b hab hsq using Nat.sq_mul_squarefree
  let f : ℕ → ℕ × ℕ := fun n => (a n, b n)
  let w : ℕ × ℕ → ℝ := fun z => if Squarefree z.1 then 1 / (z.1 : ℝ) / (z.2 : ℝ)^2 else 0
  have hinj : Set.InjOn f (↑(Ioc 0 R) : Set ℕ) := by
    intro n hn m hm he
    have ha : a n = a m := congrArg Prod.fst he
    have hb : b n = b m := congrArg Prod.snd he
    rw [← hab n, ← hab m, ha, hb]
  have hmem (n : ℕ) (hn : n ∈ Ioc 0 R) : f n ∈ Ioc 0 R ×ˢ Ioc 0 R := by
    have hn0 := (mem_Ioc.mp hn).1
    have hnR := (mem_Ioc.mp hn).2
    have ha0 : 0 < a n := by
      by_contra h
      have ha : a n = 0 := by omega
      have := hab n
      rw [ha, mul_zero] at this
      omega
    have hb0 : 0 < b n := by
      by_contra h
      have hb : b n = 0 := by omega
      have := hab n
      rw [hb, zero_pow (by decide), zero_mul] at this
      omega
    have haD : a n ∣ n := by
      conv_rhs => rw [← hab n]
      exact dvd_mul_left (a n) ((b n)^2)
    have hbD : b n ∣ n := by
      conv_rhs => rw [← hab n]
      exact ⟨b n * a n, by ring⟩
    exact mem_product.mpr ⟨mem_Ioc.mpr ⟨ha0, (Nat.le_of_dvd hn0 haD).trans hnR⟩,
      mem_Ioc.mpr ⟨hb0, (Nat.le_of_dvd hn0 hbD).trans hnR⟩⟩
  have hw (n : ℕ) : w (f n) = (n : ℝ)⁻¹ := by
    simp only [w, f, hsq n, if_true]
    rw [div_div, one_div]
    conv_rhs => rw [← hab n]
    push_cast
    ring
  have hh : (harmonic R : ℝ) = ∑ n ∈ Ioc 0 R, (n : ℝ)⁻¹ := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    congr 1
  rw [hh]
  calc
    (∑ n ∈ Ioc 0 R, (n : ℝ)⁻¹) = ∑ z ∈ (Ioc 0 R).image f, w z := by
      rw [sum_image hinj]
      exact sum_congr rfl (fun n _ => (hw n).symm)
    _ ≤ ∑ z ∈ Ioc 0 R ×ˢ Ioc 0 R, w z := by
      apply sum_le_sum_of_subset_of_nonneg
      · rintro z hz
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hz
        exact hmem n hn
      · intro z _ _
        dsimp [w]
        split_ifs <;> positivity
    _ = _ := by
      rw [sum_product, sum_mul_sum]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      dsimp [w]
      split_ifs <;> simp_all [div_eq_mul_inv]

lemma squarefree_reciprocal_le_sieveMass (R : ℕ) :
    (∑ a ∈ Ioc 0 R, if Squarefree a then 1 / (a : ℝ) else 0) ≤ sieveMass R := by
  classical
  apply sum_le_sum
  intro a ha
  have ha0 := (mem_Ioc.mp ha).1
  have ht : (0 : ℝ) < a.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr ha0)
  by_cases hs : Squarefree a
  · rw [if_pos hs]
    have hmu : (μ a : ℝ)^2 = 1 := by exact_mod_cast moebius_sq_eq_one_of_squarefree hs
    rw [hmu]
    apply one_div_le_one_div_of_le ht
    exact_mod_cast Nat.totient_le a
  · rw [if_neg hs]
    positivity

lemma harmonic_le_two_sieveMass (R : ℕ) : (harmonic R : ℝ) ≤ 2 * sieveMass R := by
  apply (harmonic_le_squarefree_product R).trans
  have h := mul_le_mul (squarefree_reciprocal_le_sieveMass R)
    (sum_reciprocal_squares_le_two R) (by positivity) (sieveMass_nonneg R)
  simpa only [mul_comm] using h

/-- The normalizing sum grows at least logarithmically, without using the
prime number theorem or Mertens' theorem. -/
theorem log_le_two_sieveMass (R : ℕ) : Real.log (R + 1) ≤ 2 * sieveMass R := by
  have h := log_add_one_le_harmonic R
  push_cast at h
  exact h.trans (harmonic_le_two_sieveMass R)

#print axioms log_le_two_sieveMass

end Erdos972SieveMassLower
