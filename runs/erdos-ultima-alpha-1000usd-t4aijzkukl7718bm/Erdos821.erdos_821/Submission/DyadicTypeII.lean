import Submission.TypeIIBounds

/-!
# Dyadic assembly of Vaughan's Type II term

The active dyadic levels retain both short-part cutoff parameters.
The resulting upper bound is uniform in a separate endpoint for each character.
-/

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos821.AnalyticSieve

def typeIILeftBlock (N V j : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun m => V < m ∧ Nat.log 2 (m - 1) = j)

def typeIIRightBlock (N U j : ℕ) : Finset ℕ := Icc (U + 1) (N / 2 ^ j)

def typeIILevels (N U V : ℕ) : Finset ℕ :=
  (range (Nat.log 2 N + 1)).filter (fun j => V < 2 ^ (j + 1) ∧ (U + 1) * 2 ^ j ≤ N)

lemma typeIILeftBlock_bounds {N V j m : ℕ} (hV : 1 ≤ V) (hm : m ∈ typeIILeftBlock N V j) :
    1 ≤ m ∧ m ≤ N ∧ V < m ∧ 2 ^ j < m ∧ m ≤ 2 ^ (j + 1) := by
  obtain ⟨hm, hVm, hj⟩ := mem_filter.mp hm
  obtain ⟨hm1, hmN⟩ := mem_Icc.mp hm
  have hlo := Nat.pow_log_le_self 2 (show m - 1 ≠ 0 by omega)
  have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (m - 1)
  rw [hj] at hlo hhi
  exact ⟨hm1, hmN, hVm, by omega, by simpa only [Nat.succ_eq_add_one] using (show m ≤ 2 ^ (j + 1) by omega)⟩

lemma typeII_inactive_blocks {N U V j : ℕ} (hV : 1 ≤ V)
    (h : ¬(V < 2 ^ (j + 1) ∧ (U + 1) * 2 ^ j ≤ N)) :
    typeIILeftBlock N V j = ∅ ∨ typeIIRightBlock N U j = ∅ := by
  by_cases hVj : V < 2 ^ (j + 1)
  · right
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    obtain ⟨hnU, hnN⟩ := mem_Icc.mp hn
    have hp : n * 2 ^ j ≤ N := (Nat.le_div_iff_mul_le (by positivity)).mp hnN
    have hprod := Nat.mul_le_mul_right (2 ^ j) hnU
    exact h ⟨hVj, hprod.trans hp⟩
  · left
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro m hm
    obtain ⟨hm1, hmN, hVm, hlow, hhigh⟩ := typeIILeftBlock_bounds hV hm
    omega

lemma sum_typeII_left_blocks {E : Type*} [AddCommMonoid E] (F : ℕ → E) (N V : ℕ) :
    (∑ m ∈ (Icc 1 N).filter (fun m => V < m), F m) =
      ∑ j ∈ range (Nat.log 2 N + 1), ∑ m ∈ typeIILeftBlock N V j, F m := by
  have hmap (m : ℕ) (hm : m ∈ (Icc 1 N).filter (fun m => V < m)) :
      Nat.log 2 (m - 1) ∈ range (Nat.log 2 N + 1) := by
    have hmN := (mem_Icc.mp (mem_filter.mp hm).1).2
    have hlog := Nat.log_mono_right (b := 2) (show m - 1 ≤ N by omega)
    exact mem_range.mpr (by omega)
  have h := (Finset.sum_fiberwise_of_maps_to hmap F).symm
  simpa only [typeIILeftBlock, Finset.filter_filter] using h

lemma twisted_typeII_dyadic {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N R U V : ℕ) (hRN : R ≤ N) (hV : 1 ≤ V) :
    twistedArithmeticSum χ (vaughanTypeII V * longPart vonMangoldt U) R =
      ∑ j ∈ typeIILevels N U V, ∑ m ∈ typeIILeftBlock N V j, ∑ n ∈ typeIIRightBlock N U j,
        if m * n ≤ R then ((vaughanTypeII V m : ℂ) * (longPart vonMangoldt U n : ℂ)) *
          χ ((m * n : ℕ) : ZMod q) else 0 := by
  classical
  let F (m n : ℕ) : ℂ := if m * n ≤ R then
    ((vaughanTypeII V m : ℂ) * (longPart vonMangoldt U n : ℂ)) *
      χ ((m * n : ℕ) : ZMod q) else 0
  have hf (m : ℕ) (hm : m ≤ V) (n : ℕ) : F m n = 0 := by
    simp only [F, vaughanTypeII_eq_zero hm, Complex.ofReal_zero, zero_mul, ite_self]
  have hfilter : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, F m n) =
      ∑ m ∈ (Icc 1 N).filter (fun m => V < m), ∑ n ∈ Icc 1 N, F m n := by
    symm
    apply Finset.sum_filter_of_ne
    intro m hm h
    by_contra hn
    exact h (by simp only [hf m (Nat.le_of_not_gt hn), Finset.sum_const_zero])
  have hright (j m : ℕ) (hm : m ∈ typeIILeftBlock N V j) :
      (∑ n ∈ Icc 1 N, F m n) = ∑ n ∈ typeIIRightBlock N U j, F m n := by
    have hmj := typeIILeftBlock_bounds hV hm
    symm
    apply Finset.sum_subset
    · intro n hn
      obtain ⟨hnU, hnN⟩ := mem_Icc.mp hn
      exact mem_Icc.mpr ⟨by omega, hnN.trans (Nat.div_le_self N _)⟩
    · intro n hn hnB
      obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
      by_cases hUn : U < n
      · have hnDiv : ¬ n ≤ N / 2 ^ j := by
          intro hnd
          exact hnB (mem_Icc.mpr ⟨hUn, hnd⟩)
        have hmn : ¬m * n ≤ R := by
          intro hmn
          have hh : n * 2 ^ j ≤ N := by
            have hh' := Nat.mul_le_mul_right n (Nat.le_of_lt hmj.2.2.2.1)
            nlinarith
          exact hnDiv ((Nat.le_div_iff_mul_le (by positivity)).mpr hh)
        simp only [F, if_neg hmn]
      · simp only [F, longPart_apply, if_neg hUn, Complex.ofReal_zero, mul_zero, zero_mul, ite_self]
  calc
    _ = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, F m n := twistedArithmeticSum_convolution χ _ _ hRN
    _ = ∑ j ∈ range (Nat.log 2 N + 1), ∑ m ∈ typeIILeftBlock N V j, ∑ n ∈ Icc 1 N, F m n := by
      rw [hfilter, sum_typeII_left_blocks]
    _ = ∑ j ∈ range (Nat.log 2 N + 1), ∑ m ∈ typeIILeftBlock N V j,
        ∑ n ∈ typeIIRightBlock N U j, F m n := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_congr rfl (fun m hm => hright j m hm)
    _ = _ := by
      symm
      apply Finset.sum_filter_of_ne
      intro j hj h
      by_contra hn
      rcases typeII_inactive_blocks hV hn with he | he
      · exact h (by simp only [he, Finset.sum_empty])
      · exact h (by simp only [he, Finset.sum_empty, Finset.sum_const_zero])

noncomputable def typeIIBlockMajorant (Q X Y : ℕ) : ℝ :=
  Real.sqrt ((2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * X + 1)) *
    (2 * (Q : ℝ) ^ 2 + 4 * (2 * Real.pi * Y + 1)) *
    ((X : ℝ) * (1 + Real.log X) ^ 3) * ((Y : ℝ) * (Real.log Y) ^ 2))

lemma weighted_norm_sum_le_sum {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (w : ι → ℝ) (F : κ → ι → ℂ) (hw : ∀ i ∈ I, 0 ≤ w i) :
    (∑ i ∈ I, w i * ‖∑ j ∈ J, F j i‖) ≤ ∑ j ∈ J, ∑ i ∈ I, w i * ‖F j i‖ := by
  calc
    _ ≤ ∑ i ∈ I, w i * ∑ j ∈ J, ‖F j i‖ :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hw i hi))
    _ = _ := by simp only [Finset.mul_sum]; rw [Finset.sum_comm]

/-- A complete dyadic Type II bound, retaining the active scale range. -/
theorem vaughan_typeII_dyadic_bound
    (M : Finset ℕ+) (Q : ℕ) (hQ : 0 < Q) (hM : ∀ q ∈ M, (q : ℕ) ≤ Q)
    (C : ∀ q : ℕ+, Finset (DirichletCharacter ℂ (q : ℕ)))
    (hC : ∀ q ∈ M, ∀ χ ∈ C q, χ.IsPrimitive)
    (U V N : ℕ) (hV : 1 ≤ V)
    (R : (q : ℕ+) → DirichletCharacter ℂ (q : ℕ) → ℕ)
    (hR : ∀ q ∈ M, ∀ χ ∈ C q, R q χ ≤ N) :
    (∑ q ∈ M, ((q : ℕ) : ℝ) / (q : ℕ).totient * ∑ χ ∈ C q,
      ‖twistedArithmeticSum χ (vaughanTypeII V * longPart vonMangoldt U) (R q χ)‖) ≤
      (6 + 2 * Real.log ((N : ℝ) + 1)) *
        ∑ j ∈ typeIILevels N U V, typeIIBlockMajorant Q (2 ^ (j + 1)) (N / 2 ^ j) := by
  classical
  let F (j : ℕ) (z : Σ q : ℕ+, DirichletCharacter ℂ (q : ℕ)) : ℂ :=
    ∑ m ∈ typeIILeftBlock N V j, ∑ n ∈ typeIIRightBlock N U j,
      if m * n ≤ R z.1 z.2 then ((vaughanTypeII V m : ℂ) * (longPart vonMangoldt U n : ℂ)) *
        z.2 ((m * n : ℕ) : ZMod (z.1 : ℕ)) else 0
  have heq (z : Σ q : ℕ+, DirichletCharacter ℂ (q : ℕ)) (hz : z ∈ M.sigma C) :
      twistedArithmeticSum z.2 (vaughanTypeII V * longPart vonMangoldt U) (R z.1 z.2) =
        ∑ j ∈ typeIILevels N U V, F j z :=
    twisted_typeII_dyadic z.2 N _ U V (hR z.1 (mem_sigma.mp hz).1 z.2 (mem_sigma.mp hz).2) hV
  calc
    _ = ∑ z ∈ M.sigma C, ((z.1 : ℕ) : ℝ) / (z.1 : ℕ).totient *
        ‖twistedArithmeticSum z.2 (vaughanTypeII V * longPart vonMangoldt U) (R z.1 z.2)‖ := by
      rw [Finset.sum_sigma]
      simp only [Finset.mul_sum]
    _ = ∑ z ∈ M.sigma C, ((z.1 : ℕ) : ℝ) / (z.1 : ℕ).totient * ‖∑ j ∈ typeIILevels N U V, F j z‖ :=
      Finset.sum_congr rfl (fun z hz => by rw [heq z hz])
    _ ≤ ∑ j ∈ typeIILevels N U V, ∑ z ∈ M.sigma C,
        ((z.1 : ℕ) : ℝ) / (z.1 : ℕ).totient * ‖F j z‖ :=
      weighted_norm_sum_le_sum _ _ _ _ (fun z hz => by positivity)
    _ ≤ ∑ j ∈ typeIILevels N U V, (6 + 2 * Real.log ((N : ℝ) + 1)) *
        typeIIBlockMajorant Q (2 ^ (j + 1)) (N / 2 ^ j) := by
      apply Finset.sum_le_sum
      intro j hj
      have hleft : typeIILeftBlock N V j ⊆ Icc 1 (2 ^ (j + 1)) := by
        intro m hm
        have hb := typeIILeftBlock_bounds hV hm
        exact mem_Icc.mpr ⟨hb.1, hb.2.2.2.2⟩
      have hright : typeIIRightBlock N U j ⊆ Icc 1 (N / 2 ^ j) := by
        intro n hn
        exact mem_Icc.mpr ⟨by have := mem_Icc.mp hn; omega, (mem_Icc.mp hn).2⟩
      have h := vaughan_typeII_block_bound M Q hQ hM C hC U V (2 ^ (j + 1)) (N / 2 ^ j) N
        (typeIILeftBlock N V j) (typeIIRightBlock N U j) hleft hright
        (fun m hm => (typeIILeftBlock_bounds hV hm).2.1)
        (fun n hn => (mem_Icc.mp hn).2.trans (Nat.div_le_self N _)) R hR
      simpa only [typeIIBlockMajorant, Finset.sum_sigma, ← Finset.mul_sum, F] using h
    _ = _ := by rw [Finset.mul_sum]

end Erdos821.AnalyticSieve
