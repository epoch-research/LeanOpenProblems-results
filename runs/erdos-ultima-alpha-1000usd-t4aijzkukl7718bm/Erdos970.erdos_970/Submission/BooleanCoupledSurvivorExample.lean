import Submission.BooleanSymmetric

/-! A certified survivor-detection separation between global coverage
polynomials and ALL normalized prior-supported first-hit kernels, at eight
equal marginals 1/4 and m=1700. Not a distinct-prime or Jacobsthal example. -/
namespace Erdos970.FiniteSelberg.CoupledSurvivorExample
open Finset BooleanSymmetric

def qRat (_ : Fin 8) : ℚ := 1 / 4
def hitCount (ω : Fin 8 → Bool) : ℕ := (univ.filter (fun i => ω i = true)).card
def prefixTable : ℕ → ℕ → ℚ
  | 0, 0 => 426
  | 1, 0 => 1283 / 4
  | 1, 1 => 421 / 4
  | 2, 0 => 3889 / 16
  | 2, 1 => 1243 / 16
  | 2, 2 => 441 / 16
  | 3, 0 => 11987 / 64
  | 3, 1 => 3569 / 64
  | 3, 2 => 1403 / 64
  | 3, 3 => 361 / 64
  | 4, 0 => 38521 / 256
  | 4, 1 => 9427 / 256
  | 4, 2 => 4849 / 256
  | 4, 3 => 763 / 256
  | 4, 4 => 681 / 256
  | 5, 0 => 33861 / 256
  | 5, 1 => 1165 / 64
  | 5, 2 => 4767 / 256
  | 5, 3 => 41 / 128
  | 5, 4 => 681 / 256
  | 6, 0 => 33369 / 256
  | 6, 1 => 877 / 768
  | 6, 2 => 6851 / 384
  | 6, 4 => 845 / 768
  | 6, 5 => 599 / 768
  | 7, 0 => 484629 / 4096
  | 7, 2 => 78157 / 8192
  | 7, 3 => 12017 / 4096
  | 7, 6 => 5291 / 8192
  | 7, 7 => 505 / 4096
  | _, _ => 0

def globalTable : ℕ → ℚ
  | 1 => 484629 / 4096
  | 3 => 78157 / 8192
  | 4 => 12017 / 4096
  | 7 => 5291 / 8192
  | 8 => 505 / 4096
  | _ => 0

def prefixWeight (i : Fin 8) (ω : Fin 8 → Bool) : ℚ :=
  if ∀ j : Fin 8, i ≤ j → ω j = false then prefixTable i.val (hitCount ω) else 0

def globalWeight (ω : Fin 8 → Bool) : ℚ := globalTable (hitCount ω)

def coefficientTable : ℕ → ℚ
  | 1 => 1
  | 2 => -199 / 224
  | 3 => 149 / 224
  | 4 => -37 / 112
  | 6 => 15 / 112
  | _ => 0

def coefficient (T : Finset (Fin 8)) : ℚ := coefficientTable T.card

def hitRat (T : Finset (Fin 8)) (ω : Fin 8 → Bool) : ℚ :=
  if ∀ i ∈ T, ω i = true then 1 else 0

def valueRat (ω : Fin 8 → Bool) : ℚ :=
  ∑ T : Finset (Fin 8), coefficient T * hitRat T ω

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem prefix_reduced :
    (∀ i : Fin 8, ∀ h : Fin 9, 0 ≤ prefixTable i h) ∧
    (∀ i : Fin 8, ∀ t : Fin 9, t.val ≤ i.val →
      |(∑ h ∈ range (i.val - t.val + 1),
        ((i.val - t.val).choose h : ℚ) * prefixTable i (t.val + h)) -
        425 * (1 / 4 : ℚ) ^ t.val| ≤ 1) ∧
    (∑ i : Fin 8, prefixTable i 0) = 6998085 / 4096 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem global_reduced :
    (∀ h : Fin 9, 0 ≤ globalTable h) ∧ globalTable 0 = 0 ∧
    (∀ t : Fin 9, 0 < t.val →
      |(∑ h ∈ range (8 - t.val + 1),
        ((8 - t.val).choose h : ℚ) * globalTable (t.val + h)) -
        1700 * (1 / 4 : ℚ) ^ t.val| ≤ 1) ∧
    (∑ h ∈ range 9, (Nat.choose 8 h : ℚ) * globalTable h) = 6928287 / 4096 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem primal_reduced :
    coefficientTable 0 = 0 ∧
    (∀ h : Fin 9, 0 < h.val → 1 ≤
      ∑ t ∈ range (h.val + 1), (h.val.choose t : ℚ) * coefficientTable t) ∧
    (1700 * (∑ t ∈ range 9,
        (Nat.choose 8 t : ℚ) * (coefficientTable t * (1 / 4 : ℚ) ^ t)) +
      ∑ t ∈ range 9, (Nat.choose 8 t : ℚ) * |coefficientTable t|) =
        6928287 / 4096 := by
  decide +kernel

lemma hitCount_le (ω : Fin 8 → Bool) : hitCount ω ≤ 8 := by
  exact (card_filter_le _ _).trans_eq (card_fin 8)

lemma hitRat_eq (T : Finset (Fin 8)) (ω : Fin 8 → Bool) :
    hitRat T ω = if T ⊆ patternSet ω then 1 else 0 := by
  simp [hitRat, subset_iff]

lemma prefix_condition (i : Fin 8) (ω : Fin 8 → Bool) :
    (∀ j : Fin 8, i ≤ j → ω j = false) ↔ patternSet ω ⊆ Iio i := by
  simp only [subset_iff, mem_patternSet, mem_Iio]
  constructor
  · intro hh j hj
    by_contra hn
    have := hh j (le_of_not_gt hn)
    simp_all
  · intro hh j hj
    cases he : ω j with
    | false => rfl
    | true => exact False.elim ((hh he).not_ge hj)

lemma prefix_moment (i : Fin 8) (T : Finset (Fin 8))
    (hT : ∀ j ∈ T, j < i) :
    (∑ ω, prefixWeight i ω * hitRat T ω) =
      ∑ h ∈ range (i.val - T.card + 1),
        ((i.val - T.card).choose h : ℚ) * prefixTable i (T.card + h) := by
  have hTS : T ⊆ Iio i := fun j hj => mem_Iio.mpr (hT j hj)
  have hs := symmetric_moment (Iio i) T hTS (prefixTable i)
  rw [Fin.card_Iio] at hs
  rw [← hs]
  apply sum_congr rfl
  intro ω hω
  simp only [prefixWeight, prefix_condition, hitRat_eq, hitCount, patternSet]
  split_ifs <;> simp_all

lemma global_moment (T : Finset (Fin 8)) :
    (∑ ω, globalWeight ω * hitRat T ω) =
      ∑ h ∈ range (8 - T.card + 1),
        ((8 - T.card).choose h : ℚ) * globalTable (T.card + h) := by
  have hs := symmetric_moment (univ : Finset (Fin 8)) T (subset_univ T) globalTable
  simp only [card_fin, subset_univ, true_and] at hs
  rw [← hs]
  apply sum_congr rfl
  intro ω hω
  simp only [globalWeight, hitRat_eq, hitCount, patternSet]
  split_ifs <;> simp

/-- Exact dual certificates for every prior-coordinate upper-weight problem. -/
theorem prefix_certificate :
    (∀ i ω, 0 ≤ prefixWeight i ω) ∧
    (∀ i T, (∀ j ∈ T, j < i) →
      |(∑ ω, prefixWeight i ω * hitRat T ω) - (1700 * qRat i) * ∏ j ∈ T, qRat j| ≤ 1) ∧
    (∑ i, prefixWeight i (fun _ => false)) = 6998085 / 4096 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i ω
    unfold prefixWeight
    split_ifs
    · exact prefix_reduced.1 i ⟨hitCount ω, by have := hitCount_le ω; omega⟩
    · norm_num
  · intro i T hT
    rw [prefix_moment i T hT]
    have hTi : T.card ≤ i.val := by
      have hh : T ⊆ Iio i := fun j hj => mem_Iio.mpr (hT j hj)
      simpa using card_le_card hh
    have hbound : T.card < 9 := by have := i.isLt; omega
    simpa [qRat, show (1700 : ℚ) * 4⁻¹ = 425 by norm_num] using prefix_reduced.2.1 i ⟨T.card, hbound⟩ hTi
  · simpa [prefixWeight, hitCount] using prefix_reduced.2.2

/-- The global dual has no empty atom and satisfies all nonempty moment bounds. -/
theorem global_certificate :
    (∀ ω, 0 ≤ globalWeight ω) ∧ globalWeight (fun _ => false) = 0 ∧
    (∀ T : Finset (Fin 8), T.Nonempty →
      |(∑ ω, globalWeight ω * hitRat T ω) - 1700 * ∏ i ∈ T, qRat i| ≤ 1) ∧
    (∑ ω, globalWeight ω) = 6928287 / 4096 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω
    exact global_reduced.1 ⟨hitCount ω, by have := hitCount_le ω; omega⟩
  · simpa [globalWeight, hitCount] using global_reduced.2.1
  · intro T hT
    rw [global_moment]
    have hbound : T.card < 9 := by have := card_le_univ T; simp at this; omega
    simpa [qRat] using global_reduced.2.2.1 ⟨T.card, hbound⟩ (card_pos.mpr hT)
  · have hh := global_moment ∅
    simpa [hitRat] using hh.trans (by simpa using global_reduced.2.2.2)

/-- The symmetric degree-six coverage polynomial attains the global dual value. -/
theorem primal_certificate :
    coefficient ∅ = 0 ∧
    (∀ ω : Fin 8 → Bool, ω ≠ (fun _ => false) → 1 ≤ valueRat ω) ∧
    (1700 * (∑ T : Finset (Fin 8), coefficient T * ∏ i ∈ T, qRat i) +
      ∑ T : Finset (Fin 8), |coefficient T|) = 6928287 / 4096 := by
  refine ⟨primal_reduced.1, ?_, ?_⟩
  · intro ω hω
    have hs := symmetric_value coefficientTable ω
    have hc : 0 < hitCount ω := by
      change 0 < (patternSet ω).card
      rw [card_pos, nonempty_iff_ne_empty]
      exact fun he => hω ((patternSet_eq_empty ω).mp he)
    have hh := primal_reduced.2.1 ⟨hitCount ω, by have := hitCount_le ω; omega⟩ hc
    simp only [valueRat, coefficient, hitRat_eq]
    rw [hs]
    exact hh
  · simp only [coefficient, qRat, prod_const]
    rw [sum_card (fun t => coefficientTable t * (1 / 4 : ℚ) ^ t),
      sum_card (fun t => |coefficientTable t|)]
    exact primal_reduced.2.2

noncomputable def q (i : Fin 8) : ℝ := qRat i
noncomputable def a (T : Finset (Fin 8)) : ℝ := coefficient T
noncomputable def w (ω : Fin 8 → Bool) : ℝ := globalWeight ω
noncomputable def u (i : Fin 8) (ω : Fin 8 → Bool) : ℝ := prefixWeight i ω

lemma cast_hitRat (T : Finset (Fin 8)) (ω : Fin 8 → Bool) :
    (hitRat T ω : ℝ) = hitMonomial T ω := by
  rw [hitMonomial_eq]
  simp only [hitRat]
  split_ifs <;> norm_num

lemma cast_valueRat (ω : Fin 8 → Bool) : (valueRat ω : ℝ) = booleanValue a ω := by
  simp only [valueRat, Rat.cast_sum, Rat.cast_mul, cast_hitRat, booleanValue, a]

lemma prefix_dual_feasible : FirstHitDualFeasible q 1700 u := by
  constructor
  · intro i ω
    change (0 : ℝ) ≤ (prefixWeight i ω : ℝ)
    exact_mod_cast prefix_certificate.1 i ω
  · intro i T hT
    have hh : |(∑ ω, (prefixWeight i ω : ℝ) * (hitRat T ω : ℝ)) -
        (1700 * (qRat i : ℝ)) * ∏ j ∈ T, (qRat j : ℝ)| ≤ 1 := by
      exact_mod_cast prefix_certificate.2.1 i T hT
    simpa only [cast_hitRat, u, q] using hh

lemma prefix_dual_value : (∑ i, u i (fun _ => false)) = 6998085 / 4096 := by
  unfold u
  have h := congrArg (fun x : ℚ => (x : ℝ)) prefix_certificate.2.2
  push_cast at h
  exact h

lemma coverage_majorant : IsCoverageMajorant a := by
  constructor
  · unfold a
    exact_mod_cast primal_certificate.1
  · intro ω hω
    rw [← cast_valueRat]
    exact_mod_cast primal_certificate.2.1 ω hω

lemma primal_objective : booleanObjective q 1700 a = 6928287 / 4096 := by
  unfold booleanObjective q a
  have h := congrArg (fun x : ℚ => (x : ℝ)) primal_certificate.2.2
  push_cast at h
  exact h

lemma global_nonnegative (ω : Fin 8 → Bool) : 0 ≤ w ω := by
  unfold w
  exact_mod_cast global_certificate.1 ω

lemma global_empty : w (fun _ => false) = 0 := by
  unfold w
  exact_mod_cast global_certificate.2.1

lemma global_moments (T : Finset (Fin 8)) (hT : T.Nonempty) :
    |(∑ ω, w ω * hitMonomial T ω) - 1700 * ∏ i ∈ T, q i| ≤ 1 := by
  have hh : |(∑ ω, (globalWeight ω : ℝ) * (hitRat T ω : ℝ)) -
      1700 * ∏ i ∈ T, (qRat i : ℝ)| ≤ 1 := by
    exact_mod_cast global_certificate.2.2.1 T hT
  simpa only [cast_hitRat, w, q] using hh

lemma global_dual_value : (∑ ω, w ω) = 6928287 / 4096 := by
  unfold w
  have h := congrArg (fun x : ℚ => (x : ℝ)) global_certificate.2.2.2
  push_cast at h
  exact h

/-- Exact global optimality among ALL real coverage-majorant polynomials. -/
theorem global_optimal (b : Finset (Fin 8) → ℝ) (hb : IsCoverageMajorant b) :
    booleanObjective q 1700 a ≤ booleanObjective q 1700 b := by
  rw [primal_objective, ← global_dual_value]
  exact coverageObjective_dual_bound q 1700 w global_nonnegative global_empty global_moments b hb

/-- An objective lower bound for EVERY normalized signed first-hit family. -/
theorem all_firstHit_lower_bound (c : Fin 8 → Finset (Fin 8) → ℝ)
    (hc : ∀ i, (∑ Q : Finset (Fin 8), c i Q) = 1)
    (hprior : ∀ i Q, c i Q ≠ 0 → ∀ j ∈ Q, j < i) :
    (6998085 / 4096 : ℝ) ≤ ∑ i, booleanKernelObjective q (1700 * q i) (c i) := by
  rw [← prefix_dual_value]
  exact firstHit_objective_dual_bound q 1700 u prefix_dual_feasible c hc hprior

/-- The global method beats every first-hit family by at least34899/2048 in this
finite equal-marginal example. No distinct-prime or asymptotic claim is made. -/
theorem strict_method_gap (c : Fin 8 → Finset (Fin 8) → ℝ)
    (hc : ∀ i, (∑ Q : Finset (Fin 8), c i Q) = 1)
    (hprior : ∀ i Q, c i Q ≠ 0 → ∀ j ∈ Q, j < i) :
    booleanObjective q 1700 a + 34899 / 2048 ≤
      ∑ i, booleanKernelObjective q (1700 * q i) (c i) := by
  have hh := all_firstHit_lower_bound c hc hprior
  rw [primal_objective]
  linarith

/-- At these parameters the global majorant guarantees a survivor for every
population satisfying the moment assumptions. -/
theorem global_survivor (ω : ℕ → Fin 8 → Bool)
    (herr : ∀ T : Finset (Fin 8),
      |(∑ j ∈ range 1700, hitMonomial T (ω j)) - (1700 : ℝ) * ∏ i ∈ T, q i| ≤ 1) :
    ∃ j < 1700, ∀ i, ω j i = false := by
  apply survivor_of_coverage_majorant q 1700 a coverage_majorant ω herr
  norm_num only [Nat.cast_ofNat]
  rw [primal_objective]
  norm_num

/-- No normalized prior-supported first-hit family can meet its sufficient
survivor criterion at these same parameters, even with exact merged costs. -/
theorem no_successful_firstHit :
    ¬ ∃ c : Fin 8 → Finset (Fin 8) → ℝ,
      (∀ i, (∑ Q : Finset (Fin 8), c i Q) = 1) ∧
      (∀ i Q, c i Q ≠ 0 → ∀ j ∈ Q, j < i) ∧
      (∑ i, booleanKernelObjective q (1700 * q i) (c i)) < 1700 := by
  rintro ⟨c, hc, hp, hlt⟩
  have hh := all_firstHit_lower_bound c hc hp
  linarith

#print axioms global_survivor
#print axioms no_successful_firstHit
#print axioms prefix_certificate
#print axioms global_certificate
#print axioms primal_certificate
#print axioms global_optimal
#print axioms strict_method_gap
end Erdos970.FiniteSelberg.CoupledSurvivorExample
