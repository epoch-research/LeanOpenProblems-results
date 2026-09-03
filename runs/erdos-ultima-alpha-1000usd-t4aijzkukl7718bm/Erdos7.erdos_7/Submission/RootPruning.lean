import Submission.FiniteHingeComparison
import Submission.FiniteHingeFunctions

/-! Finite root pruning and positive equal-mass comparison.
These are auxiliary lemmas, not a solution of the odd covering conjecture. -/
namespace Erdos7RootPruning
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

section Prune
variable {Ω ι : Type*} [Fintype Ω]

/-- A root point survives when all the selected integer counts obey their caps. -/
def Good (S : Finset ι) (C : ι → Ω → ℕ) (T : ι → ℕ) (x : Ω) : Prop :=
  ∀ i ∈ S, C i x ≤ T i

noncomputable def keep (μ : Ω → ℝ) (G : Ω → Prop) (x : Ω) : ℝ :=
  if G x then μ x else 0

noncomputable def fill (G : Ω → Prop) (X : Ω → ℝ) (b : ℝ) (x : Ω) : ℝ :=
  if G x then X x else b

lemma keep_nonneg (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (G : Ω → Prop) (x : Ω) :
    0 ≤ keep μ G x := by
  classical
  unfold keep
  split_ifs <;> first | exact hμ x | exact le_rfl

lemma keep_le (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (G : Ω → Prop) (x : Ω) :
    keep μ G x ≤ μ x := by
  classical
  unfold keep
  split_ifs <;> first | exact le_rfl | exact hμ x

lemma keep_add_complement (μ : Ω → ℝ) (G : Ω → Prop) (x : Ω) :
    keep μ G x + keep μ (fun x => ¬ G x) x = μ x := by
  classical
  by_cases h : G x <;> simp [keep, h]

lemma keep_mass (μ : Ω → ℝ) (G : Ω → Prop) :
    (∑ x, keep μ G x) + (∑ x, keep μ (fun x => ¬ G x) x) = ∑ x, μ x := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun x _ => keep_add_complement μ G x)

/-- For integer counts, exceeding a threshold contributes at least one to
its hinge. The union bound therefore has an explicit finite hinge cost. -/
theorem discarded_mass_le_hinges (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (S : Finset ι) (C : ι → Ω → ℕ) (T : ι → ℕ) :
    (∑ x, keep μ (fun x => ¬ Good S C T x) x) ≤
      ∑ i ∈ S, ∑ x, μ x * max 0 ((C i x : ℝ) - T i) := by
  classical
  have hp (x : Ω) : keep μ (fun x => ¬ Good S C T x) x ≤
      μ x * (∑ i ∈ S, max 0 ((C i x : ℝ) - T i)) := by
    by_cases hg : Good S C T x
    · simp only [keep, hg, not_true_eq_false, if_false]
      exact mul_nonneg (hμ x) (Finset.sum_nonneg (fun _ _ => le_max_left _ _))
    · have he : ∃ i ∈ S, T i < C i x := by
        simpa only [Good, not_forall, not_le, exists_prop] using hg
      obtain ⟨i, hi, hci⟩ := he
      have hc : (1 : ℝ) ≤ (C i x : ℝ) - T i := by
        have hh : T i + 1 ≤ C i x := hci
        have hh' : (T i : ℝ) + 1 ≤ C i x := by exact_mod_cast hh
        linarith
      have hs : (1 : ℝ) ≤ ∑ j ∈ S, max 0 ((C j x : ℝ) - T j) :=
        (hc.trans (le_max_right 0 _)).trans
          (Finset.single_le_sum (f := fun j => max 0 ((C j x : ℝ) - T j))
            (fun _ _ => le_max_left _ _) hi)
      simpa only [keep, hg, not_false_eq_true, if_true, mul_one] using
        mul_le_mul_of_nonneg_left hs (hμ x)
  calc
    _ ≤ ∑ x, μ x * (∑ i ∈ S, max 0 ((C i x : ℝ) - T i)) :=
      Finset.sum_le_sum (fun x _ => hp x)
    _ = _ := by simp_rw [Finset.mul_sum]; exact Finset.sum_comm

theorem surviving_mass_lower_bound (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (S : Finset ι) (C : ι → Ω → ℕ) (T : ι → ℕ) (H : ι → ℝ)
    (hH : ∀ i ∈ S, (∑ x, μ x * max 0 ((C i x : ℝ) - T i)) ≤ H i) :
    (∑ x, μ x) - (∑ i ∈ S, H i) ≤ ∑ x, keep μ (Good S C T) x := by
  have hb := (discarded_mass_le_hinges μ hμ S C T).trans (Finset.sum_le_sum hH)
  have hm := keep_mass μ (Good S C T)
  linarith

lemma fill_le (G : Ω → Prop) (X : Ω → ℝ) (b : ℝ) (hb : ∀ x, b ≤ X x) (x : Ω) :
    fill G X b x ≤ X x := by
  classical
  unfold fill
  split_ifs <;> first | exact le_rfl | exact hb x

lemma fill_lower (G : Ω → Prop) (X : Ω → ℝ) (b : ℝ) (hb : ∀ x, b ≤ X x) (x : Ω) :
    b ≤ fill G X b x := by
  classical
  unfold fill
  split_ifs <;> first | exact hb x | exact le_rfl

lemma fill_upper (G : Ω → Prop) (X : Ω → ℝ) (b t : ℝ) (hb : b ≤ t)
    (hcap : ∀ x, G x → X x ≤ t) (x : Ω) : fill G X b x ≤ t := by
  classical
  unfold fill
  split_ifs with h
  · exact hcap x h
  · exact hb

/-- Filling deleted points at the common lower baseline preserves every
monotone comparison for the original, unpruned measure. -/
lemma fill_test_le (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (G : Ω → Prop)
    (X : Ω → ℝ) (b : ℝ) (hb : ∀ x, b ≤ X x)
    (φ : ℝ → ℝ) (hmφ : Monotone φ) :
    (∑ x, μ x * φ (fill G X b x)) ≤ ∑ x, μ x * φ (X x) :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
    (hmφ (fill_le G X b hb x)) (hμ x))

/-- On retained points the filled and actual tests agree, including signed tests. -/
lemma keep_fill_test (μ : Ω → ℝ) (G : Ω → Prop) (X : Ω → ℝ) (b : ℝ)
    (φ : ℝ → ℝ) :
    (∑ x, keep μ G x * φ (fill G X b x)) = ∑ x, keep μ G x * φ (X x) := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : G x <;> simp [keep, fill, h]

/-- Dropping points is safe for nonnegative tests, not for arbitrary signed tests. -/
lemma keep_nonnegative_test_le (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (G : Ω → Prop)
    (X : Ω → ℝ) (φ : ℝ → ℝ) (hφ : ∀ z, 0 ≤ φ z) :
    (∑ x, keep μ G x * φ (X x)) ≤ ∑ x, μ x * φ (X x) :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_right (keep_le μ hμ G x) (hφ _))

lemma averaged_fill_upper (S : Finset ι) (w : ι → ℝ) (G : Ω → Prop)
    (X : ι → Ω → ℝ) (b : ℝ) (T : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hb : ∀ i ∈ S, b ≤ T i)
    (hcap : ∀ i ∈ S, ∀ x, G x → X i x ≤ T i) (x : Ω) :
    (∑ i ∈ S, w i * fill G (X i) b x) ≤ ∑ i ∈ S, w i * T i :=
  Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
    (fill_upper G (X i) b (T i) (hb i hi) (hcap i hi) x) (hw i hi))

/-- The averaging step does not assert that normalized counts are integers. -/
theorem averaged_filled_test_le (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (S : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) (hw1 : (∑ i ∈ S, w i) = 1)
    (G : Ω → Prop) (X : ι → Ω → ℝ) (b : ℝ) (hb : ∀ i ∈ S, ∀ x, b ≤ X i x)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ)
    (B : ℝ) (hB : ∀ i ∈ S, (∑ x, μ x * φ (X i x)) ≤ B) :
    (∑ x, μ x * φ (∑ i ∈ S, w i * fill G (X i) b x)) ≤ B := by
  apply Erdos7FiniteHingeComparison.family_mixture_bound S w μ
    (fun i => fill G (X i) b) φ hφ hw hw1 hμ B
  intro i hi
  exact (fill_test_le μ hμ G (X i) b (hb i hi) φ hmφ).trans (hB i hi)
end Prune

section UpperTrim
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

noncomputable def tailMass (ν : Ξ → ℝ) (Z : Ξ → ℝ) (t : ℝ) : ℝ :=
  ∑ z, if t < Z z then ν z else 0

/-- Positive upper trimming at a prescribed cutoff. The atom at the cutoff
fills the remaining mass; positivity requires the tail to fit that mass. -/
noncomputable def upperWeight (ν : Ξ → ℝ) (Z : Ξ → ℝ) (t m : ℝ) : Option Ξ → ℝ
  | none => m - tailMass ν Z t
  | some z => if t < Z z then ν z else 0

def upperValue (Z : Ξ → ℝ) (t : ℝ) : Option Ξ → ℝ
  | none => t
  | some z => Z z

lemma upperWeight_nonneg (ν : Ξ → ℝ) (hν : ∀ z, 0 ≤ ν z) (Z : Ξ → ℝ) (t m : ℝ)
    (ht : tailMass ν Z t ≤ m) (z : Option Ξ) : 0 ≤ upperWeight ν Z t m z := by
  classical
  cases z with
  | none => exact sub_nonneg.mpr ht
  | some z => simp only [upperWeight]; split_ifs <;> first | exact hν z | exact le_rfl

lemma upperWeight_mass (ν : Ξ → ℝ) (Z : Ξ → ℝ) (t m : ℝ) :
    (∑ z, upperWeight ν Z t m z) = m := by
  classical
  rw [Fintype.sum_option]
  simp only [upperWeight, tailMass]
  ring

lemma upperWeight_formula (ν : Ξ → ℝ) (Z : Ξ → ℝ) (t m : ℝ)
    (φ : ℝ → ℝ) (hmφ : Monotone φ) :
    (∑ z, upperWeight ν Z t m z * φ (upperValue Z t z)) =
      (∑ z, ν z * max 0 (φ (Z z) - φ t)) + m * φ t := by
  classical
  have he (z : Ξ) : ν z * max 0 (φ (Z z) - φ t) =
      (if t < Z z then ν z * φ (Z z) else 0) -
      (if t < Z z then ν z else 0) * φ t := by
    by_cases hz : t < Z z
    · rw [if_pos hz, if_pos hz, max_eq_right (sub_nonneg.mpr (hmφ hz.le))]
      ring
    · rw [if_neg hz, if_neg hz, max_eq_left (sub_nonpos.mpr (hmφ (le_of_not_gt hz)))]
      ring
  rw [Fintype.sum_option]
  simp only [upperWeight, upperValue]
  simp_rw [he, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hh : (∑ z, (if t < Z z then ν z else 0) * φ (Z z)) =
      ∑ z, if t < Z z then ν z * φ (Z z) else 0 := by
    apply Finset.sum_congr rfl
    intro z _
    split_ifs <;> simp
  rw [hh]
  unfold tailMass
  ring

/-- A nonnegative-test comparison implies a comparison for all signed convex
monotone tests after the masses are matched. No signed law is integrated
against an upper bound. -/
theorem upperWeight_dominates (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (X : Ω → ℝ)
    (ν : Ξ → ℝ) (Z : Ξ → ℝ) (m t : ℝ) (hm : (∑ x, μ x) = m)
    (hraw : ∀ ψ : ℝ → ℝ, ConvexOn ℝ Set.univ ψ → Monotone ψ → (∀ z, 0 ≤ ψ z) →
      (∑ x, μ x * ψ (X x)) ≤ ∑ z, ν z * ψ (Z z))
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ) :
    (∑ x, μ x * φ (X x)) ≤ ∑ z, upperWeight ν Z t m z * φ (upperValue Z t z) := by
  let ψ : ℝ → ℝ := fun z => max 0 (φ z - φ t)
  have hψ : ConvexOn ℝ Set.univ ψ := by
    have hh := hφ.add (convexOn_const (-φ t) convex_univ)
    simpa only [sub_eq_add_neg] using (convexOn_const (0 : ℝ) convex_univ).sup hh
  have hmψ : Monotone ψ := fun x y hxy =>
    max_le_max le_rfl (sub_le_sub_right (hmφ hxy) _)
  have hr := hraw ψ hψ hmψ (fun z => le_max_left _ _)
  have hp (x : Ω) : φ (X x) ≤ ψ (X x) + φ t := by
    dsimp only [ψ]
    linarith [le_max_right 0 (φ (X x) - φ t)]
  calc
    _ ≤ ∑ x, μ x * (ψ (X x) + φ t) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hp x) (hμ x))
    _ = (∑ x, μ x * ψ (X x)) + m * φ t := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hm]
    _ ≤ (∑ z, ν z * ψ (Z z)) + m * φ t := add_le_add hr le_rfl
    _ = _ := (upperWeight_formula ν Z t m φ hmφ).symm

/-- Apply the positive equal-mass comparison directly to an arbitrary pruned
submeasure. The original comparison may even be assumed only for nonnegative
convex monotone tests. -/
theorem pruned_upperWeight_dominates (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (G : Ω → Prop) (X : Ω → ℝ) (ν : Ξ → ℝ) (Z : Ξ → ℝ) (t : ℝ)
    (hraw : ∀ ψ : ℝ → ℝ, ConvexOn ℝ Set.univ ψ → Monotone ψ → (∀ z, 0 ≤ ψ z) →
      (∑ x, μ x * ψ (X x)) ≤ ∑ z, ν z * ψ (Z z))
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ) :
    (∑ x, keep μ G x * φ (X x)) ≤
      ∑ z, upperWeight ν Z t (∑ x, keep μ G x) z * φ (upperValue Z t z) := by
  apply upperWeight_dominates (keep μ G) (keep_nonneg μ hμ G) X ν Z
    (∑ x, keep μ G x) t rfl _ φ hφ hmφ
  intro ψ hψ hmψ hψ0
  exact (keep_nonnegative_test_le μ hμ G X ψ hψ0).trans (hraw ψ hψ hmψ hψ0)
end UpperTrim

#print axioms discarded_mass_le_hinges
#print axioms averaged_filled_test_le
#print axioms upperWeight_dominates
#print axioms pruned_upperWeight_dominates
end Erdos7RootPruning
