import Submission.JointFiniteRepairExplore
import Submission.NaturalRepairBridgeExplore
import Submission.ClippedRepairExplore

/-! Local cutoff bounds for the mixed-hit potential of a whole family of
packets. The target cutoff is z, not the farthest repair center. -/
namespace Erdos66JointWindow
open AdditiveCombinatorics Erdos66NaturalRepairBridge Erdos66ClippedRepair
  Erdos66LocalWindow Erdos66FiniteRepair Erdos66HeterogeneousSelection
open scoped Classical
set_option maxHeartbeats 1000000

lemma mem_intCutoff_congr (A : Set ℕ) (X Y : ℕ) (a : ℤ)
    (hX : a ≤ X) (hY : a ≤ Y) : a ∈ intCutoff A X ↔ a ∈ intCutoff A Y := by
  by_cases ha : 0 ≤ a
  · rw [← Int.toNat_of_nonneg ha, mem_intCutoff_nat, mem_intCutoff_nat]
    have hx : a.toNat ≤ X := by omega
    have hy : a.toNat ≤ Y := by omega
    simp only [hx, hy, true_and]
  · constructor <;> intro h <;> exact (ha (intCutoff_bounds h).1).elim

lemma forbidden_cutoff_eq {α : Type*} [Fintype α] (A : Set ℕ) (X n : ℕ)
    (x : α → ℤ) (hX : n ≤ X) (hx : ∀ a, 0 ≤ x a ∧ x a ≤ n) :
    forbidden (intCutoff A X) (n : ℤ) x = forbidden (intCutoff A n) (n : ℤ) x := by
  apply Finset.filter_congr
  intro a ha
  have hnX : (n : ℤ) ≤ X := by exact_mod_cast hX
  have h₁ := mem_intCutoff_congr A X n (x a) ((hx a).2.trans hnX) (hx a).2
  have h₂ := mem_intCutoff_congr A X n ((n : ℤ)-x a) (by have := hx a; omega) (by have := hx a; omega)
  exact or_congr h₁ h₂

lemma hit_cutoff_eq {α : Type*} [Fintype α] (A : Set ℕ) (X n z : ℕ)
    (x : α → ℤ) (hz : z ≤ X) (hx : ∀ a, 0 ≤ x a ∧ x a ≤ n) :
    hitChoices (intCutoff A X) (n : ℤ) x (z : ℤ) =
      hitChoices (intCutoff A z) (n : ℤ) x (z : ℤ) := by
  apply Finset.filter_congr
  intro a ha
  have hzX : (z : ℤ) ≤ X := by exact_mod_cast hz
  have h₁ := mem_intCutoff_congr A X z ((z : ℤ)-x a) (by have := hx a; omega) (by have := hx a; omega)
  have h₂ := mem_intCutoff_congr A X z ((z : ℤ)-((n : ℤ)-x a))
    (by have := hx a; omega) (by have := hx a; omega)
  exact or_congr h₁ h₂

noncomputable def envelopeCoeff (K C : ℝ) : ℝ := K / Real.log 2 + 2*C

lemma envelopeCoeff_nonneg {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) :
    0 ≤ envelopeCoeff K C := by
  exact add_nonneg (div_nonneg hK (Real.log_pos (by norm_num)).le) (mul_nonneg (by norm_num) hC)

lemma cutoff_log_bound {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (z : ℕ) :
    K + C * Real.log (2*(z : ℝ)+2) ≤ envelopeCoeff K C * logScale z := by
  have hz := Nat.cast_nonneg (α := ℝ) z
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hl : Real.log 2 ≤ logScale z := Real.log_le_log (by norm_num) (by linarith)
  have hkb := mul_le_mul_of_nonneg_left hl (div_nonneg hK hl2.le)
  rw [div_mul_cancel₀ K hl2.ne'] at hkb
  have harg : 2*(z : ℝ)+2 ≤ ((z : ℝ)+2)^2 := by nlinarith
  have hlog := Real.log_le_log (show 0 < 2*(z : ℝ)+2 by positivity) harg
  rw [Real.log_pow] at hlog
  have hc := mul_le_mul_of_nonneg_left hlog hC
  dsimp [envelopeCoeff, logScale] at *
  norm_num at hc
  nlinarith

lemma sqrt_choice_density (V : ℝ) (hV : 0 ≤ V) (q z : ℕ) :
    2 * Real.sqrt (2*(q : ℝ)*(V*logScale z)) / q =
      (2 * Real.sqrt (2*V)) * Real.sqrt (logScale z) * (1 / Real.sqrt q) := by
  have he : 2*(q : ℝ)*(V*logScale z) = ((2*V)*logScale z)*(q : ℝ) := by ring
  have hl := (logScale_pos z).le
  rw [he, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  have he' : 2 * (Real.sqrt (2*V)*Real.sqrt (logScale z)*Real.sqrt q) / q =
      (2*Real.sqrt (2*V)*Real.sqrt (logScale z)) * (Real.sqrt q / q) := by ring
  rw [he', Real.sqrt_div_self, one_div]

lemma local_choice_bounds {A : Set ℕ} {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hA : ∀ z, (sumRep A z : ℝ) ≤ K + C*logScale z)
    (X n q : ℕ) (a : ℤ) (hn : n ≤ X)
    (hx : ∀ b : Fin q, 0 ≤ a + (b.val : ℤ) ∧ a + (b.val : ℤ) ≤ n) :
    ((forbidden (intCutoff A X) (n : ℤ) (fun b : Fin q ↦ a + (b.val : ℤ))).card : ℝ) / q ≤
      (2 * Real.sqrt (2*envelopeCoeff K C)) * Real.sqrt (logScale n) * (1 / Real.sqrt q) ∧
    ∀ z : ℕ, z ≤ X →
      ((hitChoices (intCutoff A X) (n : ℤ) (fun b : Fin q ↦ a + (b.val : ℤ)) (z : ℤ)).card : ℝ) / q ≤
        (2 * Real.sqrt (2*envelopeCoeff K C)) * Real.sqrt (logScale z) * (1 / Real.sqrt q) := by
  have hbound (z : ℕ) (y : ℤ) :
      (Erdos66OriginRepair.pairCount (intCutoff A z) (intCutoff A z) y : ℝ) ≤
        envelopeCoeff K C * logScale z :=
    (intCutoff_uniform_bound hK hC hA z y).trans (cutoff_log_bound hK hC z)
  constructor
  · rw [forbidden_cutoff_eq A X n _ hn hx]
    have hh := (interval_choice_bounds (intCutoff A n) _ (hbound n) (n : ℤ) a q).1
    have hd := div_le_div_of_nonneg_right hh (Nat.cast_nonneg (α := ℝ) q)
    rw [sqrt_choice_density _ (envelopeCoeff_nonneg hK hC)] at hd
    exact hd
  · intro z hz
    rw [hit_cutoff_eq A X n z _ hz hx]
    have hh := (interval_choice_bounds (intCutoff A z) _ (hbound z) (n : ℤ) a q).2 (z : ℤ)
    have hd := div_le_div_of_nonneg_right hh (Nat.cast_nonneg (α := ℝ) q)
    rw [sqrt_choice_density _ (envelopeCoeff_nonneg hK hC)] at hd
    exact hd

/-- The whole mixed-hit mass is at most a common constant times sqrt(log z).
In particular this bound is independent of the largest repair center. -/
theorem joint_hitMass_bound {ι : Type*} [Fintype ι] {A : Set ℕ} {K C : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hA : ∀ z, (sumRep A z : ℝ) ≤ K+C*logScale z)
    (X : ℕ) (n q : ι → ℕ) (a : ι → ℤ) (hn : ∀ i, n i ≤ X)
    (hx : ∀ i (b : Fin (q i)), 0 ≤ a i + (b.val : ℤ) ∧ a i + (b.val : ℤ) ≤ n i)
    (z : ℕ) (hz : z ≤ X) :
    hitMass (fun i ↦ hitChoices (intCutoff A X) (n i : ℤ)
      (fun b : Fin (q i) ↦ a i + (b.val : ℤ)) (z : ℤ)) ≤
      ((2 * Real.sqrt (2*envelopeCoeff K C)) * (∑ i, 1 / Real.sqrt (q i : ℝ))) *
        Real.sqrt (logScale z) := by
  unfold hitMass
  simp only [Fintype.card_fin]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) ↦
    (local_choice_bounds hK hC hA X (n i) (q i) (a i) (hn i) (hx i)).2 z hz)
  apply hh.trans_eq
  rw [← Finset.mul_sum]
  ring

end Erdos66JointWindow
