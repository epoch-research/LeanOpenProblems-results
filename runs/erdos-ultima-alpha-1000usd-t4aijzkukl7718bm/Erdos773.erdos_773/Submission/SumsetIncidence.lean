import FormalConjecturesUtil

/-! Two-path counting for finite bipartite incidence relations. -/
namespace Erdos773.SumsetIncidence
open Finset
set_option maxHeartbeats 1000000
noncomputable section

variable {α β : Type*}

/-- The number of incidences, counted in the first variable. -/
def incidenceCount (X : Finset α) (Y : Finset β) (R : α → β → Prop) [∀ x y, Decidable (R x y)] : ℕ :=
  ∑ x ∈ X, (Y.filter (R x)).card

lemma incidenceCount_comm (X : Finset α) (Y : Finset β) (R : α → β → Prop) [∀ x y, Decidable (R x y)] :
    incidenceCount X Y R = incidenceCount Y X (fun y x => R x y) := by
  classical
  simp only [incidenceCount, card_eq_sum_ones, sum_filter]
  exact sum_comm

lemma two_path_identity (X : Finset α) (Y : Finset β) (R : α → β → Prop) [∀ x y, Decidable (R x y)] :
    (∑ x ∈ X, ((Y.filter (R x)).card : ℝ)^2) =
      ∑ y ∈ Y, ∑ z ∈ Y, ((X.filter (fun x => R x y ∧ R x z)).card : ℝ) := by
  classical
  have hrow (x : α) : ((Y.filter (R x)).card : ℝ)^2 =
      ∑ y ∈ Y, ∑ z ∈ Y, if R x y ∧ R x z then (1:ℝ) else 0 := by
    simp only [ite_and]
    simp [sum_ite_irrel, ← sum_filter, sq]
  simp_rw [hrow]
  rw [sum_comm]
  apply sum_congr rfl
  intro y hy
  rw [sum_comm]
  apply sum_congr rfl
  intro z hz
  simp

/-- If each distinct pair of right vertices has at most K common neighbors,
    then the squared incidence count is bounded by the two-path count. -/
theorem incidence_sq_le (X : Finset α) (Y : Finset β) (R : α → β → Prop) [∀ x y, Decidable (R x y)]
    (K : ℝ) (hK : 0 ≤ K)
    (hcommon : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z →
      ((X.filter (fun x => R x y ∧ R x z)).card : ℝ) ≤ K) :
    (incidenceCount X Y R : ℝ)^2 ≤
      X.card * ((Y.card : ℝ)^2*K + incidenceCount X Y R) := by
  classical
  have hcs := sum_mul_sq_le_sq_mul_sq (R := ℝ) X
    (fun _ => (1:ℝ)) (fun x => ((Y.filter (R x)).card : ℝ))
  have hcs' : (incidenceCount X Y R : ℝ)^2 ≤
      X.card * ∑ x ∈ X, ((Y.filter (R x)).card : ℝ)^2 := by
    simpa [incidenceCount] using hcs
  apply hcs'.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg X.card)
  rw [two_path_identity]
  have hterm (y : β) (hy : y ∈ Y) (z : β) (hz : z ∈ Y) :
      ((X.filter (fun x => R x y ∧ R x z)).card : ℝ) ≤
        (if z = y then ((X.filter (fun x => R x y)).card : ℝ) else 0) + K := by
    by_cases he : y = z
    · subst z
      simp only [and_self, if_true]
      linarith
    · simpa [Ne.symm he] using hcommon y hy z hz he
  calc
    _ ≤ ∑ y ∈ Y, ∑ z ∈ Y,
        ((if z = y then ((X.filter (fun x => R x y)).card : ℝ) else 0) + K) := by
      exact sum_le_sum (fun y hy => sum_le_sum (fun z hz => hterm y hy z hz))
    _ = (Y.card : ℝ)^2*K + incidenceCount X Y R := by
      simp only [sum_add_distrib, sum_ite_eq', sum_const, nsmul_eq_mul]
      have he : (∑ y ∈ Y, if y ∈ Y then ((X.filter (fun x => R x y)).card : ℝ) else 0) =
          incidenceCount X Y R := by
        rw [incidenceCount_comm]
        simp [incidenceCount]
      rw [he]
      ring

/-- An explicit square-root consequence of the quadratic incidence bound. -/
theorem incidence_le (X : Finset α) (Y : Finset β) (R : α → β → Prop) [∀ x y, Decidable (R x y)]
    (K : ℝ) (hK : 0 ≤ K)
    (hcommon : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z →
      ((X.filter (fun x => R x y ∧ R x z)).card : ℝ) ≤ K) :
    (incidenceCount X Y R : ℝ) ≤ Y.card * Real.sqrt (X.card*K) + X.card := by
  have hsq := incidence_sq_le X Y R K hK hcommon
  have hr := Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg X.card) hK)
  have hr0 := Real.sqrt_nonneg (X.card*K)
  have hX := Nat.cast_nonneg (α := ℝ) X.card
  have hY := Nat.cast_nonneg (α := ℝ) Y.card
  have hE := Nat.cast_nonneg (α := ℝ) (incidenceCount X Y R)
  have hprod : 0 ≤ (Y.card : ℝ)*Real.sqrt (X.card*K) := mul_nonneg hY hr0
  have hb : ((Y.card : ℝ)*Real.sqrt (X.card*K))^2 = X.card*(Y.card : ℝ)^2*K := by
    rw [mul_pow,hr]
    ring
  by_contra! hn
  have ht : 0 < (incidenceCount X Y R : ℝ) - (Y.card*Real.sqrt (X.card*K)+X.card) := by
    linarith
  have hmul := mul_pos ht (show 0 < (incidenceCount X Y R : ℝ) +
      Y.card*Real.sqrt (X.card*K) by linarith)
  nlinarith [mul_nonneg hX hprod]

#print axioms incidence_sq_le
#print axioms incidence_le
end
end Erdos773.SumsetIncidence
