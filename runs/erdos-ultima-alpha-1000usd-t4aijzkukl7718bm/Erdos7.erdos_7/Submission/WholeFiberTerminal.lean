import Submission.RectangleBudgetTower

/-! Coverage-dependent terminal bounds on the last coordinate. These are
necessary conditions, not an unrestricted odd-covering obstruction. -/
namespace Erdos7WholeFiberTerminal
open scoped BigOperators
open Erdos7CompleteFamilyModel Erdos7BackwardFamilyBudget
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

variable {n : ℕ}
variable (A : Fin n → Type) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
  [∀ i, DecidableEq (A i)]
variable (E : Fin n → ℕ) (X : Pattern E → ∀ i, Finset (A i))

theorem last_fiber_covered (i : Fin n) (hi : i.val+1 = n)
    (x : ∀ i, A i)
    (havoid : ∀ j : Fin n, j.val < i.val → ¬ coveredAt A E X j x)
    (hcover : ∀ z, ∃ k : Pattern E, (∃ j, exponent E k j ≠ 0) ∧
      indicator A n (exponent E k) (X k) z = 1) :
    ∀ y : A i, currentBad A E X i.val i.isLt x y := by
  intro y
  obtain ⟨k,hk,hz⟩ := hcover (Function.update x i y)
  obtain ⟨j,hj⟩ := full_box_has_layer A E X k hk (Function.update x i y) hz
  by_cases hji : j = i
  · subst j
    exact (coveredAt_current_update A E X i x y).mp hj
  · have hlt : j.val < i.val := by
      have hjv := j.isLt
      have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
      omega
    exact False.elim (havoid j hlt ((coveredAt_later_update A E X j i hlt x y).mp hj))

theorem last_fiber_covered_of_positive (i : Fin n) (hi : i.val+1 = n)
    (μ : (∀ i, A i) → ℝ) (havoid : AvoidsBefore A E X i.val μ)
    (hcover : ∀ z, ∃ k : Pattern E, (∃ j, exponent E k j ≠ 0) ∧
      indicator A n (exponent E k) (X k) z = 1)
    (x : ∀ i, A i) (hx : 0 < μ x) :
    ∀ y : A i, currentBad A E X i.val i.isLt x y := by
  apply last_fiber_covered A E X i hi x _ hcover
  intro j hj hcov
  have hz := havoid j hj x hcov
  linarith

theorem count_lower_of_full_fiber (i : Fin n) (x : ∀ i, A i)
    (ρ : A i → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (hmass : (∑ y, ρ y) = 1)
    (r : ℕ → ℝ)
    (hd : ∀ k : Pattern E, exponent E k i ≠ 0 →
      (∑ y, if y ∈ X k i then ρ y else 0) ≤ r (exponent E k i-1))
    (hf : ∀ y : A i, currentBad A E X i.val i.isLt x y) :
    1 ≤ ∑ a : Fin (E i), r a.val * count A X (currentFamily E i.val i.isLt a) x := by
  have hh := currentBad_density A E X i.val i.isLt x ρ hρ r hd
  simpa only [hf, if_true, hmass] using hh

theorem padded_count_lower_of_full_fiber (i : Fin n) (x : ∀ i, A i)
    (ρ : A i → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (hmass : (∑ y, ρ y) = 1)
    (r : ℕ → ℝ)
    (hd : ∀ k : Pattern E, exponent E k i ≠ 0 →
      (∑ y, if y ∈ X k i then ρ y else 0) ≤ r (exponent E k i-1))
    (hf : ∀ y : A i, currentBad A E X i.val i.isLt x y)
    (q : ℝ) (hq : 0 ≤ q) :
    q + (1-∑ a : Fin (E i), q*r a.val) ≤
      currentCount A E X i.val i.isLt q r x := by
  have hh := mul_le_mul_of_nonneg_left
    (count_lower_of_full_fiber A E X i x ρ hρ hmass r hd hf) hq
  rw [mul_one, Finset.mul_sum] at hh
  dsimp only [currentCount]
  simp only [← mul_assoc] at hh
  linarith

lemma geometric_mass_exact (p : ℝ) (hp : p ≠ 0) (D : ℕ) :
    (∑ a : Fin D, (p-1)/p^(a.val+1)) = 1-1/p^D := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, pow_succ]
    field_simp
    ring

theorem geometric_padded_count_lower (i : Fin n) (x : ∀ i, A i)
    (p : ℝ) (hp : 1 < p)
    (ρ : A i → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (hmass : (∑ y, ρ y) = 1)
    (hd : ∀ k : Pattern E, exponent E k i ≠ 0 →
      (∑ y, if y ∈ X k i then ρ y else 0) ≤ 1/p^(exponent E k i))
    (hf : ∀ y : A i, currentBad A E X i.val i.isLt x y) :
    p-1+1/p^(E i) ≤ currentCount A E X i.val i.isLt (p-1)
      (fun a => 1/p^(a+1)) x := by
  have hh := padded_count_lower_of_full_fiber A E X i x ρ hρ hmass
    (fun a => 1/p^(a+1)) (fun k hk => by
      simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)] using hd k hk)
    hf (p-1) (by linarith)
  have he : (∑ a : Fin (E i), (p-1)*(1/p^(a.val+1))) = 1-1/p^(E i) := by
    simp only [mul_one_div]
    exact geometric_mass_exact p (by linarith) (E i)
  rw [he] at hh
  linarith

/-- An actual terminal family budget, before the last coordinate is processed.
Its count families remain separately indexed. -/
theorem last_fiber_budget (i : Fin n) (hi : i.val+1 = n)
    (μ : (∀ i, A i) → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (havoid : AvoidsBefore A E X i.val μ)
    (hcover : ∀ z, ∃ k : Pattern E, (∃ j, exponent E k j ≠ 0) ∧
      indicator A n (exponent E k) (X k) z = 1)
    (ρ : A i → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (hmass : (∑ y, ρ y) = 1)
    (r : ℕ → ℝ) (hr : ∀ a < E i, 0 ≤ r a)
    (hd : ∀ k : Pattern E, exponent E k i ≠ 0 →
      (∑ y, if y ∈ X k i then ρ y else 0) ≤ r (exponent E k i-1))
    (c : ℝ) (hc : 0 ≤ c) :
    HasBudget μ (count A X : Family E (exponent E) i.val → _)
      (fun t => 1-c+c*(∑ a : Fin (E i), r a.val)*t) 1 (capacity E i.val) := by
  refine ⟨Fin (E i), inferInstance, 1-c, currentFamily E i.val i.isLt,
    (fun a t => c*r a.val*t), ?_, ?_, ?_⟩
  · intro a
    have hw : 0 ≤ c*r a.val := mul_nonneg hc (hr a.val a.isLt)
    constructor
    · simpa only [smul_eq_mul] using (convexOn_id (convex_univ : Convex ℝ (Set.univ : Set ℝ))).smul hw
    · intro s t hst
      exact mul_le_mul_of_nonneg_left hst hw
  · intro t _
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  · apply Finset.sum_le_sum
    intro x _
    by_cases hx : μ x = 0
    · simp only [hx, zero_mul, le_refl]
    · have hpos : 0 < μ x := lt_of_le_of_ne (hμ x) (Ne.symm hx)
      have hf := last_fiber_covered_of_positive A E X i hi μ havoid hcover x hpos
      have hb := count_lower_of_full_fiber A E X i x ρ hρ hmass r hd hf
      have hm := mul_le_mul_of_nonneg_left hb hc
      have he : (∑ a : Fin (E i), c*r a.val*
          count A X (currentFamily E i.val i.isLt a) x) =
          c*(∑ a : Fin (E i), r a.val*
            count A X (currentFamily E i.val i.isLt a) x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      rw [he]
      have hcharge : 1 ≤ 1-c+c*(∑ a : Fin (E i), r a.val*
          count A X (currentFamily E i.val i.isLt a) x) := by linarith
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hcharge (hμ x)

/-- Finite geometric exponents give a positive correction to the limiting
last-coordinate affine budget. -/
theorem geometric_last_fiber_budget (i : Fin n) (hi : i.val+1 = n)
    (μ : (∀ i, A i) → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (havoid : AvoidsBefore A E X i.val μ)
    (hcover : ∀ z, ∃ k : Pattern E, (∃ j, exponent E k j ≠ 0) ∧
      indicator A n (exponent E k) (X k) z = 1)
    (p : ℝ) (hp : 1 < p)
    (ρ : A i → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (hmass : (∑ y, ρ y) = 1)
    (hd : ∀ k : Pattern E, exponent E k i ≠ 0 →
      (∑ y, if y ∈ X k i then ρ y else 0) ≤ 1/p^(exponent E k i))
    (ε : ℝ) (hε : 0 ≤ ε) :
    HasBudget μ (count A X : Family E (exponent E) i.val → _)
      (fun t => 1+ε*((1-1/p^(E i))*t-(p-1))) 1 (capacity E i.val) := by
  have hb := last_fiber_budget A E X i hi μ hμ havoid hcover ρ hρ hmass
    (fun a => 1/p^(a+1)) (fun _ _ => by positivity)
    (fun k hk => by
      simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)] using hd k hk)
    (ε*(p-1)) (mul_nonneg hε (by linarith))
  have he : (p-1)*(∑ a : Fin (E i), 1/p^(a.val+1)) = 1-1/p^(E i) := by
    rw [Finset.mul_sum]
    simp only [mul_one_div]
    exact geometric_mass_exact p (by linarith) (E i)
  convert hb using 1
  funext t
  rw [mul_assoc ε (p-1), he]
  ring

lemma finite_terminal_strict (p ε t : ℝ) (hp : 0 < p)
    (hε : 0 < ε) (ht : 0 < t) (D : ℕ) :
    1+ε*((1-1/p^D)*t-(p-1)) < 1+ε*(t-(p-1)) := by
  have hd : 0 < 1/p^D := by positivity
  nlinarith [mul_pos hd ht, mul_pos hε (mul_pos hd ht)]

#print axioms last_fiber_covered
#print axioms padded_count_lower_of_full_fiber
#print axioms geometric_mass_exact
#print axioms geometric_padded_count_lower
#print axioms last_fiber_budget
#print axioms geometric_last_fiber_budget
#print axioms finite_terminal_strict
end Erdos7WholeFiberTerminal
