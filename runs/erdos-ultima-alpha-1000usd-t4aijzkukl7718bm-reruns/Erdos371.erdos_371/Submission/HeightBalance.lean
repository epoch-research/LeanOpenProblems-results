import FormalConjecturesUtil

/-! Finite counting consequences of a bounded real height function. -/

namespace Erdos371HeightBalance

open Finset
attribute [local instance] Classical.propDecidable

lemma one_side (h : ℕ → ℝ) (up far : ℕ → Prop) (N : ℕ) {H L : ℝ}
    (hL : 0 ≤ L) (hstep : ∀ n < N, h (n+1)-h n ≤ H)
    (hdown : ∀ n < N, ¬up n → h (n+1)-h n ≤ 0)
    (hfar : ∀ n < N, far n → ¬up n → h (n+1)-h n ≤ -L)
    (hboundary : -H ≤ h N-h 0) :
    L*((range N).filter far).card ≤ (H+L)*((range N).filter up).card+H := by
  have hp (n : ℕ) (hn : n ∈ range N) :
      L*(if far n then 1 else 0) ≤
        (H+L)*(if up n then 1 else 0)-(h (n+1)-h n) := by
    have hs := hstep n (mem_range.mp hn)
    by_cases hu : up n <;> by_cases hf : far n <;> simp only [hu,hf,if_true,if_false,mul_one,mul_zero]
    · linarith
    · linarith
    · have hh := hfar n (mem_range.mp hn) hf hu; linarith
    · have hh := hdown n (mem_range.mp hn) hu; linarith
  have hs := sum_le_sum hp
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum, sum_range_sub] at hs
  simp only [sum_boole] at hs
  linarith

/-- If many steps are large but the height stays bounded, both orientations
must occur. This does not force the two counts to be equal. -/
theorem two_sides (h : ℕ → ℝ) (up far : ℕ → Prop) (N : ℕ) {H L : ℝ}
    (hL : 0 ≤ L) (hstep : ∀ n < N, |h (n+1)-h n| ≤ H)
    (hmono : ∀ n < N, (up n → 0 ≤ h (n+1)-h n) ∧ (¬up n → h (n+1)-h n ≤ 0))
    (hfar : ∀ n < N, far n → L ≤ |h (n+1)-h n|)
    (hboundary : |h N-h 0| ≤ H) :
    L*((range N).filter far).card ≤ (H+L)*((range N).filter up).card+H ∧
    L*((range N).filter far).card ≤ (H+L)*((range N).filter fun n => ¬up n).card+H := by
  constructor
  · apply one_side h up far N hL (fun n hn => (abs_le.mp (hstep n hn)).2)
      (fun n hn hu => (hmono n hn).2 hu) _ (abs_le.mp hboundary).1
    intro n hn hf hu
    have hh := hfar n hn hf
    rw [abs_of_nonpos ((hmono n hn).2 hu)] at hh
    linarith
  · convert one_side (fun n => -h n) (fun n => ¬up n) far N (H := H) hL ?_ ?_ ?_ ?_ using 1
    · congr 3
      apply congrArg Finset.card
      ext n
      simp
    · intro n hn
      have hh := (abs_le.mp (hstep n hn)).1
      linarith
    · intro n hn hu
      have hh := (hmono n hn).1 (not_not.mp hu)
      linarith
    · intro n hn hf hu
      have hh := hfar n hn hf
      rw [abs_of_nonneg ((hmono n hn).1 (not_not.mp hu))] at hh
      linarith
    · have hh := (abs_le.mp hboundary).2
      linarith


end Erdos371HeightBalance

#print axioms Erdos371HeightBalance.two_sides
