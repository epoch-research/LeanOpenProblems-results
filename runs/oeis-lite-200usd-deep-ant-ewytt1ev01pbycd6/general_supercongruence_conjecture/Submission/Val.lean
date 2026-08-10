import Mathlib
open PowerSeries
namespace Val
open Finset

/-- Every nonzero coefficient of `f` has p-adic valuation `≥ β`. -/
def Vge (p : ℕ) (β : ℤ) (f : PowerSeries ℚ) : Prop :=
  ∀ k, PowerSeries.coeff k f ≠ 0 → β ≤ padicValRat p (PowerSeries.coeff k f)

/-- (V-extract) Extract the valuation bound for a single coefficient. -/
theorem Vge_coeff (p : ℕ) (β : ℤ) (f : PowerSeries ℚ) (hf : Vge p β f) (k : ℕ)
    (hk : PowerSeries.coeff k f ≠ 0) : β ≤ padicValRat p (PowerSeries.coeff k f) :=
  hf k hk

/-- (V-mono) Monotonicity in the bound. -/
theorem Vge_mono (p : ℕ) (β β' : ℤ) (h : β' ≤ β) (f : PowerSeries ℚ) (hf : Vge p β f) :
    Vge p β' f := by
  intro k hk
  exact le_trans h (hf k hk)

/-- (V-zero) The zero series satisfies any bound (vacuously). -/
theorem Vge_zero (p : ℕ) (β : ℤ) : Vge p β (0 : PowerSeries ℚ) := by
  intro k hk
  simp at hk

/-- (V-add) The bound is preserved under addition. -/
theorem Vge_add [Fact p.Prime] (β : ℤ) (f g : PowerSeries ℚ) (hf : Vge p β f)
    (hg : Vge p β g) : Vge p β (f + g) := by
  intro k hk
  rw [map_add] at hk ⊢
  by_cases haf : PowerSeries.coeff k f = 0
  · rw [haf, zero_add] at hk ⊢
    exact hg k hk
  · by_cases hag : PowerSeries.coeff k g = 0
    · rw [hag, add_zero] at hk ⊢
      exact hf k haf
    · calc β ≤ min (padicValRat p (PowerSeries.coeff k f))
                   (padicValRat p (PowerSeries.coeff k g)) :=
              le_min (hf k haf) (hg k hag)
        _ ≤ padicValRat p (PowerSeries.coeff k f + PowerSeries.coeff k g) :=
              padicValRat.min_le_padicValRat_add hk

/-- (V-sum) The bound is preserved under finite sums. -/
theorem Vge_sum [Fact p.Prime] (β : ℤ) {ι : Type*} (s : Finset ι)
    (F : ι → PowerSeries ℚ) (hF : ∀ i ∈ s, Vge p β (F i)) :
    Vge p β (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Vge_zero p β
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine Vge_add β _ _ (hF a (Finset.mem_insert_self a s)) ?_
    exact ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))

/-- Key reusable lemma: valuation bound for a finite sum of rationals. -/
theorem le_padicValRat_finsum [Fact p.Prime] (β : ℤ) {ι : Type*} (s : Finset ι)
    (F : ι → ℚ) (h : ∀ i ∈ s, F i ≠ 0 → β ≤ padicValRat p (F i))
    (hne : ∑ i ∈ s, F i ≠ 0) : β ≤ padicValRat p (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp at hne
  | insert a s ha ih =>
    rw [Finset.sum_insert ha] at hne ⊢
    by_cases hFa : F a = 0
    · rw [hFa, zero_add] at hne ⊢
      exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) hne
    · by_cases hS : (∑ i ∈ s, F i) = 0
      · rw [hS, add_zero] at hne ⊢
        exact h a (Finset.mem_insert_self a s) hFa
      · have hIH : β ≤ padicValRat p (∑ i ∈ s, F i) :=
          ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) hS
        calc β ≤ min (padicValRat p (F a)) (padicValRat p (∑ i ∈ s, F i)) :=
                le_min (h a (Finset.mem_insert_self a s) hFa) hIH
          _ ≤ padicValRat p (F a + ∑ i ∈ s, F i) :=
                padicValRat.min_le_padicValRat_add hne

/-- (V-mul) The bounds add under multiplication. -/
theorem Vge_mul [Fact p.Prime] (hp : 1 < p) (β γ : ℤ) (f g : PowerSeries ℚ)
    (hf : Vge p β f) (hg : Vge p γ g) : Vge p (β + γ) (f * g) := by
  classical
  intro k hk
  rw [PowerSeries.coeff_mul] at hk ⊢
  refine le_padicValRat_finsum (β + γ) (antidiagonal k)
    (fun ij => PowerSeries.coeff ij.1 f * PowerSeries.coeff ij.2 g) ?_ hk
  intro ij _ hij
  rw [mul_ne_zero_iff] at hij
  obtain ⟨h1, h2⟩ := hij
  rw [padicValRat.mul h1 h2]
  exact add_le_add (hf ij.1 h1) (hg ij.2 h2)

/-- (V-Up) The bound is preserved under the `Up` operation. -/
theorem Vge_Up (p : ℕ) (β : ℤ) (f : PowerSeries ℚ) (hf : Vge p β f) :
    Vge p β (PowerSeries.mk (fun k => PowerSeries.coeff (p * k) f)) := by
  intro k hk
  rw [PowerSeries.coeff_mk] at hk ⊢
  exact hf (p * k) hk

/-- (V-smul) Scaling by a nonzero rational shifts the bound. -/
theorem Vge_smul [Fact p.Prime] (β : ℤ) (c : ℚ) (hc : c ≠ 0) (f : PowerSeries ℚ)
    (hf : Vge p β f) : Vge p (padicValRat p c + β) (c • f) := by
  intro k hk
  rw [PowerSeries.coeff_smul, smul_eq_mul] at hk ⊢
  have hcoeff : PowerSeries.coeff k f ≠ 0 := by
    intro h; rw [h, mul_zero] at hk; exact hk rfl
  rw [padicValRat.mul hc hcoeff]
  have := hf k hcoeff
  omega

#print axioms Val.Vge_mul
#print axioms Val.Vge_add

end Val
