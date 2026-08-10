import FormalConjectures.Util.ProblemImports
open Nat BigOperators Finset

-- Classic Wolstenholme: ∑_{t=1}^{p-1} 1/t ≡ 0 mod p^2 for p ≥ 5
-- Calibration attempt.
example (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (2 : ℤ) ≤ padicValRat p (∑ t ∈ Finset.Icc 1 (p-1), (1 / (t:ℚ))) := by
  sorry

-- Reusable atom: sum of x^k over ZMod p is 0 when (p-1) ∤ k (base case of generalized Wolstenholme)
theorem ZMod_sum_pow_eq_zero (p : ℕ) [Fact p.Prime] (k : ℕ) (h : ¬ (p-1) ∣ k) (hk : 0 < k) :
    ∑ x : ZMod p, x ^ k = 0 := by
  classical
  rw [← Finset.sum_sdiff (Finset.subset_univ ({0} : Finset (ZMod p))),
      Finset.sum_singleton, zero_pow hk.ne', add_zero]
  have hmap : Finset.univ.map (⟨(Units.val : (ZMod p)ˣ → ZMod p), Units.val_injective⟩)
      = Finset.univ \ {(0:ZMod p)} := by
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
      Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro ⟨u, rfl⟩; exact u.ne_zero
    · intro hx; exact ⟨(isUnit_iff_ne_zero.mpr hx).unit, IsUnit.unit_spec _⟩
  rw [← hmap, Finset.sum_map]
  have hsum := FiniteField.sum_pow_units (ZMod p) k
  rw [ZMod.card, if_neg h] at hsum
  simpa using hsum
