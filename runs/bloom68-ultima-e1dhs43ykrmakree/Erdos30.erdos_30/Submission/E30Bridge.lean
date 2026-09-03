import FormalConjecturesUtil

/-!
# Conditional bridges for research on Erdős problem 30

These lemmas reduce failure of all positive-power error bounds to a family of
finite Sidon sets with polynomial excess. They do not construct such a family.
This file is independent of `Submission.Spec`.
-/

open Filter Asymptotics

namespace Erdos30Research

/-- The largest cardinality of a Sidon subset of `{1, ..., N}`. -/
def h (N : ℕ) : ℕ :=
  Finset.maxSidonSubsetCard (Finset.Icc 1 N)

/-- A Sidon subset is one of the terms in the defining finite supremum. -/
theorem sidon_card_le_maxSidonSubsetCard {α : Type*} [AddCommMonoid α] [DecidableEq α]
    {A B : Finset α} (hBA : B ⊆ A) (hB : IsSidon (B : Set α)) :
    B.card ≤ Finset.maxSidonSubsetCard A := by
  unfold Finset.maxSidonSubsetCard
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hBA, hB⟩)

/-- Every finite Sidon set in `{1, ..., N}` has at most `h N` elements. -/
theorem card_le_h {N : ℕ} {B : Finset ℕ}
    (hBN : B ⊆ Finset.Icc 1 N) (hB : IsSidon (B : Set ℕ)) :
    B.card ≤ h N :=
  sidon_card_le_maxSidonSubsetCard hBN hB

/-- An arbitrarily large positive lower bound of order `N^δ` rules out
an upper Big-O bound with any strictly smaller exponent. No sign assumption
on `f`, `δ`, or `ε` is needed. -/
theorem not_isBigO_rpow_of_arbitrarily_large {f : ℕ → ℝ} {δ ε c : ℝ}
    (hc : 0 < c) (hεδ : ε < δ)
    (hlower : ∀ M : ℕ, ∃ N ≥ M, c * (N : ℝ) ^ δ ≤ f N) :
    ¬ f =O[atTop] (fun N : ℕ => (N : ℝ) ^ ε) := by
  intro hO
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hO
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ (δ - ε)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hεδ)).comp tendsto_natCast_atTop_atTop
  have hpow : ∀ᶠ N : ℕ in atTop, C / c < (N : ℝ) ^ (δ - ε) :=
    hlim.eventually (eventually_gt_atTop (C / c))
  have hsmall : ∀ᶠ N : ℕ in atTop, f N < c * (N : ℝ) ^ δ := by
    filter_upwards [hC, hpow, eventually_ge_atTop 1] with N hCN hpowN hN
    have hNpos : (0 : ℝ) < N := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hlt : C < c * (N : ℝ) ^ (δ - ε) := by
      simpa only [mul_comm] using (div_lt_iff₀ hc).mp hpowN
    have hbound : f N ≤ C * (N : ℝ) ^ ε := by
      exact (le_abs_self (f N)).trans (by
        simpa only [Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) ε)] using hCN)
    calc
      f N ≤ C * (N : ℝ) ^ ε := hbound
      _ < (c * (N : ℝ) ^ (δ - ε)) * (N : ℝ) ^ ε :=
        mul_lt_mul_of_pos_right hlt (Real.rpow_pos_of_pos hNpos ε)
      _ = c * (N : ℝ) ^ δ := by
        rw [mul_assoc, ← Real.rpow_add hNpos, sub_add_cancel]
  obtain ⟨M, hM⟩ := eventually_atTop.mp hsmall
  obtain ⟨N, hMN, hN⟩ := hlower M
  exact (not_le_of_gt (hM N hMN)) hN

/-- Abstract analytic criterion for failure of all positive-power Big-O bounds. -/
theorem not_forall_isBigO_rpow_of_polynomial_lower_bound {f : ℕ → ℝ}
    (hlower : ∃ δ : ℝ, 0 < δ ∧ ∃ c : ℝ, 0 < c ∧
      ∀ M : ℕ, ∃ N ≥ M, c * (N : ℝ) ^ δ ≤ f N) :
    ¬ (∀ ε : ℝ, 0 < ε → f =O[atTop] (fun N : ℕ => (N : ℝ) ^ ε)) := by
  obtain ⟨δ, hδ, c, hc, hlarge⟩ := hlower
  intro hO
  exact not_isBigO_rpow_of_arbitrarily_large hc (by linarith : δ / 2 < δ)
    hlarge (hO (δ / 2) (by linarith))

/-- It suffices to construct finite Sidon sets with a fixed positive-power
excess at arbitrarily large endpoints. This is a conditional criterion, not
an existence theorem for such sets. -/
theorem not_all_power_bounds_of_polynomial_excess
    (hexcess : ∃ δ : ℝ, 0 < δ ∧ ∃ c : ℝ, 0 < c ∧
      ∀ M : ℕ, ∃ N ≥ M, ∃ B : Finset ℕ,
        B ⊆ Finset.Icc 1 N ∧ IsSidon (B : Set ℕ) ∧
        c * (N : ℝ) ^ δ ≤ (B.card : ℝ) - Real.sqrt (N : ℝ)) :
    ¬ (∀ ε : ℝ, 0 < ε →
      (fun N : ℕ => (h N : ℝ) - Real.sqrt (N : ℝ)) =O[atTop]
        (fun N : ℕ => (N : ℝ) ^ ε)) := by
  apply not_forall_isBigO_rpow_of_polynomial_lower_bound
  obtain ⟨δ, hδ, c, hc, hlarge⟩ := hexcess
  refine ⟨δ, hδ, c, hc, fun M => ?_⟩
  obtain ⟨N, hMN, B, hBN, hB, hBexcess⟩ := hlarge M
  refine ⟨N, hMN, hBexcess.trans ?_⟩
  exact sub_le_sub_right (by exact_mod_cast card_le_h hBN hB) _

/-- Containment in `{1, ..., N}` bounds cardinality by the endpoint, without
any Sidon assumption. This supplies endpoint growth for the diameter criterion. -/
theorem card_le_endpoint {N : ℕ} {B : Finset ℕ}
    (hBN : B ⊆ Finset.Icc 1 N) : B.card ≤ N := by
  simpa using Finset.card_le_card hBN

/-- A saving of `c * k^(1+α)` below `k²` gives an excess of at least
`(c/2) * x^(α/2)` above `sqrt x`. The saving is a real inequality, so no
truncated natural subtraction is involved. Nonnegativity of `c` implies
`x ≤ k²`; positivity of `k` allows cancellation of a factor of `k`. -/
theorem sqrt_excess_of_diameter_saving {k x c α : ℝ}
    (hk : 0 < k) (hx : 0 ≤ x) (hc : 0 ≤ c) (hα : 0 ≤ α)
    (hsave : x ≤ k ^ 2 - c * k ^ (1 + α)) :
    (c / 2) * x ^ (α / 2) ≤ k - Real.sqrt x := by
  have hxk : x ≤ k ^ 2 :=
    hsave.trans (sub_le_self _ (mul_nonneg hc (Real.rpow_nonneg hk.le _)))
  have hfactor : k ^ (1 + α) = k * k ^ α := by
    rw [Real.rpow_add hk, Real.rpow_one]
  have hhalf : (c / 2) * k ^ α ≤ k - Real.sqrt x := by
    apply (mul_le_mul_iff_right₀ hk).mp
    rw [hfactor] at hsave
    nlinarith only [hsave, Real.sq_sqrt hx, sq_nonneg (k - Real.sqrt x)]
  have hexp : x ^ (α / 2) ≤ k ^ α := by
    calc
      x ^ (α / 2) ≤ (k ^ 2) ^ (α / 2) :=
        Real.rpow_le_rpow hx hxk (by positivity)
      _ = k ^ α := by
        rw [← Real.rpow_natCast_mul hk.le]
        congr 1
        ring
  exact (mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ c / 2)).trans hhalf

/-- Arbitrarily large cardinality parameters give arbitrarily large endpoints:
`k ≤ B.card ≤ N`. Taking `k ≥ 1` also provides the positivity required by
`sqrt_excess_of_diameter_saving`. Thus no independent growth assumption on
`N` and no separate assumption `N ≤ k²` are needed. -/
theorem polynomial_excess_family_of_diameter_saving {α c : ℝ}
    (hα : 0 ≤ α) (hc : 0 ≤ c)
    (hfamily : ∀ K : ℕ, ∃ k ≥ K, ∃ N : ℕ, ∃ B : Finset ℕ,
      B ⊆ Finset.Icc 1 N ∧ IsSidon (B : Set ℕ) ∧ k ≤ B.card ∧
      (N : ℝ) ≤ (k : ℝ) ^ 2 - c * (k : ℝ) ^ (1 + α)) :
    ∀ M : ℕ, ∃ N ≥ M, ∃ B : Finset ℕ,
      B ⊆ Finset.Icc 1 N ∧ IsSidon (B : Set ℕ) ∧
      (c / 2) * (N : ℝ) ^ (α / 2) ≤ (B.card : ℝ) - Real.sqrt (N : ℝ) := by
  intro M
  obtain ⟨k, hk, N, B, hBN, hB, hkB, hsave⟩ := hfamily (max M 1)
  have hkpos : 0 < k :=
    lt_of_lt_of_le Nat.zero_lt_one ((le_max_right M 1).trans hk)
  have hkN : k ≤ N := hkB.trans (card_le_endpoint hBN)
  refine ⟨N, (le_max_left M 1).trans (hk.trans hkN), B, hBN, hB, ?_⟩
  calc
    (c / 2) * (N : ℝ) ^ (α / 2) ≤ (k : ℝ) - Real.sqrt (N : ℝ) :=
      sqrt_excess_of_diameter_saving (by exact_mod_cast hkpos)
        (Nat.cast_nonneg N) hc hα hsave
    _ ≤ (B.card : ℝ) - Real.sqrt (N : ℝ) :=
      sub_le_sub_right (by exact_mod_cast hkB) _

/-- A conditional diameter-saving route to failure of all positive-power error
bounds. The family must have unbounded `k` and at least `k` points, with fixed
`α > 0` and `c > 0`. It produces polynomial excess with exponent `α/2` and
constant `c/2`. Constructing such a family is a separate mathematical task. -/
theorem not_all_power_bounds_of_diameter_saving {α c : ℝ}
    (hα : 0 < α) (hc : 0 < c)
    (hfamily : ∀ K : ℕ, ∃ k ≥ K, ∃ N : ℕ, ∃ B : Finset ℕ,
      B ⊆ Finset.Icc 1 N ∧ IsSidon (B : Set ℕ) ∧ k ≤ B.card ∧
      (N : ℝ) ≤ (k : ℝ) ^ 2 - c * (k : ℝ) ^ (1 + α)) :
    ¬ (∀ ε : ℝ, 0 < ε →
      (fun N : ℕ => (h N : ℝ) - Real.sqrt (N : ℝ)) =O[atTop]
        (fun N : ℕ => (N : ℝ) ^ ε)) := by
  apply not_all_power_bounds_of_polynomial_excess
  exact ⟨α / 2, by positivity, c / 2, by positivity,
    polynomial_excess_family_of_diameter_saving hα.le hc.le hfamily⟩

end Erdos30Research
