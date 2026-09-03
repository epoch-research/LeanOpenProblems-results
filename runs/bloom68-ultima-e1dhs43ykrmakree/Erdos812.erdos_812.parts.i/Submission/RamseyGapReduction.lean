import FormalConjecturesUtil

/-!
# A conditional scalar gap reduction

A positive scalar sequence satisfying a truncated geometric lower recurrence
is eventually at least the truncation level. This file proves only a sufficient
condition: it neither establishes that condition for Ramsey numbers nor proves
the open Ramsey conjecture in `Submission/Spec.lean`.
-/

open Filter

namespace RamseyGapReduction

/-- Iterating the truncated recurrence from an arbitrary starting index. -/
lemma min_pow_mul_le (g : ℕ → ℝ) {δ q : ℝ} {K : ℕ}
    (hδ : 0 ≤ δ) (hq : 1 ≤ q)
    (hstep : ∀ k, K ≤ k → min δ (q * g k) ≤ g (k + 1)) (t : ℕ) :
    min δ (q ^ t * g K) ≤ g (K + t) := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hδq : δ ≤ q * δ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hq hδ
  induction t with
  | zero => simp
  | succ t ih =>
    calc
      min δ (q ^ (t + 1) * g K)
          ≤ min δ (q * min δ (q ^ t * g K)) := by
        refine le_min (min_le_left _ _) ?_
        rw [mul_min_of_nonneg _ _ hq0]
        apply min_le_min hδq
        rw [pow_succ]
        exact le_of_eq (by ring)
      _ ≤ min δ (q * g (K + t)) :=
        min_le_min_left δ (mul_le_mul_of_nonneg_left ih hq0)
      _ ≤ g (K + (t + 1)) := by
        simpa only [Nat.add_assoc] using hstep (K + t) (Nat.le_add_right K t)

/-- A positive initial value and a truncated geometric lower recurrence with
factor strictly greater than one suffice for an eventual uniform lower bound. -/
theorem eventually_ge_of_min_mul (g : ℕ → ℝ) {δ q : ℝ} {K : ℕ}
    (hδ : 0 < δ) (hq : 1 < q) (hgK : 0 < g K)
    (hstep : ∀ k, K ≤ k → min δ (q * g k) ≤ g (k + 1)) :
    ∀ᶠ k in atTop, δ ≤ g k := by
  have hpow : ∀ᶠ t : ℕ in atTop, δ ≤ q ^ t * g K :=
    ((tendsto_pow_atTop_atTop_of_one_lt hq).atTop_mul_const hgK).eventually_ge_atTop δ
  obtain ⟨T, hT⟩ := eventually_atTop.1 hpow
  apply eventually_atTop.2
  refine ⟨K + T, ?_⟩
  intro k hk
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le ((Nat.le_add_right K T).trans hk)
  have ht : T ≤ t := by omega
  have hi := min_pow_mul_le g hδ.le hq.le hstep t
  simpa only [min_eq_left (hT t ht)] using hi

/-- Dividing by a positive normalizing sequence reduces an eventual pair of
recurrences to the scalar condition, with geometric factor `a / C`.
The recurrence assumptions are hypotheses, not claims about Ramsey numbers. -/
theorem eventually_mul_le_of_min_recurrence (N D : ℕ → ℝ) {δ a C : ℝ}
    (hδ : 0 < δ) (hC : 0 < C) (hCa : C < a)
    (hN : ∀ k, 0 < N k) (hD : ∀ k, 0 < D k)
    (hNstep : ∀ᶠ k in atTop, N (k + 1) ≤ C * N k)
    (hDstep : ∀ᶠ k in atTop,
      min (δ * N (k + 1)) (a * D k) ≤ D (k + 1)) :
    ∀ᶠ k in atTop, δ * N k ≤ D k := by
  have ha : 0 < a := hC.trans hCa
  have hrstep : ∀ᶠ k in atTop,
      min δ ((a / C) * (D k / N k)) ≤ D (k + 1) / N (k + 1) := by
    filter_upwards [hNstep, hDstep] with k hNk hDk
    have hratio : (a / C) * (D k / N k) ≤ (a * D k) / N (k + 1) := by
      rw [div_mul_div_comm]
      exact div_le_div_of_nonneg_left (mul_pos ha (hD k)).le (hN (k + 1)) hNk
    calc
      min δ ((a / C) * (D k / N k))
          ≤ min δ ((a * D k) / N (k + 1)) := min_le_min_left δ hratio
      _ = min (δ * N (k + 1)) (a * D k) / N (k + 1) := by
        rw [← min_div_div_right (hN (k + 1)).le,
          mul_div_cancel_right₀ δ (hN (k + 1)).ne']
      _ ≤ D (k + 1) / N (k + 1) :=
        div_le_div_of_nonneg_right hDk (hN (k + 1)).le
  obtain ⟨K, hK⟩ := eventually_atTop.1 hrstep
  have hevent := eventually_ge_of_min_mul (fun k => D k / N k)
    hδ ((one_lt_div hC).2 hCa) (div_pos (hD K) (hN K)) hK
  filter_upwards [hevent] with k hk
  exact (le_div_iff₀ (hN k)).1 hk

/-- Below a smaller positive truncation, the fractional recurrence still
expands geometrically. No assertion about Ramsey numbers is made here. -/
lemma min_mul_le_min_frac {η δ a x : ℝ}
    (hη : 0 < η) (hηδ : η ≤ δ) (ha : 1 + η ≤ a) (hx : 0 ≤ x) :
    min η ((a / (1 + η)) * x) ≤ min δ (a * x / (1 + x)) := by
  have h1η : 0 < 1 + η := by linarith
  have h1x : 0 < 1 + x := by linarith
  have ha0 : 0 ≤ a := by linarith
  apply le_min ((min_le_left _ _).trans hηδ)
  apply (le_div_iff₀ h1x).2
  rcases le_total x η with h | h
  · calc
      min η (a / (1 + η) * x) * (1 + x)
          ≤ (a / (1 + η) * x) * (1 + x) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) h1x.le
      _ ≤ (a / (1 + η) * x) * (1 + η) :=
        mul_le_mul_of_nonneg_left (by linarith)
          (mul_nonneg (div_nonneg ha0 h1η.le) hx)
      _ = a * x := by field_simp
  · calc
      min η (a / (1 + η) * x) * (1 + x)
          ≤ η * (1 + x) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) h1x.le
      _ ≤ (1 + η) * x := by nlinarith
      _ ≤ a * x := mul_le_mul_of_nonneg_right ha hx

/-- A truncated fractional recurrence with multiplier greater than one
implies an eventual fixed positive lower bound. -/
theorem eventually_ge_of_min_frac (g : ℕ → ℝ) {δ a : ℝ}
    (hδ : 0 < δ) (ha : 1 < a) (hg : ∀ k, 0 < g k)
    (hstep : ∀ᶠ k in atTop, min δ (a * g k / (1 + g k)) ≤ g (k + 1)) :
    ∀ᶠ k in atTop, min δ ((a - 1) / 2) ≤ g k := by
  let η : ℝ := min δ ((a - 1) / 2)
  have hη : 0 < η := lt_min hδ (by linarith)
  have hηδ : η ≤ δ := min_le_left _ _
  have hηa : η ≤ (a - 1) / 2 := min_le_right _ _
  have h1η : 0 < 1 + η := by linarith
  have haq : 1 < a / (1 + η) := (one_lt_div h1η).2 (by linarith)
  have hstep' : ∀ᶠ k in atTop,
      min η ((a / (1 + η)) * g k) ≤ g (k + 1) := by
    filter_upwards [hstep] with k hk
    exact (min_mul_le_min_frac hη hηδ (by linarith) (hg k).le).trans hk
  obtain ⟨K, hK⟩ := eventually_atTop.1 hstep'
  exact eventually_ge_of_min_mul g hη haq (hg K) hK

/-- When `D` is the increment of `N`, a factor strictly greater than one
already suffices. Unlike the earlier normalization lemma, no upper bound on
consecutive ratios of `N` is required. The Ramsey-specific recurrence remains
an unproved hypothesis, not a conclusion of this theorem. -/
theorem eventually_mul_le_of_min_difference (N D : ℕ → ℝ) {δ a : ℝ}
    (hδ : 0 < δ) (ha : 1 < a)
    (hN : ∀ k, 0 < N k) (hD : ∀ k, 0 < D k)
    (hNstep : ∀ k, N (k + 1) = N k + D k)
    (hDstep : ∀ᶠ k in atTop,
      min (δ * N (k + 1)) (a * D k) ≤ D (k + 1)) :
    ∀ᶠ k in atTop, min δ ((a - 1) / 2) * N k ≤ D k := by
  have hrstep : ∀ᶠ k in atTop,
      min δ (a * (D k / N k) / (1 + D k / N k))
        ≤ D (k + 1) / N (k + 1) := by
    filter_upwards [hDstep] with k hk
    have heq : a * (D k / N k) / (1 + D k / N k)
        = (a * D k) / N (k + 1) := by
      rw [hNstep]
      field_simp [(hN k).ne']
    rw [heq]
    calc
      min δ ((a * D k) / N (k + 1))
          = min (δ * N (k + 1)) (a * D k) / N (k + 1) := by
        rw [← min_div_div_right (hN (k + 1)).le,
          mul_div_cancel_right₀ δ (hN (k + 1)).ne']
      _ ≤ D (k + 1) / N (k + 1) :=
        div_le_div_of_nonneg_right hk (hN (k + 1)).le
  have hevent := eventually_ge_of_min_frac (fun k => D k / N k)
    hδ ha (fun k => div_pos (hD k) (hN k)) hrstep
  filter_upwards [hevent] with k hk
  exact (le_div_iff₀ (hN k)).1 hk

/-- The sharp conditional difference reduction, stated as a ratio bound. -/
theorem eventually_ratio_gap_of_min_difference (N D : ℕ → ℝ) {δ a : ℝ}
    (hδ : 0 < δ) (ha : 1 < a)
    (hN : ∀ k, 0 < N k) (hD : ∀ k, 0 < D k)
    (hNstep : ∀ k, N (k + 1) = N k + D k)
    (hDstep : ∀ᶠ k in atTop,
      min (δ * N (k + 1)) (a * D k) ≤ D (k + 1)) :
    ∃ ε > 0, ∀ᶠ k in atTop, 1 + ε ≤ N (k + 1) / N k := by
  refine ⟨min δ ((a - 1) / 2), lt_min hδ (by linarith), ?_⟩
  filter_upwards [eventually_mul_le_of_min_difference N D hδ ha hN hD hNstep hDstep]
    with k hk
  rw [le_div_iff₀ (hN k), hNstep]
  nlinarith

end RamseyGapReduction

#print axioms RamseyGapReduction.eventually_mul_le_of_min_difference
#print axioms RamseyGapReduction.eventually_ratio_gap_of_min_difference
#print axioms RamseyGapReduction.min_mul_le_min_frac
#print axioms RamseyGapReduction.eventually_ge_of_min_frac
#print axioms RamseyGapReduction.min_pow_mul_le
#print axioms RamseyGapReduction.eventually_ge_of_min_mul
#print axioms RamseyGapReduction.eventually_mul_le_of_min_recurrence
