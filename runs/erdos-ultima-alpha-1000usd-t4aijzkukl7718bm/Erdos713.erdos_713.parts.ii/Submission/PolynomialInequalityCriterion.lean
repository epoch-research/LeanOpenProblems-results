import FormalConjecturesUtil
import Submission.PolynomialRateCriterion

/-! Finite polynomial inequalities force rational growth when the relaxation
is sharp up to a constant factor. This is a conditional criterion only: no
finite sharp relaxation for arbitrary graph extremal numbers is asserted. -/
open Filter Asymptotics
open scoped Topology
namespace Erdos713PolynomialInequality
open Erdos713PolynomialRate

noncomputable def eval (s : Finset (ℕ × ℕ)) (a : (ℕ × ℕ) → ℝ)
    (x y : ℝ) : ℝ := ∑ p ∈ s, a p*x^p.1*y^p.2

lemma leading_term_limit {f : ℕ → ℝ} {α c : ℝ}
    (hf : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α))
    (s : Finset (ℕ × ℕ)) (a : (ℕ × ℕ) → ℝ) {r : ℕ × ℕ}
    (hr : r ∈ s) (hmax : ∀ p ∈ s, p ≠ r → weight α p < weight α r) :
    Tendsto (fun n : ℕ => eval s a n (f n)/(n : ℝ)^(weight α r))
      atTop (𝓝 (a r*c^r.2)) := by
  classical
  have hlim := ratio_limit hf
  have hterms (p : ℕ × ℕ) (hp : p ∈ s) :
      Tendsto (fun n : ℕ => (a p*(n : ℝ)^p.1*(f n)^p.2)/(n : ℝ)^(weight α r))
        atTop (𝓝 (if p = r then a r*c^r.2 else 0)) := by
    by_cases he : p = r
    · subst p
      simp only [ite_true]
      have hh : Tendsto (fun n : ℕ => (n : ℝ)^(weight α r-weight α r))
          atTop (𝓝 (1 : ℝ)) := by simp
      simpa using term_limit (a r) r hlim hh
    · simp only [if_neg he]
      have hh : Tendsto (fun n : ℕ => (n : ℝ)^(weight α p-weight α r))
          atTop (𝓝 (0 : ℝ)) := by
        simpa only [neg_sub] using
          (tendsto_rpow_neg_atTop (sub_pos.mpr (hmax p hp he))).comp
            (tendsto_natCast_atTop_atTop (R := ℝ))
      simpa using term_limit (a p) p hlim hh
  simpa only [eval, Finset.sum_div, Finset.sum_ite_eq', hr, if_true] using
    tendsto_finset_sum s hterms

lemma leading_coefficient_pos {f : ℕ → ℝ} {α c : ℝ} (hc : 0 < c)
    (hf : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α))
    (s : Finset (ℕ × ℕ)) (a : (ℕ × ℕ) → ℝ) {r : ℕ × ℕ}
    (hr : r ∈ s) (ha : a r ≠ 0)
    (hmax : ∀ p ∈ s, p ≠ r → weight α p < weight α r)
    (hfeas : ∀ᶠ n : ℕ in atTop, 0 ≤ eval s a n (f n)) : 0 < a r := by
  have hlim := leading_term_limit hf s a hr hmax
  have hnonneg : 0 ≤ a r*c^r.2 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim (by
    filter_upwards [hfeas] with n hn
    exact div_nonneg hn (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  have : 0 ≤ a r := (mul_nonneg_iff_of_pos_right (pow_pos hc _)).mp hnonneg
  exact lt_of_le_of_ne this (Ne.symm ha)

lemma eventually_pos_of_leading_coefficient {f : ℕ → ℝ} {α c : ℝ} (hc : 0 < c)
    (hf : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α))
    (s : Finset (ℕ × ℕ)) (a : (ℕ × ℕ) → ℝ) {r : ℕ × ℕ}
    (hr : r ∈ s) (ha : 0 < a r)
    (hmax : ∀ p ∈ s, p ≠ r → weight α p < weight α r) :
    ∀ᶠ n : ℕ in atTop, 0 < eval s a n (f n) := by
  have hlim := leading_term_limit hf s a hr hmax
  filter_upwards [hlim.eventually_const_lt (mul_pos ha (pow_pos hc _)),
    eventually_gt_atTop (0 : ℕ)] with n hn hnp
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnp
  exact (div_pos_iff_of_pos_right (Real.rpow_pos_of_pos hnr _)).mp hn

/-- The finitely many strict leading-term comparisons persist after increasing
an irrational exponent slightly. -/
lemma exists_larger_exponent {I : Type*} [Fintype I] {α : ℝ}
    (hα : α ∉ Set.range ((↑) : ℚ → ℝ))
    (s : I → Finset (ℕ × ℕ)) (hs : ∀ i, (s i).Nonempty) :
    ∃ (r : I → ℕ × ℕ) (β : ℝ), α < β ∧
      (∀ i, r i ∈ s i) ∧
      (∀ i p, p ∈ s i → p ≠ r i → weight α p < weight α (r i)) ∧
      (∀ i p, p ∈ s i → p ≠ r i → weight β p < weight β (r i)) := by
  classical
  choose r hr hmax using fun i => (s i).exists_max_image (weight α) (hs i)
  have hstrict : ∀ i p, p ∈ s i → p ≠ r i → weight α p < weight α (r i) := by
    intro i p hp hne
    exact lt_of_le_of_ne (hmax i p hp) (fun he => hne (weight_injective hα he))
  have hloc : ∀ᶠ β : ℝ in 𝓝 α,
      ∀ i p, p ∈ s i → p ≠ r i → weight β p < weight β (r i) := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all_finset]
    intro p hp
    by_cases he : p = r i
    · exact Filter.Eventually.of_forall (fun _ hne => (hne he).elim)
    have hcont (t : ℕ × ℕ) : Continuous (fun β : ℝ => weight β t) := by
      dsimp [weight]
      fun_prop
    filter_upwards [(hcont p).continuousAt.tendsto.eventually_lt
      (hcont (r i)).continuousAt.tendsto (hstrict i p hp he)] with β hβ _
    exact hβ
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hloc
  refine ⟨r,α+ε/2,by linarith,hr,hstrict,hball ?_⟩
  rw [Real.dist_eq]
  have he : α+ε/2-α = ε/2 := by ring
  rw [he,abs_of_pos (by positivity : 0 < ε/2)]
  linarith

lemma floor_rpow_asymptotic {β : ℝ} (hβ : 0 < β) :
    (fun n : ℕ => (⌊(n : ℝ)^β⌋₊ : ℝ)) ~[atTop]
      (fun n : ℕ => (1 : ℝ)*(n : ℝ)^β) := by
  simpa using isEquivalent_nat_floor.comp_tendsto
    ((tendsto_rpow_atTop hβ).comp (tendsto_natCast_atTop_atTop (R := ℝ)))

lemma eventually_floor_rpow_gt {f : ℕ → ℝ} {α β c : ℝ}
    (hf : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α))
    (hαβ : α < β) (hβ : 0 < β) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, K*f n < (⌊(n : ℝ)^β⌋₊ : ℝ) := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ)^(weight α (0,1)-β))
      atTop (𝓝 (0 : ℝ)) := by
    simpa [weight,neg_sub] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hαβ)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hfβ : Tendsto (fun n : ℕ => f n/(n : ℝ)^β) atTop (𝓝 (0 : ℝ)) := by
    simpa using term_limit (1 : ℝ) (0,1) (ratio_limit hf) hpow
  have hK : Tendsto (fun n : ℕ => K*f n/(n : ℝ)^β) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, mul_div_assoc] using hfβ.const_mul K
  have hg := ratio_limit (floor_rpow_asymptotic hβ)
  filter_upwards [hK.eventually_lt_const (by norm_num : (0 : ℝ) < 1/2),
    hg.eventually_const_lt (by norm_num : (1/2 : ℝ) < 1),
    eventually_gt_atTop (0 : ℕ)] with n hnK hng hnp
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnp
  exact (div_lt_div_iff_of_pos_right (Real.rpow_pos_of_pos hnr β)).mp (hnK.trans hng)

/-- At an irrational pure-power exponent, finitely many polynomial
inequalities admitting f also admit an integer-valued sequence of strictly
larger exponent. This is a limitation on a finite relaxation, not a claim
that the larger sequence can be realized by graphs. -/
theorem exists_feasible_larger_power {I : Type*} [Fintype I]
    {f : ℕ → ℕ} {α c : ℝ} (hα : 0 < α) (hc : 0 < c)
    (hf : (fun n => (f n : ℝ)) ~[atTop] (fun n : ℕ => c*(n : ℝ)^α))
    (hirr : α ∉ Set.range ((↑) : ℚ → ℝ))
    (s : I → Finset (ℕ × ℕ)) (hs : ∀ i, (s i).Nonempty)
    (a : I → (ℕ × ℕ) → ℝ) (ha : ∀ i p, p ∈ s i → a i p ≠ 0)
    (hfeas : ∀ i, ∀ᶠ n : ℕ in atTop, 0 ≤ eval (s i) (a i) n (f n)) :
    ∃ β : ℝ, α < β ∧
      (∀ᶠ n : ℕ in atTop, ∀ i,
        0 ≤ eval (s i) (a i) n (⌊(n : ℝ)^β⌋₊ : ℝ)) ∧
      (∀ K : ℝ, ∀ᶠ n : ℕ in atTop, K*f n < (⌊(n : ℝ)^β⌋₊ : ℝ)) := by
  classical
  obtain ⟨r,β,hαβ,hr,hmaxα,hmaxβ⟩ := exists_larger_exponent hirr s hs
  have hβ : 0 < β := hα.trans hαβ
  have hcoeff (i : I) : 0 < a i (r i) :=
    leading_coefficient_pos hc hf (s i) (a i) (hr i) (ha i _ (hr i))
      (hmaxα i) (hfeas i)
  refine ⟨β,hαβ,?_,eventually_floor_rpow_gt hf hαβ hβ⟩
  rw [Filter.eventually_all]
  intro i
  exact (eventually_pos_of_leading_coefficient (by norm_num : (0 : ℝ) < 1)
    (floor_rpow_asymptotic hβ) (s i) (a i) (hr i) (hcoeff i)
      (hmaxβ i)).mono (fun _ hn => hn.le)

/-- A fixed finite polynomial relaxation of an integer optimization problem,
sharp up to a constant factor, forces any positive pure-power exponent to be
rational. Both feasibility of f and the upper bound on every feasible integer
are substantive hypotheses. -/
theorem rational_of_finite_sharp_relaxation {I : Type*} [Fintype I]
    {f : ℕ → ℕ} {α c : ℝ} (hα : 0 < α) (hc : 0 < c)
    (hf : (fun n => (f n : ℝ)) ~[atTop] (fun n : ℕ => c*(n : ℝ)^α))
    (s : I → Finset (ℕ × ℕ)) (hs : ∀ i, (s i).Nonempty)
    (a : I → (ℕ × ℕ) → ℝ) (ha : ∀ i p, p ∈ s i → a i p ≠ 0)
    (hfeas : ∀ i, ∀ᶠ n : ℕ in atTop, 0 ≤ eval (s i) (a i) n (f n))
    (K : ℝ)
    (hsharp : ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      (∀ i, 0 ≤ eval (s i) (a i) n m) → (m : ℝ) ≤ K*f n) :
    α ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  by_contra hirr
  obtain ⟨β,_hαβ,hg,hgt⟩ := exists_feasible_larger_power hα hc hf hirr s hs a ha hfeas
  obtain ⟨n,hnsharp,hng,hngt⟩ := (hsharp.and (hg.and (hgt K))).exists
  exact (not_lt_of_ge (hnsharp _ hng)) hngt

#print axioms exists_feasible_larger_power
#print axioms rational_of_finite_sharp_relaxation
end Erdos713PolynomialInequality
