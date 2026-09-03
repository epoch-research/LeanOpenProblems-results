import Submission.CoreTailSieve
import Submission.PrimeSetMertens

/-! Power bounds for covers with a fixed multiplicity cap. The cap is NOT
part of the Jacobsthal conjecture; none of these theorems removes it. -/
namespace Erdos970.BoundedMultiplicity
open Finset Real
open CoreTailSieve WeightedMertens

/-- Every set of d+1 selected primes has product greater than the length of
an interval with no (d+1)-fold hit. -/
lemma product_gt_of_cap (P T : Finset ℕ) (r : ℕ → ℕ) (m d : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hTP : T ⊆ P) (hT : T.card = d+1)
    (hcap : ∀ x < m, (P.filter (fun p => x ≡ r p [MOD p])).card ≤ d) :
    m < ∏ p ∈ T, p := by
  classical
  have ht : ∀ p ∈ T, p ≠ 0 := fun p hp => (hP p (hTP hp)).ne_zero
  have hco : Set.Pairwise (↑T : Set ℕ) Nat.Coprime :=
    fun p hp q hq hpq => (Nat.coprime_primes (hP p (hTP hp)) (hP q (hTP hq))).mpr hpq
  let b := Nat.chineseRemainderOfFinset r id T ht hco
  have hb : b.val < ∏ p ∈ T, p := Nat.chineseRemainderOfFinset_lt_prod r id ht hco
  by_contra hn
  have hbm : b.val < m := by omega
  have hs : T ⊆ P.filter (fun p => b.val ≡ r p [MOD p]) :=
    fun p hp => mem_filter.mpr ⟨hTP hp, b.property p hp⟩
  have hh := (card_le_card hs).trans (hcap b.val hbm)
  omega

lemma small_core_card_le (P : Finset ℕ) (r : ℕ → ℕ) (m d : ℕ) (a : ℝ)
    (hP : ∀ p ∈ P, p.Prime)
    (hcap : ∀ x < m, (P.filter (fun p => x ≡ r p [MOD p])).card ≤ d)
    (ha : a^(d+1) ≤ (m : ℝ)) :
    (P.filter (fun p : ℕ => (p : ℝ) ≤ a)).card ≤ d := by
  classical
  by_contra hn
  obtain ⟨T, hTsub, hTcard⟩ := exists_subset_card_eq
    (show d+1 ≤ (P.filter (fun p : ℕ => (p : ℝ) ≤ a)).card by omega)
  have hTP : T ⊆ P := hTsub.trans (filter_subset _ _)
  have hprod := product_gt_of_cap P T r m d hP hTP hTcard hcap
  have hupper : (∏ p ∈ T, (p : ℝ)) ≤ a ^ (d+1) := by
    rw [← hTcard, ← prod_const]
    exact prod_le_prod (fun p hp => Nat.cast_nonneg p)
      (fun p hp => (mem_filter.mp (hTsub hp)).2)
  have hlower : (m : ℝ) < ∏ p ∈ T, (p : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast hprod
  linarith

/-- Uniformly small reciprocal tail beyond D*k^β, for every fixed
β with log(1/β)<1. The scale D depends on β, not on k or the prime set. -/
theorem exists_sparse_power_cutoff (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hlogβ : log (1/β) < 1) :
    ∃ D ε : ℝ, 2 ≤ D ∧ 0 < ε ∧
      ∀ k : ℕ, 0 < k → ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      (∑ p ∈ P.filter (fun p : ℕ => D*(k : ℝ)^β < (p : ℝ)), 1/(p : ℝ)) ≤ 1-ε := by
  let η : ℝ := (1-log (1/β))/4
  have hη : 0 < η := by dsimp [η]; linarith
  let D : ℝ := max 2 (max (1/η) (exp (2*(boundConstant+1)/η)))
  have hD2 : 2 ≤ D := le_max_left _ _
  have hDη : 1/η ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hDe : exp (2*(boundConstant+1)/η) ≤ D :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hD0 : 0 < D := by linarith
  have hlD : 2*(boundConstant+1)/η ≤ log D := by
    have hh := log_le_log (exp_pos _) hDe
    rwa [log_exp] at hh
  refine ⟨D, 2*η, hD2, by positivity, ?_⟩
  intro k hk P hP hPk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by positivity
  have hkp : (1 : ℝ) ≤ (k : ℝ)^β := one_le_rpow hk1 hβ.le
  have hkp1 : (k : ℝ)^β ≤ k := by
    simpa using rpow_le_rpow_of_exponent_le hk1 hβ1
  have ha : 2 ≤ D*(k : ℝ)^β := by nlinarith
  have hab : D*(k : ℝ)^β ≤ D*k := mul_le_mul_of_nonneg_left hkp1 hD0.le
  have hla : log (D*(k : ℝ)^β) = log D + β*log k := by
    rw [log_mul hD0.ne' (rpow_pos_of_pos hk0 _).ne', log_rpow hk0]
  have hlb : log (D*(k : ℝ)) = log D + log k := by
    rw [log_mul hD0.ne' hk0.ne']
  have hla0 : 0 < log (D*(k : ℝ)^β) := log_pos (by linarith)
  have hlb0 : 0 < log (D*(k : ℝ)) := log_pos (by linarith)
  have hlogD0 : 0 ≤ log D := log_nonneg (by linarith)
  have hlogk0 : 0 ≤ log (k : ℝ) := log_nonneg hk1
  have hratio : log (D*(k : ℝ)) / log (D*(k : ℝ)^β) ≤ 1/β := by
    apply (div_le_div_iff₀ hla0 hβ).mpr
    rw [hla, hlb]
    nlinarith only [mul_le_mul_of_nonneg_right hβ1 hlogD0]
  have hlogratio : log (log (D*(k : ℝ))) - log (log (D*(k : ℝ)^β)) ≤ log (1/β) := by
    rw [← log_div hlb0.ne' hla0.ne']
    exact log_le_log (div_pos hlb0 hla0) hratio
  have herr : 2*(boundConstant+1)/log (D*(k : ℝ)^β) ≤ η := by
    apply (div_le_iff₀ hla0).mpr
    have hh := (div_le_iff₀ hη).mp hlD
    rw [hla]
    nlinarith only [hh, mul_nonneg hη.le (mul_nonneg hβ.le hlogk0)]
  have hbudget : (P.card : ℝ)/(D*k) ≤ η := by
    apply (div_le_iff₀ (mul_pos hD0 hk0)).mpr
    have hh := (div_le_iff₀ hη).mp hDη
    have hhh := mul_le_mul_of_nonneg_right hh hk0.le
    have hc : (P.card : ℝ) ≤ k := by exact_mod_cast hPk
    nlinarith only [hhh, hc]
  have hh := prime_set_tail P hP ha hab
  simp only [one_div] at ⊢
  dsimp only [η] at *
  linarith

/-- A bounded core and a tail with a fixed reciprocal gap give a linear
bound. The entire exponential-in-core-size remainder is retained. -/
lemma core_tail_linear (P : Finset ℕ) (r : ℕ → ℕ) (m d : ℕ) (a ε : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hε : 0 < ε)
    (hcover : ∀ x < m, ∃ p ∈ P, x ≡ r p [MOD p])
    (hsmall : (P.filter (fun p : ℕ => (p : ℝ) ≤ a)).card ≤ d)
    (htail : (∑ p ∈ P.filter (fun p : ℕ => a < (p : ℝ)), 1/(p : ℝ)) ≤ 1-ε) :
    (m : ℝ) ≤ ((d : ℝ)+1)*(2 : ℝ)^d*((P.card : ℝ)+1)/ε := by
  classical
  let Q := P.filter (fun p : ℕ => (p : ℝ) ≤ a)
  let R := P.filter (fun p : ℕ => a < (p : ℝ))
  have hQR : Q ∪ R = P := by
    simpa only [Q, R, not_le] using filter_union_filter_not_eq (fun p : ℕ => (p : ℝ) ≤ a) P
  have hdis : Disjoint Q R := by
    apply disjoint_left.mpr
    intro p hp hq
    exact (mem_filter.mp hq).2.not_ge (mem_filter.mp hp).2
  have hc := cover_core_tail_bound Q R (fun p hp => hP p (mem_filter.mp hp).1)
    (fun p hp => hP p (mem_filter.mp hp).1) hdis r m (by simpa only [hQR] using hcover)
  have hden := (BrunCriterion.prime_product_bounds Q
    (fun p hp => hP p (mem_filter.mp hp).1)).1
  change 1/((Q.card : ℝ)+1) ≤ density Q at hden
  have hdR : (Q.card : ℝ) ≤ d := by exact_mod_cast hsmall
  have hden' : 1/((d : ℝ)+1) ≤ density Q :=
    (one_div_le_one_div_of_le (by positivity) (by linarith)).trans hden
  have hden0 : 0 ≤ density Q := (by positivity : (0 : ℝ) ≤ 1/((d : ℝ)+1)).trans hden'
  have ht : ε ≤ 1-∑ p ∈ R, 1/(p : ℝ) := by simpa only [R] using (by linarith : ε ≤ 1-∑ p ∈ P.filter (fun p : ℕ => a < (p : ℝ)), 1/(p : ℝ))
  have hp := mul_le_mul hden' ht hε.le hden0
  have hp' := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg m)
  have hpow : (2 : ℝ)^Q.card ≤ (2 : ℝ)^d := pow_le_pow_right₀ (by norm_num) hsmall
  have hRc : (R.card : ℝ) ≤ P.card := by exact_mod_cast card_filter_le P (fun p : ℕ => a < (p : ℝ))
  have hcost := mul_le_mul hpow (show (R.card : ℝ)+1 ≤ P.card+1 by linarith)
    (by positivity) (by positivity : (0 : ℝ) ≤ (2 : ℝ)^d)
  have hmain : (m : ℝ) / ((d : ℝ)+1) * ε ≤ (2 : ℝ)^d*((P.card : ℝ)+1) := by
    calc
      _ = (m : ℝ)*(1/((d : ℝ)+1)*ε) := by ring
      _ ≤ (m : ℝ)*(density Q*(1-∑ p ∈ R, 1/(p : ℝ))) := hp'
      _ = (m : ℝ)*density Q*(1-∑ p ∈ R, 1/(p : ℝ)) := by ring
      _ ≤ _ := hc.trans hcost
  have hmain' := mul_le_mul_of_nonneg_right hmain (show 0 ≤ (d : ℝ)+1 by positivity)
  have he : (m : ℝ)/((d : ℝ)+1)*ε*((d : ℝ)+1) = m*ε := by field_simp
  rw [he] at hmain'
  apply (le_div_iff₀ hε).mpr
  nlinarith only [hmain']

/-- A general restricted power theorem. The constant may depend on the fixed
multiplicity cap d and exponent β. No unrestricted assertion is made. -/
theorem exists_power_bound (d : ℕ) (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hlogβ : log (1/β) < 1) (hexp : 1 ≤ β*((d : ℝ)+1)) :
    ∃ C > (0 : ℝ), ∀ (P : Finset ℕ) (r : ℕ → ℕ) (m : ℕ),
      (∀ p ∈ P, p.Prime) →
      (∀ x < m, ∃ p ∈ P, x ≡ r p [MOD p]) →
      (∀ x < m, (P.filter (fun p => x ≡ r p [MOD p])).card ≤ d) →
      (m : ℝ) ≤ C*(P.card : ℝ)^(β*((d : ℝ)+1)) := by
  obtain ⟨D, ε, hD, hε, htail⟩ := exists_sparse_power_cutoff β hβ hβ1 hlogβ
  let A : ℝ := 2*((d : ℝ)+1)*(2 : ℝ)^d/ε
  have hA : 0 < A := by dsimp [A]; positivity
  have hDp : 0 < D^(d+1) := pow_pos (by linarith) _
  refine ⟨D^(d+1)+A, by positivity, ?_⟩
  intro P r m hP hcover hcap
  by_cases hm : m = 0
  · subst m
    simp only [Nat.cast_zero]
    positivity
  have hk : 0 < P.card := by
    obtain ⟨p, hp, _⟩ := hcover 0 (by omega)
    exact card_pos.mpr ⟨p,hp⟩
  have hk1 : (1 : ℝ) ≤ P.card := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  have hkpow : (P.card : ℝ) ≤ (P.card : ℝ)^(β*((d : ℝ)+1)) := by
    simpa using rpow_le_rpow_of_exponent_le hk1 hexp
  have he : (D*(P.card : ℝ)^β)^(d+1) =
      D^(d+1)*(P.card : ℝ)^(β*((d : ℝ)+1)) := by
    rw [mul_pow, ← rpow_mul_natCast hk0]
    simp only [Nat.cast_add, Nat.cast_one]
  by_cases hlarge : (D*(P.card : ℝ)^β)^(d+1) ≤ (m : ℝ)
  · have hsmall := small_core_card_le P r m d (D*(P.card : ℝ)^β) hP hcap hlarge
    have hc := core_tail_linear P r m d (D*(P.card : ℝ)^β) ε hP hε hcover hsmall
      (htail P.card hk P hP le_rfl)
    have hlinear : (m : ℝ) ≤ A*P.card := by
      apply hc.trans
      dsimp [A]
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hε.le
      have hsize : (P.card : ℝ)+1 ≤ 2*P.card := by linarith
      nlinarith only [mul_le_mul_of_nonneg_left hsize
        (show 0 ≤ ((d : ℝ)+1)*(2 : ℝ)^d by positivity)]
    have hh := hlinear.trans (mul_le_mul_of_nonneg_left hkpow hA.le)
    have hnon : 0 ≤ D^(d+1)*(P.card : ℝ)^(β*((d : ℝ)+1)) := by positivity
    nlinarith only [hh, hnon]
  · rw [he] at hlarge
    have hh := le_of_not_ge hlarge
    have hnon : 0 ≤ A*(P.card : ℝ)^(β*((d : ℝ)+1)) := by positivity
    nlinarith only [hh, hnon]

lemma log_eight_thirds_lt_one : log ((8 : ℝ)/3) < 1 := by
  have hh := sum_range_sub_log_div_le (x := (5/11 : ℝ)) (by norm_num) 6
  norm_num [sum_range_succ] at hh
  linarith [(abs_le.mp hh).2]

/-- Triple covers have length O(k^(3/2)), a restricted subquadratic estimate. -/
theorem triple_cover_three_halves :
    ∃ C > (0 : ℝ), ∀ (P : Finset ℕ) (r : ℕ → ℕ) (m : ℕ),
      (∀ p ∈ P, p.Prime) →
      (∀ x < m, ∃ p ∈ P, x ≡ r p [MOD p]) →
      (∀ x < m, (P.filter (fun p => x ≡ r p [MOD p])).card ≤ 3) →
      (m : ℝ) ≤ C*(P.card : ℝ)^(3/2 : ℝ) := by
  have hh := exists_power_bound 3 (3/8) (by norm_num) (by norm_num)
    (by norm_num; exact log_eight_thirds_lt_one) (by norm_num)
  norm_num at hh ⊢
  exact hh

/-- Covers of multiplicity at most four have length O(k^(15/8)). -/
theorem quadruple_cover_fifteen_eighths :
    ∃ C > (0 : ℝ), ∀ (P : Finset ℕ) (r : ℕ → ℕ) (m : ℕ),
      (∀ p ∈ P, p.Prime) →
      (∀ x < m, ∃ p ∈ P, x ≡ r p [MOD p]) →
      (∀ x < m, (P.filter (fun p => x ≡ r p [MOD p])).card ≤ 4) →
      (m : ℝ) ≤ C*(P.card : ℝ)^(15/8 : ℝ) := by
  have hh := exists_power_bound 4 (3/8) (by norm_num) (by norm_num)
    (by norm_num; exact log_eight_thirds_lt_one) (by norm_num)
  norm_num at hh ⊢
  exact hh

#print axioms exists_power_bound
#print axioms triple_cover_three_halves
#print axioms quadruple_cover_fifteen_eighths
end Erdos970.BoundedMultiplicity
