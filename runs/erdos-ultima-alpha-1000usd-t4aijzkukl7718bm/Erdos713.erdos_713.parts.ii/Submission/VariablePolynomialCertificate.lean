import FormalConjecturesUtil
import Submission.PolynomialRateCriterion

/-! Rationality from bounded-support integer polynomial certificates of
subpolynomial height. The certificate may vary with n. This is conditional:
no such certificates for graph extremal numbers are established here. -/

open Filter Asymptotics
open scoped Topology
namespace Erdos713VariablePolynomialCertificate
open Erdos713PolynomialRate
set_option maxHeartbeats 1000000

/-- A coefficient of subpolynomial growth cannot overcome a fixed negative
power gap. -/
lemma subpolynomial_mul_rpow_tendsto_zero {a : ℕ → ℝ} {d : ℝ} (hd : d < 0)
    (ha : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, |a n| ≤ (n : ℝ)^ε) :
    Tendsto (fun n : ℕ => a n*(n : ℝ)^d) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => (n : ℝ)^(d/2)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [neg_div,neg_neg] using
      (tendsto_rpow_neg_atTop (show 0 < -d/2 by linarith)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hlim
  filter_upwards [ha (-d/2) (by linarith),eventually_gt_atTop (0 : ℕ)] with n hn hnp
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnp
  rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg hnr.le d)]
  calc
    |a n| *(n : ℝ)^d ≤ (n : ℝ)^(-d/2)*(n : ℝ)^d :=
      mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hnr.le d)
    _ = (n : ℝ)^(d/2) := by rw [← Real.rpow_add hnr]; congr 1; ring

lemma variable_term_limit {f a : ℕ → ℝ} {α c β : ℝ} (p : ℕ × ℕ)
    (hf : Tendsto (fun n : ℕ => f n/(n : ℝ)^α) atTop (𝓝 c))
    (hp : weight α p < β)
    (ha : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, |a n| ≤ (n : ℝ)^ε) :
    Tendsto (fun n : ℕ => (a n*(n : ℝ)^p.1*(f n)^p.2)/(n : ℝ)^β)
      atTop (𝓝 0) := by
  have hm := (subpolynomial_mul_rpow_tendsto_zero (sub_neg.mpr hp) ha).mul (hf.pow p.2)
  simp only [zero_mul] at hm
  apply hm.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [normalized_monomial (a n) (f n) α β p (by exact_mod_cast hn)]
  ring

/-- A nonzero integer polynomial of fixed bounded support may change with n.
If its coefficients have subpolynomial height and it vanishes on a positive
pure-power sequence at arbitrarily large orders, the exponent is rational. -/
theorem rational_of_subpolynomial_certificates {f : ℕ → ℝ} {α c : ℝ}
    (hc : 0 < c) (hf : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α))
    (s : Finset (ℕ × ℕ)) (a : ℕ → (ℕ × ℕ) → ℤ)
    (ha : ∀ p ∈ s, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, |(a n p : ℝ)| ≤ (n : ℝ)^ε)
    (hz : ∃ᶠ n : ℕ in atTop,
      (∃ p ∈ s, a n p ≠ 0) ∧
      ∑ p ∈ s, (a n p : ℝ)*(n : ℝ)^p.1*(f n)^p.2 = 0) :
    α ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  by_contra hirr
  have hfreq : ∃ᶠ n : ℕ in atTop, ∃ t ∈ s.powerset,
      t.Nonempty ∧ (∀ p ∈ t, a n p ≠ 0) ∧
      ∑ p ∈ t, (a n p : ℝ)*(n : ℝ)^p.1*(f n)^p.2 = 0 := by
    apply hz.mono
    intro n hn
    let t := s.filter (fun p => a n p ≠ 0)
    have ht : t ⊆ s := Finset.filter_subset _ _
    refine ⟨t,Finset.mem_powerset.mpr ht,?_,?_,?_⟩
    · obtain ⟨p,hp,hap⟩ := hn.1
      exact ⟨p,Finset.mem_filter.mpr ⟨hp,hap⟩⟩
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
    · have he : (∑ p ∈ t, (a n p : ℝ)*(n : ℝ)^p.1*(f n)^p.2) =
          ∑ p ∈ s, (a n p : ℝ)*(n : ℝ)^p.1*(f n)^p.2 := by
        apply Finset.sum_subset ht
        intro p hp hpt
        have hap : a n p = 0 := by
          by_contra h
          exact hpt (Finset.mem_filter.mpr ⟨hp,h⟩)
        simp [hap]
      exact he.trans hn.2
  obtain ⟨t,ht,hfreq⟩ := (Filter.frequently_exists_finset s.powerset).mp hfreq
  have hts : t ⊆ s := Finset.mem_powerset.mp ht
  have htne : t.Nonempty := hfreq.exists.choose_spec.1
  obtain ⟨r,hr,hmax⟩ := t.exists_max_image (weight α) htne
  have hstrict (p : ℕ × ℕ) (hp : p ∈ t.erase r) : weight α p < weight α r := by
    obtain ⟨hne,hpt⟩ := Finset.mem_erase.mp hp
    exact lt_of_le_of_ne (hmax p hpt) (fun he => hne (weight_injective hirr he))
  let low : ℕ → ℝ := fun n => ∑ p ∈ t.erase r,
    (a n p : ℝ)*(n : ℝ)^p.1*(f n)^p.2/(n : ℝ)^(weight α r)
  let base : ℕ → ℝ := fun n =>
    (n : ℝ)^r.1*(f n)^r.2/(n : ℝ)^(weight α r)
  have hlow : Tendsto low atTop (𝓝 0) := by
    have hterms (p : ℕ × ℕ) (hp : p ∈ t.erase r) :=
      variable_term_limit p (ratio_limit hf) (hstrict p hp)
        (ha p (hts (Finset.mem_of_mem_erase hp)))
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum (t.erase r) hterms
  have hbase : Tendsto base atTop (𝓝 (c^r.2)) := by
    have hp : Tendsto (fun n : ℕ => (n : ℝ)^(weight α r-weight α r))
        atTop (𝓝 (1 : ℝ)) := by simp
    simpa only [one_mul,mul_one] using term_limit (1 : ℝ) r (ratio_limit hf) hp
  have hcpos : 0 < c^r.2 := pow_pos hc _
  have hlowSmall : ∀ᶠ n : ℕ in atTop, |low n| < c^r.2/2 := by
    have h := hlow.abs
    simp only [abs_zero] at h
    exact h.eventually_lt_const (by positivity)
  have hbaseLarge : ∀ᶠ n : ℕ in atTop, c^r.2/2 < base n :=
    hbase.eventually_const_lt (by linarith)
  obtain ⟨n,hn,hsmall,hlarge⟩ := (hfreq.and_eventually (hlowSmall.and hbaseLarge)).exists
  have hint : (1 : ℝ) ≤ |(a n r : ℝ)| := by
    exact_mod_cast Int.one_le_abs (hn.2.1 r hr)
  have he : low n+(a n r : ℝ)*base n = 0 := by
    have he : (∑ p ∈ t, (a n p : ℝ)*(n : ℝ)^p.1*(f n)^p.2)/
        (n : ℝ)^(weight α r) = 0 := by rw [hn.2.2,zero_div]
    rw [Finset.sum_div,← Finset.sum_erase_add _ _ hr] at he
    dsimp [low,base]
    convert he using 1; ring
  have hle : base n ≤ |low n| := by
    calc
      base n = 1*base n := by ring
      _ ≤ |(a n r : ℝ)| *base n :=
        mul_le_mul_of_nonneg_right hint (by linarith)
      _ = |(a n r : ℝ)*base n| := by
        rw [abs_mul,abs_of_pos (by linarith : 0 < base n)]
      _ = |low n| := by
        have hh : (a n r : ℝ)*base n = -low n := by linarith [he]
        rw [hh,abs_neg]
  exact (not_lt_of_ge (hlarge.le.trans hle)) hsmall

#print axioms subpolynomial_mul_rpow_tendsto_zero
#print axioms variable_term_limit
#print axioms rational_of_subpolynomial_certificates
end Erdos713VariablePolynomialCertificate
