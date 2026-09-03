import Submission.CompactPrimePool

/-!
# Polynomial logarithmic-weight bounds for finite prime pools

A weighted support count bounds any finite totient fiber inside a specified
prime pool. Polynomial-size fibers require pool weight exceeding every
power of log n below 1/(1-alpha). This is a necessary support condition,
not an increase of the multiplicity exponent.
-/

open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821.LogarithmicOverlap
set_option maxHeartbeats 2000000

lemma finite_fiber_weight_le_pool_product (F P : Finset ℕ) (n : ℕ) (hn : 0 < n)
    (hF : ∀ a ∈ F, totient a = n ∧ a.primeFactors ⊆ P)
    (s : ℝ) (hs : 0 ≤ s) :
    (F.card : ℝ)*(n : ℝ)^(-s) ≤
      ∏ p ∈ P, (1+((p-1 : ℕ) : ℝ)^(-s)) := by
  let w : Finset ℕ → ℝ := fun S => ∏ p ∈ S, ((p-1 : ℕ) : ℝ)^(-s)
  have hinj : Set.InjOn Nat.primeFactors (↑F : Set ℕ) := by
    intro a ha b hb he
    exact eq_of_totient_eq_of_primeFactors_eq ((hF a ha).1.trans (hF b hb).1.symm) he
  have hsub : F.image Nat.primeFactors ⊆ P.powerset := by
    intro S hS
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hS
    exact mem_powerset.mpr (hF a ha).2
  have hpoint (a : ℕ) (ha : a ∈ F) : (n : ℝ)^(-s) ≤ w a.primeFactors := by
    have hdiv : (∏ p ∈ a.primeFactors, (p-1)) ∣ n := by
      rw [← totient_prod_primes _ (fun p hp => Nat.prime_of_mem_primeFactors hp),
        ← (hF a ha).1]
      exact Nat.totient_dvd_of_dvd (Nat.prod_primeFactors_dvd a)
    have hpos : 0 < ∏ p ∈ a.primeFactors, (p-1) :=
      prod_pos (fun p hp => Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt)
    have hr := Real.rpow_le_rpow_of_nonpos
      (show (0 : ℝ) < ((∏ p ∈ a.primeFactors, (p-1) : ℕ) : ℝ) by exact_mod_cast hpos)
      (show ((∏ p ∈ a.primeFactors, (p-1) : ℕ) : ℝ) ≤ n by
        exact_mod_cast Nat.le_of_dvd hn hdiv) (neg_nonpos.mpr hs)
    simpa only [Nat.cast_prod, ← Real.finset_prod_rpow a.primeFactors
      (fun p => ((p-1 : ℕ) : ℝ)) (fun p _ => Nat.cast_nonneg _) (-s), w] using hr
  calc
    _ = ∑ _a ∈ F, (n : ℝ)^(-s) := by simp
    _ ≤ ∑ a ∈ F, w a.primeFactors := sum_le_sum hpoint
    _ = ∑ S ∈ F.image Nat.primeFactors, w S := (sum_image hinj).symm
    _ ≤ ∑ S ∈ P.powerset, w S := sum_le_sum_of_subset_of_nonneg hsub
      (fun S _ _ => prod_nonneg (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
    _ = _ := (prod_one_add P).symm

lemma log_finite_fiber_le_pool_sum (F P : Finset ℕ) (n : ℕ) (hn : 0 < n)
    (hFne : F.Nonempty) (hF : ∀ a ∈ F, totient a = n ∧ a.primeFactors ⊆ P)
    (s : ℝ) (hs : 0 ≤ s) :
    Real.log (F.card : ℝ) ≤ s*Real.log (n : ℝ) +
      ∑ p ∈ P, ((p-1 : ℕ) : ℝ)^(-s) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard : (0 : ℝ) < F.card := by exact_mod_cast card_pos.mpr hFne
  have he : (∏ p ∈ P, (1+((p-1 : ℕ) : ℝ)^(-s))) ≤
      Real.exp (∑ p ∈ P, ((p-1 : ℕ) : ℝ)^(-s)) := by
    calc
      _ ≤ ∏ p ∈ P, Real.exp (((p-1 : ℕ) : ℝ)^(-s)) := by
        apply Finset.prod_le_prod
        · intro p hp; positivity
        · intro p hp
          simpa only [add_comm] using Real.add_one_le_exp (((p-1 : ℕ) : ℝ)^(-s))
      _ = _ := (Real.exp_sum _ _).symm
  have h := Real.log_le_log (mul_pos hcard (Real.rpow_pos_of_pos hnR _))
    ((finite_fiber_weight_le_pool_product F P n hn hF s hs).trans he)
  rw [Real.log_mul hcard.ne' (Real.rpow_pos_of_pos hnR _).ne',
    Real.log_rpow hnR, Real.log_exp] at h
  linarith

lemma finite_rpow_sum_le_card_power (D : Finset ℕ) (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : 1 < t) (hD : ∀ d ∈ D, 0 < d) :
    (∑ d ∈ D, (d : ℝ)^(-s)) ≤
      ((∑' d : ℕ, (d : ℝ)^(-t))+1)*((D.card+1 : ℕ) : ℝ)^(t-s) := by
  let R := D.card+1
  let Z : ℝ := ∑' d : ℕ, (d : ℝ)^(-t)
  have hR : (0 : ℝ) < R := by dsimp [R]; positivity
  have hR1 : (1 : ℝ) ≤ R := by dsimp [R]; exact_mod_cast Nat.le_add_left 1 D.card
  have hZ : 0 ≤ Z := tsum_nonneg (fun d => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hser : Summable (fun d : ℕ => (d : ℝ)^(-t)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hsmall : (∑ d ∈ D with d ≤ R, (d : ℝ)^(-s)) ≤ (R : ℝ)^(t-s)*Z := by
    calc
      _ ≤ ∑ d ∈ D with d ≤ R, (R : ℝ)^(t-s)*(d : ℝ)^(-t) := by
        apply sum_le_sum
        intro d hd
        obtain ⟨hdD, hdR⟩ := mem_filter.mp hd
        have hd0 : (0 : ℝ) < d := by exact_mod_cast hD d hdD
        calc
          (d : ℝ)^(-s) = (d : ℝ)^(t-s)*(d : ℝ)^(-t) := by
            rw [← Real.rpow_add hd0]; congr 1; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow hd0.le (by exact_mod_cast hdR) (sub_nonneg.mpr hst))
            (Real.rpow_nonneg hd0.le _)
      _ = (R : ℝ)^(t-s)*(∑ d ∈ D with d ≤ R, (d : ℝ)^(-t)) := (mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hser.sum_le_tsum _ (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (Real.rpow_nonneg hR.le _)
  have hlarge : (∑ d ∈ D with ¬d ≤ R, (d : ℝ)^(-s)) ≤ (R : ℝ)^(t-s) := by
    calc
      _ ≤ ∑ d ∈ D with ¬d ≤ R, (R : ℝ)^(-s) := by
        apply sum_le_sum
        intro d hd
        exact Real.rpow_le_rpow_of_nonpos hR (by
          exact_mod_cast (show R ≤ d by have := (mem_filter.mp hd).2; omega)) (neg_nonpos.mpr hs)
      _ = ((D.filter (fun d => ¬d ≤ R)).card : ℝ)*(R : ℝ)^(-s) := by simp
      _ ≤ (R : ℝ)*(R : ℝ)^(-s) := mul_le_mul_of_nonneg_right
        (by exact_mod_cast (card_filter_le D (fun d => ¬d ≤ R)).trans (Nat.le_succ _))
        (Real.rpow_nonneg hR.le _)
      _ = (R : ℝ)^(1-s) := by rw [Real.rpow_sub hR, Real.rpow_one, Real.rpow_neg hR.le, div_eq_mul_inv]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
  rw [← sum_filter_add_sum_filter_not D (fun d => d ≤ R)]
  change _ ≤ (Z+1)*(R : ℝ)^(t-s)
  nlinarith only [hsmall, hlarge]

noncomputable def poolRankinConstant (s t : ℝ) : ℝ :=
  ((∑' d : ℕ, (d : ℝ)^(-t))+1)*(4+(Real.log 2)⁻¹)^(t-s)

lemma poolRankinConstant_pos (s t : ℝ) : 0 < poolRankinConstant s t := by
  have hZ : 0 ≤ ∑' d : ℕ, (d : ℝ)^(-t) :=
    tsum_nonneg (fun d => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold poolRankinConstant
  exact mul_pos (by linarith) (Real.rpow_pos_of_pos (by positivity) _)

lemma prime_pool_sum_le_weight_power (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : 1 < t) :
    (∑ p ∈ P, ((p-1 : ℕ) : ℝ)^(-s)) ≤
      poolRankinConstant s t*(poolWeight P+1)^(t-s) := by
  let D := P.image (fun p => p-1)
  have hinj : Set.InjOn (fun p : ℕ => p-1) (↑P : Set ℕ) := by
    intro p hp q hq he
    have := (hP p hp).two_le
    have := (hP q hq).two_le
    change p-1=q-1 at he
    omega
  have hD : ∀ d ∈ D, 0 < d := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hd
    exact Nat.sub_pos_of_lt (hP p hp).one_lt
  have hcard : D.card=P.card := card_image_of_injOn hinj
  have hsum := finite_rpow_sum_le_card_power D s t hs hst ht hD
  rw [hcard, sum_image hinj] at hsum
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hW := poolWeight_nonneg P
  have hB : ((P.card+1 : ℕ) : ℝ) ≤ (4+(Real.log 2)⁻¹)*(poolWeight P+1) := by
    have hc := pool_card_le_weight P 2 (by decide)
    norm_num only [Nat.cast_ofNat] at hc
    push_cast
    rw [div_eq_mul_inv] at hc
    have hpos : 0 ≤ (Real.log 2)⁻¹ := (inv_pos.mpr hlog).le
    nlinarith only [hc, hW, hpos]
  calc
    _ ≤ ((∑' d : ℕ, (d : ℝ)^(-t))+1)*((P.card+1 : ℕ) : ℝ)^(t-s) := hsum
    _ ≤ ((∑' d : ℕ, (d : ℝ)^(-t))+1)*
        ((4+(Real.log 2)⁻¹)*(poolWeight P+1))^(t-s) := by
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hB (sub_nonneg.mpr hst))
      exact add_nonneg (tsum_nonneg (fun d => Real.rpow_nonneg (Nat.cast_nonneg _) _)) (by norm_num)
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      unfold poolRankinConstant
      ring

theorem log_finite_fiber_le_pool_weight_power (F P : Finset ℕ) (n : ℕ) (hn : 0 < n)
    (hFne : F.Nonempty) (hP : ∀ p ∈ P, p.Prime)
    (hF : ∀ a ∈ F, totient a=n ∧ a.primeFactors ⊆ P)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : 1 < t) :
    Real.log (F.card : ℝ) ≤ s*Real.log (n : ℝ)+
      poolRankinConstant s t*(poolWeight P+1)^(t-s) :=
  (log_finite_fiber_le_pool_sum F P n hn hFne hF s hs).trans
    (add_le_add le_rfl (prime_pool_sum_le_weight_power P hP s t hs hst ht))


/-- A uniform consequence of the weighted count. The exponent of log n in
its error is strictly less than one. -/
theorem eventually_pool_weight_bound_controls_fiber
    (C α β s t : ℝ) (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : 1 < t) (hsα : s < α)
    (he : β*(t-s) < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ F P : Finset ℕ,
      (∀ p ∈ P, p.Prime) →
      (∀ a ∈ F, totient a=n ∧ a.primeFactors ⊆ P) →
      poolWeight P ≤ C*(Real.log (n : ℝ))^β →
      (F.card : ℝ) ≤ (n : ℝ)^α := by
  let e : ℝ := β*(t-s)
  let D : ℝ := poolRankinConstant s t*(C+1)^(t-s)
  have hD : 0 < D := mul_pos (poolRankinConstant_pos s t)
    (Real.rpow_pos_of_pos (by linarith) _)
  have hloglim : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => (Real.log (n : ℝ))^(1-e)) atTop atTop :=
    (tendsto_rpow_atTop (by dsimp [e]; linarith)).comp hloglim
  filter_upwards [hlim.eventually (eventually_ge_atTop (D/(α-s))),
    hloglim.eventually (eventually_ge_atTop 1), eventually_ge_atTop 1]
    with n hnD hnlog hn
  intro F P hP hF hW
  by_cases hFne : F.Nonempty
  · have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlog : 0 < Real.log (n : ℝ) := by linarith
    have hlogpow : 1 ≤ (Real.log (n : ℝ))^β := Real.one_le_rpow hnlog hβ
    have hW' : poolWeight P+1 ≤ (C+1)*(Real.log (n : ℝ))^β := by
      nlinarith only [hW, hlogpow]
    have herr : poolRankinConstant s t*(poolWeight P+1)^(t-s) ≤
        (α-s)*Real.log (n : ℝ) := by
      calc
        _ ≤ poolRankinConstant s t*((C+1)*(Real.log (n : ℝ))^β)^(t-s) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by have := poolWeight_nonneg P; linarith) hW'
              (sub_nonneg.mpr hst)) (poolRankinConstant_pos s t).le
        _ = D*(Real.log (n : ℝ))^e := by
          rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg hlog.le _),
            ← Real.rpow_mul hlog.le]
          dsimp [D, e]
          ring
        _ ≤ ((α-s)*(Real.log (n : ℝ))^(1-e))*(Real.log (n : ℝ))^e :=
          mul_le_mul_of_nonneg_right
            (by have := (div_le_iff₀ (sub_pos.mpr hsα)).mp hnD; nlinarith only [this])
            (Real.rpow_nonneg hlog.le _)
        _ = (α-s)*Real.log (n : ℝ) := by
          rw [mul_assoc, ← Real.rpow_add hlog, sub_add_cancel, Real.rpow_one]
    have hlogF := (log_finite_fiber_le_pool_weight_power F P n (by omega)
      hFne hP hF s t hs hst ht).trans (add_le_add le_rfl herr)
    have hFpos : (0 : ℝ) < F.card := by exact_mod_cast card_pos.mpr hFne
    apply (Real.log_le_log_iff hFpos (Real.rpow_pos_of_pos hnR α)).mp
    rw [Real.log_rpow hnR]
    nlinarith only [hlogF]
  · simp only [not_nonempty_iff_eq_empty.mp hFne, card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma exists_pool_rankin_parameters (α β : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hβα : β*(1-α) < 1) :
    ∃ s t : ℝ, 0 < s ∧ s < α ∧ s < t ∧ 1 < t ∧ β*(t-s) < 1 := by
  have hdiv : 1-α < 1/β := (lt_div_iff₀ hβ).mpr (by nlinarith only [hβα])
  have hlo : max 0 (1-1/β) < α := max_lt hα (by linarith)
  obtain ⟨s, hslo, hsα⟩ := exists_between hlo
  have hs0 : 0 < s := (le_max_left _ _).trans_lt hslo
  have hslow : 1-1/β < s := (le_max_right _ _).trans_lt hslo
  let t : ℝ := (1+s+1/β)/2
  have ht : 1 < t := by dsimp [t]; linarith
  have hts : t-s < 1/β := by dsimp [t]; linarith
  refine ⟨s, t, hs0, hsα, (hsα.trans hα1).trans ht, ht, ?_⟩
  have hh := (lt_div_iff₀ hβ).mp hts
  nlinarith only [hh]

/-- No squarefreeness or record hypothesis is needed. Every polynomial-size
finite totient fiber forces a power-logarithmic lower bound on the weight
of every containing prime pool. -/
theorem eventually_large_fiber_requires_polynomial_pool
    (C α β : ℝ) (hC : 0 ≤ C) (hα : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hβα : β*(1-α) < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ F P : Finset ℕ,
      (∀ p ∈ P, p.Prime) →
      (∀ a ∈ F, totient a=n ∧ a.primeFactors ⊆ P) →
      (n : ℝ)^α < (F.card : ℝ) →
      C*(Real.log (n : ℝ))^β < poolWeight P := by
  obtain ⟨s, t, hs, hsα, hst, ht, he⟩ :=
    exists_pool_rankin_parameters α β hα hα1 hβ hβα
  filter_upwards [eventually_pool_weight_bound_controls_fiber C α β s t hC hβ.le
    hs.le hst.le ht hsα he] with n hn
  intro F P hP hF hcard
  by_contra h
  exact hcard.not_ge (hn F P hP hF (le_of_not_gt h))

end Erdos821.LogarithmicOverlap
