import Submission.RecordInputScale

/-!
# Logarithmic size accounting for normalized record fibers

An exact incidence identity and its record-frequency consequence. The
result is an upper bound on the output size for a prescribed input-prime
cutoff, not a multiplicity amplification or a settlement of Erdős 821.
-/

open Nat Finset Filter
open scoped Classical BigOperators Topology

namespace Erdos821

set_option maxHeartbeats 2000000

lemma log_output_eq_sum_predecessor_logs (n m : ℕ)
    (hm : m ∈ oddSquarefreeFiber n) :
    Real.log (n : ℝ) = ∑ p ∈ m.primeFactors, Real.log ((p-1 : ℕ) : ℝ) := by
  obtain ⟨hmSq, _, hmφ⟩ := mem_oddSquarefreeFiber.mp hm
  have he : n = ∏ p ∈ m.primeFactors, (p-1) := by
    rw [← totient_prod_primes m.primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp),
      Nat.prod_primeFactors_of_squarefree hmSq, hmφ]
  rw [he, Nat.cast_prod, Real.log_prod]
  intro p hp
  exact_mod_cast (Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt).ne'

lemma log_output_eq_sum_pool_predecessor_logs (n m P : ℕ)
    (hm : m ∈ oddSquarefreeFiber n)
    (hcut : ∀ p ∈ m.primeFactors, p ≤ P) :
    Real.log (n : ℝ) = ∑ p ∈ (P+1).primesBelow,
      if p ∣ m then Real.log ((p-1 : ℕ) : ℝ) else 0 := by
  have hm0 := (mem_oddSquarefreeFiber.mp hm).1.ne_zero
  have hset : (P+1).primesBelow.filter (fun p => p ∣ m) = m.primeFactors := by
    ext p
    simp only [mem_filter, Nat.mem_primesBelow, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨_, hp⟩, hpm⟩
      exact ⟨hp, hpm, hm0⟩
    · rintro ⟨hp, hpm, _⟩
      exact ⟨⟨by have := hcut p (hp.mem_primeFactors hpm hm0); omega, hp⟩, hpm⟩
  rw [← sum_filter, hset]
  exact log_output_eq_sum_predecessor_logs n m hm

/-- Exact accounting: no independence of the input-prime incidences is used. -/
lemma record_fiber_log_incidence (n P : ℕ)
    (hcut : ∀ m ∈ oddSquarefreeFiber n, ∀ p ∈ m.primeFactors, p ≤ P) :
    (gOddSquarefree n : ℝ)*Real.log (n : ℝ) =
      ∑ p ∈ (P+1).primesBelow, Real.log ((p-1 : ℕ) : ℝ) *
        (((oddSquarefreeFiber n).filter (fun m => p ∣ m)).card : ℝ) := by
  calc
    _ = ∑ _m ∈ oddSquarefreeFiber n, Real.log (n : ℝ) := by
      simp only [sum_const, nsmul_eq_mul, card_oddSquarefreeFiber]
    _ = ∑ m ∈ oddSquarefreeFiber n, ∑ p ∈ (P+1).primesBelow,
        if p ∣ m then Real.log ((p-1 : ℕ) : ℝ) else 0 :=
      sum_congr rfl (fun m hm => log_output_eq_sum_pool_predecessor_logs n m P hm (hcut m hm))
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro p hp
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]

/-- At a normalized record, the output logarithm is bounded by the
weighted logarithmic mass of its allowed input-prime pool. -/
theorem normalized_record_log_budget (n P : ℕ) (hn : 0 < n)
    (hg : 0 < gOddSquarefree n) (s : ℝ)
    (hrec : ∀ j : ℕ, j ≤ n →
      (gOddSquarefree j : ℝ)/(j : ℝ)^s ≤ (gOddSquarefree n : ℝ)/(n : ℝ)^s)
    (hcut : ∀ m ∈ oddSquarefreeFiber n, ∀ p ∈ m.primeFactors, p ≤ P) :
    Real.log (n : ℝ) ≤ ∑ p ∈ (P+1).primesBelow,
      Real.log ((p-1 : ℕ) : ℝ)*((p-1 : ℕ) : ℝ)^(-s) := by
  have hfreq (p : ℕ) (hp : p ∈ (P+1).primesBelow) :
      (((oddSquarefreeFiber n).filter (fun m => p ∣ m)).card : ℝ) ≤
        (gOddSquarefree n : ℝ)*((p-1 : ℕ) : ℝ)^(-s) := by
    have hpr := (Nat.mem_primesBelow.mp hp).2
    have hpR : (0 : ℝ) < (p-1 : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hpr.one_lt
    have h := normalized_record_odd_fiber_core_bound n p hn s hrec
    rw [Nat.totient_prime hpr] at h
    have hdiv := (le_div_iff₀ (Real.rpow_pos_of_pos hpR s)).mpr
      (by simpa only [mul_comm] using h)
    simpa only [Real.rpow_neg hpR.le, div_eq_mul_inv] using hdiv
  have hgR : (0 : ℝ) < gOddSquarefree n := by exact_mod_cast hg
  apply (mul_le_mul_iff_right₀ hgR).mp
  calc
    _ = ∑ p ∈ (P+1).primesBelow, Real.log ((p-1 : ℕ) : ℝ) *
        (((oddSquarefreeFiber n).filter (fun m => p ∣ m)).card : ℝ) :=
      record_fiber_log_incidence n P hcut
    _ ≤ ∑ p ∈ (P+1).primesBelow, Real.log ((p-1 : ℕ) : ℝ) *
        ((gOddSquarefree n : ℝ)*((p-1 : ℕ) : ℝ)^(-s)) := by
      apply sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left (hfreq p hp)
      exact Real.log_natCast_nonneg _
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro p hp; ring

lemma normalized_record_log_budget_pseries (n P : ℕ) (hn : 0 < n) (hP : 1 ≤ P)
    (hg : 0 < gOddSquarefree n) (s u : ℝ) (hsu : s ≤ u) (hu : 1 < u)
    (hrec : ∀ j : ℕ, j ≤ n →
      (gOddSquarefree j : ℝ)/(j : ℝ)^s ≤ (gOddSquarefree n : ℝ)/(n : ℝ)^s)
    (hcut : ∀ m ∈ oddSquarefreeFiber n, ∀ p ∈ m.primeFactors, p ≤ P) :
    Real.log (n : ℝ) ≤ Real.log (P : ℝ)*(P : ℝ)^(u-s)*
      ∑' a : ℕ, (a : ℝ)^(-u) := by
  let Q := (P+1).primesBelow
  let D := Q.image (fun p => p-1)
  have hQ (p : ℕ) (hp : p ∈ Q) : p.Prime ∧ p ≤ P := by
    obtain ⟨hpP, hpr⟩ := Nat.mem_primesBelow.mp hp
    exact ⟨hpr, by omega⟩
  have hinj : Set.InjOn (fun p : ℕ => p-1) (Q : Set ℕ) := by
    intro p hp q hq he
    change p-1 = q-1 at he
    have := (hQ p hp).1.two_le
    have := (hQ q hq).1.two_le
    omega
  have hmass : (∑ p ∈ Q, ((p-1 : ℕ) : ℝ)^(-s)) ≤
      (P : ℝ)^(u-s)*∑' a : ℕ, (a : ℝ)^(-u) := by
    have h := bounded_multiples_rpow_sum D P 1 (by decide) s u hsu hu (by
      intro d hd
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hd
      exact ⟨Nat.sub_pos_of_lt (hQ p hp).1.one_lt,
        (Nat.sub_le p 1).trans (hQ p hp).2, one_dvd _⟩)
    simpa only [D, sum_image hinj, Nat.cast_one, Real.one_rpow, mul_one] using h
  calc
    _ ≤ ∑ p ∈ Q, Real.log ((p-1 : ℕ) : ℝ)*((p-1 : ℕ) : ℝ)^(-s) :=
      normalized_record_log_budget n P hn hg s hrec hcut
    _ ≤ ∑ p ∈ Q, Real.log (P : ℝ)*((p-1 : ℕ) : ℝ)^(-s) := by
      apply sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      apply Real.log_le_log
      · exact_mod_cast Nat.sub_pos_of_lt (hQ p hp).1.one_lt
      · exact_mod_cast (Nat.sub_le p 1).trans (hQ p hp).2
    _ = Real.log (P : ℝ)*∑ p ∈ Q, ((p-1 : ℕ) : ℝ)^(-s) := (mul_sum _ _ _).symm
    _ ≤ _ := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hmass (Real.log_nonneg (by exact_mod_cast hP))

/-- Uniform in the record output: an input-prime cutoff P supports an
output logarithm of at most P^(1-s+epsilon), for all sufficiently large P.
The slack epsilon is arbitrary but fixed. This is a necessary size bound,
not an assertion that a record with that size exists. -/
theorem eventually_record_log_le_input_cutoff_power (s ε : ℝ) (hs : s < 1) (hε : 0 < ε) :
    ∀ᶠ P : ℕ in atTop, ∀ n : ℕ, 0 < n → 0 < gOddSquarefree n →
      (∀ j : ℕ, j ≤ n →
        (gOddSquarefree j : ℝ)/(j : ℝ)^s ≤ (gOddSquarefree n : ℝ)/(n : ℝ)^s) →
      (∀ m ∈ oddSquarefreeFiber n, ∀ p ∈ m.primeFactors, p ≤ P) →
      Real.log (n : ℝ) ≤ (P : ℝ)^(1-s+ε) := by
  let u : ℝ := 1+ε/2
  let C : ℝ := ∑' a : ℕ, (a : ℝ)^(-u)
  have hu : 1 < u := by dsimp only [u]; linarith
  have hsu : s ≤ u := hs.le.trans hu.le
  have hC : 0 ≤ C := tsum_nonneg (fun a => Real.rpow_nonneg (Nat.cast_nonneg a) _)
  have ho : (fun P : ℕ => Real.log (P : ℝ)) =o[atTop]
      (fun P : ℕ => (P : ℝ)^(ε/2)) :=
    (isLittleO_log_rpow_atTop (half_pos hε)).comp_tendsto tendsto_natCast_atTop_atTop
  filter_upwards [ho.bound (by positivity : (0 : ℝ) < 1/(C+1)),
    eventually_ge_atTop 1] with P hlog hP
  intro n hn hg hrec hcut
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hlog0 : 0 ≤ Real.log (P : ℝ) := Real.log_nonneg (by exact_mod_cast hP)
  simp only [Real.norm_eq_abs, abs_of_nonneg hlog0,
    abs_of_nonneg (Real.rpow_nonneg hP0.le _)] at hlog
  have hlog' : C*Real.log (P : ℝ) ≤ (P : ℝ)^(ε/2) := by
    have hdiv : Real.log (P : ℝ) ≤ (P : ℝ)^(ε/2)/(C+1) := by
      convert hlog using 1; ring
    have hmul := (le_div_iff₀ (by positivity : 0 < C+1)).mp hdiv
    nlinarith only [hmul, hlog0]
  calc
    _ ≤ Real.log (P : ℝ)*(P : ℝ)^(u-s)*C :=
      normalized_record_log_budget_pseries n P hn hP hg s u hsu hu hrec hcut
    _ = (C*Real.log (P : ℝ))*(P : ℝ)^(u-s) := by ring
    _ ≤ (P : ℝ)^(ε/2)*(P : ℝ)^(u-s) :=
      mul_le_mul_of_nonneg_right hlog' (Real.rpow_nonneg hP0.le _)
    _ = _ := by rw [← Real.rpow_add hP0]; congr 1; dsimp only [u]; ring

/-- A positive record fiber contains an input prime exceeding every fixed
power (log n)^c with c*(1-s)<1, once n is large enough. This is only a
polylogarithmic input scale, not a polynomial scale in n. -/
theorem eventually_record_has_polylog_large_input_prime (s c : ℝ)
    (hs : s < 1) (hc : 0 < c) (hcs : c*(1-s) < 1) :
    ∀ᶠ n : ℕ in atTop, 0 < gOddSquarefree n →
      (∀ j : ℕ, j ≤ n →
        (gOddSquarefree j : ℝ)/(j : ℝ)^s ≤ (gOddSquarefree n : ℝ)/(n : ℝ)^s) →
      ∃ m ∈ oddSquarefreeFiber n, ∃ p ∈ m.primeFactors,
        (Real.log (n : ℝ))^c < (p : ℝ) := by
  let ε : ℝ := (1-c*(1-s))/(2*c)
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  have hεid : 2*c*ε = 1-c*(1-s) := by dsimp only [ε]; field_simp
  have hb : 0 < 1-s+ε := by linarith
  have hcb : c*(1-s+ε) < 1 := by nlinarith only [hεid, hcs]
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hfloor : Tendsto (fun n : ℕ => ⌊(Real.log (n : ℝ))^c⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop hc).comp hlog)
  filter_upwards [hfloor.eventually (eventually_record_log_le_input_cutoff_power s ε hs hε),
    hlog.eventually (eventually_gt_atTop (1 : ℝ)), eventually_ge_atTop 1]
    with n hbound hlogn hn
  intro hg hrec
  by_contra h
  push_neg at h
  have hcut : ∀ m ∈ oddSquarefreeFiber n, ∀ p ∈ m.primeFactors,
      p ≤ ⌊(Real.log (n : ℝ))^c⌋₊ := by
    intro m hm p hp
    exact Nat.le_floor (h m hm p hp)
  have hlower := hbound n (by omega) hg hrec hcut
  have hupper : (⌊(Real.log (n : ℝ))^c⌋₊ : ℝ)^(1-s+ε) < Real.log (n : ℝ) := by
    calc
      _ ≤ ((Real.log (n : ℝ))^c)^(1-s+ε) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _)
          (Nat.floor_le (Real.rpow_nonneg (by linarith) _)) hb.le
      _ = (Real.log (n : ℝ))^(c*(1-s+ε)) :=
        (Real.rpow_mul (by linarith : 0 ≤ Real.log (n : ℝ)) _ _).symm
      _ < (Real.log (n : ℝ))^(1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hlogn hcb
      _ = _ := Real.rpow_one _
  exact hlower.not_gt hupper

end Erdos821
