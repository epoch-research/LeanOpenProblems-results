import Submission.WeightedMertens

/-! Elementary obstruction to an eventual prime-counting leading coefficient
strictly below one. The weighted Mertens estimate suffices; no PNT is used. -/
namespace Erdos970.PrimeLeading
open Finset Real Filter
open scoped Topology

lemma sum_mul_le_of_prefix_le (a b f : ℕ → ℝ) (n : ℕ)
    (hf : ∀ i, 0 ≤ f i) (hanti : Antitone f)
    (hprefix : ∀ k ≤ n, (∑ i ∈ range k, a i) ≤ ∑ i ∈ range k, b i) :
    (∑ i ∈ range n, f i*a i) ≤ ∑ i ∈ range n, f i*b i := by
  have ha := sum_range_by_parts f a n
  have hb := sum_range_by_parts f b n
  simp only [smul_eq_mul] at ha hb
  rw [ha,hb]
  apply sub_le_sub
  · exact mul_le_mul_of_nonneg_left (hprefix n le_rfl) (hf _)
  · apply sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonpos_left (hprefix (i+1) (by have := mem_range.mp hi; omega))
      (sub_nonpos.mpr (hanti (Nat.le_succ i)))

noncomputable def primeLogTerm (i : ℕ) : ℝ :=
  if (i+1).Prime then log (i+1 : ℕ) else 0

lemma theta_eq_prefix (n : ℕ) :
    Chebyshev.theta (n : ℝ) = ∑ i ∈ range n, primeLogTerm i := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, ← Nat.range_succ_eq_Icc_zero, sum_filter,
    sum_range_succ']
  simp [primeLogTerm]

lemma primeSum_eq_weighted_prefix (n : ℕ) :
    WeightedMertens.primeSum n = ∑ i ∈ range n, (1/(i+1 : ℕ))*primeLogTerm i := by
  rw [WeightedMertens.primeSum, Nat.primesBelow, sum_filter, sum_range_succ']
  simp only [Nat.not_prime_zero, if_false, add_zero]
  apply sum_congr rfl
  intro i hi
  unfold primeLogTerm
  split_ifs <;> ring

lemma weighted_primeSum_le_of_theta (c D : ℝ)
    (hθ : ∀ n : ℕ, Chebyshev.theta (n : ℝ) ≤ c*n+D) (n : ℕ) :
    WeightedMertens.primeSum n ≤ c*(harmonic n : ℝ)+D := by
  have hD : 0 ≤ D := by simpa [Chebyshev.theta] using hθ 0
  by_cases hn : n = 0
  · subst n
    simpa [WeightedMertens.primeSum, Nat.primesBelow, harmonic] using hD
  have htemplate (k : ℕ) (hk : 0 < k) :
      (∑ i ∈ range k, (c + if i = 0 then D else 0)) = c*k+D := by
    simp [sum_add_distrib, hk, mul_comm]
  have hpref (k : ℕ) (hk : k ≤ n) :
      (∑ i ∈ range k, primeLogTerm i) ≤
        ∑ i ∈ range k, (c + if i = 0 then D else 0) := by
    by_cases hk0 : k = 0
    · simp [hk0]
    · rw [htemplate k (Nat.pos_of_ne_zero hk0), ← theta_eq_prefix]
      exact hθ k
  have h := sum_mul_le_of_prefix_le primeLogTerm
    (fun i => c + if i = 0 then D else 0) (fun i => 1/(i+1 : ℕ)) n
    (fun i => by positivity) (fun i j hij => one_div_le_one_div_of_le
      (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)) hpref
  rw [← primeSum_eq_weighted_prefix] at h
  have ht : (∑ i ∈ range n, 1/(i+1 : ℕ)*(c + if i = 0 then D else 0)) =
      c*(harmonic n : ℝ)+D := by
    simp only [mul_add, sum_add_distrib]
    have hz : (∑ i ∈ range n, 1/(i+1 : ℕ)*(if i = 0 then D else 0)) = D := by
      simp [mul_ite, Nat.pos_of_ne_zero hn]
    rw [hz]
    congr 1
    rw [harmonic, Rat.cast_sum, mul_sum]
    apply sum_congr rfl
    intro i hi
    push_cast
    ring
  rwa [ht] at h

/-- A global theta bound with slope below one contradicts elementary Mertens. -/
theorem not_theta_linear_bound (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (D : ℝ) :
    ¬∀ n : ℕ, Chebyshev.theta (n : ℝ) ≤ c*n+D := by
  intro hθ
  have hlogtop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨n,hn,hn1⟩ := ((hlogtop.eventually_gt_atTop
    ((c+D+WeightedMertens.boundConstant)/(1-c))).and
    (eventually_ge_atTop 1)).exists
  have hnpos : 0 < n := by omega
  have hlo := (abs_le.mp (WeightedMertens.abs_primeSum_sub_log n hnpos)).1
  have hup := (weighted_primeSum_le_of_theta c D hθ n).trans
    (add_le_add (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log n) hc0) le_rfl)
  have hdiv := (div_lt_iff₀ (show 0 < 1-c by linarith)).mp hn
  dsimp only [Function.comp_def] at hdiv
  nlinarith only [hlo,hup,hdiv]

/-- Finitely many exceptions cannot repair a leading coefficient below one. -/
theorem not_eventually_theta_linear (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ¬∀ᶠ n : ℕ in atTop, Chebyshev.theta (n : ℝ) ≤ c*n := by
  intro he
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  let D := ∑ n ∈ range N, max 0 (Chebyshev.theta (n : ℝ)-c*n)
  have hD : 0 ≤ D := sum_nonneg (fun _ _ => le_max_left _ _)
  apply not_theta_linear_bound c hc0 hc1 D
  intro n
  by_cases hn : N ≤ n
  · linarith [hN n hn]
  · have hs := single_le_sum (s := range N)
      (f := fun n : ℕ => max 0 (Chebyshev.theta (n : ℝ)-c*n))
      (fun _ _ => le_max_left _ _) (mem_range.mpr (by omega : n < N))
    have hh := (le_max_right 0 (Chebyshev.theta (n : ℝ)-c*n)).trans hs
    change Chebyshev.theta (n : ℝ)-c*n ≤ D at hh
    linarith

lemma theta_le_primeCounting_mul_log (n : ℕ) :
    Chebyshev.theta (n : ℝ) ≤ (n.primeCounting : ℝ)*log n := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, ← Nat.range_succ_eq_Icc_zero]
  calc
    _ ≤ ∑ _p ∈ (range (n+1)).filter Nat.Prime, log (n : ℝ) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpn,hp⟩ := mem_filter.mp hp
      apply log_le_log (by exact_mod_cast hp.pos)
      exact_mod_cast (show p ≤ n by have := mem_range.mp hpn; omega)
    _ = _ := by
      simp only [sum_const, nsmul_eq_mul]
      congr 1
      exact_mod_cast Nat.primesBelow_card_eq_primeCounting' (n+1)

/-- No appeal to the prime number theorem is hidden in this obstruction. -/
theorem not_eventually_primeCounting_leading (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ¬∀ᶠ n : ℕ in atTop, (n.primeCounting : ℝ)*log n ≤ c*n := by
  intro he
  apply not_eventually_theta_linear c hc0 hc1
  filter_upwards [he] with n hn
  exact (theta_le_primeCounting_mul_log n).trans hn

lemma exists_nat_pow_bracket (n d : ℕ) (hd : 0 < d) :
    ∃ t : ℕ, t^d ≤ n ∧ n < (t+1)^d := by
  have hex : ∃ s : ℕ, n < s^d :=
    ⟨n+1, (Nat.lt_succ_self n).trans_le (Nat.le_self_pow hd.ne' (n+1))⟩
  let s := Nat.find hex
  have hs : n < s^d := Nat.find_spec hex
  have hs0 : 0 < s := by
    by_contra hh
    have h0 : s = 0 := by omega
    simp [h0, hd.ne'] at hs
  have hlo : s-1 < s := by omega
  have hmin : ¬n < (s-1)^d := Nat.find_min hex hlo
  refine ⟨s-1, by omega, ?_⟩
  simpa only [Nat.sub_add_cancel hs0] using hs

lemma eventually_le_of_power_subsequence (f : ℕ → ℝ) (hf : Monotone f)
    (d : ℕ) (hd : 0 < d) (c c' : ℝ) (hc' : 0 ≤ c') (hcc' : c < c')
    (he : ∀ᶠ t : ℕ in atTop, f (t^d) ≤ c*(t : ℝ)^d) :
    ∀ᶠ n : ℕ in atTop, f n ≤ c'*n := by
  have hlim : Tendsto (fun t : ℕ => c*(1+1/(t : ℝ))^d) atTop (𝓝 c) := by
    have hh := ((tendsto_one_div_atTop_nhds_zero_nat.const_add 1).pow d).const_mul c
    simpa using hh
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (he.and ((hlim.eventually_le_const hcc').and (eventually_ge_atTop 1)))
  filter_upwards [eventually_ge_atTop ((N+1)^d)] with n hn
  obtain ⟨t,htlo,hthi⟩ := exists_nat_pow_bracket n d hd
  have hNt : N ≤ t := by
    by_contra hh
    have hu := Nat.pow_le_pow_left (show t+1 ≤ N+1 by omega) d
    omega
  have htpos : 0 < t := by have := (hN t hNt).2.2; omega
  have htR : (0 : ℝ) < t := by exact_mod_cast htpos
  have hrat := mul_le_mul_of_nonneg_right (hN t hNt).2.1
    (pow_nonneg htR.le d)
  have hid : c*(1+1/(t : ℝ))^d*(t : ℝ)^d = c*((t : ℝ)+1)^d := by
    rw [mul_assoc, ← mul_pow]
    congr 1
    congr 1
    field_simp
  rw [hid] at hrat
  calc
    f n ≤ f ((t+1)^d) := hf hthi.le
    _ ≤ c*((t+1 : ℕ) : ℝ)^d := (hN (t+1) (by omega)).1
    _ ≤ c'*(t : ℝ)^d := by simpa only [Nat.cast_add, Nat.cast_one] using hrat
    _ ≤ c'*n := mul_le_mul_of_nonneg_left (by exact_mod_cast htlo) hc'

/-- A polynomially sampled eventual bound also cannot have slope below one. -/
theorem not_eventually_theta_power (d : ℕ) (hd : 0 < d)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ¬∀ᶠ t : ℕ in atTop, Chebyshev.theta (t^d : ℕ) ≤ c*(t : ℝ)^d := by
  intro he
  have hmid0 : 0 ≤ (c+1)/2 := by linarith
  have hmid1 : (c+1)/2 < 1 := by linarith
  apply not_eventually_theta_linear ((c+1)/2) hmid0 hmid1
  exact eventually_le_of_power_subsequence (fun n => Chebyshev.theta (n : ℝ))
    (fun a b hab => Chebyshev.theta_mono (by exact_mod_cast hab)) d hd c ((c+1)/2)
    hmid0 (by linarith) he

#print axioms not_eventually_primeCounting_leading
#print axioms not_eventually_theta_power
end Erdos970.PrimeLeading
