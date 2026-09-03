import Submission.SquarefreeCoprimeDensity

/-! An elementary logarithmic lower bound for the coprime squarefree sieve.
No density conclusion about cube-Sidon sets is claimed. -/

namespace Erdos1206.SquarefreeCoprimeDensity
open Finset Filter
open scoped Classical Topology
set_option maxHeartbeats 1000000

lemma squarefree_div_gcd_coprime {n h : ℕ} (hn : Squarefree n) :
    h.Coprime (n / Nat.gcd n h) := by
  apply Nat.coprime_of_dvd
  intro p hp hph hpq
  have hd : Nat.gcd n h ∣ n := Nat.gcd_dvd_left n h
  have he : Nat.gcd n h*(n/Nat.gcd n h)=n := Nat.mul_div_cancel' hd
  have hpn : p ∣ n := hpq.trans (Nat.div_dvd_of_dvd hd)
  have hpg : p ∣ Nat.gcd n h := Nat.dvd_gcd hpn hph
  have hs : p*p ∣ n := by rw [← he]; exact mul_dvd_mul hpg hpq
  exact (Nat.squarefree_iff_prime_squarefree.mp hn p hp) hs

lemma sfCount_divisor_cover {h : ℕ} (hh : 0<h) (N : ℕ) :
    sfCount 1 N ≤ ∑ d ∈ h.divisors, copCount h (N/d+1) := by
  let S := (range N).filter (fun n => Squarefree n ∧ Nat.Coprime 1 n)
  let T (d : ℕ) := ((range (N/d+1)).filter (fun q => h.Coprime q)).image (fun q => d*q)
  have hsub : S ⊆ h.divisors.biUnion T := by
    intro n hn
    have hn' := mem_filter.mp hn
    let d := Nat.gcd n h
    have hd : d ∈ h.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n h,hh.ne'⟩
    have hdv : d ∣ n := Nat.gcd_dvd_left n h
    refine mem_biUnion.mpr ⟨d,hd,?_⟩
    apply mem_image.mpr
    refine ⟨n/d,mem_filter.mpr ⟨mem_range.mpr ?_,squarefree_div_gcd_coprime hn'.2.1⟩,
      Nat.mul_div_cancel' hdv⟩
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (mem_range.mp hn'.1).le)
  have hc := (card_le_card hsub).trans (card_biUnion_le)
  have hi : ∀ d ∈ h.divisors, (T d).card ≤ copCount h (N/d+1) := by
    intro d hd
    exact card_image_le
  exact hc.trans (sum_le_sum hi)

lemma harmonic_divisor_bound {h : ℕ} (hh : 0<h) :
    (∑ d ∈ h.divisors, (1:ℝ)/d) ≤ (harmonic h : ℝ) := by
  have hsub : h.divisors ⊆ Icc 1 h := by
    intro d hd
    exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,Nat.le_of_dvd hh (Nat.dvd_of_mem_divisors hd)⟩
  have hs := sum_le_sum_of_subset_of_nonneg hsub
    (fun d _ _ => by positivity : ∀ d ∈ Icc 1 h, d ∉ h.divisors → 0 ≤ (1:ℝ)/d)
  simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div] using hs

lemma sfCount_harmonic_upper {h : ℕ} (hh : 0<h) (N : ℕ) :
    (sfCount 1 N : ℝ) ≤ copRate h*N*(harmonic h : ℝ)+(h.divisors.card : ℝ)*(h+1) := by
  have hc : (sfCount 1 N : ℝ) ≤ ∑ d ∈ h.divisors, (copCount h (N/d+1) : ℝ) := by
    exact_mod_cast sfCount_divisor_cover hh N
  have hterm (d : ℕ) (hd : d ∈ h.divisors) :
      (copCount h (N/d+1) : ℝ) ≤ copRate h*N*((1:ℝ)/d)+(h+1) := by
    have hb := (copCount_bounds hh (N/d+1)).2
    have hf : (((N/d : ℕ):ℝ)) ≤ (N:ℝ)/d := Nat.cast_div_le
    have hm := mul_le_mul_of_nonneg_left hf (copRate_nonneg h)
    have hr := copRate_le_one hh
    simp only [Nat.cast_add,Nat.cast_one] at hb
    nlinarith [show copRate h*((N:ℝ)/d)=copRate h*N*((1:ℝ)/d) by ring]
  have hs := sum_le_sum hterm
  rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at hs
  have hm := mul_le_mul_of_nonneg_left (harmonic_divisor_bound hh)
    (mul_nonneg (copRate_nonneg h) (Nat.cast_nonneg N))
  linarith

private lemma quadratic_coefficient_le {a b C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n : ℕ, a*(n:ℝ)^2 ≤ b*(n:ℝ)^2+C*n+C) : a ≤ b := by
  by_contra! hab
  have he : 0<a-b := sub_pos.mpr hab
  obtain ⟨n,hn⟩ := exists_nat_gt (max 1 (3*C/(a-b)))
  have hn1 : (1:ℝ)<n := (le_max_left _ _).trans_lt hn
  have hnε : 3*C < (a-b)*(n:ℝ) := by
    have hh := (div_lt_iff₀ he).mp ((le_max_right _ _).trans_lt hn)
    nlinarith
  have hh := mul_lt_mul_of_pos_right hnε (by linarith : (0:ℝ)<n)
  have hCn : C ≤ C*(n:ℝ) := by nlinarith
  nlinarith [h n]

/-- A weak totient bound needing no estimates for the distribution of primes. -/
theorem copRate_mul_harmonic_lower (h : ℕ) (hh : 0<h) :
    (1:ℝ)/4 ≤ copRate h*(harmonic h : ℝ) := by
  let C : ℝ := (h.divisors.card : ℝ)*(h+1)+2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply quadratic_coefficient_le (C := C) hC
  intro n
  have hl := sfCount_lower (h := 1) (by decide) (n^2)
  have hu := sfCount_harmonic_upper hh (n^2)
  norm_num only [copRate,Nat.totient_one,Nat.cast_one,div_one,Nat.sqrt_eq',Nat.cast_pow] at hl
  simp only [Nat.cast_pow] at hu
  have hc : 2*(n:ℝ) ≤ C*n := by
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg n)
    dsimp [C]
    have hz : (0:ℝ) ≤ (h.divisors.card : ℝ)*(h+1) := by positivity
    linarith
  dsimp [C] at hc ⊢
  nlinarith

/-- A logarithmic quantitative bound on the supply of coprime squarefree multipliers. -/
theorem lowerDensity_log_bound (h : ℕ) (hh : 0<h) :
    (1:ℝ)/(16*(1+Real.log h)) ≤
      ({n : ℕ | Squarefree n ∧ h.Coprime n} : Set ℕ).lowerDensity := by
  have hlog : 0 ≤ Real.log (h:ℝ) := Real.log_nonneg (by exact_mod_cast hh)
  have hm := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log h) (copRate_nonneg h)
  have hb := copRate_mul_harmonic_lower h hh
  have he : (1:ℝ)/(16*(1+Real.log h)) ≤ copRate h/4 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<16*(1+Real.log h))).mpr
    nlinarith
  have hd := lowerDensity_bound h hh
  have heq : (h.totient : ℝ)/(4*h)=copRate h/4 := by dsimp [copRate]; ring
  rw [heq] at hd
  exact he.trans hd

#print axioms copRate_mul_harmonic_lower
#print axioms lowerDensity_log_bound
end Erdos1206.SquarefreeCoprimeDensity
