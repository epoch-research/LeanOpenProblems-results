import Submission.PrimeRoughOutputs

/-! An unconditional bounded-almost-prime output theorem for every irrational
slope above one. The bound is deliberately non-optimal, and this does not
assert simultaneous primality of input and output. -/
namespace Erdos972PrimeAlmostPrime

open Finset ArithmeticFunction
open Erdos972PrimeRoughOutputs Erdos972PrimePowerError
open Erdos972GrowingCoprimeCandidates Erdos972ChebyshevRowMean
open Erdos972PolynomialRowScales

set_option maxHeartbeats 3000000
set_option exponentiation.threshold 524288

lemma prime_beyond_of_coprime_weight {α : ℝ} {D N B : ℕ}
    (hlarge : 7*(B:ℝ) < coprimePrimeWeight α D N) :
    ∃ p : ℕ, B < p ∧ p ≤ N ∧ p.Prime ∧ (floorMul α p).Coprime D := by
  by_contra hh
  have hsmall : ∀ p : ℕ, p ≤ N → p.Prime → (floorMul α p).Coprime D → p ≤ B := by
    intro p hpN hp hc
    exact le_of_not_gt (fun hBp => hh ⟨p, hBp, hpN, hp, hc⟩)
  have hbound : coprimePrimeWeight α D N ≤ Chebyshev.theta B := by
    unfold coprimePrimeWeight Chebyshev.theta
    rw [Nat.floor_natCast]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpI, hpp, hpc⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hpI).1,
        hsmall p (mem_Ioc.mp hpI).2 hpp hpc⟩, hpp⟩
    · intro p hp _
      exact Real.log_natCast_nonneg p
  have hθ := (Chebyshev.theta_le_psi (B:ℝ)).trans (psi_le_seven_mul (Nat.cast_nonneg B))
  linarith only [hlarge, hbound, hθ]

lemma factor_length_bound {q Z K : ℕ} (hq : 0 < q) (hZ : 1 < Z)
    (hc : q.Coprime Z.factorial) (hsize : q ≤ Z^K) :
    q.primeFactorsList.length ≤ K := by
  have hfac : ∀ r ∈ q.primeFactorsList, Z ≤ r := by
    intro r hr
    have hp := Nat.prime_of_mem_primeFactorsList hr
    have hrd := Nat.dvd_of_mem_primeFactorsList hr
    have hlt : Z < r := by
      by_contra hnot
      have hrf : r ∣ Z.factorial := hp.dvd_factorial.mpr (le_of_not_gt hnot)
      exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hc hrd hrf)
    exact hlt.le
  have hh := List.pow_card_le_prod q.primeFactorsList Z hfac
  rw [Nat.prod_primeFactorsList hq.ne'] at hh
  exact (Nat.pow_le_pow_iff_right hZ).mp (hh.trans hsize)

lemma roughRoot_upper {u : ℕ} (hZ : 2 ≤ roughRoot u) : u ≤ (roughRoot u)^1048576 := by
  have hu : u < (roughRoot u+1)^524288 := by
    apply Nat.lt_of_not_ge
    intro h
    have hh := (le_roughRoot_iff (roughRoot u+1) u).mpr h
    omega
  have hz : roughRoot u+1 ≤ (roughRoot u)^2 := by nlinarith only [hZ]
  calc
    u ≤ (roughRoot u+1)^524288 := hu.le
    _ ≤ ((roughRoot u)^2)^524288 := Nat.pow_le_pow_left hz _
    _ = _ := by rw [← pow_mul]

lemma floor_output_power_bound {α : ℝ} {p u : ℕ} (hα : α ≤ roughRoot u)
    (hZ : 2 ≤ roughRoot u) (hp : p ≤ u^6) :
    floorMul α p ≤ (roughRoot u)^6291457 := by
  have hfloor : floorMul α p ≤ roughRoot u*p := by
    unfold floorMul
    have hh := Nat.floor_mono (mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg (α := ℝ) p))
    simpa only [← Nat.cast_mul, Nat.floor_natCast] using hh
  have hscale : u^6 ≤ (roughRoot u)^6291456 := by
    have hh := Nat.pow_le_pow_left (roughRoot_upper hZ) 6
    simpa only [← pow_mul, Nat.reduceMul] using hh
  calc
    _ ≤ roughRoot u*p := hfloor
    _ ≤ roughRoot u*(roughRoot u)^6291456 := Nat.mul_le_mul_left _ (hp.trans hscale)
    _ = _ := by rw [← pow_succ']

lemma main_weight_lower {u v : ℕ} (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u) :
    (u:ℝ)/8 ≤ (u:ℝ)^6/(8*v) := by
  have hu1 : (1:ℝ) ≤ u := by exact_mod_cast hu
  have hvR : (0:ℝ) < v := Nat.cast_pos.mpr hv
  apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<8) hvR)).mpr
  calc
    _ = (u:ℝ)*v := by ring
    _ ≤ (u:ℝ)^2 := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hvu) (Nat.cast_nonneg (α := ℝ) u)
    _ ≤ _ := pow_le_pow_right₀ hu1 (by decide : 2 ≤ 6)

/-- Every sufficiently large search threshold is exceeded by a genuine prime
input whose output has a uniformly bounded number of prime factors, counted
with multiplicity. The fixed bound here is not close to the primality case. -/
theorem exists_prime_almost_prime_beyond {α : ℝ} (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧ (floorMul α p).primeFactorsList.length ≤ 6291457 := by
  let C := max (56*B) (max ⌈α⌉₊ 2)
  obtain ⟨u, hu, hZ, hw⟩ := exists_prime_rough_output_scale hα hI C
  have hZ2 : 2 ≤ roughRoot u := (le_max_right ⌈α⌉₊ 2).trans ((le_max_right (56*B) _).trans hZ.le)
  have hu0 : 0 < u := (Nat.zero_le C).trans_lt hu
  have huB : 56*B < u := (le_max_left (56*B) _).trans_lt hu
  have hv : root64 u ≤ u := root64_le_self u
  have hvR : (0:ℝ) < root64 u := Nat.cast_pos.mpr (root64_bounds hu0).1
  have huR : (0:ℝ) < u := Nat.cast_pos.mpr hu0
  have hu1 : (1:ℝ) ≤ u := by exact_mod_cast hu0
  have hlarge : 7*(B:ℝ) < coprimePrimeWeight α (roughRoot u).factorial (u^6) := by
    have hBuR : 56*(B:ℝ) < u := by exact_mod_cast huB
    have hlow := main_weight_lower hu0 (root64_bounds hu0).1 hv
    linarith only [hBuR, hlow, hw]
  obtain ⟨p, hBp, hpN, hp, hc⟩ := prime_beyond_of_coprime_weight hlarge
  have hαZ : α ≤ roughRoot u := (Nat.le_ceil α).trans (Nat.cast_le.mpr
    ((le_max_left ⌈α⌉₊ 2).trans ((le_max_right (56*B) _).trans hZ.le)))
  exact ⟨p, hBp, hp, factor_length_bound (floorMul_pos hα.le hp.pos) (by omega) hc
    (floor_output_power_bound hαZ hZ2 hpN)⟩

theorem infinite_prime_almost_prime_inputs {α : ℝ} (hα : 1 < α) (hI : Irrational α) :
    {p : ℕ | p.Prime ∧ (floorMul α p).primeFactorsList.length ≤ 6291457}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨p, hBp, hp, hq⟩ := exists_prime_almost_prime_beyond hα hI B
  exact ⟨p, ⟨hp, hq⟩, hBp⟩

#print axioms infinite_prime_almost_prime_inputs

end Erdos972PrimeAlmostPrime
