import Submission.PrimeCountingPowerSavingObstruction
import Submission.LowCountCylinder

/-! A full-centred high-moment shortcut is false even at quadratic lengths.
The budget parameter is an upper bound for the number of primes. This is an
auxiliary obstruction, not a disproof of the Jacobsthal conjecture. -/
namespace Erdos970.GapAverages
open Finset Real Filter
open scoped Topology

/-- The right side deliberately omits the density factor, making this weaker
than a Gaussian estimate based on the actual mean m*density(P). -/
def UniformQuadraticCountMoment (C : ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
    ∀ m : ℕ, k^2 ≤ m →
      phaseMean P (fun r => |intervalCount P m r - (m : ℝ)*density P|^(2*k)) ≤
        (C*(k : ℝ)*m)^k

lemma UniformQuadraticCountMoment.mono {C D : ℝ} (hC0 : 0 ≤ C)
    (hC : UniformQuadraticCountMoment C) (hCD : C ≤ D) :
    UniformQuadraticCountMoment D := by
  intro k hk P hP hPk m hm
  exact (hC k hk P hP hPk m hm).trans
    (pow_le_pow_left₀ (by positivity) (by gcongr) k)

lemma value_le_phaseMean_mul_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : Phase P → ℝ) (hF : ∀ r, 0 ≤ F r) (r : Phase P) :
    F r ≤ (∏ p ∈ P, (p : ℝ))*phaseMean P F := by
  have hd : (∏ p ∈ P, (p : ℝ)) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun p hp => by exact_mod_cast (hP p hp).ne_zero)
  have hh := single_le_sum (s := (univ : Finset (Phase P))) (f := F)
    (fun s _ => hF s) (mem_univ r)
  unfold phaseMean
  rw [prod_coe_sort P (fun p : ℕ => (p : ℝ)), mul_div_cancel₀ _ hd]
  exact hh

lemma primesBelow_product_le_four (y : ℕ) :
    (∏ p ∈ y.primesBelow, (p : ℝ)) ≤ (4 : ℝ)^y := by
  have hsub : y.primesBelow ⊆ (y+1).primesBelow := by
    intro p hp
    obtain ⟨hpy,hp⟩ := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr ⟨by omega,hp⟩
  have hprod : (∏ p ∈ y.primesBelow, p) ≤ primorial y := by
    change (∏ p ∈ y.primesBelow, p) ≤ ∏ p ∈ (y+1).primesBelow, p
    exact prod_le_prod_of_subset_of_one_le' hsub
      (fun p hp _ => (Nat.prime_of_mem_primesBelow hp).one_le)
  have hh := hprod.trans (primorial_le_4_pow y)
  rw [← Nat.cast_prod]
  exact_mod_cast hh

lemma moment_count_discrepancy (C : ℝ) (hC : 1 ≤ C)
    (hM : UniformQuadraticCountMoment C) (t : ℕ) (ht : 1 ≤ t)
    (hcard : (64*t^6).primesBelow.card ≤ t^6) (m : ℕ)
    (hmlo : t^12 ≤ m) (hmhi : m ≤ 4096*t^12) :
    |roughCount (64*t^6).primesBelow m - (m : ℝ)*density (64*t^6).primesBelow| ≤
      (4 : ℝ)^32*64*C*(t : ℝ)^9 := by
  let P := (64*t^6).primesBelow
  have hP : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primesBelow hp
  have ht0 : 0 < t := by omega
  have htR : (0 : ℝ) < t := by exact_mod_cast ht0
  have hM' := hM (t^6) (by positivity) P hP hcard m
    (by convert hmlo using 1; ring)
  have hs := value_le_phaseMean_mul_product P hP
    (fun r => |intervalCount P m r-(m : ℝ)*density P|^(2*t^6))
    (fun r => by positivity) (zeroPhase P hP)
  rw [intervalCount_zeroPhase] at hs
  have hp := primesBelow_product_le_four (64*t^6)
  have hmul := mul_le_mul hp hM' (by unfold phaseMean; positivity) (by positivity : (0 : ℝ) ≤ (4 : ℝ)^(64*t^6))
  have hbase : C*(t^6 : ℕ)*m ≤ (64*C*(t : ℝ)^9)^2 := by
    have hmR : (m : ℝ) ≤ 4096*(t : ℝ)^12 := by exact_mod_cast hmhi
    have hC2 : C ≤ C^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hmR (show 0 ≤ C*(t : ℝ)^6 by positivity)
    have hc := mul_le_mul_of_nonneg_right hC2 (show 0 ≤ 4096*(t : ℝ)^18 by positivity)
    push_cast
    nlinarith only [hm,hc]
  have hpow := pow_le_pow_left₀ (by positivity) hbase (t^6)
  have hfinal : (4 : ℝ)^(64*t^6)*(C*(t^6 : ℕ)*m)^(t^6) ≤
      ((4 : ℝ)^32*64*C*(t : ℝ)^9)^(2*t^6) := by
    calc
      _ ≤ (4 : ℝ)^(64*t^6)*((64*C*(t : ℝ)^9)^2)^(t^6) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by
        rw [← pow_mul, show 64*t^6 = 32*(2*t^6) by omega, pow_mul]
        rw [← mul_pow]
        congr 1
        ring
  apply le_of_pow_le_pow_left₀ (show 2*t^6 ≠ 0 by positivity) (by positivity)
  exact hs.trans (hmul.trans hfinal)

lemma eventually_small_prime_core :
    ∀ᶠ t : ℕ in atTop, (64*t^6).primesBelow.card ≤ t^6 := by
  have htop : Tendsto (fun t : ℕ => 64*t^6) atTop atTop := by
    apply tendsto_atTop_mono (f := fun t : ℕ => t) _ tendsto_id
    intro t
    have h1 := Nat.le_self_pow (by omega : 6 ≠ 0) t
    dsimp only
    omega
  have hlim := PrimeCountingDyadic.density'_tendsto_zero.comp htop
  filter_upwards [hlim.eventually_le_const (by norm_num : (0 : ℝ) < 1/64),
    eventually_ge_atTop 1] with t ht ht1
  have ht0 : 0 < t := by omega
  have hy : (0 : ℝ) < (64*t^6 : ℕ) := by positivity
  have hh := (div_le_iff₀ hy).mp ht
  rw [Nat.primesBelow_card_eq_primeCounting']
  have hh' : ((64*t^6).primeCounting' : ℝ) ≤ (t : ℝ)^6 := by
    push_cast at hh
    linarith only [hh]
  exact_mod_cast hh'

lemma prime_recurrence_of_quadratic_moments (C : ℝ) (hC : 1 ≤ C)
    (hM : UniformQuadraticCountMoment C) (t : ℕ) (ht : 2 ≤ t)
    (hcard : (64*t^6).primesBelow.card ≤ t^6) :
    4096*((t^12).primeCounting' : ℝ)-(4096*t^12).primeCounting' ≤
      (4097*((4 : ℝ)^32*64*C)+262080)*(t : ℝ)^11 := by
  have ht0 : 0 < t := by omega
  have ht1 : 1 ≤ t := by omega
  let y := 64*t^6
  let P := y.primesBelow
  let A := (4 : ℝ)^32*64*C
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hcount (m : ℕ) (hml : t^12 ≤ m) (hmh : m ≤ 4096*t^12) :
      |roughCount P m-(m : ℝ)*density P| ≤ A*(t : ℝ)^11 := by
    have hh := moment_count_discrepancy C hC hM t ht1 hcard m hml hmh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by exact_mod_cast ht1) (show 9 ≤ 11 by omega)) hA)
  have hshort := hcount (t^12) le_rfl (by omega)
  have hlong := hcount (4096*t^12) (by omega) le_rfl
  have hy3 : 2 < y := by
    have hh := Nat.one_le_pow 6 t ht0
    dsimp [y]
    omega
  have hyn : y ≤ t^12 := by
    have hh := Nat.pow_le_pow_left ht 6
    norm_num at hh
    have hid : t^12 = (t^6)^2 := by ring
    rw [hid]
    dsimp [y]
    nlinarith
  have hsq : y^2 = 4096*t^12 := by dsimp [y]; ring
  have he1 := roughCount_primesBelow_eq y (t^12) hy3 hyn (by rw [hsq]; omega)
  have he2 := roughCount_primesBelow_eq y (4096*t^12) hy3 (by omega) (by rw [hsq])
  change roughCount P _ = _ at he1 he2
  rw [he1] at hshort
  rw [he2] at hlong
  have hpi : (y.primeCounting' : ℝ) ≤ 64*(t : ℝ)^11 := by
    have hh : y.primeCounting' ≤ y := Nat.count_le _
    have hp := Nat.pow_le_pow_right ht0 (show 6 ≤ 11 by omega)
    exact_mod_cast hh.trans (Nat.mul_le_mul_left 64 hp)
  have hu := (abs_le.mp hshort).2
  have hl := (abs_le.mp hlong).1
  push_cast at hu hl
  change 4096*((t^12).primeCounting' : ℝ)-(4096*t^12).primeCounting' ≤
    (4097*A+262080)*(t : ℝ)^11
  nlinarith only [hu,hl,hpi]

/-- Even the density-free version of this budget-uniform Gaussian-shaped
moment estimate is false. There is no assertion here about an individual
fixed moment order or a sub-mean truncated statistic. -/
theorem not_uniformQuadraticCountMoment (C : ℝ) : ¬UniformQuadraticCountMoment C := by
  intro hM
  have hC0 : 0 ≤ C := by
    have hh := hM 1 (by omega) ∅ (by simp) (by simp) 1 (by simp)
    simpa [phaseMean, intervalCount, point, density] using hh
  let D := max C 1
  have hD : 1 ≤ D := le_max_right _ _
  have hM' := hM.mono hC0 (le_max_left _ 1)
  apply PrimeCountingDyadic.not_eventually_bounded_4096_difference
    (4097*((4 : ℝ)^32*64*D)+262080)
  have htop : Tendsto (fun j : ℕ => 2^j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega : (1 : ℕ) < 2)
  filter_upwards [htop.eventually eventually_small_prime_core,
    eventually_ge_atTop 1] with j hj hj1
  have ht : 2 ≤ 2^j := by
    have hh := Nat.pow_le_pow_right (show 0 < 2 by omega) hj1
    norm_num at hh
    exact hh
  have hh := prime_recurrence_of_quadratic_moments D hD hM' (2^j) ht hj
  have hn : (2^j : ℕ)^12 = 4096^j := by
    rw [← pow_mul, Nat.mul_comm j 12, pow_mul]
    norm_num
  have hm : 4096*(2^j : ℕ)^12 = 4096^(j+1) := by rw [hn,pow_succ]; ring
  have he : (((2^j : ℕ) : ℝ))^11 = 2048^j := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, Nat.mul_comm j 11, pow_mul]
    norm_num
  rw [hm,hn,he] at hh
  exact hh

#print axioms moment_count_discrepancy
#print axioms not_uniformQuadraticCountMoment
end Erdos970.GapAverages
