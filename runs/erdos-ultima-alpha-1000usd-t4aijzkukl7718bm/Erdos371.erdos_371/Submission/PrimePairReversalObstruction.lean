import Submission.PrimePairEndpointObstruction

/-! Exact adjacent prime-pair laws need not be reversible in total variation.
The witness below depends on the endpoint and on the individual prime values;
it is NOT the comparison sign in the Erdős conjecture. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology
set_option autoImplicit false

/-- A pair with product at least `2*N` has no reversed occurrence below `N`. -/
lemma exactPrimePair_reverse_impossible (N m n : ℕ) (hm : m<N) (hn : n<N)
    (hprod : 2*N ≤ (exactPrimePair n).1*(exactPrimePair n).2) :
    exactPrimePair m ≠ (exactPrimePair n).swap := by
  intro he
  have hp : (exactPrimePair n).1 ∣ m+1 := by
    have hh := congrArg Prod.snd he
    simp only [Prod.snd_swap] at hh
    rw [← hh]
    exact Nat.maxPrimeFac_dvd
  have hq : (exactPrimePair n).2 ∣ m := by
    have hh := congrArg Prod.fst he
    simp only [Prod.fst_swap] at hh
    rw [← hh]
    exact Nat.maxPrimeFac_dvd
  have hp' : (exactPrimePair n).1 ∣ n := Nat.maxPrimeFac_dvd
  have hq' : (exactPrimePair n).2 ∣ n+1 := Nat.maxPrimeFac_dvd
  have hpd : (exactPrimePair n).1 ∣ n+m+1 := by
    simpa only [Nat.add_assoc] using Nat.dvd_add hp' hp
  have hqd : (exactPrimePair n).2 ∣ n+m+1 := by
    convert Nat.dvd_add hq' hq using 1
    omega
  have hmul := (exactPrimePair_coprime n).mul_dvd_of_dvd_of_dvd hpd hqd
  have hh := Nat.le_of_dvd (by omega : 0<n+m+1) hmul
  omega

noncomputable def primePairAsymmetryTest (B N : ℕ) (a b : ℕ) : ℝ :=
  (if (a,b)∈(bothAboveSet B N).image exactPrimePair then 1 else 0)-
    (if (b,a)∈(bothAboveSet B N).image exactPrimePair then 1 else 0)

lemma primePairAsymmetryTest_skew (B N a b : ℕ) :
    primePairAsymmetryTest B N b a = -primePairAsymmetryTest B N a b := by
  unfold primePairAsymmetryTest
  ring

lemma primePairAsymmetryTest_bound (B N a b : ℕ) :
    |primePairAsymmetryTest B N a b|≤1 := by
  unfold primePairAsymmetryTest
  split_ifs <;> norm_num

/-- The witness is exactly the indicator of the large-pair set when
sampled on the actual adjacent sequence up to `N`. -/
lemma primePairAsymmetryTest_on_sequence (B N n : ℕ) (hn : n<N)
    (hprod : 2*N≤(B+1)^2) :
    primePairAsymmetryTest B N (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)) =
      if n∈bothAboveSet B N then 1 else 0 := by
  classical
  have hf : exactPrimePair n∈(bothAboveSet B N).image exactPrimePair ↔
      n∈bothAboveSet B N := by
    constructor
    · intro h
      obtain ⟨m,hm,he⟩ := mem_image.mp h
      have hmN := mem_range.mp (mem_filter.mp hm).1
      have hh := hprod.trans (bothAboveSet_primePair_product B N m hm)
      have hnm := exactPrimePair_unique (2*N) n m (by omega) (by omega) hh he.symm
      simpa only [hnm] using hm
    · intro h
      exact mem_image.mpr ⟨n,h,rfl⟩
  have hr : (exactPrimePair n).swap∉(bothAboveSet B N).image exactPrimePair := by
    intro h
    obtain ⟨m,hm,he⟩ := mem_image.mp h
    have hmN := mem_range.mp (mem_filter.mp hm).1
    have hh := hprod.trans (bothAboveSet_primePair_product B N m hm)
    apply exactPrimePair_reverse_impossible N n m hn hmN hh
    simpa only [Prod.swap_swap] using (congrArg Prod.swap he).symm
  change (if exactPrimePair n∈(bothAboveSet B N).image exactPrimePair then (1 : ℝ) else 0)-
    (if (exactPrimePair n).swap∈(bothAboveSet B N).image exactPrimePair then 1 else 0)=_
  simp only [hf,if_neg hr,sub_zero]

lemma primePairAsymmetryTest_mean (B N : ℕ) (hprod : 2*N≤(B+1)^2) :
    (∑ n∈range N, primePairAsymmetryTest B N (Nat.maxPrimeFac n)
      (Nat.maxPrimeFac (n+1)))/(N : ℝ) = ((bothAboveSet B N).card : ℝ)/N := by
  congr 1
  calc
    _ = ∑ n∈range N, if n∈bothAboveSet B N then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro n hn
      exact primePairAsymmetryTest_on_sequence B N n (mem_range.mp hn) hprod
    _ = _ := by
      rw [sum_boole]
      have hs : (range N).filter (fun n => n∈bothAboveSet B N)=bothAboveSet B N := by
        ext n
        simp only [mem_filter]
        exact and_iff_right_of_imp (fun hn => (mem_filter.mp hn).1)
      rw [hs]

/-- There is an endpoint-dependent unit-bounded antisymmetric exact-prime
observable with a positive adjacent natural mean. It need not depend only
on the order of its arguments, or factor through any fixed quantization. -/
theorem exists_moving_prime_pair_skew_with_positive_mean :
    ∃ C : ℕ → ℕ → ℕ → ℝ,
      (∀ N a b, C N b a = -C N a b) ∧
      (∀ N a b, |C N a b|≤1) ∧
      ∀ᶠ N : ℕ in atTop, (1/20 : ℝ)≤
        (∑ n∈range N, C N (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)))/(N : ℝ) := by
  refine ⟨fun N => primePairAsymmetryTest (ceilPowerCutoff (21/40) N) N,
    (fun N a b => primePairAsymmetryTest_skew _ N a b),
    (fun N a b => primePairAsymmetryTest_bound _ N a b),?_⟩
  filter_upwards [bothAbove_upperHalf_positive_proportion,
    ceilPowerCutoff_upperHalf_product_eventually] with N hmass hprod
  rwa [primePairAsymmetryTest_mean _ N hprod]

#print axioms exactPrimePair_reverse_impossible
#print axioms exists_moving_prime_pair_skew_with_positive_mean
end Erdos371
