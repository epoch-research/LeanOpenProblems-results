import Submission.ClosedSmoothFibers
import Submission.ParametricWideDensity

/-!
# Closed small-radical outputs at the current uniform multiplicity exponent

This preserves, but does not amplify, the exponent from a smooth-prime count.
It is not a settlement of Erdős 821.
-/
open Nat Filter
open scoped Classical BigOperators
namespace Erdos821.ClosedPadding
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

lemma primeProduct_primesBelow_le_four_pow (y : ℕ) :
    primeProduct y.primesBelow ≤ 4^y := by
  apply le_trans ?_ (primorial_le_4_pow y)
  unfold primeProduct primorial
  apply Finset.prod_le_prod_of_subset_of_one_le'
  · intro p hp
    obtain ⟨hpy,hp⟩ := Nat.mem_primesBelow.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp⟩
  · intro p hp _
    exact (Finset.mem_filter.mp hp).2.pos

lemma small_core_fibers_of_general_density (t a b : ℕ)
    (hbt : b+4 ≤ t) (hba : b+3 ≤ a) (hat : a ≤ t)
    (H : ∀ M : ℕ, ∃ L : ℕ, M ≤ L ∧ ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2^(t*L) ∧
        p-1 ∈ Nat.smoothNumbers (2^(b*L))) ∧ 2^(a*L) ≤ P.card)
    (r N : ℕ) :
    ∃ n y : ℕ, N < n ∧ (n : ℝ)^((a-b-2 : ℕ)/(t : ℝ)) < g n ∧
      n.primeFactors ⊆ y.primesBelow ∧ (primeProduct y.primesBelow)^r ≤ n := by
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0<t by omega)
  have hδ : 0 < ((a-b-2 : ℕ) : ℝ)/(t : ℝ) := by
    apply div_pos _ htR
    exact_mod_cast (show 0<a-b-2 by omega)
  obtain ⟨L,hLM,P,hP,hcard⟩ := H (max 1 (max t (max N (2*r+1))))
  have hL : 1 ≤ L := (le_max_left _ _).trans hLM
  have htL : t ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hLM)
  have hNL : N ≤ L := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hLM))
  have hrL : 2*r+1 ≤ L := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hLM))
  let k := 2^((b+1)*L)
  let y := 2^(b*L)
  have hk : 0<k := by dsimp [k]; positivity
  have hy : 0<y := by dsimp [y]; positivity
  have hky : k = 2^L*y := by
    dsimp [k,y]
    rw [← pow_add]
    congr 1
    ring
  have hLk : L ≤ k-1 := by
    have hLp := Nat.lt_two_pow_self (n := L)
    have hmul : 2^L ≤ 2^L*y := Nat.le_mul_of_pos_right _ hy
    omega
  have hmargin : ((t*L*k+1)^y : ℝ)*(2 : ℝ)^((a-b-2)*L*k) < (P.card.choose k : ℝ) := by
    exact_mod_cast (general_smooth_prime_counting_margin t a b L hbt hba hat hL htL).trans_le
      (Nat.choose_le_choose k hcard)
  obtain ⟨n,R,hnlo,hnhi,hRcard,hR⟩ := large_squarefree_fiber_of_smooth_shifted_primes
    P (t*L) y k ((2 : ℝ)^((a-b-2)*L*k)) (by positivity) hP
    (by simpa only [Nat.cast_mul] using hmargin)
  have hNn : N<n := hNL.trans_lt ((Nat.lt_two_pow_self (n := L)).trans_le
    ((Nat.pow_le_pow_right (by decide) hLk).trans hnlo))
  have hexp : ((t*L*k : ℕ) : ℝ)*(((a-b-2 : ℕ) : ℝ)/t) =
      (((a-b-2)*L*k : ℕ) : ℝ) := by
    push_cast
    field_simp
  have hpow : (n : ℝ)^((a-b-2 : ℕ)/(t : ℝ)) ≤ (2 : ℝ)^((a-b-2)*L*k) := by
    calc
      _ ≤ ((2 : ℝ)^(t*L*k))^((a-b-2 : ℕ)/(t : ℝ)) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hnhi) hδ.le
      _ = (2 : ℝ)^(((t*L*k : ℕ) : ℝ)*(((a-b-2 : ℕ) : ℝ)/t)) :=
        (Real.rpow_natCast_mul (by norm_num) _ _).symm
      _ = _ := by rw [hexp,Real.rpow_natCast]
  have hRle : R.card ≤ g n := by
    have h := Set.ncard_le_ncard (s := (R : Set ℕ)) (t := {m : ℕ | totient m=n})
      (fun m hm => (hR m hm).2.1) (finite_totient_fiber n)
    simpa only [Set.ncard_coe_finset,g] using h
  have hRpos : 0<R.card := by
    exact_mod_cast (lt_of_lt_of_le (by positivity : (0 : ℝ)<(2 : ℝ)^((a-b-2)*L*k)) hRcard.le)
  obtain ⟨m,hm⟩ := Finset.card_pos.mp hRpos
  have hφ : totient (∏ p ∈ m.primeFactors, p)=n := by
    rw [Nat.prod_primeFactors_of_squarefree (hR m hm).1]
    exact (hR m hm).2.1
  have hnSmooth : n ∈ Nat.smoothNumbers y := by
    rw [← hφ,totient_prod_primes _ (fun p hp => Nat.prime_of_mem_primeFactors hp)]
    exact prod_smooth _ (fun p => p-1) y
      (fun p hp => (hP p ((hR m hm).2.2.2 hp)).2.2)
  have hcore : (primeProduct y.primesBelow)^r ≤ n := by
    have hcoeff : 2*y*r ≤ k-1 := by
      have htwo : 2*r+1 ≤ 2^L := hrL.trans Nat.lt_two_pow_self.le
      have hh := Nat.mul_le_mul_right y htwo
      have hlt : 2*y*r < k := by rw [hky]; nlinarith only [hh,hy]
      omega
    calc
      _ ≤ (4^y)^r := Nat.pow_le_pow_left (primeProduct_primesBelow_le_four_pow y) r
      _ = 2^(2*y*r) := by
        rw [show (4 : ℕ)=2^2 by decide,← pow_mul,← pow_mul,mul_assoc]
      _ ≤ 2^(k-1) := Nat.pow_le_pow_right (by decide) hcoeff
      _ ≤ n := hnlo
  exact ⟨n,y,hNn,(hpow.trans_lt hRcard).trans_le (by exact_mod_cast hRle),
    Nat.primeFactors_subset_of_mem_smoothNumbers hnSmooth,hcore⟩

lemma closed_fibers_of_small_cores (α γ : ℝ) (hγ : 0 ≤ γ) (hγα : γ<α)
    (H : ∀ s N : ℕ, ∃ n y : ℕ, N<n ∧ (n : ℝ)^α < g n ∧
      n.primeFactors ⊆ y.primesBelow ∧ (primeProduct y.primesBelow)^s ≤ n)
    (r N : ℕ) :
    ∃ n : ℕ, N<n ∧ (n : ℝ)^γ < g n ∧
      RadicalLift.radical n^r ≤ n ∧ totient (RadicalLift.radical n) ∣ n := by
  have hgap : 0<α-γ := sub_pos.mpr hγα
  obtain ⟨u,hu⟩ := exists_nat_gt ((γ+1)/(α-γ))
  let s := max (r+1) u
  have hsN : 0<s := lt_of_lt_of_le (Nat.succ_pos r) (le_max_left _ _)
  have hs : (0 : ℝ)<s := by exact_mod_cast hsN
  have hus : (u : ℝ) ≤ s := by exact_mod_cast (le_max_right (r+1) u)
  have hratio := (div_lt_iff₀ hgap).mp (hu.trans_le hus)
  have hdiv : (γ+1)/(s : ℝ) < α-γ := (div_lt_iff₀ hs).mpr (by nlinarith [hratio])
  have hbudget : (1+1/(s : ℝ))*γ+1/(s : ℝ) ≤ α := by
    have he : (1+1/(s : ℝ))*γ+1/(s : ℝ) = γ+(γ+1)/(s : ℝ) := by ring
    rw [he]
    linarith
  obtain ⟨n,y,hNn,hgn,hnC,hcore⟩ := H s N
  have hn : 0<n := lt_of_le_of_lt (Nat.zero_le _) hNn
  let C := y.primesBelow
  have hC : ∀ p ∈ C, p.Prime := fun p hp => (Nat.mem_primesBelow.mp hp).2
  have hclosed : (predProduct C).primeFactors ⊆ C := primesBelow_closed y
  have hcoreR : (primeProduct C : ℝ) ≤ (n : ℝ)^(1/(s : ℝ)) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg _) (Nat.cast_nonneg _) hs).mpr
    rw [Real.rpow_natCast]
    exact_mod_cast hcore
  have hstr := padded_output_structure hn C hC hclosed hnC
  refine ⟨n*predProduct C,hNn.trans_le hstr.1,
    padding_power_bound hn C hC hclosed α γ (1/(s : ℝ)) hγ hbudget hcoreR hgn,
    ?_,hstr.2.2.2⟩
  calc
    _ ≤ primeProduct C^r := Nat.pow_le_pow_left hstr.2.2.1 r
    _ ≤ primeProduct C^s := Nat.pow_le_pow_right (primeProduct_pos C hC)
      (Nat.le_succ r |>.trans (le_max_left _ _))
    _ ≤ n := hcore
    _ ≤ n*predProduct C := hstr.1

theorem closed_fibers_of_eventual_polynomial_count (t b K C d : ℕ)
    (hbt : b<t)
    (H : ∀ᶠ m : ℕ in atTop, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2^(t*m) ∧
        p-1 ∈ Nat.smoothNumbers (K*2^(b*m))) ∧
      2^(t*m) ≤ C*(m+1)^d*P.card)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγb : γ<1-(b : ℝ)/t) (r N : ℕ) :
    ∃ n : ℕ, N<n ∧ (n : ℝ)^γ < g n ∧
      RadicalLift.radical n^r ≤ n ∧ totient (RadicalLift.radical n) ∣ n := by
  have ht : 0<t := lt_of_le_of_lt (Nat.zero_le b) hbt
  have htR : (0 : ℝ)<t := by exact_mod_cast ht
  have hγ' : γ < ((t : ℝ)-b)/t := by
    convert hγb using 1
    field_simp
  have hmargin : 0 < (t : ℝ)-b-t*γ := by
    have h := (lt_div_iff₀ htR).mp hγ'
    nlinarith only [h]
  obtain ⟨k,hk⟩ := exists_nat_gt (max 5 (4/((t : ℝ)-b-t*γ)))
  have hk5R : (5 : ℝ)<k := (le_max_left _ _).trans_lt hk
  have hk5 : 5 ≤ k := by exact_mod_cast hk5R.le
  have h4 : 4 < (k : ℝ)*((t : ℝ)-b-t*γ) :=
    (div_lt_iff₀ hmargin).mp ((le_max_right _ _).trans_lt hk)
  have hgap : b*k+5 ≤ t*k := by
    have h := Nat.mul_le_mul_right k (show b+1 ≤ t by omega)
    nlinarith only [h,hk5]
  have hnum : ((t*k-1-(b*k+1)-2 : ℕ) : ℝ) = (t : ℝ)*k-b*k-4 := by
    rw [Nat.cast_sub (by omega : 2 ≤ t*k-1-(b*k+1)),
      Nat.cast_sub (by omega : b*k+1 ≤ t*k-1),Nat.cast_sub (by omega : 1 ≤ t*k)]
    push_cast
    ring
  have htkR : (0 : ℝ)<(t*k : ℕ) := by
    exact_mod_cast Nat.mul_pos ht (by omega : 0<k)
  have hγk : γ < ((t*k-1-(b*k+1)-2 : ℕ) : ℝ)/(t*k : ℕ) := by
    apply (lt_div_iff₀ htkR).mpr
    rw [hnum,Nat.cast_mul]
    nlinarith only [h4]
  exact closed_fibers_of_small_cores _ γ hγ hγk
    (small_core_fibers_of_general_density (t*k) (t*k-1) (b*k+1)
      (by omega) (by omega) (by omega)
      (dyadic_family_of_eventual_polynomial_count t b K C d k ht (by omega) H)) r N

/-- The strongest current exponent is compatible with arbitrarily large
closed outputs having radicals below every prescribed root. No increase
of the multiplicity exponent is asserted. -/
theorem wide_block_closed_small_radical_fibers (γ : ℝ) (hγ : 0 ≤ γ)
    (hγb : γ<1036568/2000001) (r N : ℕ) :
    ∃ n : ℕ, N<n ∧ (n : ℝ)^γ < g n ∧
      RadicalLift.radical n^r ≤ n ∧ totient (RadicalLift.radical n) ∣ n := by
  obtain ⟨C,_hC,H⟩ := exists_wide_block_smooth_prime_count
  apply closed_fibers_of_eventual_polynomial_count (64*40000020) (64*19268660)
    1 C 1 (by omega) ?_ γ hγ ?_ r N
  · filter_upwards [H] with m hm
    refine ⟨smoothPrimePool (independentN 40000020 m) (independentN 19268660 m),?_,?_⟩
    · intro p hp
      obtain ⟨hp,hs⟩ := Finset.mem_filter.mp hp
      obtain ⟨hN,hpr⟩ := Nat.mem_primesBelow.mp hp
      refine ⟨hpr,?_,?_⟩
      · change p ≤ independentN 40000020 m
        omega
      · simpa only [one_mul] using hs
    · have hh : independentN 40000020 m ≤
          C*m*(smoothPrimePool (independentN 40000020 m) (independentN 19268660 m)).card := by
        exact_mod_cast hm
      exact hh.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left C (by simp)))
  · norm_num
    exact hγb

end Erdos821.ClosedPadding
