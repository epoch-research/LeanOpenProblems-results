import Submission.ClosedSupportPadding
import Submission.SmoothInputFamilies

/-!
# Positive-power fibers at closed outputs with small radicals

The weak smooth-prime supply can be used while making the padding core
subpower at the selected output's own scale. This preserves a fixed positive
multiplicity exponent, but does not establish exponents approaching one.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821.ClosedPadding

set_option maxHeartbeats 2000000

lemma small_core_fibers_of_weak_density (t : ℕ) (ht : 6 ≤ t)
    (H : ∀ M : ℕ, ∃ L : ℕ, M ≤ L ∧ ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (t * L) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ ((t - 5) * L))) ∧
      2 ^ ((t - 1) * L) ≤ P.card) (r N : ℕ) :
    ∃ n y : ℕ, N < n ∧ (n : ℝ) ^ (2 / (t : ℝ)) < g n ∧
      n.primeFactors ⊆ y.primesBelow ∧ (primeProduct y.primesBelow) ^ r ≤ n := by
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hδ : 0 < 2 / (t : ℝ) := div_pos (by norm_num) htR
  obtain ⟨L, hLM, P, hP, hcard⟩ := H (max 4 (max t (max N (t * r + 2))))
  have hL4 : 4 ≤ L := (le_max_left _ _).trans hLM
  have htL : t ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hLM)
  have hNL : N ≤ L := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hLM))
  have hrL : t * r + 2 ≤ L := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hLM))
  let k := 2 ^ ((t - 4) * L)
  let y := 2 ^ ((t - 5) * L)
  have hkpos : 0 < k := by dsimp [k]; positivity
  have hksq : L ^ 2 ≤ k := by
    apply (Sieve.sq_le_two_pow L hL4).trans
    apply Nat.pow_le_pow_right (by decide)
    have hcoeff : 1 ≤ t - 4 := by omega
    nlinarith
  have hLk : L ≤ k - 1 := by
    have hle : L + 1 ≤ k := by nlinarith
    omega
  have hmargin : ((t * L * k + 1) ^ y : ℝ) *
      (2 : ℝ) ^ (2 * L * k) < (P.card.choose k : ℝ) := by
    exact_mod_cast (weak_smooth_prime_counting_margin t L ht (by omega) htL).trans_le
      (Nat.choose_le_choose k hcard)
  obtain ⟨n, R, hnlower, hnupper, hRcard, hR⟩ :=
    large_squarefree_fiber_of_smooth_shifted_primes P (t * L) y k
      ((2 : ℝ) ^ (2 * L * k)) (by positivity) hP
      (by simpa only [Nat.cast_mul] using hmargin)
  have hNn : N < n := by
    calc
      N ≤ L := hNL
      _ < 2 ^ L := Nat.lt_two_pow_self
      _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by decide) hLk
      _ ≤ n := hnlower
  have hexp : ((t * L * k : ℕ) : ℝ) * (2 / (t : ℝ)) =
      ((2 * L * k : ℕ) : ℝ) := by
    push_cast
    field_simp
  have hpow : (n : ℝ) ^ (2 / (t : ℝ)) ≤ (2 : ℝ) ^ (2 * L * k) := by
    calc
      (n : ℝ) ^ (2 / (t : ℝ)) ≤ ((2 : ℝ) ^ (t * L * k)) ^ (2 / (t : ℝ)) :=
        Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnupper) hδ.le
      _ = (2 : ℝ) ^ (((t * L * k : ℕ) : ℝ) * (2 / (t : ℝ))) :=
        (Real.rpow_natCast_mul (by norm_num) _ _).symm
      _ = _ := by rw [hexp, Real.rpow_natCast]
  have hRle : R.card ≤ g n := by
    have h := Set.ncard_le_ncard (s := (R : Set ℕ)) (t := {m : ℕ | totient m = n})
      (fun m hm => (hR m hm).2.1) (finite_totient_fiber n)
    simpa only [Set.ncard_coe_finset, g] using h
  have hRpos : 0 < R.card := by
    have h : (0 : ℝ) < R.card := (by positivity : (0 : ℝ) < (2 : ℝ) ^ (2 * L * k)).trans hRcard
    exact_mod_cast h
  obtain ⟨m, hm⟩ := Finset.card_pos.mp hRpos
  have hφ : totient (∏ p ∈ m.primeFactors, p) = n := by
    rw [Nat.prod_primeFactors_of_squarefree (hR m hm).1]
    exact (hR m hm).2.1
  have hnSmooth : n ∈ Nat.smoothNumbers y := by
    rw [← hφ, totient_prod_primes _ (fun p hp => Nat.prime_of_mem_primeFactors hp)]
    exact prod_smooth _ (fun p => p - 1) y
      (fun p hp => (hP p ((hR m hm).2.2.2 hp)).2.2)
  have hyk : y ≤ k := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right L (by omega))
  have hyB : y ≤ t * L * k + 1 := by
    have hcoef : 1 ≤ t * L := Nat.mul_pos (by omega) (by omega)
    nlinarith
  have hcore : (primeProduct y.primesBelow)^r ≤ n := by
    calc
      (primeProduct y.primesBelow)^r ≤ ((t * L * k + 1)^y)^r :=
        Nat.pow_le_pow_left (primeProduct_primesBelow_le y _ (by omega) hyB) r
      _ ≤ 2^(k-1) := dyadic_output_bound_pow_le_totient_lower t L r ht hL4 htL hrL
      _ ≤ n := hnlower
  exact ⟨n, y, hNn, (hpow.trans_lt hRcard).trans_le (by exact_mod_cast hRle),
    Nat.primeFactors_subset_of_mem_smoothNumbers hnSmooth, hcore⟩

/-- Every exponent strictly below the finite weak-density construction's
exponent survives, with both a closed output and an arbitrarily small
radical at that output's own scale. -/
theorem exists_closed_small_radical_fiber_of_weak_density (t : ℕ) (ht : 6 ≤ t)
    (H : ∀ M : ℕ, ∃ L : ℕ, M ≤ L ∧ ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (t * L) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ ((t - 5) * L))) ∧
      2 ^ ((t - 1) * L) ≤ P.card) (γ : ℝ) (hγ : 0 ≤ γ)
    (hγt : γ < 2 / (t : ℝ)) (r N : ℕ) :
    ∃ n : ℕ, N < n ∧ (n : ℝ) ^ γ < g n ∧
      RadicalLift.radical n ^ r ≤ n ∧ totient (RadicalLift.radical n) ∣ n := by
  let α : ℝ := 2 / (t : ℝ)
  have hgap : 0 < α - γ := sub_pos.mpr hγt
  obtain ⟨u, hu⟩ := exists_nat_gt ((γ + 1) / (α - γ))
  let s := max (r + 1) u
  have hsN : 0 < s := lt_of_lt_of_le (Nat.succ_pos r) (le_max_left _ _)
  have hs : (0 : ℝ) < s := by exact_mod_cast hsN
  have hus : (u : ℝ) ≤ s := by exact_mod_cast (le_max_right (r + 1) u)
  have hratio := (div_lt_iff₀ hgap).mp (hu.trans_le hus)
  have hdiv : (γ + 1) / (s : ℝ) < α - γ :=
    (div_lt_iff₀ hs).mpr (by nlinarith [hratio])
  have hbudget : (1 + 1 / (s : ℝ)) * γ + 1 / (s : ℝ) ≤ α := by
    have heq : (1 + 1 / (s : ℝ)) * γ + 1 / (s : ℝ) = γ + (γ + 1) / (s : ℝ) := by ring
    rw [heq]
    linarith
  obtain ⟨n, y, hNn, hgn, hnC, hcore⟩ := small_core_fibers_of_weak_density t ht H s N
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hNn
  let C := y.primesBelow
  have hC : ∀ p ∈ C, p.Prime := fun p hp => (Nat.mem_primesBelow.mp hp).2
  have hclosed : (predProduct C).primeFactors ⊆ C := primesBelow_closed y
  have hcoreR : (primeProduct C : ℝ) ≤ (n : ℝ) ^ (1 / (s : ℝ)) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg _) (Nat.cast_nonneg _) hs).mpr
    rw [Real.rpow_natCast]
    exact_mod_cast hcore
  have hstr := padded_output_structure hn C hC hclosed hnC
  refine ⟨n * predProduct C, hNn.trans_le hstr.1,
    padding_power_bound hn C hC hclosed α γ (1 / (s : ℝ)) hγ hbudget hcoreR hgn,
    ?_, hstr.2.2.2⟩
  calc
    RadicalLift.radical (n * predProduct C) ^ r ≤ primeProduct C ^ r :=
      Nat.pow_le_pow_left hstr.2.2.1 r
    _ ≤ primeProduct C ^ s := Nat.pow_le_pow_right (primeProduct_pos C hC)
      (Nat.le_succ r |>.trans (le_max_left _ _))
    _ ≤ n := hcore
    _ ≤ n * predProduct C := hstr.1

/-- There are unconditionally positive-power fibers at arbitrarily large
closed outputs whose radicals are below every prescribed root. The exponent
here is one fixed positive number, not exponents tending to one. -/
theorem exists_fixed_power_closed_small_radical_fibers :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ r N : ℕ,
      ∃ n : ℕ, N < n ∧ (n : ℝ) ^ δ < g n ∧
        RadicalLift.radical n ^ r ≤ n ∧ totient (RadicalLift.radical n) ∣ n := by
  obtain ⟨t, ht, H⟩ := Sieve.exists_fixed_smooth_shifted_prime_density
  have htR : (6 : ℝ) ≤ t := by exact_mod_cast ht
  have htpos : (0 : ℝ) < t := by linarith
  have hδ : 0 < 1 / (t : ℝ) := one_div_pos.mpr htpos
  refine ⟨1 / (t : ℝ), hδ, (div_lt_one htpos).mpr (by linarith), ?_⟩
  exact exists_closed_small_radical_fiber_of_weak_density t ht H _ hδ.le
    ((div_lt_div_iff_of_pos_right htpos).mpr (by norm_num))

end Erdos821.ClosedPadding
