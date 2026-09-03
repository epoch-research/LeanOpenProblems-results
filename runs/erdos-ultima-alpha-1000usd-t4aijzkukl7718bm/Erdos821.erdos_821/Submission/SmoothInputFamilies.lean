import Submission.SquarefreeInput
import Submission.Sieve

/-!
# Polynomial-size fibers with root-smooth squarefree inputs

This file traces the inputs in the previously proved fixed-exponent lower
bound. It does not improve the multiplicity exponent or settle Erdős 821.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

lemma two_pow_card_sub_one_le_totient_prod_primes (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    2 ^ (P.card - 1) ≤ totient (∏ p ∈ P, p) := by
  rw [totient_prod_primes P hP]
  calc
    2 ^ (P.card - 1) ≤ 2 ^ (P.erase 2).card :=
      Nat.pow_le_pow_right (by decide) Finset.pred_card_le_card_erase
    _ = ∏ _p ∈ P.erase 2, 2 := by simp
    _ ≤ ∏ p ∈ P.erase 2, (p - 1) := by
      apply Finset.prod_le_prod'
      intro p hp
      obtain ⟨hp2, hpP⟩ := Finset.mem_erase.mp hp
      have := (hP p hpP).two_le
      omega
    _ ≤ ∏ p ∈ P, (p - 1) :=
      Finset.prod_le_prod_of_subset_of_one_le' (Finset.erase_subset _ _)
        (fun p hp _ => by have := (hP p hp).two_le; omega)

/-- The finite pigeonhole construction retains squarefree inputs with exactly
`k` prime factors drawn from `P`, and the output is at least `2^(k-1)`. -/
lemma large_squarefree_fiber_of_smooth_shifted_primes (P : Finset ℕ) (L y k : ℕ)
    (B : ℝ) (hB : 0 ≤ B)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ L ∧ p - 1 ∈ Nat.smoothNumbers y)
    (hcard : ((L * k + 1) ^ y : ℝ) * B < (P.card.choose k : ℝ)) :
    ∃ (n : ℕ) (R : Finset ℕ),
      2 ^ (k - 1) ≤ n ∧ n ≤ 2 ^ (L * k) ∧ B < (R.card : ℝ) ∧
      ∀ m ∈ R, Squarefree m ∧ totient m = n ∧
        m.primeFactors.card = k ∧ m.primeFactors ⊆ P := by
  let S := (P.powersetCard k).image (fun T : Finset ℕ => ∏ p ∈ T, p)
  let T := Nat.smoothNumbersUpTo (2 ^ (L * k)) y
  have hSinj : Set.InjOn (fun s : Finset ℕ => ∏ p ∈ s, p)
      (↑(P.powersetCard k) : Set (Finset ℕ)) := by
    intro s hs t ht heq
    have hsp : ∀ p ∈ s, p.Prime := fun p hp => (hP p ((Finset.mem_powersetCard.mp hs).1 hp)).1
    have htp : ∀ p ∈ t, p.Prime := fun p hp => (hP p ((Finset.mem_powersetCard.mp ht).1 hp)).1
    have heq' := congrArg Nat.primeFactors heq
    simpa only [Nat.primeFactors_prod hsp, Nat.primeFactors_prod htp] using heq'
  have hScard : S.card = P.card.choose k := by
    dsimp only [S]
    rw [Finset.card_image_of_injOn hSinj, Finset.card_powersetCard]
  have hSstructure (m : ℕ) (hm : m ∈ S) :
      Squarefree m ∧ m.primeFactors.card = k ∧ m.primeFactors ⊆ P ∧
        2 ^ (k - 1) ≤ totient m := by
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hsP, hsk⟩ := Finset.mem_powersetCard.mp hs
    have hsp : ∀ p ∈ s, p.Prime := fun p hp => (hP p (hsP hp)).1
    refine ⟨squarefree_prod_of_primes s hsp, ?_, ?_, ?_⟩
    · rw [Nat.primeFactors_prod hsp, hsk]
    · rwa [Nat.primeFactors_prod hsp]
    · rw [← hsk]
      exact two_pow_card_sub_one_le_totient_prod_primes s hsp
  have hmap : ∀ m ∈ S, totient m ∈ T := by
    intro m hm
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hsP, hsk⟩ := Finset.mem_powersetCard.mp hs
    have hsp : ∀ p ∈ s, p.Prime := fun p hp => (hP p (hsP hp)).1
    apply Nat.mem_smoothNumbersUpTo.mpr
    constructor
    · calc
        totient (∏ p ∈ s, p) ≤ ∏ p ∈ s, p := Nat.totient_le _
        _ ≤ (2 ^ L) ^ s.card := Finset.prod_le_pow_card s id (2 ^ L)
          (fun p hp => (hP p (hsP hp)).2.1)
        _ = 2 ^ (L * k) := by rw [hsk, pow_mul]
    · rw [totient_prod_primes s hsp]
      exact prod_smooth s (fun p => p - 1) y (fun p hp => (hP p (hsP hp)).2.2)
  have hTcard : (T.card : ℝ) ≤ ((L * k + 1) ^ y : ℝ) := by
    exact_mod_cast smoothNumbersUpTo_two_pow_card_le (L * k) y
  have hcount : (T.card : ℝ) * B < S.card := by
    rw [hScard]
    exact (mul_le_mul_of_nonneg_right hTcard hB).trans_lt hcard
  obtain ⟨n, hn, hg⟩ := Finset.exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to
    hmap (by simpa only [nsmul_eq_mul] using hcount)
  let R := S.filter (fun m => totient m = n)
  have hRpos : 0 < R.card := by exact_mod_cast hB.trans_lt hg
  obtain ⟨m, hm⟩ := Finset.card_pos.mp hRpos
  obtain ⟨hmS, hmφ⟩ := Finset.mem_filter.mp hm
  refine ⟨n, R, hmφ ▸ (hSstructure m hmS).2.2.2,
    (Nat.mem_smoothNumbersUpTo.mp hn).1, hg, ?_⟩
  intro a ha
  obtain ⟨haS, haφ⟩ := Finset.mem_filter.mp ha
  have h := hSstructure a haS
  exact ⟨h.1, haφ, h.2.1, h.2.2.1⟩

/-- Retaining the inputs in the fixed-scale construction gives large
squarefree fibers whose prime factors are smooth to any prescribed root of
the output. The multiplicity exponent is still the old fixed exponent. -/
lemma root_smooth_input_fibers_of_weak_density (t : ℕ) (ht : 6 ≤ t)
    (H : ∀ M : ℕ, ∃ L : ℕ, M ≤ L ∧ ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (t * L) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ ((t - 5) * L))) ∧
      2 ^ ((t - 1) * L) ≤ P.card) (r N : ℕ) :
    ∃ (n : ℕ) (R : Finset ℕ), N < n ∧ (n : ℝ) ^ (2 / (t : ℝ)) < R.card ∧
      ∀ m ∈ R, Squarefree m ∧ totient m = n ∧
        ∀ p ∈ m.primeFactors, p ^ r ≤ n := by
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
  have hksq : L ^ 2 ≤ k := by
    apply (Sieve.sq_le_two_pow L hL4).trans
    apply Nat.pow_le_pow_right (by decide)
    have hcoeff : 1 ≤ t - 4 := by omega
    nlinarith
  have hrk : t * L * r ≤ k - 1 := by
    have hprod := Nat.mul_le_mul_right L hrL
    have hle : t * L * r + 1 ≤ k := by nlinarith
    omega
  have hLk : L ≤ k - 1 := by
    have hle : L + 1 ≤ k := by nlinarith
    omega
  have hmargin : ((t * L * k + 1) ^ (2 ^ ((t - 5) * L)) : ℝ) *
      (2 : ℝ) ^ (2 * L * k) < (P.card.choose k : ℝ) := by
    exact_mod_cast (weak_smooth_prime_counting_margin t L ht (by omega) htL).trans_le
      (Nat.choose_le_choose (2 ^ ((t - 4) * L)) hcard)
  obtain ⟨n, R, hnlower, hnupper, hRcard, hR⟩ :=
    large_squarefree_fiber_of_smooth_shifted_primes P (t * L)
      (2 ^ ((t - 5) * L)) k ((2 : ℝ) ^ (2 * L * k)) (by positivity) hP
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
  refine ⟨n, R, hNn, hpow.trans_lt hRcard, ?_⟩
  intro m hm
  have h := hR m hm
  refine ⟨h.1, h.2.1, ?_⟩
  intro p hp
  calc
    p ^ r ≤ (2 ^ (t * L)) ^ r := Nat.pow_le_pow_left (hP p (h.2.2.2 hp)).2.1 r
    _ = 2 ^ (t * L * r) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by decide) hrk
    _ ≤ n := hnlower

/-- Unconditionally, one fixed positive multiplicity exponent is compatible
with inputs whose prime factors lie below every fixed root of the output. -/
theorem exists_fixed_power_root_smooth_input_fibers :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ r N : ℕ,
      ∃ (n : ℕ) (R : Finset ℕ), N < n ∧ (n : ℝ) ^ δ < R.card ∧
        ∀ m ∈ R, Squarefree m ∧ totient m = n ∧
          ∀ p ∈ m.primeFactors, p ^ r ≤ n := by
  obtain ⟨t, ht, H⟩ := Sieve.exists_fixed_smooth_shifted_prime_density
  have htR : (6 : ℝ) ≤ t := by exact_mod_cast ht
  refine ⟨2 / (t : ℝ), div_pos (by norm_num) (by linarith), ?_, ?_⟩
  · exact (div_lt_one (by linarith)).mpr (by linarith)
  · exact root_smooth_input_fibers_of_weak_density t ht H

/-- A real-exponent version: polynomial-size subfamilies need not contain
ANY input prime at least `n^η`, for any fixed `η>0`. Thus polynomial size alone
cannot justify that hypothesis in the popular-prime extraction lemma. -/
theorem exists_fixed_power_fibers_without_large_input_primes :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ η : ℝ, 0 < η → ∀ N : ℕ,
      ∃ (n : ℕ) (R : Finset ℕ), N < n ∧ (n : ℝ) ^ δ < R.card ∧
        ∀ m ∈ R, Squarefree m ∧ totient m = n ∧
          ∀ p : ℕ, p.Prime → p ∣ m → (p : ℝ) < (n : ℝ) ^ η := by
  obtain ⟨δ, hδ, hδ1, H⟩ := exists_fixed_power_root_smooth_input_fibers
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro η hη N
  obtain ⟨r, hr⟩ := exists_nat_gt (1 / η)
  have hrR : (0 : ℝ) < r := (div_pos (by norm_num) hη).trans hr
  have hrN : r ≠ 0 := by exact_mod_cast hrR.ne'
  have hηr : 1 < η * (r : ℝ) := by
    have h := (div_lt_iff₀ hη).mp hr
    linarith
  obtain ⟨n, R, hnN, hcard, hR⟩ := H r (max N 1)
  have hn1 : (1 : ℝ) < n := by
    exact_mod_cast (le_max_right N 1).trans_lt hnN
  refine ⟨n, R, (le_max_left _ _).trans_lt hnN, hcard, ?_⟩
  intro m hm
  have hmR := hR m hm
  refine ⟨hmR.1, hmR.2.1, ?_⟩
  intro p hp hpm
  have hroot : (p : ℝ) ^ r ≤ (n : ℝ) := by
    exact_mod_cast hmR.2.2 p (hp.mem_primeFactors hpm hmR.1.ne_zero)
  have hstrict : (n : ℝ) < ((n : ℝ) ^ η) ^ r := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ η) r, ← Real.rpow_mul (Nat.cast_nonneg n)]
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hn1 hηr
  exact (pow_lt_pow_iff_left₀ (Nat.cast_nonneg p)
    (Real.rpow_nonneg (Nat.cast_nonneg n) η) hrN).mp (hroot.trans_lt hstrict)

/-- Removing a possible factor of two costs at most a factor of two in
cardinality and preserves the totient of squarefree inputs. -/
lemma exists_odd_squarefree_subfiber (S : Finset ℕ) (n : ℕ)
    (hS : ∀ m ∈ S, Squarefree m ∧ totient m = n) :
    ∃ R : Finset ℕ, S.card ≤ 2 * R.card ∧
      ∀ m ∈ R, Squarefree m ∧ Odd m ∧ totient m = n ∧ ∃ a ∈ S, m ∣ a := by
  let O := S.filter Odd
  let E := S.filter (fun m => ¬Odd m)
  let D := E.image (fun m => m / 2)
  let R := O ∪ D
  have hEdiv (m : ℕ) (hm : m ∈ E) : 2 ∣ m :=
    (Nat.not_odd_iff_even.mp (Finset.mem_filter.mp hm).2).two_dvd
  have hinj : Set.InjOn (fun m : ℕ => m / 2) (E : Set ℕ) := by
    intro a ha b hb hab
    calc
      a = 2 * (a / 2) := (Nat.mul_div_cancel' (hEdiv a ha)).symm
      _ = 2 * (b / 2) := congrArg (fun m : ℕ => 2 * m) hab
      _ = b := Nat.mul_div_cancel' (hEdiv b hb)
  have hDcard : D.card = E.card := Finset.card_image_of_injOn hinj
  have hOcard : O.card ≤ R.card := Finset.card_le_card (Finset.subset_union_left)
  have hEcard : E.card ≤ R.card := by
    rw [← hDcard]
    exact Finset.card_le_card (Finset.subset_union_right)
  have hsum : O.card + E.card = S.card := Finset.card_filter_add_card_filter_not _
  refine ⟨R, by omega, ?_⟩
  intro m hm
  obtain hm | hm := Finset.mem_union.mp hm
  · obtain ⟨hmS, hmO⟩ := Finset.mem_filter.mp hm
    exact ⟨(hS m hmS).1, hmO, (hS m hmS).2, m, hmS, dvd_rfl⟩
  · obtain ⟨a, haE, rfl⟩ := Finset.mem_image.mp hm
    have haS := (Finset.mem_filter.mp haE).1
    have ha2 := hEdiv a haE
    have hdiv := Nat.div_dvd_of_dvd ha2
    have hcop : Nat.Coprime 2 (a / 2) := by
      apply Nat.coprime_of_squarefree_mul
      rw [Nat.mul_div_cancel' ha2]
      exact (hS a haS).1
    have hφ : totient (a / 2) = n := by
      have h := Nat.totient_mul hcop
      rw [Nat.mul_div_cancel' ha2, Nat.totient_two, one_mul, (hS a haS).2] at h
      exact h.symm
    exact ⟨(hS a haS).1.squarefree_of_dvd hdiv, Nat.coprime_two_left.mp hcop,
      hφ, a, haS, hdiv⟩

/-- The obstruction to extracting a polynomially large input prime persists
even for squarefree ODD subfamilies of polynomial size. -/
theorem exists_fixed_power_odd_fibers_without_large_input_primes :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ η : ℝ, 0 < η → ∀ N : ℕ,
      ∃ (n : ℕ) (R : Finset ℕ), N < n ∧ (n : ℝ) ^ δ < R.card ∧
        ∀ m ∈ R, Squarefree m ∧ Odd m ∧ totient m = n ∧
          ∀ p : ℕ, p.Prime → p ∣ m → (p : ℝ) < (n : ℝ) ^ η := by
  obtain ⟨δ, hδ, hδ1, H⟩ := exists_fixed_power_fibers_without_large_input_primes
  refine ⟨δ / 2, half_pos hδ, by linarith, ?_⟩
  intro η hη N
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (δ / 2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hδ)).comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hlim.eventually (eventually_gt_atTop (2 : ℝ)))
  obtain ⟨n, S, hnN, hScard, hS⟩ := H η hη (max N (max M 1))
  have hnM : M ≤ n := (le_max_left M 1).trans ((le_max_right _ _).trans hnN.le)
  have hnpos : (0 : ℝ) < n := by
    have hn1 : 1 ≤ n := (le_max_right M 1).trans ((le_max_right _ _).trans hnN.le)
    exact_mod_cast (show 0 < n by omega)
  have hpow2 : 2 < (n : ℝ) ^ (δ / 2) := hM n hnM
  have hpowid : (n : ℝ) ^ δ = (n : ℝ) ^ (δ / 2) * (n : ℝ) ^ (δ / 2) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  have hsmall : 2 * (n : ℝ) ^ (δ / 2) < (n : ℝ) ^ δ := by
    rw [hpowid]
    nlinarith
  obtain ⟨R, hRcard, hR⟩ := exists_odd_squarefree_subfiber S n
    (fun m hm => ⟨(hS m hm).1, (hS m hm).2.1⟩)
  have hRcardR : (S.card : ℝ) ≤ 2 * (R.card : ℝ) := by exact_mod_cast hRcard
  refine ⟨n, R, (le_max_left _ _).trans_lt hnN, by linarith, ?_⟩
  intro m hm
  have h := hR m hm
  obtain ⟨a, ha, hma⟩ := h.2.2.2
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro p hp hpm
  exact (hS a ha).2.2 p hp (hpm.trans hma)

#print axioms large_squarefree_fiber_of_smooth_shifted_primes
#print axioms root_smooth_input_fibers_of_weak_density
#print axioms exists_fixed_power_root_smooth_input_fibers
#print axioms exists_fixed_power_fibers_without_large_input_primes
#print axioms exists_odd_squarefree_subfiber
#print axioms exists_fixed_power_odd_fibers_without_large_input_primes

end Erdos821
