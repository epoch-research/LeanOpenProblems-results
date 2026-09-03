import Submission.CommonCore
import Submission.SmoothInputFamilies

/-!
# Polynomial-size fibers with a quantitative cost for every large common divisor

This combines the finite common-core estimates with the fixed-exponent sieve
construction. It is an obstruction to one proposed amplification hypothesis,
not a proof or disproof of Erdős 821.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

lemma large_squarefree_fiber_with_core_control (P : Finset ℕ) (L y k : ℕ)
    (B s : ℝ) (hB : 0 ≤ B) (hk : 0 < k) (hs : 0 ≤ s)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ L ∧ p - 1 ∈ Nat.smoothNumbers y)
    (hscale : (k : ℝ) * ((2 : ℝ) ^ L) ^ s ≤ P.card)
    (hcard : (((L * k + 1) ^ y : ℕ) : ℝ) * B < (P.card.choose k : ℝ)) :
    ∃ (n : ℕ) (R : Finset ℕ),
      2 ^ (k - 1) ≤ n ∧ n ≤ 2 ^ (L * k) ∧ B < (R.card : ℝ) ∧
      (∀ m ∈ R, Squarefree m ∧ totient m = n ∧
        m.primeFactors.card = k ∧ m.primeFactors ⊆ P) ∧
      ∀ d : ℕ, (d : ℝ) ^ s * ((R.filter (fun m => d ∣ m)).card : ℝ) ≤
        (((L * k + 1) ^ y : ℕ) : ℝ) * (R.card : ℝ) := by
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
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨huP, huk⟩ := Finset.mem_powersetCard.mp hu
    have hup : ∀ p ∈ u, p.Prime := fun p hp => (hP p (huP hp)).1
    refine ⟨squarefree_prod_of_primes u hup, ?_, ?_, ?_⟩
    · rw [Nat.primeFactors_prod hup, huk]
    · rwa [Nat.primeFactors_prod hup]
    · rw [← huk]
      exact two_pow_card_sub_one_le_totient_prod_primes u hup
  have hmap : ∀ m ∈ S, totient m ∈ T := by
    intro m hm
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨huP, huk⟩ := Finset.mem_powersetCard.mp hu
    have hup : ∀ p ∈ u, p.Prime := fun p hp => (hP p (huP hp)).1
    apply Nat.mem_smoothNumbersUpTo.mpr
    constructor
    · calc
        totient (∏ p ∈ u, p) ≤ ∏ p ∈ u, p := Nat.totient_le _
        _ ≤ (2 ^ L) ^ u.card := Finset.prod_le_pow_card u id (2 ^ L)
          (fun p hp => (hP p (huP hp)).2.1)
        _ = 2 ^ (L * k) := by rw [huk, pow_mul]
    · rw [totient_prod_primes u hup]
      exact prod_smooth u (fun p => p - 1) y (fun p hp => (hP p (huP hp)).2.2)
  have hTcard : (T.card : ℝ) ≤ (((L * k + 1) ^ y : ℕ) : ℝ) := by
    exact_mod_cast smoothNumbersUpTo_two_pow_card_le (L * k) y
  have hSpos : 0 < S.card := by
    rw [hScard]
    have hpos : (0 : ℝ) < P.card.choose k := (by positivity :
      (0 : ℝ) ≤ (((L * k + 1) ^ y : ℕ) : ℝ) * B).trans_lt hcard
    exact_mod_cast hpos
  obtain ⟨n, hnT, R, hRS, hRne, hRφ, hpoolT, _⟩ :=
    exists_fiber_with_common_divisor_score_bound P S T k ((2 : ℝ) ^ L) s hk
      (by positivity) hs (fun p hp => by exact_mod_cast (hP p hp).2.1) hscale
      (fun m hm => ⟨(hSstructure m hm).1, (hSstructure m hm).2.1,
        (hSstructure m hm).2.2.1⟩) hScard (Finset.card_pos.mp hSpos) hmap
  have hpool : (P.card.choose k : ℝ) ≤
      (((L * k + 1) ^ y : ℕ) : ℝ) * (R.card : ℝ) :=
    hpoolT.trans (mul_le_mul_of_nonneg_right hTcard (Nat.cast_nonneg _))
  have hDpos : (0 : ℝ) < (((L * k + 1) ^ y : ℕ) : ℝ) := by positivity
  have hRcard : B < (R.card : ℝ) := (mul_lt_mul_iff_right₀ hDpos).mp (hcard.trans_le hpool)
  obtain ⟨m, hm⟩ := hRne
  refine ⟨n, R, (hRφ m hm) ▸ (hSstructure m (hRS hm)).2.2.2,
    (Nat.mem_smoothNumbersUpTo.mp hnT).1, hRcard, ?_, ?_⟩
  · intro a ha
    have h := hSstructure a (hRS ha)
    exact ⟨h.1, hRφ a ha, h.2.1, h.2.2.1⟩
  · intro d
    exact common_divisor_relative_frequency_bound P R k d ((2 : ℝ) ^ L) s
      (((L * k + 1) ^ y : ℕ) : ℝ) hk (by positivity) hs
      (fun p hp => by exact_mod_cast (hP p hp).2.1) hscale
      (fun a ha => ⟨(hSstructure a (hRS ha)).1, (hSstructure a (hRS ha)).2.1,
        (hSstructure a (hRS ha)).2.2.1⟩) hpool

lemma weak_dyadic_fiber_with_core_control (t L r : ℕ) (ht : 6 ≤ t)
    (hL : 4 ≤ L) (htL : t ≤ L) (hrL : t * r + 2 ≤ L) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (t * L) ∧
      p - 1 ∈ Nat.smoothNumbers (2 ^ ((t - 5) * L)))
    (hcard : 2 ^ ((t - 1) * L) ≤ P.card) :
    ∃ (n : ℕ) (R : Finset ℕ),
      2 ^ (2 ^ ((t - 4) * L) - 1) ≤ n ∧ n ≤ 2 ^ (t * L * 2 ^ ((t - 4) * L)) ∧
      (2 : ℝ) ^ (2 * L * 2 ^ ((t - 4) * L)) < R.card ∧
      (∀ m ∈ R, Squarefree m ∧ totient m = n) ∧
      ∀ d : ℕ, ((d : ℝ) ^ (2 / (t : ℝ)) * ((R.filter (fun m => d ∣ m)).card : ℝ)) ^ r ≤
        (n : ℝ) * (R.card : ℝ) ^ r := by
  let k := 2 ^ ((t - 4) * L)
  let y := 2 ^ ((t - 5) * L)
  let D := (t * L * k + 1) ^ y
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hs : 0 < 2 / (t : ℝ) := div_pos (by norm_num) htR
  have hk : 0 < k := by dsimp [k]; positivity
  have hexp : ((t * L : ℕ) : ℝ) * (2 / (t : ℝ)) = ((2 * L : ℕ) : ℝ) := by
    push_cast
    field_simp
  have hpower : ((2 : ℝ) ^ (t * L)) ^ (2 / (t : ℝ)) = (2 : ℝ) ^ (2 * L) := by
    rw [← Real.rpow_natCast_mul (by norm_num), hexp, Real.rpow_natCast]
  have hscale : (k : ℝ) * ((2 : ℝ) ^ (t * L)) ^ (2 / (t : ℝ)) ≤ P.card := by
    rw [hpower]
    have hk2 : k * 2 ^ (2 * L) = 2 ^ ((t - 2) * L) := by
      dsimp [k]
      rw [← pow_add]
      congr 1
      have hcoeff : t - 4 + 2 = t - 2 := by omega
      nlinarith
    have hN : k * 2 ^ (2 * L) ≤ P.card := by
      rw [hk2]
      exact (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right L (by omega : t - 2 ≤ t - 1))).trans hcard
    exact_mod_cast hN
  have hmargin : (D : ℝ) * (2 : ℝ) ^ (2 * L * k) < (P.card.choose k : ℝ) := by
    exact_mod_cast (weak_smooth_prime_counting_margin t L ht (by omega) htL).trans_le
      (Nat.choose_le_choose k hcard)
  obtain ⟨n, R, hnlower, hnupper, hRcard, hR, hcore⟩ :=
    large_squarefree_fiber_with_core_control P (t * L) y k ((2 : ℝ) ^ (2 * L * k))
      (2 / (t : ℝ)) (by positivity) hk hs.le hP hscale hmargin
  refine ⟨n, R, hnlower, hnupper, hRcard, fun m hm => ⟨(hR m hm).1, (hR m hm).2.1⟩, ?_⟩
  intro d
  have hDpow : D ^ r ≤ n :=
    (dyadic_output_bound_pow_le_totient_lower t L r ht hL htL hrL).trans hnlower
  calc
    ((d : ℝ) ^ (2 / (t : ℝ)) * ((R.filter (fun m => d ∣ m)).card : ℝ)) ^ r ≤
        ((D : ℝ) * (R.card : ℝ)) ^ r :=
      pow_le_pow_left₀ (by positivity) (hcore d) r
    _ = (D : ℝ) ^ r * (R.card : ℝ) ^ r := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hDpow) (by positivity)

lemma core_controlled_fibers_of_weak_density (t : ℕ) (ht : 6 ≤ t)
    (H : ∀ M : ℕ, ∃ L : ℕ, M ≤ L ∧ ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (t * L) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ ((t - 5) * L))) ∧
      2 ^ ((t - 1) * L) ≤ P.card) (r N : ℕ) :
    ∃ (n : ℕ) (R : Finset ℕ), N < n ∧ (n : ℝ) ^ (2 / (t : ℝ)) < R.card ∧
      (∀ m ∈ R, Squarefree m ∧ totient m = n) ∧
      ∀ d : ℕ, ((d : ℝ) ^ (2 / (t : ℝ)) * ((R.filter (fun m => d ∣ m)).card : ℝ)) ^ r ≤
        (n : ℝ) * (R.card : ℝ) ^ r := by
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hs : 0 < 2 / (t : ℝ) := div_pos (by norm_num) htR
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
  have hLk : L ≤ k - 1 := by
    have hle : L + 1 ≤ k := by nlinarith
    omega
  obtain ⟨n, R, hnlower, hnupper, hRcard, hR, hcore⟩ :=
    weak_dyadic_fiber_with_core_control t L r ht hL4 htL hrL P hP hcard
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
        Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnupper) hs.le
      _ = (2 : ℝ) ^ (((t * L * k : ℕ) : ℝ) * (2 / (t : ℝ))) :=
        (Real.rpow_natCast_mul (by norm_num) _ _).symm
      _ = _ := by rw [hexp, Real.rpow_natCast]
  exact ⟨n, R, hNn, hpow.trans_lt hRcard, hR, hcore⟩

/-- The constructed polynomial-size fibers satisfy a uniform bound over ALL
divisors, with an arbitrarily small root loss depending on the chosen scale. -/
theorem exists_fixed_power_core_controlled_fibers :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ r N : ℕ,
      ∃ (n : ℕ) (R : Finset ℕ), N < n ∧ (n : ℝ) ^ δ < R.card ∧
        (∀ m ∈ R, Squarefree m ∧ totient m = n) ∧
        ∀ d : ℕ, ((d : ℝ) ^ δ * ((R.filter (fun m => d ∣ m)).card : ℝ)) ^ r ≤
          (n : ℝ) * (R.card : ℝ) ^ r := by
  obtain ⟨t, ht, H⟩ := Sieve.exists_fixed_smooth_shifted_prime_density
  have htR : (6 : ℝ) ≤ t := by exact_mod_cast ht
  refine ⟨2 / (t : ℝ), div_pos (by norm_num) (by linarith), ?_, ?_⟩
  · exact (div_lt_one (by linarith)).mpr (by linarith)
  · exact core_controlled_fibers_of_weak_density t ht H

/-- A large common divisor can force a positive-power loss, even in a
polynomial-size squarefree totient fiber. This disproves the proposed GENERAL
extraction principle with subpower loss, not Erdős 821 itself. -/
theorem exists_fixed_power_fibers_with_sparse_large_common_divisors :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ η : ℝ, 0 < η → ∀ N : ℕ,
      ∃ (n : ℕ) (R : Finset ℕ), N < n ∧ (n : ℝ) ^ δ < R.card ∧
        (∀ m ∈ R, Squarefree m ∧ totient m = n) ∧
        ∀ d : ℕ, (n : ℝ) ^ η ≤ d →
          (n : ℝ) ^ (δ * η / 2) * ((R.filter (fun m => d ∣ m)).card : ℝ) ≤ R.card := by
  obtain ⟨δ, hδ, hδ1, H⟩ := exists_fixed_power_core_controlled_fibers
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro η hη N
  have hδη : 0 < δ * η := mul_pos hδ hη
  obtain ⟨r, hr⟩ := exists_nat_gt (2 / (δ * η))
  have hrR : (0 : ℝ) < r := (div_pos (by norm_num) hδη).trans hr
  have hrN : r ≠ 0 := by exact_mod_cast hrR.ne'
  let e : ℝ := δ * η / 2
  have he : 0 < e := half_pos hδη
  have her : 1 < e * (r : ℝ) := by
    have h := (div_lt_iff₀ hδη).mp hr
    dsimp [e]
    nlinarith
  obtain ⟨n, R, hnN, hRcard, hR, hcore⟩ := H r (max N 1)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (le_max_right N 1).trans_lt hnN
  have hnpos : (0 : ℝ) < n := by linarith
  let B : ℝ := (n : ℝ) ^ e
  have hBpos : 0 < B := Real.rpow_pos_of_pos hnpos e
  have hBpow : (n : ℝ) ≤ B ^ r := by
    dsimp [B]
    rw [← Real.rpow_natCast ((n : ℝ) ^ e) r, ← Real.rpow_mul (Nat.cast_nonneg n)]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1.le her.le
  refine ⟨n, R, (le_max_left _ _).trans_lt hnN, hRcard, hR, ?_⟩
  intro d hd
  let F : ℝ := (R.filter (fun m => d ∣ m)).card
  have hF : 0 ≤ F := Nat.cast_nonneg _
  have hBd : B ^ 2 ≤ (d : ℝ) ^ δ := by
    calc
      B ^ 2 = (n : ℝ) ^ (η * δ) := by
        dsimp [B]
        rw [← Real.rpow_natCast ((n : ℝ) ^ e) 2, ← Real.rpow_mul (Nat.cast_nonneg n)]
        congr 1
        dsimp [e]
        norm_num
        ring
      _ = ((n : ℝ) ^ η) ^ δ := Real.rpow_mul (Nat.cast_nonneg n) η δ
      _ ≤ (d : ℝ) ^ δ :=
        Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg n) _) hd hδ.le
  have hbig : B ^ r * (B * F) ^ r ≤ B ^ r * (R.card : ℝ) ^ r := by
    calc
      B ^ r * (B * F) ^ r = (B ^ 2 * F) ^ r := by rw [← mul_pow]; congr 1; ring
      _ ≤ ((d : ℝ) ^ δ * F) ^ r :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hBd hF) r
      _ ≤ (n : ℝ) * (R.card : ℝ) ^ r := hcore d
      _ ≤ _ := mul_le_mul_of_nonneg_right hBpow (by positivity)
  have hroot : (B * F) ^ r ≤ (R.card : ℝ) ^ r :=
    (mul_le_mul_iff_right₀ (pow_pos hBpos r)).mp hbig
  exact (pow_le_pow_iff_left₀ (by positivity) (Nat.cast_nonneg R.card) hrN).mp hroot

lemma odd_squarefree_subfiber_with_divisor_control (S : Finset ℕ) (n : ℕ)
    (hS : ∀ m ∈ S, Squarefree m ∧ totient m = n) :
    ∃ R : Finset ℕ, S.card ≤ 2 * R.card ∧
      (∀ m ∈ R, Squarefree m ∧ Odd m ∧ totient m = n) ∧
      ∀ d : ℕ, (R.filter (fun m => d ∣ m)).card ≤ (S.filter (fun m => d ∣ m)).card := by
  let O := S.filter Odd
  let E := S.filter (fun m => ¬Odd m)
  let Q := E.image (fun m => m / 2)
  let R := O ∪ Q
  have hEdiv (m : ℕ) (hm : m ∈ E) : 2 ∣ m :=
    (Nat.not_odd_iff_even.mp (Finset.mem_filter.mp hm).2).two_dvd
  have hinj : Set.InjOn (fun m : ℕ => m / 2) (E : Set ℕ) := by
    intro a ha b hb hab
    calc
      a = 2 * (a / 2) := (Nat.mul_div_cancel' (hEdiv a ha)).symm
      _ = 2 * (b / 2) := congrArg (fun m : ℕ => 2 * m) hab
      _ = b := Nat.mul_div_cancel' (hEdiv b hb)
  have hQcard : Q.card = E.card := Finset.card_image_of_injOn hinj
  have hOcard : O.card ≤ R.card := Finset.card_le_card Finset.subset_union_left
  have hEcard : E.card ≤ R.card := by
    rw [← hQcard]
    exact Finset.card_le_card Finset.subset_union_right
  have hsum : O.card + E.card = S.card := Finset.card_filter_add_card_filter_not _
  refine ⟨R, by omega, ?_, ?_⟩
  · intro m hm
    obtain hm | hm := Finset.mem_union.mp hm
    · obtain ⟨hmS, hmO⟩ := Finset.mem_filter.mp hm
      exact ⟨(hS m hmS).1, hmO, (hS m hmS).2⟩
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
      exact ⟨(hS a haS).1.squarefree_of_dvd hdiv, Nat.coprime_two_left.mp hcop, hφ⟩
  · intro d
    have hsub : R.filter (fun m => d ∣ m) ⊆
        (O.filter (fun m => d ∣ m)) ∪ ((E.filter (fun m => d ∣ m)).image (fun m => m / 2)) := by
      intro m hm
      obtain ⟨hmR, hdm⟩ := Finset.mem_filter.mp hm
      obtain hmO | hmQ := Finset.mem_union.mp hmR
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hmO, hdm⟩)
      · obtain ⟨a, haE, rfl⟩ := Finset.mem_image.mp hmQ
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨a, Finset.mem_filter.mpr ⟨haE, hdm.trans (Nat.div_dvd_of_dvd (hEdiv a haE))⟩, rfl⟩)
    have hsplit : (O.filter (fun m => d ∣ m)).card + (E.filter (fun m => d ∣ m)).card =
        (S.filter (fun m => d ∣ m)).card := by
      simpa only [O, E, Finset.filter_filter, and_comm] using
        Finset.card_filter_add_card_filter_not (s := S.filter (fun m => d ∣ m)) Odd
    calc
      (R.filter (fun m => d ∣ m)).card ≤ _ := Finset.card_le_card hsub
      _ ≤ (O.filter (fun m => d ∣ m)).card +
          ((E.filter (fun m => d ∣ m)).image (fun m => m / 2)).card := Finset.card_union_le _ _
      _ ≤ (O.filter (fun m => d ∣ m)).card + (E.filter (fun m => d ∣ m)).card :=
        Nat.add_le_add_left Finset.card_image_le _
      _ = _ := hsplit

/-- The failure of a general large-common-divisor extraction with subpower
loss persists for squarefree odd families. It does not rule out specialized
amplification arguments or disprove the original conjecture. -/
theorem exists_fixed_power_odd_fibers_with_sparse_large_common_divisors :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ η : ℝ, 0 < η → ∀ N : ℕ,
      ∃ (n : ℕ) (R : Finset ℕ), N < n ∧ (n : ℝ) ^ δ < R.card ∧
        (∀ m ∈ R, Squarefree m ∧ Odd m ∧ totient m = n) ∧
        ∀ d : ℕ, (n : ℝ) ^ η ≤ d →
          (n : ℝ) ^ (δ * η / 2) * ((R.filter (fun m => d ∣ m)).card : ℝ) ≤ R.card := by
  obtain ⟨δ, hδ, hδ1, H⟩ := exists_fixed_power_fibers_with_sparse_large_common_divisors
  refine ⟨δ / 2, half_pos hδ, by linarith, ?_⟩
  intro η hη N
  let e : ℝ := δ * η / 4
  have he : 0 < e := by dsimp [e]; positivity
  have hlim₁ : Tendsto (fun n : ℕ => (n : ℝ) ^ (δ / 2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hδ)).comp tendsto_natCast_atTop_atTop
  have hlim₂ : Tendsto (fun n : ℕ => (n : ℝ) ^ e) atTop atTop :=
    (tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 2 < (n : ℝ) ^ (δ / 2) ∧ 2 ≤ (n : ℝ) ^ e := by
    filter_upwards [eventually_ge_atTop 1, hlim₁.eventually (eventually_gt_atTop (2 : ℝ)),
      hlim₂.eventually (eventually_ge_atTop (2 : ℝ))] with n hn h₁ h₂
    exact ⟨hn, h₁, h₂⟩
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  obtain ⟨n, S, hnN, hScard, hS, hcore⟩ := H η hη (max N M)
  obtain ⟨hn1, hpow2, hB2⟩ := hM n ((le_max_right _ _).trans hnN.le)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpowid : (n : ℝ) ^ δ = (n : ℝ) ^ (δ / 2) * (n : ℝ) ^ (δ / 2) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  have hsmall : 2 * (n : ℝ) ^ (δ / 2) < (n : ℝ) ^ δ := by
    rw [hpowid]
    nlinarith
  obtain ⟨R, hRcard, hR, hdivcount⟩ := odd_squarefree_subfiber_with_divisor_control S n hS
  have hRcardR : (S.card : ℝ) ≤ 2 * (R.card : ℝ) := by exact_mod_cast hRcard
  refine ⟨n, R, (le_max_left _ _).trans_lt hnN, by linarith, hR, ?_⟩
  intro d hd
  let B : ℝ := (n : ℝ) ^ e
  have hBpos : 0 < B := Real.rpow_pos_of_pos hnpos e
  have hBsq : B ^ 2 = (n : ℝ) ^ (δ * η / 2) := by
    dsimp [B]
    rw [← Real.rpow_natCast ((n : ℝ) ^ e) 2, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    dsimp [e]
    ring
  have hfilter : ((R.filter (fun m => d ∣ m)).card : ℝ) ≤
      ((S.filter (fun m => d ∣ m)).card : ℝ) := by exact_mod_cast hdivcount d
  have hmul : B * (B * ((R.filter (fun m => d ∣ m)).card : ℝ)) ≤ B * (R.card : ℝ) := by
    calc
      B * (B * ((R.filter (fun m => d ∣ m)).card : ℝ)) =
          B ^ 2 * ((R.filter (fun m => d ∣ m)).card : ℝ) := by ring
      _ ≤ B ^ 2 * ((S.filter (fun m => d ∣ m)).card : ℝ) :=
        mul_le_mul_of_nonneg_left hfilter (sq_nonneg B)
      _ = (n : ℝ) ^ (δ * η / 2) * ((S.filter (fun m => d ∣ m)).card : ℝ) := by rw [hBsq]
      _ ≤ (S.card : ℝ) := hcore d hd
      _ ≤ 2 * (R.card : ℝ) := hRcardR
      _ ≤ B * (R.card : ℝ) := mul_le_mul_of_nonneg_right hB2 (Nat.cast_nonneg _)
  have hresult := (mul_le_mul_iff_right₀ hBpos).mp hmul
  have heq : (δ / 2) * η / 2 = e := by dsimp [e]; ring
  rw [heq]
  exact hresult

#print axioms large_squarefree_fiber_with_core_control
#print axioms weak_dyadic_fiber_with_core_control
#print axioms exists_fixed_power_core_controlled_fibers
#print axioms exists_fixed_power_fibers_with_sparse_large_common_divisors
#print axioms odd_squarefree_subfiber_with_divisor_control
#print axioms exists_fixed_power_odd_fibers_with_sparse_large_common_divisors

end Erdos821
