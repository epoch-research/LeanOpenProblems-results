import Submission.RecordFibers

/-!
# Weighted input-scale bounds at odd squarefree records

These finite estimates quantify the scale gap in the record argument. They
are not an unconditional exponent improvement or a settlement of Erdős 821.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

lemma bounded_multiples_rpow_sum (D : Finset ℕ) (P q : ℕ) (hq : 0 < q)
    (s u : ℝ) (hsu : s ≤ u) (hu : 1 < u)
    (hD : ∀ d ∈ D, 0 < d ∧ d ≤ P ∧ q ∣ d) :
    (∑ d ∈ D, (d : ℝ) ^ (-s)) ≤
      (P : ℝ) ^ (u - s) * (q : ℝ) ^ (-u) *
        ∑' a : ℕ, (a : ℝ) ^ (-u) := by
  have hsum : Summable (fun a : ℕ => (a : ℝ) ^ (-u)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hinj : Set.InjOn (fun d : ℕ => d / q) (↑D : Set ℕ) := by
    intro d hd e he h
    change d / q = e / q at h
    rw [← Nat.mul_div_cancel' (hD d hd).2.2,
      ← Nat.mul_div_cancel' (hD e he).2.2, h]
  have hpoint (d : ℕ) (hd : d ∈ D) :
      (d : ℝ) ^ (-s) ≤ (P : ℝ) ^ (u - s) * (q : ℝ) ^ (-u) *
        ((d / q : ℕ) : ℝ) ^ (-u) := by
    obtain ⟨hdpos, hdP, hqd⟩ := hD d hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    calc
      (d : ℝ) ^ (-s) = (d : ℝ) ^ (u - s) * (d : ℝ) ^ (-u) := by
        rw [← Real.rpow_add hdR]; congr 1; ring
      _ ≤ (P : ℝ) ^ (u - s) * (d : ℝ) ^ (-u) :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hdR.le (by exact_mod_cast hdP) (sub_nonneg.mpr hsu))
          (Real.rpow_nonneg hdR.le _)
      _ = _ := by
        nth_rw 1 [← Nat.mul_div_cancel' hqd]
        rw [Nat.cast_mul, Real.mul_rpow hqR.le (Nat.cast_nonneg _)]
        ring
  calc
    (∑ d ∈ D, (d : ℝ) ^ (-s)) ≤
        ∑ d ∈ D, (P : ℝ) ^ (u - s) * (q : ℝ) ^ (-u) *
          ((d / q : ℕ) : ℝ) ^ (-u) := Finset.sum_le_sum hpoint
    _ = (P : ℝ) ^ (u - s) * (q : ℝ) ^ (-u) *
        ∑ a ∈ D.image (fun d => d / q), (a : ℝ) ^ (-u) := by
      rw [← Finset.mul_sum, Finset.sum_image hinj]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Summable.sum_le_tsum _ (fun a _ => Real.rpow_nonneg (Nat.cast_nonneg a) _) hsum)
      (by positivity)

/-- Every output prime must occur in some predecessor in every input. The
record-frequency bound turns that cover into a lower bound on a weighted
sum over the possible input primes. -/
lemma one_le_record_prime_cover_sum (n q P : ℕ) (hn : 0 < n)
    (hg : 0 < gOddSquarefree n) (hq : q.Prime) (hqn : q ∣ n) (s : ℝ)
    (hrec : ∀ j : ℕ, j ≤ n →
      (gOddSquarefree j : ℝ) / (j : ℝ) ^ s ≤
        (gOddSquarefree n : ℝ) / (n : ℝ) ^ s)
    (hcut : ∀ m ∈ oddSquarefreeFiber n, ∀ p ∈ m.primeFactors, p ≤ P) :
    1 ≤ ∑ p ∈ ((P + 1).primesBelow.filter (fun p => q ∣ p - 1)),
      ((p - 1 : ℕ) : ℝ) ^ (-s) := by
  let Q := (P + 1).primesBelow.filter (fun p => q ∣ p - 1)
  have hQprime (p : ℕ) (hp : p ∈ Q) : p.Prime :=
    Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1
  have hcover : oddSquarefreeFiber n ⊆
      Q.biUnion (fun p => (oddSquarefreeFiber n).filter (fun m => p ∣ m)) := by
    intro m hm
    obtain ⟨hmSq, _, hmφ⟩ := mem_oddSquarefreeFiber.mp hm
    have hnprod : n = ∏ p ∈ m.primeFactors, (p - 1) := by
      rw [← totient_prod_primes m.primeFactors
        (fun p hp => Nat.prime_of_mem_primeFactors hp),
        Nat.prod_primeFactors_of_squarefree hmSq, hmφ]
    rw [hnprod] at hqn
    obtain ⟨p, hp, hqp⟩ := (hq.prime.dvd_finset_prod_iff _).mp hqn
    have hpQ : p ∈ Q := Finset.mem_filter.mpr
      ⟨Nat.mem_primesBelow.mpr ⟨by have := hcut m hm p hp; omega,
        Nat.prime_of_mem_primeFactors hp⟩, hqp⟩
    exact Finset.mem_biUnion.mpr
      ⟨p, hpQ, Finset.mem_filter.mpr ⟨hm, Nat.dvd_of_mem_primeFactors hp⟩⟩
  have hcard : (gOddSquarefree n : ℝ) ≤
      ∑ p ∈ Q, (((oddSquarefreeFiber n).filter (fun m => p ∣ m)).card : ℝ) := by
    have h := (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)
    rw [card_oddSquarefreeFiber] at h
    exact_mod_cast h
  have hfreq (p : ℕ) (hp : p ∈ Q) :
      (((oddSquarefreeFiber n).filter (fun m => p ∣ m)).card : ℝ) ≤
        (gOddSquarefree n : ℝ) * ((p - 1 : ℕ) : ℝ) ^ (-s) := by
    have hpR : (0 : ℝ) < (p - 1 : ℕ) := by
      exact_mod_cast Nat.sub_pos_of_lt (hQprime p hp).one_lt
    have h := normalized_record_odd_fiber_core_bound n p hn s hrec
    rw [Nat.totient_prime (hQprime p hp)] at h
    have hdiv := (le_div_iff₀ (Real.rpow_pos_of_pos hpR s)).mpr
      (by simpa only [mul_comm] using h)
    simpa only [Real.rpow_neg hpR.le, div_eq_mul_inv] using hdiv
  have hbound : (gOddSquarefree n : ℝ) ≤ (gOddSquarefree n : ℝ) *
      ∑ p ∈ Q, ((p - 1 : ℕ) : ℝ) ^ (-s) := by
    calc
      _ ≤ ∑ p ∈ Q, (gOddSquarefree n : ℝ) * ((p - 1 : ℕ) : ℝ) ^ (-s) :=
        hcard.trans (Finset.sum_le_sum hfreq)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hgR : (0 : ℝ) < gOddSquarefree n := by exact_mod_cast hg
  exact (mul_le_mul_iff_right₀ hgR).mp (by simpa only [mul_one] using hbound)

lemma normalized_record_output_prime_le_input_scale (n q P : ℕ) (hn : 0 < n)
    (hg : 0 < gOddSquarefree n) (hq : q.Prime) (hqn : q ∣ n)
    (s u : ℝ) (hsu : s ≤ u) (hu : 1 < u)
    (hrec : ∀ j : ℕ, j ≤ n →
      (gOddSquarefree j : ℝ) / (j : ℝ) ^ s ≤
        (gOddSquarefree n : ℝ) / (n : ℝ) ^ s)
    (hcut : ∀ m ∈ oddSquarefreeFiber n, ∀ p ∈ m.primeFactors, p ≤ P) :
    (q : ℝ) ^ u ≤ (P : ℝ) ^ (u - s) * ∑' a : ℕ, (a : ℝ) ^ (-u) := by
  let Q := (P + 1).primesBelow.filter (fun p => q ∣ p - 1)
  let D := Q.image (fun p => p - 1)
  have hQ (p : ℕ) (hp : p ∈ Q) : p ≤ P ∧ p.Prime ∧ q ∣ p - 1 := by
    obtain ⟨hpb, hqp⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpP, hprime⟩ := Nat.mem_primesBelow.mp hpb
    exact ⟨by omega, hprime, hqp⟩
  have hinj : Set.InjOn (fun p : ℕ => p - 1) (↑Q : Set ℕ) := by
    intro p hp r hr h
    change p - 1 = r - 1 at h
    have := (hQ p hp).2.1.two_le
    have := (hQ r hr).2.1.two_le
    omega
  have hlow : 1 ≤ ∑ d ∈ D, (d : ℝ) ^ (-s) := by
    rw [Finset.sum_image hinj]
    exact one_le_record_prime_cover_sum n q P hn hg hq hqn s hrec hcut
  have hup := bounded_multiples_rpow_sum D P q hq.pos s u hsu hu (by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    exact ⟨Nat.sub_pos_of_lt (hQ p hp).2.1.one_lt,
      (Nat.sub_le p 1).trans (hQ p hp).1, (hQ p hp).2.2⟩)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hb := mul_le_mul_of_nonneg_right (hlow.trans hup)
    (Real.rpow_nonneg hqR.le u)
  have hpows : (q : ℝ) ^ (-u) * (q : ℝ) ^ u = 1 := by
    rw [← Real.rpow_add hqR, neg_add_cancel, Real.rpow_zero]
  calc
    (q : ℝ) ^ u ≤ ((P : ℝ) ^ (u - s) * (q : ℝ) ^ (-u) *
        ∑' a : ℕ, (a : ℝ) ^ (-u)) * (q : ℝ) ^ u := by
      simpa only [one_mul] using hb
    _ = ((P : ℝ) ^ (u - s) * ∑' a : ℕ, (a : ℝ) ^ (-u)) *
        ((q : ℝ) ^ (-u) * (q : ℝ) ^ u) := by ring
    _ = _ := by rw [hpows, mul_one]


/-- Uniformly in the output n, a sufficiently large input-prime cutoff P
forces output primes below its K-th root, provided the explicit weight
exponents have a strictly positive margin. -/
lemma eventually_record_output_roots_below_input_cutoff (K : ℕ)
    (s u : ℝ) (hsu : s ≤ u) (hu : 1 < u)
    (hmargin : (K : ℝ) * (u - s) < u) :
    ∀ᶠ P : ℕ in atTop, ∀ n : ℕ, 0 < n → 0 < gOddSquarefree n →
      (∀ j : ℕ, j ≤ n →
        (gOddSquarefree j : ℝ) / (j : ℝ) ^ s ≤
          (gOddSquarefree n : ℝ) / (n : ℝ) ^ s) →
      (∀ m ∈ oddSquarefreeFiber n, ∀ p ∈ m.primeFactors, p ≤ P) →
      ∀ q ∈ n.primeFactors, q ^ K < P := by
  let C := ∑' a : ℕ, (a : ℝ) ^ (-u)
  have hC : 0 ≤ C := tsum_nonneg (fun a => Real.rpow_nonneg (Nat.cast_nonneg a) _)
  have he : 0 < u - (K : ℝ) * (u - s) := sub_pos.mpr hmargin
  have hlim : Tendsto (fun P : ℕ => (P : ℝ) ^ (u - (K : ℝ) * (u - s)))
      atTop atTop := (tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (eventually_gt_atTop (C ^ K)), eventually_ge_atTop 1]
    with P hPbig hP n hn hg hrec hcut q hq
  by_contra h
  have hPq : P ≤ q ^ K := Nat.le_of_not_gt h
  have hqprime := Nat.prime_of_mem_primeFactors hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
  have hPR : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hbound := normalized_record_output_prime_le_input_scale n q P hn hg hqprime
    (Nat.dvd_of_mem_primeFactors hq) s u hsu hu hrec hcut
  have hpow : (P : ℝ) ^ u ≤ C ^ K * (P : ℝ) ^ ((K : ℝ) * (u - s)) := by
    calc
      (P : ℝ) ^ u ≤ ((q : ℝ) ^ K) ^ u :=
        Real.rpow_le_rpow (Nat.cast_nonneg P) (by exact_mod_cast hPq) (by linarith)
      _ = ((q : ℝ) ^ u) ^ K := by
        rw [← Real.rpow_natCast_mul hqR.le, ← Real.rpow_mul_natCast hqR.le]
        congr 1
        ring
      _ ≤ ((P : ℝ) ^ (u - s) * C) ^ K := by
        exact pow_le_pow_left₀ (Real.rpow_nonneg hqR.le _) hbound K
      _ = C ^ K * (P : ℝ) ^ ((K : ℝ) * (u - s)) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hPR.le, mul_comm (u - s) (K : ℝ)]
        exact mul_comm _ _
  have hcancel : (P : ℝ) ^ (u - (K : ℝ) * (u - s)) ≤ C ^ K := by
    rw [Real.rpow_sub hPR]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hPR ((K : ℝ) * (u - s)))).mpr hpow
  exact (not_lt_of_ge hcancel) hPbig

/-- The margin required by this weighted estimate is attainable exactly
above 1 - 1/k. Thus this mechanism does not reach arbitrarily large root
parameters from one fixed positive record exponent. -/
lemma exists_record_weight_margin_iff (k s : ℝ) (hk : 1 ≤ k) (hs : s ≤ 1) :
    (∃ u : ℝ, 1 < u ∧ s ≤ u ∧ k * (u - s) < u) ↔ 1 - 1 / k < s := by
  have hkpos : 0 < k := by linarith
  have heq : 1 - 1 / k = (k - 1) / k := by field_simp
  rw [heq, div_lt_iff₀ hkpos]
  constructor
  · rintro ⟨u, hu, _, hmargin⟩
    have hnonneg : 0 ≤ (k - 1) * (u - 1) :=
      mul_nonneg (sub_nonneg.mpr hk) (sub_pos.mpr hu).le
    nlinarith
  · intro hgap
    let d := (k * s - k + 1) / (2 * k)
    have hd : 0 < d := div_pos (by nlinarith) (by positivity)
    have hdid : 2 * k * d = k * s - k + 1 := by
      dsimp [d]
      field_simp
    refine ⟨1 + d, by linarith, by linarith, ?_⟩
    nlinarith

#print axioms bounded_multiples_rpow_sum
#print axioms eventually_record_output_roots_below_input_cutoff
#print axioms exists_record_weight_margin_iff

#print axioms one_le_record_prime_cover_sum
#print axioms normalized_record_output_prime_le_input_scale

end Erdos821
