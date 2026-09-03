import Submission.IteratedPowerfulTotient
import Submission.PrimeModulusSupply
import Submission.Sublinear

/-!
# Testing a radical lift of a two-step totient fiber

Adding just the prime factors missing from the input gives an exact identity,
but not a common one-step output. This auxiliary investigation does not settle
Erdős 821.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821.RadicalLift

set_option maxHeartbeats 2000000

noncomputable def radical (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

lemma radical_pos (n : ℕ) : 0 < radical n :=
  Finset.prod_pos (fun _ hp => Nat.pos_of_mem_primeFactors hp)

lemma radical_dvd (n : ℕ) : radical n ∣ n := Nat.prod_primeFactors_dvd n

lemma radical_primeFactors (n : ℕ) : (radical n).primeFactors = n.primeFactors :=
  Nat.primeFactors_prod (fun _ hp => Nat.prime_of_mem_primeFactors hp)

lemma totient_radical (n : ℕ) :
    Nat.totient (radical n) = ∏ p ∈ n.primeFactors, (p-1) :=
  totient_prod_primes n.primeFactors (fun _ hp => Nat.prime_of_mem_primeFactors hp)

lemma totient_mul_radical (n : ℕ) :
    Nat.totient n * radical n = n * Nat.totient (radical n) := by
  rw [totient_radical]
  exact Nat.totient_mul_prod_primeFactors n

noncomputable def missingPrimes (m : ℕ) : Finset ℕ :=
  (Nat.totient m).primeFactors \ m.primeFactors

noncomputable def commonPrimes (m : ℕ) : Finset ℕ :=
  (Nat.totient m).primeFactors ∩ m.primeFactors

noncomputable def missingPart (m : ℕ) : ℕ := ∏ p ∈ missingPrimes m, p

noncomputable def commonPart (m : ℕ) : ℕ := ∏ p ∈ commonPrimes m, p

noncomputable def lift (m : ℕ) : ℕ := m * missingPart m

lemma missingPart_pos (m : ℕ) : 0 < missingPart m := by
  apply Finset.prod_pos
  intro p hp
  exact Nat.pos_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1

lemma commonPart_pos (m : ℕ) : 0 < commonPart m := by
  apply Finset.prod_pos
  intro p hp
  exact Nat.pos_of_mem_primeFactors (Finset.mem_inter.mp hp).1

lemma missing_coprime_input (m : ℕ) (hm : m ≠ 0) : m.Coprime (missingPart m) := by
  apply Nat.Coprime.prod_right
  intro p hp
  have hpr := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1
  apply Nat.Coprime.symm
  apply hpr.coprime_iff_not_dvd.mpr
  intro hpm
  exact (Finset.mem_sdiff.mp hp).2 (hpr.mem_primeFactors hpm hm)

lemma missing_mul_common (m : ℕ) :
    missingPart m * commonPart m = radical (Nat.totient m) := by
  dsimp [missingPart, commonPart, missingPrimes, commonPrimes, radical]
  have h := Finset.prod_sdiff (f := fun p : ℕ => p)
    (Finset.inter_subset_left (s₁ := (Nat.totient m).primeFactors)
      (s₂ := m.primeFactors))
  have he : (Nat.totient m).primeFactors \
      ((Nat.totient m).primeFactors ∩ m.primeFactors) =
      (Nat.totient m).primeFactors \ m.primeFactors := by ext p; simp
  rw [he] at h
  exact h

lemma missing_coprime_common (m : ℕ) : (missingPart m).Coprime (commonPart m) := by
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro q hq
  have hpr := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1
  have hqr := Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hq).1
  apply hpr.coprime_iff_not_dvd.mpr
  intro hd
  have he : q = p := (hqr.dvd_iff_eq hpr.ne_one).mp hd
  exact (Finset.mem_sdiff.mp hp).2 (he ▸ (Finset.mem_inter.mp hq).2)

/-- The cheaper lift adds each missing intermediate prime only once. The
remaining output factor depends on the intermediate radical and common part. -/
theorem lift_identity (m : ℕ) (hm : m ≠ 0) :
    Nat.totient (commonPart m) * Nat.totient (lift m) =
      Nat.totient (Nat.totient m) * radical (Nat.totient m) := by
  rw [lift, Nat.totient_mul (missing_coprime_input m hm),
    totient_mul_radical, ← missing_mul_common,
    Nat.totient_mul (missing_coprime_common m)]
  ring

lemma lift_output_ge_missing (m : ℕ) (hm : m ≠ 0) :
    Nat.totient (Nat.totient m) * missingPart m ≤ Nat.totient (lift m) := by
  have h := lift_identity m hm
  rw [← missing_mul_common] at h
  have hc := Nat.totient_le (commonPart m)
  have he : commonPart m * (Nat.totient (Nat.totient m) * missingPart m) ≤
      commonPart m * Nat.totient (lift m) := by nlinarith
  exact Nat.le_of_mul_le_mul_left he (commonPart_pos m)

lemma missingPart_prime (p : ℕ) (hp : p.Prime) :
    missingPart p = radical (p-1) := by
  have hnot : p ∉ (p-1).primeFactors := by
    intro h
    have hd := Nat.dvd_of_mem_primeFactors h
    have := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hd
    have hp2 := hp.two_le
    omega
  simp [missingPart, missingPrimes, Nat.totient_prime hp, hp.primeFactors,
    Finset.sdiff_singleton_eq_erase, Finset.erase_eq_of_notMem hnot, radical]

lemma commonPart_prime (p : ℕ) (hp : p.Prime) : commonPart p = 1 := by
  have hnot : p ∉ (p-1).primeFactors := by
    intro h
    have hd := Nat.dvd_of_mem_primeFactors h
    have := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hd
    have hp2 := hp.two_le
    omega
  simp [commonPart, commonPrimes, Nat.totient_prime hp, hp.primeFactors, hnot]

lemma lift_prime_output (p : ℕ) (hp : p.Prime) :
    Nat.totient (lift p) = Nat.totient (p-1) * radical (p-1) := by
  simpa only [commonPart_prime p hp, Nat.totient_one, one_mul, Nat.totient_prime hp]
    using lift_identity p hp.ne_zero

lemma squarefree_divisor_le_radical {a n : ℕ} (ha : Squarefree a)
    (han : a ∣ n) (hn : n ≠ 0) : a ≤ radical n := by
  rw [← Nat.prod_primeFactors_of_squarefree ha]
  apply Finset.prod_le_prod_of_subset_of_one_le' (Nat.primeFactors_mono han hn)
  intro p hp _
  exact (Nat.pos_of_mem_primeFactors hp)

lemma large_square_of_small_radical (n y : ℕ) (hn : 0 < n)
    (hyn : y^4 ≤ n) (hr : (radical n)^2 ≤ n) :
    ∃ d : ℕ, y ≤ d ∧ d^2 ∣ n := by
  obtain ⟨a, b, ha, hb, hab, hsf⟩ := Nat.sq_mul_squarefree_of_pos hn
  have had : a ∣ n := by rw [← hab]; exact dvd_mul_left _ _
  have har : a ≤ radical n := squarefree_divisor_le_radical hsf had hn.ne'
  have haa : a^2 ≤ b^2*a := (Nat.pow_le_pow_left har 2).trans (hab ▸ hr)
  have hab2 : a ≤ b^2 := Nat.le_of_mul_le_mul_left (by nlinarith [haa]) ha
  have hnb : n ≤ b^4 := by nlinarith [Nat.mul_le_mul_left (b^2) hab2]
  refine ⟨b, (Nat.pow_le_pow_iff_left (by decide : 4 ≠ 0)).mp (hyn.trans hnb), ?_⟩
  rw [← hab]
  exact dvd_mul_right _ _

lemma small_radical_card_le (S : Finset ℕ) (X y : ℕ) (hy : 0 < y)
    (hS : ∀ n ∈ S, 0 < n ∧ y^4 ≤ n ∧ n ≤ X ∧ (radical n)^2 ≤ n) :
    (S.card : ℝ) ≤ 2*(X : ℝ)/y := by
  apply card_large_square_divisor_le S X y hy
  intro n hn
  obtain ⟨hn0, hyn, hnX, hr⟩ := hS n hn
  exact ⟨hn0, hnX, large_square_of_small_radical n y hn0 hyn hr⟩

/-- The small-radical exceptional set is too sparse to contain all large
primes shifted by one. Only the elementary dyadic prime count is used. -/
theorem exists_prime_large_radical (N : ℕ) :
    ∃ p : ℕ, p.Prime ∧ N < p ∧ p-1 < (radical (p-1))^2 := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (AnalyticSieve.eventually_nat_poly_le_two_pow 1 64 1)
  let t := max 1 (max N M)
  have ht : 1 ≤ t := le_max_left _ _
  have hNt : N ≤ t := (le_max_left N M).trans (le_max_right _ _)
  have hMt : M ≤ t := (le_max_right N M).trans (le_max_right _ _)
  let y := 2^t
  let X := y^8
  let P := (X+1).primesBelow
  have hy : 0 < y := by dsimp [y]; positivity
  have hX : 0 < X := by dsimp [X]; positivity
  have hyt : 64*(t+1) ≤ y := by simpa only [one_mul, pow_one] using hM t hMt
  have htY : t < y := Nat.lt_two_pow_self
  have hcheb : X ≤ (8*t)*(P.card+1) := by
    have h := AnalyticSieve.dyadic_prime_count_bound (8*t) (by omega)
    simpa only [P, X, y, ← pow_mul, Nat.mul_comm t 8] using h
  have hex : ∃ p ∈ P, y^4 < p ∧ p-1 < (radical (p-1))^2 := by
    by_contra h
    have hbad (p : ℕ) (hp : p ∈ P) (hyp : y^4 < p) :
        (radical (p-1))^2 ≤ p-1 :=
      le_of_not_gt (fun hg => h ⟨p, hp, hyp, hg⟩)
    let S := P.filter (fun p => y^4 < p)
    let B := S.image (fun p => p-1)
    have hS (p : ℕ) (hp : p ∈ S) : p.Prime ∧ y^4 < p ∧ p ≤ X := by
      obtain ⟨hpP, hyp⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpX, hpr⟩ := Nat.mem_primesBelow.mp hpP
      exact ⟨hpr, hyp, by omega⟩
    have hBcard : B.card = S.card := by
      apply Finset.card_image_of_injOn
      intro p hp q hq he
      have hp2 := (hS p hp).1.two_le
      have hq2 := (hS q hq).1.two_le
      change p-1 = q-1 at he
      omega
    have hB : (B.card : ℝ) ≤ 2*(X : ℝ)/y := by
      apply small_radical_card_le B X y hy
      intro n hn
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨hpr, hyp, hpX⟩ := hS p hp
      have hp2 := hpr.two_le
      exact ⟨by omega, by omega, by omega,
        hbad p (Finset.mem_filter.mp hp).1 hyp⟩
    have hBN : B.card*y ≤ 2*X := by
      have hYR : (0 : ℝ) < y := by exact_mod_cast hy
      have hb := (le_div_iff₀ hYR).mp hB
      exact_mod_cast hb
    have hcover : P ⊆ Finset.range (y^4+1) ∪ S := by
      intro p hp
      by_cases hyp : y^4 < p
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hyp⟩)
      · exact Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))
    have hcard : P.card ≤ y^4+1+B.card := by
      calc
        P.card ≤ (Finset.range (y^4+1) ∪ S).card := Finset.card_le_card hcover
        _ ≤ _ := by
          simpa only [Finset.card_range, hBcard] using
            Finset.card_union_le (Finset.range (y^4+1)) S
    have h5 : y^5 ≤ X := Nat.pow_le_pow_right hy (by decide : 5 ≤ 8)
    have h1 : y ≤ X := Nat.le_self_pow (by decide : 8 ≠ 0) y
    have hsmall : (y^4+2)*y ≤ 3*X := by nlinarith [h5]
    have hsum : (P.card+1)*y ≤ 5*X := by nlinarith [hcard, hBN]
    have hmain : X*y ≤ (40*t)*X := by
      calc
        X*y ≤ ((8*t)*(P.card+1))*y := Nat.mul_le_mul_right y hcheb
        _ = (8*t)*((P.card+1)*y) := by ring
        _ ≤ (8*t)*(5*X) := Nat.mul_le_mul_left _ hsum
        _ = (40*t)*X := by ring
    have hyup : y ≤ 40*t := Nat.le_of_mul_le_mul_left (by nlinarith [hmain]) hX
    omega
  obtain ⟨p, hp, hyp, hr⟩ := hex
  have hpr := (Nat.mem_primesBelow.mp hp).2
  refine ⟨p, hpr, ?_, hr⟩
  exact (hNt.trans_lt htY).trans_le
    ((Nat.le_self_pow (by decide : 4 ≠ 0) y).trans hyp.le)

lemma exists_prime_large_radical_above_output (B : ℕ) :
    ∃ p : ℕ, p.Prime ∧ B < Nat.totient (p-1) ∧ p-1 < (radical (p-1))^2 := by
  obtain ⟨p, hp, hpB, hr⟩ := exists_prime_large_radical (24*B^2+1)
  refine ⟨p, hp, ?_, hr⟩
  have hi := input_pow_le_totient_pow (p-1) 1 (by decide)
  norm_num at hi
  by_contra h
  have hle : Nat.totient (p-1) ≤ B := by omega
  have hsq := Nat.pow_le_pow_left hle 2
  have hp2 := hp.two_le
  nlinarith

/-- Even the cheaper missing-prime lift has a polynomial size loss at
arbitrarily large two-step outputs. This concerns this map, not all possible
encodings of large fibers. -/
theorem exists_prime_lift_power_loss (B : ℕ) :
    ∃ p : ℕ, p.Prime ∧ B < Nat.totient (Nat.totient p) ∧
      (Nat.totient (Nat.totient p))^3 < (Nat.totient (lift p))^2 := by
  obtain ⟨p, hp, hpB, hr⟩ := exists_prime_large_radical_above_output B
  refine ⟨p, hp, by simpa only [Nat.totient_prime hp] using hpB, ?_⟩
  rw [Nat.totient_prime hp, lift_prime_output p hp]
  have hn : 0 < Nat.totient (p-1) :=
    Nat.totient_pos.mpr (Nat.sub_pos_of_lt hp.one_lt)
  have hlt : Nat.totient (p-1) < (radical (p-1))^2 :=
    (Nat.totient_le (p-1)).trans_lt hr
  have h := Nat.mul_lt_mul_of_pos_left hlt (pow_pos hn 2)
  nlinarith

/-- A uniform near-size-preserving bound for this particular lift is false.
This is not a disproof of Erdős 821 or of all possible fiber encodings. -/
theorem not_eventually_lift_output_le (ε : ℝ) (hε : ε < 1/2) :
    ¬ (∀ᶠ m : ℕ in atTop,
      (Nat.totient (lift m) : ℝ) ≤
        (Nat.totient (Nat.totient m) : ℝ)^(1+ε)) := by
  intro H
  obtain ⟨M, hM⟩ := eventually_atTop.mp H
  obtain ⟨p, hp, hnB, hloss⟩ := exists_prime_lift_power_loss (max M 1)
  have hnle : Nat.totient (Nat.totient p) ≤ p :=
    (Nat.totient_le _).trans (Nat.totient_le _)
  have hpM : M ≤ p := (le_max_left _ _).trans (hnB.le.trans hnle)
  have hn1 : (1 : ℝ) ≤ Nat.totient (Nat.totient p) := by
    exact_mod_cast (le_max_right M 1).trans hnB.le
  have hb := pow_le_pow_left₀ (Nat.cast_nonneg (Nat.totient (lift p))) (hM p hpM) 2
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg (Nat.totient (Nat.totient p)))] at hb
  have hexp : (1+ε)*(2 : ℝ) ≤ 3 := by linarith
  have hc := Real.rpow_le_rpow_of_exponent_le hn1 hexp
  have hd : (Nat.totient (lift p) : ℝ)^2 ≤
      (Nat.totient (Nat.totient p) : ℝ)^3 := by
    convert hb.trans hc using 1
    exact (Real.rpow_natCast _ 3).symm
  have he : (Nat.totient (Nat.totient p) : ℝ)^3 <
      (Nat.totient (lift p) : ℝ)^2 := by exact_mod_cast hloss
  exact (not_lt_of_ge hd) he

end Erdos821.RadicalLift
