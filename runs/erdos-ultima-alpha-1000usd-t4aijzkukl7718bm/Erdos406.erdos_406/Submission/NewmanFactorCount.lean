import Submission.NewmanFactorParity
import Submission.NewmanRootBounds

/-! Bounds on the number of monic nonconstant factors of an Erdős 406
candidate. These do not bound the degree of an individual factor. -/
namespace Erdos406FactorCount
open Polynomial Erdos406Cyclotomic Erdos406FactorParity

lemma one_le_norm_multiset_prod (s : Multiset ℂ) (hs : ∀ z ∈ s, 1 ≤ ‖z‖) :
    1 ≤ ‖s.prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
    rw [Multiset.prod_cons, norm_mul]
    have hz : 1 ≤ ‖z‖ := hs z (by simp)
    have ht : 1 ≤ ‖s.prod‖ := ih (fun a ha => hs a (by simp [ha]))
    nlinarith

lemma one_lt_norm_multiset_prod (s : Multiset ℂ) (hne : s ≠ 0)
    (hs : ∀ z ∈ s, 1 < ‖z‖) : 1 < ‖s.prod‖ := by
  induction s using Multiset.induction_on with
  | empty => contradiction
  | @cons z s ih =>
    rw [Multiset.prod_cons, norm_mul]
    have hz : 1 < ‖z‖ := hs z (by simp)
    have ht : 1 ≤ ‖s.prod‖ := one_le_norm_multiset_prod s
      (fun a ha => (hs a (by simp [ha])).le)
    nlinarith

lemma monic_norm_eval_three_gt_one (Q : ℂ[X]) (hQ : Q.Monic)
    (hdeg : 0 < Q.natDegree) (hroot : ∀ z ∈ Q.roots, ‖z‖ < 2) :
    1 < ‖Q.eval 3‖ := by
  have hsplit := IsAlgClosed.splits Q
  rw [hsplit.eval_eq_prod_roots_of_monic hQ]
  apply one_lt_norm_multiset_prod
  · have hcard : 0 < (Q.roots.map (fun z => (3 : ℂ) - z)).card := by
      rw [Multiset.card_map, ← hsplit.natDegree_eq_card_roots]
      exact hdeg
    intro hh
    simp [hh] at hcard
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hz
    have hh := norm_sub_norm_le (3 : ℂ) a
    have hr := hroot a ha
    norm_num at hh
    linarith

lemma eval_map_digitPoly_complex (w : List ℕ) (x : ℂ) :
    ((digitPoly w).map (Int.castRingHom ℂ)).eval x = Nat.ofDigits x w := by
  induction w with
  | nil => simp [digitPoly, Nat.ofDigits]
  | cons d w ih =>
    simpa [digitPoly, Nat.ofDigits] using congrArg (fun y : ℂ => d + x * y) ih

lemma candidate_factor_root_bound (k : ℕ) (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1])
    (Q : ℤ[X]) (hQ : Q.Monic) (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) :
    ∀ z ∈ (Q.map (Int.castRingHom ℂ)).roots, ‖z‖ < 2 := by
  intro z hz
  have hQr := (mem_roots (hQ.map _).ne_zero).mp hz
  have hdiv := eval_dvd (x := z) (map_dvd (Int.castRingHom ℂ) hd)
  have hroot : Nat.ofDigits z (Nat.digits 3 (2 ^ k)) = 0 := by
    change (Q.map (Int.castRingHom ℂ)).eval z = 0 at hQr
    rw [hQr, zero_dvd_iff, eval_map_digitPoly_complex] at hdiv
    exact hdiv
  have hb := (Erdos406Newman.good_power_digit_root_bounds
    (show (2 ^ k).isPowerOfTwo from ⟨k, rfl⟩) hg hroot).2
  have hn := norm_nonneg z
  nlinarith

/-- Nonconstant factors have a positive power of four as their value at three. -/
theorem candidate_factor_four_exponent_positive (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) (hdeg : 0 < Q.natDegree) :
    ∃ t : ℕ, 0 < t ∧ 2 * t ≤ k ∧ Q.eval 3 = (4 : ℤ) ^ t := by
  obtain ⟨hc, t, htk, ht⟩ := candidate_monic_factor k hg Q hQ hd
  have hb := monic_norm_eval_three_gt_one (Q.map (Int.castRingHom ℂ)) (hQ.map _)
    (by rwa [hQ.natDegree_map]) (candidate_factor_root_bound k hg Q hQ hd)
  refine ⟨t, ?_, htk, ht⟩
  by_contra hn
  have hz : t = 0 := by omega
  rw [hz, pow_zero] at ht
  have he : (Q.map (Int.castRingHom ℂ)).eval 3 = 1 := by
    rw [eval_map]
    simp [ht]
  rw [he] at hb
  norm_num at hb

/-- Each nonconstant monic factor has a positive even value at one. -/
theorem candidate_factor_eval_one_even (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) (hdeg : 0 < Q.natDegree) :
    (2 : ℤ) ∣ Q.eval 1 ∧ 2 ≤ Q.eval 1 := by
  obtain ⟨t, htpos, _, ht⟩ := candidate_factor_four_exponent_positive k hg Q hQ hd hdeg
  have h2three : (2 : ℤ) ∣ Q.eval 3 := by
    rw [ht]
    exact dvd_trans (by decide : (2 : ℤ) ∣ 4) (dvd_pow_self 4 (ne_of_gt htpos))
  have hdiff : (2 : ℤ) ∣ Q.eval 3 - Q.eval 1 := sub_dvd_eval_sub 3 1 Q
  have h2one : (2 : ℤ) ∣ Q.eval 1 := by
    convert dvd_sub h2three hdiff using 1
    ring
  have hh := good_two_power_digits_head k hg
  have hd' := hd
  rw [hh] at hd'
  have hp := factor_positive_on_ray _ Q hQ hd' 1 (by norm_num)
  have hpos : 0 < Q.eval 1 := by
    have he := eval_map_int Q 1
    norm_num only [Int.cast_one] at he
    rw [he] at hp
    exact_mod_cast hp
  refine ⟨h2one, ?_⟩
  obtain ⟨r, hr⟩ := h2one
  omega

lemma eval_one_prod_ge (L : List ℤ[X]) (hL : ∀ Q ∈ L, 2 ≤ Q.eval 1) :
    (2 : ℤ) ^ L.length ≤ L.prod.eval 1 := by
  induction L with
  | nil => simp
  | cons Q L ih =>
    have hq := hL Q (by simp)
    have hi := ih (fun R hR => hL R (by simp [hR]))
    simp only [List.length_cons, pow_succ, List.prod_cons, eval_mul]
    have hp : 0 < (2 : ℤ) ^ L.length := by positivity
    nlinarith

/-- Even without irreducibility, a factorization into monic nonconstant
polynomials has at most log₂(digit length) factors, counted with multiplicity.
There is no bound here on the degrees of those factors. -/
theorem candidate_factor_count_bound (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (L : List ℤ[X])
    (hL : ∀ Q ∈ L, Q.Monic ∧ 0 < Q.natDegree)
    (hprod : L.prod = digitPoly (Nat.digits 3 (2 ^ k))) :
    2 ^ L.length ≤ (Nat.digits 3 (2 ^ k)).length := by
  have heach : ∀ Q ∈ L, 2 ≤ Q.eval 1 := by
    intro Q hQ
    have hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k)) := by
      rw [← hprod]
      exact List.dvd_prod hQ
    exact (candidate_factor_eval_one_even k hg Q (hL Q hQ).1 hd (hL Q hQ).2).2
  have hb := eval_one_prod_ge L heach
  rw [hprod] at hb
  change (2 : ℤ) ^ L.length ≤ (Nat.ofDigits X (Nat.digits 3 (2 ^ k))).eval 1 at hb
  rw [Erdos406Newman.eval_one_digitPoly] at hb
  have hbN : 2 ^ L.length ≤ (Nat.digits 3 (2 ^ k)).sum := by exact_mod_cast hb
  exact hbN.trans (Erdos406Newman.sum_le_length hg)

/-- The logarithmic multiplicity bound is not restricted to X+1: it holds
for every monic nonconstant factor of a candidate digit polynomial. -/
theorem candidate_factor_multiplicity_bound (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hdeg : 0 < Q.natDegree) (r : ℕ)
    (hd : Q ^ r ∣ digitPoly (Nat.digits 3 (2 ^ k))) :
    2 ^ r ≤ (Nat.digits 3 (2 ^ k)).length := by
  by_cases hr : r = 0
  · subst r
    have hh := good_two_power_digits_head k hg
    rw [hh]
    simp
  have hQd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k)) := (dvd_pow_self Q hr).trans hd
  have he := (candidate_factor_eval_one_even k hg Q hQ hQd hdeg).1
  have hpow : (2 : ℤ) ^ r ∣ (Q.eval 1) ^ r := pow_dvd_pow_of_dvd he r
  have hv := eval_dvd (x := (1 : ℤ)) hd
  rw [eval_pow] at hv
  have htwo := hpow.trans hv
  change (2 : ℤ) ^ r ∣ (Nat.ofDigits X (Nat.digits 3 (2 ^ k))).eval 1 at htwo
  rw [Erdos406Newman.eval_one_digitPoly] at htwo
  have hn : 2 ^ r ∣ (Nat.digits 3 (2 ^ k)).sum := by exact_mod_cast htwo
  have hpos : 0 < (Nat.digits 3 (2 ^ k)).sum := by
    rw [good_two_power_digits_head k hg, List.sum_cons]
    omega
  exact (Nat.le_of_dvd hpos hn).trans (Erdos406Newman.sum_le_length hg)

#print axioms candidate_factor_root_bound
#print axioms candidate_factor_four_exponent_positive
#print axioms candidate_factor_eval_one_even
#print axioms candidate_factor_count_bound
#print axioms candidate_factor_multiplicity_bound
end Erdos406FactorCount
