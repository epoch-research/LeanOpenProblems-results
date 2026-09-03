import Submission.NewmanFactorBridge

/-! Trace restrictions for quartic factors. These restrictions do not control
arbitrary higher degrees and do not settle Erdős 406. -/
namespace Erdos406QuarticTrace
open Polynomial Erdos406Cyclotomic Erdos406FactorParity Erdos406FactorCount
  Erdos406FactorBridge

lemma norm_sum_four_lt (u v w z : ℂ) (r : ℝ)
    (hu : ‖u‖ < r) (hv : ‖v‖ < r) (hw : ‖w‖ < r) (hz : ‖z‖ < r) :
    ‖u + v + w + z‖ < 4 * r := by
  have h1 := norm_add_le u v
  have h2 := norm_add_le (u + v) w
  have h3 := norm_add_le (u + v + w) z
  linarith

lemma trace_abs_bound (u v w z : ℂ) (t B : ℤ) (e : ℕ) (he : e ≠ 0)
    (hu : ‖u‖ < 13 / 8) (hv : ‖v‖ < 13 / 8)
    (hw : ‖w‖ < 13 / 8) (hz : ‖z‖ < 13 / 8)
    (ht : (t : ℂ) = u ^ e + v ^ e + w ^ e + z ^ e)
    (hB : 4 * (13 / 8 : ℝ) ^ e ≤ (B : ℝ) + 1) : |t| ≤ B := by
  have hp (x : ℂ) (hx : ‖x‖ < 13 / 8) : ‖x ^ e‖ < (13 / 8 : ℝ) ^ e := by
    rw [norm_pow]
    exact pow_lt_pow_left₀ hx (norm_nonneg x) he
  have hb := (norm_sum_four_lt (u ^ e) (v ^ e) (w ^ e) (z ^ e) _
    (hp u hu) (hp v hv) (hp w hw) (hp z hz)).trans_le hB
  rw [← ht, Complex.norm_intCast] at hb
  have hb' : |t| < B + 1 := by exact_mod_cast hb
  omega

lemma quartic_trace_constraints (a b c : ℤ) (u v w z : ℂ)
    (ha : (a : ℂ) = -(u + v + w + z))
    (hb : (b : ℂ) = u*v + u*w + u*z + v*w + v*z + w*z)
    (hc : (c : ℂ) = -(u*v*w + u*v*z + u*w*z + v*w*z))
    (hprod : u*v*w*z = 1)
    (hu : ‖u‖ < 13 / 8) (hv : ‖v‖ < 13 / 8)
    (hw : ‖w‖ < 13 / 8) (hz : ‖z‖ < 13 / 8)
    (hui : ‖u⁻¹‖ < 13 / 8) (hvi : ‖v⁻¹‖ < 13 / 8)
    (hwi : ‖w⁻¹‖ < 13 / 8) (hzi : ‖z⁻¹‖ < 13 / 8) :
    |a| ≤ 6 ∧ |c| ≤ 6 ∧ |a^2 - 2*b| ≤ 10 ∧ |c^2 - 2*b| ≤ 10 ∧
      |a^4 - 4*a^2*b + 4*a*c + 2*b^2 - 4| ≤ 27 := by
  have hu0 : u ≠ 0 := by intro h; simpa [h] using hprod
  have hv0 : v ≠ 0 := by intro h; simpa [h] using hprod
  have hw0 : w ≠ 0 := by intro h; simpa [h] using hprod
  have hz0 : z ≠ 0 := by intro h; simpa [h] using hprod
  have hi1 : u⁻¹ + v⁻¹ + w⁻¹ + z⁻¹ = u*v*w + u*v*z + u*w*z + v*w*z := by
    calc
      _ = (u*v*w*z) * (u⁻¹ + v⁻¹ + w⁻¹ + z⁻¹) := by rw [hprod, one_mul]
      _ = _ := by field_simp [hu0, hv0, hw0, hz0]; ring
  have hi2 : u⁻¹*v⁻¹ + u⁻¹*w⁻¹ + u⁻¹*z⁻¹ + v⁻¹*w⁻¹ + v⁻¹*z⁻¹ + w⁻¹*z⁻¹ =
      u*v + u*w + u*z + v*w + v*z + w*z := by
    calc
      _ = (u*v*w*z) *
          (u⁻¹*v⁻¹ + u⁻¹*w⁻¹ + u⁻¹*z⁻¹ + v⁻¹*w⁻¹ + v⁻¹*z⁻¹ + w⁻¹*z⁻¹) := by
        rw [hprod, one_mul]
      _ = _ := by field_simp [hu0, hv0, hw0, hz0]; ring
  have hci : (c : ℂ) = -(u⁻¹ + v⁻¹ + w⁻¹ + z⁻¹) := by rw [hi1]; exact hc
  have hbi : (b : ℂ) =
      u⁻¹*v⁻¹ + u⁻¹*w⁻¹ + u⁻¹*z⁻¹ + v⁻¹*w⁻¹ + v⁻¹*z⁻¹ + w⁻¹*z⁻¹ := by
    rw [hi2]; exact hb
  have ht1 : ((-a : ℤ) : ℂ) = u ^ 1 + v ^ 1 + w ^ 1 + z ^ 1 := by
    push_cast
    rw [ha]
    simp
  have ht1i : ((-c : ℤ) : ℂ) = (u⁻¹)^1 + (v⁻¹)^1 + (w⁻¹)^1 + (z⁻¹)^1 := by
    push_cast
    rw [hci]
    simp
  have ht2 : ((a^2 - 2*b : ℤ) : ℂ) = u^2 + v^2 + w^2 + z^2 := by
    push_cast
    rw [ha, hb]
    ring
  have ht2i : ((c^2 - 2*b : ℤ) : ℂ) = (u⁻¹)^2 + (v⁻¹)^2 + (w⁻¹)^2 + (z⁻¹)^2 := by
    push_cast
    rw [hci, hbi]
    ring
  have ht4 : ((a^4 - 4*a^2*b + 4*a*c + 2*b^2 - 4 : ℤ) : ℂ) =
      u^4 + v^4 + w^4 + z^4 := by
    calc
      _ = u^4 + v^4 + w^4 + z^4 + 4 * (u*v*w*z - 1) := by
        push_cast
        rw [ha, hb, hc]
        ring
      _ = _ := by rw [hprod]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using trace_abs_bound u v w z (-a) 6 1 (by decide) hu hv hw hz ht1 (by norm_num)
  · simpa using trace_abs_bound u⁻¹ v⁻¹ w⁻¹ z⁻¹ (-c) 6 1 (by decide)
      hui hvi hwi hzi ht1i (by norm_num)
  · exact trace_abs_bound u v w z _ 10 2 (by decide) hu hv hw hz ht2 (by norm_num)
  · exact trace_abs_bound u⁻¹ v⁻¹ w⁻¹ z⁻¹ _ 10 2 (by decide)
      hui hvi hwi hzi ht2i (by norm_num)
  · exact trace_abs_bound u v w z _ 27 4 (by decide) hu hv hw hz ht4 (by norm_num)

set_option maxHeartbeats 4000000 in
lemma quartic_eval_256_coefficients (a b c : ℤ)
    (ha : |a| ≤ 6) (hc : |c| ≤ 6)
    (h2a : |a^2 - 2*b| ≤ 10) (h2c : |c^2 - 2*b| ≤ 10)
    (h4 : |a^4 - 4*a^2*b + 4*a*c + 2*b^2 - 4| ≤ 27)
    (hv : 9*a + 3*b + c = 58) : a = 4 ∧ b = 6 ∧ c = 4 := by
  obtain ⟨ha0, ha1⟩ := abs_le.mp ha
  obtain ⟨hc0, hc1⟩ := abs_le.mp hc
  have hh : (a = 3 ∧ b = 9 ∧ c = 4) ∨ (a = 4 ∧ b = 9 ∧ c = -5) ∨
      (a = 4 ∧ b = 6 ∧ c = 4) := by
    obtain ⟨h2a0, h2a1⟩ := abs_le.mp h2a
    obtain ⟨h2c0, h2c1⟩ := abs_le.mp h2c
    clear h4 h2a h2c ha hc
    interval_cases a <;> interval_cases c <;> norm_num at * <;> omega
  rcases hh with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | h
  · norm_num at h4
  · norm_num at h4
  · exact h

lemma candidate_factor_radial_bound (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) (z : ℂ)
    (hz : z ∈ (Q.map (Int.castRingHom ℂ)).roots) :
    ‖z‖ < 13 / 8 ∧ ‖z⁻¹‖ < 13 / 8 := by
  have hQr := (mem_roots (hQ.map _).ne_zero).mp hz
  have hdiv := eval_dvd (x := z) (map_dvd (Int.castRingHom ℂ) hd)
  have hroot : Nat.ofDigits z (Nat.digits 3 (2 ^ k)) = 0 := by
    change (Q.map (Int.castRingHom ℂ)).eval z = 0 at hQr
    rw [hQr, zero_dvd_iff, eval_map_digitPoly_complex] at hdiv
    exact hdiv
  have hb := Erdos406Newman.good_power_digit_root_bounds ⟨k, rfl⟩ hg hroot
  have hn := norm_nonneg z
  have hlo : 8 / 13 < ‖z‖ := by
    by_contra hh
    have hs := pow_le_pow_left₀ hn (le_of_not_gt hh) 2
    norm_num at hs
    nlinarith [hb.1]
  have hhi : ‖z‖ < 13 / 8 := by
    by_contra hh
    have hs := mul_le_mul_of_nonneg_right (le_of_not_gt hh) hn
    nlinarith [hb.2]
  refine ⟨hhi, ?_⟩
  rw [norm_inv, inv_eq_one_div, div_lt_iff₀ (by linarith : 0 < ‖z‖)]
  linarith

lemma candidate_quartic_trace_constraints (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (a b c : ℤ)
    (hd : (X^4 + C a * X^3 + C b * X^2 + C c * X + 1 : ℤ[X]) ∣
      digitPoly (Nat.digits 3 (2 ^ k))) :
    |a| ≤ 6 ∧ |c| ≤ 6 ∧ |a^2 - 2*b| ≤ 10 ∧ |c^2 - 2*b| ≤ 10 ∧
      |a^4 - 4*a^2*b + 4*a*c + 2*b^2 - 4| ≤ 27 := by
  let Q : ℤ[X] := X^4 + C a * X^3 + C b * X^2 + C c * X + 1
  have hQ : Q.Monic := by dsimp [Q]; monicity <;> norm_num
  have hdeg : Q.natDegree = 4 := by dsimp [Q]; compute_degree!
  let F := Q.map (Int.castRingHom ℂ)
  have hs := IsAlgClosed.splits F
  have hcard : F.roots.card = 4 := by
    rw [← hs.natDegree_eq_card_roots]
    exact (hQ.natDegree_map _).trans hdeg
  obtain ⟨u, v, w, z, hroots⟩ := Multiset.card_eq_four.mp hcard
  have hprod : F = (X - C u) * (X - C v) * (X - C w) * (X - C z) := by
    rw [hs.eq_prod_roots_of_monic (hQ.map _), hroots]
    simp
    ring
  have he : F = X^4 - C (u+v+w+z) * X^3 +
      C (u*v + u*w + u*z + v*w + v*z + w*z) * X^2 -
      C (u*v*w + u*v*z + u*w*z + v*w*z) * X + C (u*v*w*z) := by
    rw [hprod]
    simp only [map_add, map_mul]
    ring
  have h0 := congrArg (fun p : ℂ[X] => p.coeff 0) he
  have h1 := congrArg (fun p : ℂ[X] => p.coeff 1) he
  have h2 := congrArg (fun p : ℂ[X] => p.coeff 2) he
  have h3 := congrArg (fun p : ℂ[X] => p.coeff 3) he
  simp only [F, Q, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_one, coeff_add, coeff_sub,
    coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_one] at h0 h1 h2 h3
  norm_num at h0 h1 h2 h3
  have hu := candidate_factor_radial_bound k hg Q hQ hd u (by change u ∈ F.roots; simp [hroots])
  have hv := candidate_factor_radial_bound k hg Q hQ hd v (by change v ∈ F.roots; simp [hroots])
  have hw := candidate_factor_radial_bound k hg Q hQ hd w (by change w ∈ F.roots; simp [hroots])
  have hz := candidate_factor_radial_bound k hg Q hQ hd z (by change z ∈ F.roots; simp [hroots])
  exact quartic_trace_constraints a b c u v w z (h3.trans (by ring))
    (h2.trans (by ring)) (h1.trans (by ring)) h0.symm
    hu.1 hv.1 hw.1 hz.1 hu.2 hv.2 hw.2 hz.2

/-- A quartic candidate factor taking value256 at three is not irreducible:
it must be (X+1)^4. -/
theorem quartic_factor_eval_256_shape (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) (hdeg : Q.natDegree = 4)
    (hv : Q.eval 3 = 256) : Q = (X + 1) ^ 4 := by
  have hc := (candidate_monic_factor k hg Q hQ hd).1
  have h4 : Q.coeff 4 = 1 := by rw [← hdeg, coeff_natDegree, hQ.leadingCoeff]
  have he := Q.as_sum_range_C_mul_X_pow
  rw [hdeg] at he
  norm_num [Finset.sum_range_succ, hc, h4] at he
  change Q = 1 + C (Q.coeff 1) * X + C (Q.coeff 2) * X^2 +
    C (Q.coeff 3) * X^3 + X^4 at he
  have hshape : Q = X^4 + C (Q.coeff 3) * X^3 + C (Q.coeff 2) * X^2 +
      C (Q.coeff 1) * X + 1 := he.trans (by ring)
  have hd' := hd
  rw [hshape] at hd'
  obtain ⟨ha, hc, h2a, h2c, h4⟩ := candidate_quartic_trace_constraints k hg _ _ _ hd'
  have hv' := hv
  rw [hshape] at hv'
  norm_num at hv'
  obtain ⟨ha', hb', hc'⟩ := quartic_eval_256_coefficients _ _ _ ha hc h2a h2c h4 (by omega)
  rw [hshape, ha', hb', hc']
  norm_num
  ring

lemma norm_multiset_prod_le_five (s : Multiset ℂ)
    (hs : ∀ z ∈ s, ‖z‖ ≤ 5) : ‖s.prod‖ ≤ (5 : ℝ) ^ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
    have hz := hs z (by simp)
    have ht := ih (fun a ha => hs a (by simp [ha]))
    rw [Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ]
    calc
      _ ≤ 5 * (5 : ℝ) ^ s.card := mul_le_mul hz ht (norm_nonneg _) (by norm_num)
      _ = _ := by ring

lemma monic_eval_three_abs_bound (Q : ℤ[X]) (hQ : Q.Monic)
    (hr : ∀ z ∈ (Q.map (Int.castRingHom ℂ)).roots, ‖z‖ < 2) :
    |Q.eval 3| ≤ (5 : ℤ) ^ Q.natDegree := by
  have hs := IsAlgClosed.splits (Q.map (Int.castRingHom ℂ))
  have hb : ‖(Q.map (Int.castRingHom ℂ)).eval 3‖ ≤
      (5 : ℝ) ^ Q.natDegree := by
    rw [hs.eval_eq_prod_roots_of_monic (hQ.map _)]
    have hh := norm_multiset_prod_le_five
      ((Q.map (Int.castRingHom ℂ)).roots.map (fun z => (3 : ℂ) - z)) ?_
    · simpa only [Multiset.card_map, ← hs.natDegree_eq_card_roots, hQ.natDegree_map] using hh
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz
      have hb := norm_sub_le (3 : ℂ) w
      have hh := hr w hw
      norm_num at hb
      linarith
  have he : (Q.map (Int.castRingHom ℂ)).eval 3 = ((Q.eval 3 : ℤ) : ℂ) := by
    rw [eval_map]
    exact eval₂_at_apply (Int.castRingHom ℂ) 3
  rw [he, Complex.norm_intCast] at hb
  exact_mod_cast hb

/-- Every irreducible monic quartic factor of a candidate has value at most64
at three. In particular it obeys the proposed factor gap. -/
theorem irreducible_quartic_eval_bound (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) (hI : Irreducible Q)
    (hdeg : Q.natDegree = 4) : Q.eval 3 ≤ 64 := by
  obtain ⟨t, htpos, _, ht⟩ := candidate_factor_four_exponent_positive k hg Q hQ hd (by omega)
  have hb := monic_eval_three_abs_bound Q hQ (candidate_factor_root_bound k hg Q hQ hd)
  rw [ht, abs_of_nonneg (by positivity), hdeg] at hb
  have ht4 : t ≤ 4 := by
    by_contra hh
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 4) (by omega : 5 ≤ t)
    norm_num at hb hp
    omega
  have hne : t ≠ 4 := by
    intro hte
    have hv : Q.eval 3 = 256 := by rw [ht, hte]; norm_num
    have hshape := quartic_factor_eval_256_shape k hg Q hQ hd hdeg hv
    have hn : ¬ IsUnit (X + 1 : ℤ[X]) := by
      intro hu
      have hh := natDegree_eq_zero_of_isUnit hu
      have hg : (X + 1 : ℤ[X]).natDegree = 1 := by compute_degree!
      omega
    have hi := hI.isUnit_or_isUnit
      (show Q = (X + 1) * (X + 1) ^ 3 by rw [hshape]; ring)
    rcases hi with hi | hi
    · exact hn hi
    · exact hn ((isUnit_pow_iff (by decide : 3 ≠ 0)).mp hi)
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 4) (by omega : t ≤ 3)
  norm_num at hp
  rwa [ht]

/-- The soft factor bound is unconditional through degree four. -/
theorem irreducible_degree_le_four_bound (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) (hI : Irreducible Q)
    (hdeg : Q.natDegree ≤ 4) : (Q.eval 3) ^ 2 ≤ 2 * (8 : ℤ) ^ Q.natDegree := by
  rcases Erdos406SmallFactors.irreducible_factor_alternative k hg Q hQ hd hI with hlin | h4
  · rw [hlin]
    have he : (X + 1 : ℤ[X]).natDegree = 1 := by compute_degree!
    norm_num [he]
  · have he : Q.natDegree = 4 := by omega
    have hb := irreducible_quartic_eval_bound k hg Q hQ hd hI he
    obtain ⟨_, t, _, ht⟩ := candidate_monic_factor k hg Q hQ hd
    have hpos : 0 ≤ Q.eval 3 := by rw [ht]; positivity
    rw [he]
    norm_num
    nlinarith

/-- Any large candidate must have a bad irreducible factor of degree at least
five. There is no bound here on these higher-degree factors. -/
theorem large_candidate_has_bad_factor_degree_ge_five (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (hk : 56 < k) :
    ∃ Q : ℤ[X], Q.Monic ∧ Irreducible Q ∧
      Q ∣ digitPoly (Nat.digits 3 (2 ^ k)) ∧ 5 ≤ Q.natDegree ∧
      2 * (8 : ℤ) ^ Q.natDegree < (Q.eval 3) ^ 2 := by
  obtain ⟨Q, hQ, hI, hd, hb⟩ := large_candidate_has_bad_factor k hg hk
  refine ⟨Q, hQ, hI, hd, ?_, hb⟩
  by_contra hh
  have hl := irreducible_degree_le_four_bound k hg Q hQ hd hI (by omega)
  omega

#print axioms irreducible_quartic_eval_bound
#print axioms irreducible_degree_le_four_bound
#print axioms large_candidate_has_bad_factor_degree_ge_five
#print axioms quartic_factor_eval_256_shape
#print axioms quartic_trace_constraints
#print axioms quartic_eval_256_coefficients
end Erdos406QuarticTrace
