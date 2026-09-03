import Submission.NewmanQuarticClassification

/-! Exact trace restrictions for quintic factors; no global degree bound. -/
namespace Erdos406QuinticTrace
open Polynomial Erdos406Cyclotomic Erdos406FactorParity Erdos406FactorCount
open Erdos406QuarticTrace Erdos406ReciprocalFlip

noncomputable def quintic (a b c d : ℤ) : ℤ[X] :=
  X^5 + C a * X^4 + C b * X^3 + C c * X^2 + C d * X + 1

lemma quintic_monic (a b c d : ℤ) : (quintic a b c d).Monic := by
  unfold quintic
  monicity <;> norm_num

lemma quintic_degree (a b c d : ℤ) : (quintic a b c d).natDegree = 5 := by
  unfold quintic
  compute_degree!

lemma norm_sum_five_lt (u v w z t : ℂ) (r : ℝ)
    (hu : ‖u‖ < r) (hv : ‖v‖ < r) (hw : ‖w‖ < r)
    (hz : ‖z‖ < r) (ht : ‖t‖ < r) :
    ‖u + v + w + z + t‖ < 5 * r := by
  have h4 := norm_sum_four_lt u v w z r hu hv hw hz
  have h5 := norm_add_le (u + v + w + z) t
  linarith

lemma trace_five_abs_bound (u v w z t : ℂ) (a B : ℤ) (e : ℕ) (he : e ≠ 0)
    (hu : ‖u‖ < 13 / 8) (hv : ‖v‖ < 13 / 8) (hw : ‖w‖ < 13 / 8)
    (hz : ‖z‖ < 13 / 8) (ht : ‖t‖ < 13 / 8)
    (ha : (a : ℂ) = u^e + v^e + w^e + z^e + t^e)
    (hB : 5 * (13 / 8 : ℝ)^e ≤ (B : ℝ) + 1) : |a| ≤ B := by
  have hp (x : ℂ) (hx : ‖x‖ < 13 / 8) : ‖x^e‖ < (13 / 8 : ℝ)^e := by
    rw [norm_pow]
    exact pow_lt_pow_left₀ hx (norm_nonneg x) he
  have hb := (norm_sum_five_lt (u^e) (v^e) (w^e) (z^e) (t^e) _
    (hp u hu) (hp v hv) (hp w hw) (hp z hz) (hp t ht)).trans_le hB
  rw [← ha, Complex.norm_intCast] at hb
  have hb' : |a| < B + 1 := by exact_mod_cast hb
  omega

/-- Newton trace bounds through degree five. -/
lemma quintic_trace_constraints (a b c d : ℤ)
    (hr : ∀ z ∈ ((quintic a b c d).map (Int.castRingHom ℂ)).roots, ‖z‖ < 13 / 8) :
    |a| ≤ 8 ∧ |a^2 - 2*b| ≤ 13 ∧ |-a^3 + 3*a*b - 3*c| ≤ 21 ∧
    |a^4 - 4*a^2*b + 2*b^2 + 4*a*c - 4*d| ≤ 34 ∧
    |-a^5 + 5*a^3*b - 5*a*b^2 - 5*a^2*c + 5*b*c + 5*a*d - 5| ≤ 56 := by
  let Q := quintic a b c d
  have hQ : Q.Monic := quintic_monic a b c d
  have hdeg : Q.natDegree = 5 := quintic_degree a b c d
  let F := Q.map (Int.castRingHom ℂ)
  have hs := IsAlgClosed.splits F
  have hcard : F.roots.card = 5 := by
    rw [← hs.natDegree_eq_card_roots]
    exact (hQ.natDegree_map _).trans hdeg
  obtain ⟨u, hu⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < F.roots.card)
  obtain ⟨s, hrs⟩ := Multiset.exists_cons_of_mem hu
  have hcs : s.card = 4 := by rw [hrs, Multiset.card_cons] at hcard; omega
  obtain ⟨v, w, z, t, hst⟩ := Multiset.card_eq_four.mp hcs
  have hroots : F.roots = {u, v, w, z, t} := by rw [hrs, hst]; rfl
  have hprod : F = (X - C u) * (X - C v) * (X - C w) * (X - C z) * (X - C t) := by
    rw [hs.eq_prod_roots_of_monic (hQ.map _), hroots]
    simp
    ring
  have he : F = X^5 - C (u + v + w + z + t) * X^4 + C (u*v + u*w + u*z + u*t + v*w + v*z + v*t + w*z + w*t + z*t) * X^3 - C (u*v*w + u*v*z + u*v*t + u*w*z + u*w*t + u*z*t + v*w*z + v*w*t + v*z*t + w*z*t) * X^2 + C (u*v*w*z + u*v*w*t + u*v*z*t + u*w*z*t + v*w*z*t) * X^1 - C (u*v*w*z*t) := by
    rw [hprod]
    simp only [map_add, map_mul]
    ring
  have h0 := congrArg (fun p : ℂ[X] => p.coeff 0) he
  have h1 := congrArg (fun p : ℂ[X] => p.coeff 1) he
  have h2 := congrArg (fun p : ℂ[X] => p.coeff 2) he
  have h3 := congrArg (fun p : ℂ[X] => p.coeff 3) he
  have h4 := congrArg (fun p : ℂ[X] => p.coeff 4) he
  simp only [F, Q, quintic, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_one, coeff_add, coeff_sub,
    coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_one] at h0 h1 h2 h3 h4
  norm_num at h0 h1 h2 h3 h4
  have ha : (a : ℂ) = -(u + v + w + z + t) := h4.trans (by ring)
  have hb : (b : ℂ) = (u*v + u*w + u*z + u*t + v*w + v*z + v*t + w*z + w*t + z*t) := h3.trans (by ring)
  have hc : (c : ℂ) = -(u*v*w + u*v*z + u*v*t + u*w*z + u*w*t + u*z*t + v*w*z + v*w*t + v*z*t + w*z*t) := h2.trans (by ring)
  have hd : (d : ℂ) = (u*v*w*z + u*v*w*t + u*v*z*t + u*w*z*t + v*w*z*t) := h1.trans (by ring)
  have hconst : (1 : ℂ) = -(u*v*w*z*t) := h0.trans (by ring)
  have ht1 : ((-a : ℤ) : ℂ) = u^1 + v^1 + w^1 + z^1 + t^1 := by
    push_cast
    rw [ha]
    ring
  have ht2 : ((a^2 - 2*b : ℤ) : ℂ) = u^2 + v^2 + w^2 + z^2 + t^2 := by
    push_cast
    rw [ha, hb]
    ring
  have ht3 : ((-a^3 + 3*a*b - 3*c : ℤ) : ℂ) = u^3 + v^3 + w^3 + z^3 + t^3 := by
    push_cast
    rw [ha, hb, hc]
    ring
  have ht4 : ((a^4 - 4*a^2*b + 2*b^2 + 4*a*c - 4*d : ℤ) : ℂ) = u^4 + v^4 + w^4 + z^4 + t^4 := by
    push_cast
    rw [ha, hb, hc, hd]
    ring
  have ht5 : ((-a^5 + 5*a^3*b - 5*a*b^2 - 5*a^2*c + 5*b*c + 5*a*d - 5 : ℤ) : ℂ) = u^5 + v^5 + w^5 + z^5 + t^5 := by
    push_cast
    rw [ha, hb, hc, hd]
    linear_combination -5 * hconst
  have hur := hr u (by change u ∈ F.roots; simp [hroots])
  have hvr := hr v (by change v ∈ F.roots; simp [hroots])
  have hwr := hr w (by change w ∈ F.roots; simp [hroots])
  have hzr := hr z (by change z ∈ F.roots; simp [hroots])
  have htr := hr t (by change t ∈ F.roots; simp [hroots])
  have hB1 := trace_five_abs_bound u v w z t _ 8 1 (by decide)
    hur hvr hwr hzr htr ht1 (by norm_num)
  have hB2 := trace_five_abs_bound u v w z t _ 13 2 (by decide)
    hur hvr hwr hzr htr ht2 (by norm_num)
  have hB3 := trace_five_abs_bound u v w z t _ 21 3 (by decide)
    hur hvr hwr hzr htr ht3 (by norm_num)
  have hB4 := trace_five_abs_bound u v w z t _ 34 4 (by decide)
    hur hvr hwr hzr htr ht4 (by norm_num)
  have hB5 := trace_five_abs_bound u v w z t _ 56 5 (by decide)
    hur hvr hwr hzr htr ht5 (by norm_num)
  exact ⟨by simpa only [abs_neg] using hB1, hB2, hB3, hB4, hB5⟩

lemma reverse_root_radial_bound (Q : ℤ[X]) (hQ : Q.Monic) (h0 : Q.coeff 0 = 1)
    (hr : ∀ z ∈ (Q.map (Int.castRingHom ℂ)).roots, ‖z⁻¹‖ < 13 / 8) :
    ∀ z ∈ (Q.reverse.map (Int.castRingHom ℂ)).roots, ‖z‖ < 13 / 8 := by
  have hR := (monic_reverse_of_constant_one Q hQ h0).1
  intro z hz
  have hev := (mem_roots (hR.map _).ne_zero).mp hz
  change (Q.reverse.map (Int.castRingHom ℂ)).eval z = 0 at hev
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, ← coeff_zero_eq_eval_zero, coeff_map, coeff_reverse, revAt_le (Nat.zero_le _),
      Nat.sub_zero, coeff_natDegree, hQ.leadingCoeff] at hev
    norm_num at hev
  letI : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz0)
  have he : (Q.map (Int.castRingHom ℂ)).eval z⁻¹ = 0 := by
    rw [eval_map]
    apply (eval₂_reverse_eq_zero_iff (Int.castRingHom ℂ) z⁻¹ Q).mp
    simpa only [invOf_eq_inv, inv_inv, eval_map] using hev
  have hh := hr z⁻¹ ((mem_roots (hQ.map _).ne_zero).mpr he)
  simpa using hh

lemma ofDigits_three_fifths_interval (w : List ℕ) (hw : w ⊆ [0, 1]) (x : ℝ)
    (hx : -(3 / 5 : ℝ) ≤ x) (hx0 : x ≤ 0) :
    -(15 / 16 : ℝ) ≤ Nat.ofDigits x w ∧ Nat.ofDigits x w ≤ 25 / 16 := by
  induction w with
  | nil => norm_num [Nat.ofDigits]
  | cons d w ih =>
    have hd := hw (List.mem_cons_self ..)
    have hh := ih (fun a ha => hw (List.mem_cons_of_mem d ha))
    have hlo := mul_le_mul_of_nonpos_left hh.2 hx0
    have hhi := mul_le_mul_of_nonpos_left hh.1 hx0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> simp only [Nat.ofDigits, Nat.cast_zero, Nat.cast_one]
    · constructor <;> nlinarith
    · constructor <;> nlinarith

lemma candidate_factor_neg_three_fifths_positive (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) :
    0 < (Q.map (Int.castRingHom ℝ)).eval (-(3 / 5)) := by
  have h0 := (candidate_monic_factor k hg Q hQ hd).1
  let F := Q.map (Int.castRingHom ℝ)
  have hF0 : F.eval 0 = 1 := by simp [F, ← coeff_zero_eq_eval_zero, h0]
  by_contra hh
  have hn : F.eval (-(3 / 5)) ≤ 0 := le_of_not_gt hh
  obtain ⟨x, hx, he⟩ := intermediate_value_Icc (by norm_num : -(3 / 5 : ℝ) ≤ 0)
    F.continuous.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (F.eval (-(3 / 5))) (F.eval 0) from ⟨hn, by rw [hF0]; norm_num⟩)
  change F.eval x = 0 at he
  have hv := eval_dvd (x := x) (map_dvd (Int.castRingHom ℝ) hd)
  change F.eval x ∣ _ at hv
  rw [he, zero_dvd_iff, eval_map_digitPoly, good_two_power_digits_head k hg] at hv
  have hg' := hg
  rw [good_two_power_digits_head k hg] at hg'
  have hw : Nat.digits 3 (2 ^ k / 3) ⊆ [0, 1] :=
    fun d hd => hg' (List.mem_cons_of_mem _ hd)
  have hb := (ofDigits_three_fifths_interval _ hw x hx.1 hx.2).2
  have hm := mul_le_mul_of_nonpos_left hb hx.2
  simp only [Nat.ofDigits, Nat.cast_one] at hv
  nlinarith [hx.1]

#print axioms quintic_trace_constraints
#print axioms reverse_root_radial_bound
#print axioms candidate_factor_neg_three_fifths_positive
end Erdos406QuinticTrace
