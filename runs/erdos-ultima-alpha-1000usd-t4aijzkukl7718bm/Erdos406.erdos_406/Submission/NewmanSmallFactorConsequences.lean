import Submission.NewmanQuarticClassification
import Submission.ReciprocalEvaluationCongruence

/-! Consequences of the complete factor classification through degree four.
This leaves all higher degrees open and does not settle Erdős406. -/

namespace Erdos406SmallFactorConsequences
open Polynomial Erdos406Cyclotomic Erdos406FactorBridge Erdos406QuarticSquare
open Erdos406QuarticClassification Erdos406ReciprocalCandidate Erdos406SmallFactors
open Erdos406ReciprocalCongruence

lemma prod_two_shapes (L : List ℤ[X])
    (hL : ∀ Q ∈ L, Q = X + 1 ∨ Q = qQuartic) :
    ∃ r s : ℕ, L.prod = (X + 1) ^ r * qQuartic ^ s := by
  induction L with
  | nil => exact ⟨0, 0, by simp⟩
  | cons Q L ih =>
    obtain ⟨r, s, he⟩ := ih (fun R hR => hL R (by simp [hR]))
    rcases hL Q (by simp) with hQ | hQ
    · refine ⟨r + 1, s, ?_⟩
      simp only [List.prod_cons, he, hQ, pow_succ]
      ring
    · refine ⟨r, s + 1, ?_⟩
      simp only [List.prod_cons, he, hQ, pow_succ]
      ring

/-- With no irreducible factor of degree at least five, the three known
values exhaust all possibilities. The degree premise remains essential. -/
theorem known_values_of_factor_degree_bound (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1])
    (hbound : ∀ Q : ℤ[X], Q.Monic → Irreducible Q →
      Q ∣ digitPoly (Nat.digits 3 (2 ^ k)) → Q.natDegree ≤ 4) :
    2 ^ k = 1 ∨ 2 ^ k = 4 ∨ 2 ^ k = 256 := by
  let P := digitPoly (Nat.digits 3 (2 ^ k))
  have hP : P.Monic := (candidate_digitPoly_isMonicOfDegree k hg).monic
  obtain ⟨L, hL, he⟩ := monic_irreducible_list P hP
  have hshapes : ∀ Q ∈ L, Q = X + 1 ∨ Q = qQuartic := by
    intro Q hQ
    have hd : Q ∣ P := by rw [← he]; exact List.dvd_prod hQ
    have hmax := hbound Q (hL Q hQ).1 (hL Q hQ).2 hd
    rcases irreducible_factor_alternative k hg Q (hL Q hQ).1 hd (hL Q hQ).2 with h | h
    · exact Or.inl h
    · exact Or.inr (irreducible_quartic_classification k hg Q
        (hL Q hQ).1 hd (by omega) (hL Q hQ).2)
  obtain ⟨r, s, hrs⟩ := prod_two_shapes L hshapes
  have hfamily := known_factor_family P (binary_digitPoly _ hg) r s (he.symm.trans hrs)
  rcases hfamily with h | h | h
  · have hv := congrArg (eval (3 : ℤ)) h
    change (digitPoly (Nat.digits 3 (2 ^ k))).eval 3 = (1 : ℤ[X]).eval 3 at hv
    rw [digitPoly_eval_three] at hv
    norm_num at hv
    exact Or.inl (by exact_mod_cast hv)
  · have hv := congrArg (eval (3 : ℤ)) h
    change (digitPoly (Nat.digits 3 (2 ^ k))).eval 3 = (X + 1 : ℤ[X]).eval 3 at hv
    rw [digitPoly_eval_three] at hv
    norm_num at hv
    exact Or.inr (Or.inl (by exact_mod_cast hv))
  · have hv := congrArg (eval (3 : ℤ)) h
    change (digitPoly (Nat.digits 3 (2 ^ k))).eval 3 = ((X + 1) * qQuartic).eval 3 at hv
    rw [digitPoly_eval_three] at hv
    norm_num [qQuartic] at hv
    exact Or.inr (Or.inr (by exact_mod_cast hv))

/-- Any additional good power necessarily introduces a higher-degree
irreducible factor. No bound on those degrees is asserted. -/
theorem additional_good_power_has_degree_five_factor (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1])
    (h1 : 2 ^ k ≠ 1) (h4 : 2 ^ k ≠ 4) (h256 : 2 ^ k ≠ 256) :
    ∃ Q : ℤ[X], Q.Monic ∧ Irreducible Q ∧
      Q ∣ digitPoly (Nat.digits 3 (2 ^ k)) ∧ 5 ≤ Q.natDegree := by
  by_contra hn
  push_neg at hn
  have hb := known_values_of_factor_degree_bound k hg (by
    intro Q hQ hI hd
    have hh := hn Q hQ hI hd
    omega)
  exact hb.elim h1 (fun h => h.elim h4 h256)

lemma known_quartic_nonreciprocal : qQuartic.reverse ≠ qQuartic := by
  intro he
  have hd : qQuartic.natDegree = 4 := by unfold qQuartic; compute_degree!
  have hc := congrArg (fun P : ℤ[X] => P.coeff 1) he
  change qQuartic.reverse.coeff 1 = qQuartic.coeff 1 at hc
  rw [coeff_reverse, hd, revAt_le (by decide : 1 ≤ 4)] at hc
  norm_num [qQuartic, coeff_one] at hc

/-- A nonlinear reciprocal irreducible candidate factor has even degree
at least six. It also obeys the stronger evaluation congruences. -/
theorem reciprocal_irreducible_factor_degree_six (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) (hI : Irreducible Q)
    (hr : Q.reverse = Q) (hn : Q ≠ X + 1) :
    Even Q.natDegree ∧ 6 ≤ Q.natDegree ∧ (4 : ℤ) ∣ Q.eval 1 := by
  have hmin : 4 ≤ Q.natDegree := (irreducible_factor_alternative k hg Q hQ hd hI).resolve_left hn
  have heven := irreducible_reciprocal_degree_even Q hr hI (by omega)
  have hnot4 : Q.natDegree ≠ 4 := by
    intro h4
    have hq := irreducible_quartic_classification k hg Q hQ hd h4 hI
    rw [hq] at hr
    exact known_quartic_nonreciprocal hr
  have h6 : 6 ≤ Q.natDegree := by obtain ⟨m, hm⟩ := heven; omega
  exact ⟨heven, h6, (reciprocal_candidate_eval_one_bound k hg Q hQ hd hI hr (by omega)).1⟩

lemma norm_prod_map (s : Multiset ℂ) (f : ℂ → ℂ) :
    ‖(s.map f).prod‖ = (s.map (fun z => ‖f z‖)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih => simp [Multiset.prod_cons, ih]

lemma eval_three_gt_eval_one (Q : ℤ[X]) (hQ : Q.Monic)
    (hdeg : 0 < Q.natDegree) (h1 : 0 < Q.eval 1) (h3 : 0 < Q.eval 3)
    (hroots : ∀ z ∈ (Q.map (Int.castRingHom ℂ)).roots, ‖z‖ < 2) :
    Q.eval 1 < Q.eval 3 := by
  let F := Q.map (Int.castRingHom ℂ)
  have hs := IsAlgClosed.splits F
  have he (a : ℤ) : F.eval (a : ℂ) = ((Q.eval a : ℤ) : ℂ) := by
    dsimp only [F]
    rw [eval_map]
    exact eval₂_at_apply (Int.castRingHom ℂ) a
  have hne : F.roots ≠ 0 := by
    intro hh
    have hc : F.roots.card = Q.natDegree := by
      rw [← hs.natDegree_eq_card_roots, hQ.natDegree_map]
    simp [hh] at hc
    omega
  have hpos (z : ℂ) (hz : z ∈ F.roots) : 0 < ‖(1 : ℂ) - z‖ := by
    apply norm_pos_iff.mpr
    intro heq
    have hz1 : z = 1 := (sub_eq_zero.mp heq).symm
    have hroot := (mem_roots (hQ.map _).ne_zero).mp hz
    change F.eval z = 0 at hroot
    rw [hz1, ← Int.cast_one, he 1] at hroot
    have : Q.eval 1 = 0 := by exact_mod_cast hroot
    omega
  have hlt (z : ℂ) (hz : z ∈ F.roots) : ‖(1 : ℂ) - z‖ < ‖(3 : ℂ) - z‖ := by
    have hr : z.re < 2 := (Complex.re_le_norm z).trans_lt (hroots z hz)
    have hsq : ‖(1 : ℂ) - z‖ ^ 2 < ‖(3 : ℂ) - z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm]
      norm_num [Complex.normSq_apply]
      nlinarith
    nlinarith [norm_nonneg ((1 : ℂ) - z), norm_nonneg ((3 : ℂ) - z)]
  have hh : ‖F.eval 1‖ < ‖F.eval 3‖ := by
    rw [hs.eval_eq_prod_roots_of_monic (hQ.map _),
      hs.eval_eq_prod_roots_of_monic (hQ.map _), norm_prod_map, norm_prod_map]
    exact Multiset.prod_map_lt_prod_map hne _ _ hpos hlt
  have he1 : F.eval 1 = ((Q.eval 1 : ℤ) : ℂ) := by simpa using he 1
  have he3 : F.eval 3 = ((Q.eval 3 : ℤ) : ℂ) := by simpa using he 3
  rw [he1, he3, Complex.norm_intCast, Complex.norm_intCast,
    abs_of_pos (by exact_mod_cast h1), abs_of_pos (by exact_mod_cast h3)] at hh
  exact_mod_cast hh

/-- The earlier exceptional value-four premise is unnecessary for nonlinear
reciprocal irreducible candidate factors. -/
theorem reciprocal_irreducible_evaluation_bounds (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) (hI : Irreducible Q)
    (hr : Q.reverse = Q) (hn : Q ≠ X + 1) :
    (4 : ℤ) ∣ Q.eval 1 ∧ 4 ≤ Q.eval 1 ∧
      (16 : ℤ) ∣ Q.eval (-1) ∧ 16 ≤ |Q.eval (-1)| := by
  have hD := (reciprocal_irreducible_factor_degree_six k hg Q hQ hd hI hr hn).2.1
  have h1 := reciprocal_candidate_eval_one_bound k hg Q hQ hd hI hr (by omega)
  obtain ⟨_, t, _, ht⟩ := Erdos406FactorParity.candidate_monic_factor k hg Q hQ hd
  have h3 : 0 < Q.eval 3 := by rw [ht]; positivity
  have hlt := eval_three_gt_eval_one Q hQ (by omega) (by omega) h3
    (Erdos406FactorCount.candidate_factor_root_bound k hg Q hQ hd)
  have hm := reciprocal_candidate_neg_one_bound k hg Q hQ hd hI hr (by omega) (by omega)
  exact ⟨h1.1, h1.2, hm.1, hm.2⟩

#print axioms reciprocal_irreducible_evaluation_bounds
#print axioms known_values_of_factor_degree_bound
#print axioms additional_good_power_has_degree_five_factor
#print axioms reciprocal_irreducible_factor_degree_six
end Erdos406SmallFactorConsequences
