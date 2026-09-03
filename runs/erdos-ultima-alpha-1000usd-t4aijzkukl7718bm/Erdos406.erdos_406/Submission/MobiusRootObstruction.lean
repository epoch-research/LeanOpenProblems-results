import Submission.PositivePerturbationPolynomials
import Submission.NewmanSmallFactorConsequences

/-! The small-conjugate Möbius transformation supplies a lower evaluation
bound, not an upper one. Arbitrarily large irreducible root-only examples
already satisfy this transformed bound. No Newman divisibility is asserted
for these examples; this file does not settle Erdős 406. -/

namespace Erdos406Mobius
open Polynomial Erdos406Perturbation Erdos406SmallFactorConsequences

lemma distance_square_comparison (z : ℂ) (hz : ‖z‖ ^ 2 < 3) :
    3 * ‖(1 : ℂ) - z‖ ^ 2 < ‖(3 : ℂ) - z‖ ^ 2 := by
  rw [Complex.sq_norm] at hz
  rw [Complex.sq_norm, Complex.sq_norm]
  norm_num [Complex.normSq_apply] at hz ⊢
  nlinarith

lemma mobius_small (z : ℂ) (hz : ‖z‖ ^ 2 < 3) :
    ‖((1 : ℂ) - z) / (3 - z)‖ ^ 2 < 1 / 3 := by
  have hh := distance_square_comparison z hz
  have hp : 0 < ‖(3 : ℂ) - z‖ ^ 2 := by nlinarith [sq_nonneg ‖(1 : ℂ) - z‖]
  rw [norm_div, div_pow, div_lt_iff₀ hp]
  linarith

lemma mobius_inverse_large (z : ℂ) (hz : ‖z‖ ^ 2 < 3) (h1 : z ≠ 1) :
    3 < ‖((3 : ℂ) - z) / (1 - z)‖ ^ 2 := by
  have hp : 0 < ‖(1 : ℂ) - z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (by
    intro he
    exact h1 (sub_eq_zero.mp he).symm))
  rw [norm_div, div_pow, lt_div_iff₀ hp]
  exact distance_square_comparison z hz

lemma lower_evaluation_bound (Q : ℤ[X]) (hQ : Q.Monic)
    (hD : 0 < Q.natDegree) (h1 : Q.eval 1 ≠ 0)
    (hroot : ∀ z ∈ (Q.map (Int.castRingHom ℂ)).roots, ‖z‖ ^ 2 < 3) :
    (3 : ℤ) ^ Q.natDegree * (Q.eval 1) ^ 2 < (Q.eval 3) ^ 2 := by
  let F := Q.map (Int.castRingHom ℂ)
  have hs := IsAlgClosed.splits F
  have he (a : ℤ) : F.eval (a : ℂ) = ((Q.eval a : ℤ) : ℂ) := by
    dsimp only [F]
    rw [eval_map]
    exact eval₂_at_apply (Int.castRingHom ℂ) a
  have hcard : F.roots.card = Q.natDegree := by
    rw [← hs.natDegree_eq_card_roots, hQ.natDegree_map]
  have hne : F.roots ≠ 0 := by
    intro hh
    simp [hh] at hcard
    omega
  have hpos (z : ℂ) (hz : z ∈ F.roots) : 0 < 3 * ‖(1 : ℂ) - z‖ ^ 2 := by
    have hn : (1 : ℂ) - z ≠ 0 := by
      intro hh
      have hz1 : z = 1 := (sub_eq_zero.mp hh).symm
      have hr := (mem_roots (hQ.map _).ne_zero).mp hz
      change F.eval z = 0 at hr
      rw [hz1, ← Int.cast_one, he 1] at hr
      exact h1 (by exact_mod_cast hr)
    exact mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr hn))
  have hb := Multiset.prod_map_lt_prod_map hne
    (fun z : ℂ => 3 * ‖(1 : ℂ) - z‖ ^ 2)
    (fun z : ℂ => ‖(3 : ℂ) - z‖ ^ 2) hpos
    (fun z hz => distance_square_comparison z (hroot z hz))
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
    Multiset.prod_map_pow, Multiset.prod_map_pow, hcard] at hb
  have hprod (a : ℤ) :
      (F.roots.map (fun z => ‖(a : ℂ) - z‖)).prod = |((Q.eval a : ℤ) : ℝ)| := by
    rw [← norm_prod_map, ← hs.eval_eq_prod_roots_of_monic (hQ.map _), he a,
      Complex.norm_intCast]
  have hprod1 := hprod 1
  have hprod3 := hprod 3
  norm_num only [Int.cast_one, Int.cast_ofNat] at hprod1 hprod3
  rw [hprod1, hprod3, sq_abs, sq_abs] at hb
  exact_mod_cast hb

/-- For actual positive-degree candidate factors the comparison is strictly
in the lower-bound direction. -/
theorem candidate_lower_evaluation_bound (k : ℕ)
    (hg : Nat.digits 3 (2^k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ Erdos406Cyclotomic.digitPoly (Nat.digits 3 (2^k)))
    (hD : 0 < Q.natDegree) :
    (3 : ℤ)^Q.natDegree * (Q.eval 1)^2 < (Q.eval 3)^2 := by
  have h1 := (Erdos406FactorCount.candidate_factor_eval_one_even k hg Q hQ hd hD).2
  apply lower_evaluation_bound Q hQ hD (by omega)
  intro z hz
  have hn := (Erdos406QuarticTrace.candidate_factor_radial_bound k hg Q hQ hd z hz).1
  nlinarith [norm_nonneg z]

/-- All the proposed rootwise Möbius inequalities hold in an existing
arbitrarily large family of irreducible root-only exceptions. -/
theorem unbounded_transformed_root_only_exceptions (B c : ℕ) :
    ∃ Q : ℤ[X], Q.Monic ∧ Irreducible Q ∧ B < Q.natDegree ∧
      Q.coeff 0 = 1 ∧ Q.eval 1 = 2 ∧
      (∃ e : ℕ, Q.eval 3 = (2 : ℤ) ^ e) ∧
      (∀ z ∈ (Q.map (Int.castRingHom ℂ)).roots,
        ‖((1 : ℂ) - z) / (3 - z)‖ ^ 2 < 1 / 3 ∧
        3 < ‖((3 : ℂ) - z) / (1 - z)‖ ^ 2) ∧
      (2 : ℤ) ^ c * 8 ^ Q.natDegree < (Q.eval 3) ^ 2 := by
  obtain ⟨Q, hQ, hI, hD, h0, h1, h3, _, _, hr, hgap⟩ :=
    arbitrarily_large_root_only_exceptions (5 / 4) (by norm_num) (by norm_num) B c
  refine ⟨Q, hQ, hI, hD, h0, h1, h3, ?_, hgap⟩
  intro z hz
  have hn : ‖z‖ ^ 2 < 3 := by
    have hh := (hr z hz).2
    nlinarith [norm_nonneg z]
  refine ⟨mobius_small z hn, mobius_inverse_large z hn ?_⟩
  intro he
  have hval := (mem_roots (hQ.map _).ne_zero).mp hz
  rw [he] at hval
  have hv : (Q.map (Int.castRingHom ℂ)).eval 1 = (2 : ℂ) := by
    simpa using congrArg (fun x : ℤ => (x : ℂ)) h1
  change (Q.map (Int.castRingHom ℂ)).eval 1 = 0 at hval
  rw [hv] at hval
  norm_num at hval

#print axioms candidate_lower_evaluation_bound
#print axioms lower_evaluation_bound
#print axioms unbounded_transformed_root_only_exceptions
end Erdos406Mobius
