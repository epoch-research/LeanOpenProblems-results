import Submission.NewmanPatternDilations
import Submission.NewmanEventualFactorBound

/-! A fixed even-degree irreducible polynomial has only finitely many
uniform dilations that can occur as factors of ANY candidate polynomial.
A finite-family reduction is proved with an explicit, unproved covering
hypothesis. This file does not settle Erdős406. -/
namespace Erdos406DilatedFactors
open Polynomial Erdos406Cyclotomic Erdos406FactorParity
open Erdos406PatternDilations Erdos406EventualFactorBound

def Occurs (Q : ℤ[X]) : Prop :=
  ∃ k : ℕ, Nat.digits 3 (2^k) ⊆ [0, 1] ∧ Q ∣ digitPoly (Nat.digits 3 (2^k))

def dilationSpacings (Q : ℤ[X]) : Set ℕ := {L | Occurs (expand ℤ L Q)}

lemma irreducible_not_square (Q : ℤ[X]) (hI : Irreducible Q) : ¬ IsSquare Q := by
  rintro ⟨R, he⟩
  have he' : Q = R^2 := by simpa only [pow_two] using he
  rw [he'] at hI
  exact not_irreducible_pow (by decide : 2 ≠ 1) hI

/-- The parent candidate may vary: only the undilated factor is fixed. -/
theorem finite_candidate_dilation_spacings (Q : ℤ[X]) (hm : Q.Monic)
    (hI : Irreducible Q) (h0 : Q.coeff 0 = 1) (hE : Even Q.natDegree) :
    (dilationSpacings Q).Finite := by
  have hD := hm.natDegree_pos_of_not_isUnit hI.not_isUnit
  have hf := finite_power_dilations_even_degree Q hm h0 hD hE (irreducible_not_square Q hI)
  apply ((Set.finite_singleton 0).union hf).subset
  intro L hL
  by_cases hz : L = 0
  · exact Or.inl hz
  obtain ⟨k, hg, hd⟩ := hL
  have hM : (expand ℤ L Q).Monic := Monic.expand (by omega : 0 < L) hm
  obtain ⟨_, t, _, ht⟩ := candidate_monic_factor k hg (expand ℤ L Q) hM hd
  have he : (expand ℤ L Q).eval 3 = Q.eval ((3 : ℤ)^L) := by
    simp only [expand_eq_comp_X_pow, eval_comp, eval_pow, eval_X]
  right
  refine ⟨2*t, ?_⟩
  rw [← he, ht, pow_mul]
  norm_num

/-- A finite set of fixed even-degree irreducible base polynomials gives
only finitely many dilated factors that actually occur in candidates. -/
theorem finite_occurring_dilations (S : Set ℤ[X]) (hS : S.Finite)
    (hb : ∀ Q ∈ S, Q.Monic ∧ Irreducible Q ∧ Q.coeff 0 = 1 ∧ Even Q.natDegree) :
    (⋃ Q ∈ S, (fun L => expand ℤ L Q) '' dilationSpacings Q).Finite := by
  apply hS.biUnion
  intro Q hQ
  obtain ⟨hm, hI, h0, hE⟩ := hb Q hQ
  exact (finite_candidate_dilation_spacings Q hm hI h0 hE).image _

/-- A CONDITIONAL reduction. The finite covering family is not proved to
exist. Its members have even degree, but their dilations initially have no
uniform degree restriction; Runge supplies that restriction. -/
theorem finite_of_finite_even_dilation_cover (S : Set ℤ[X]) (hS : S.Finite)
    (hb : ∀ Q ∈ S, Q.Monic ∧ Irreducible Q ∧ Q.coeff 0 = 1 ∧ Even Q.natDegree)
    (hcover : ∀ k : ℕ, Nat.digits 3 (2^k) ⊆ [0, 1] →
      ∀ R : ℤ[X], R.Monic → Irreducible R →
        R ∣ digitPoly (Nat.digits 3 (2^k)) →
        R = X+1 ∨ ∃ Q ∈ S, ∃ L : ℕ, R = expand ℤ L Q) :
    {n | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  let A : Set ℤ[X] := {X+1} ∪ ⋃ Q ∈ S, (fun L => expand ℤ L Q) '' dilationSpacings Q
  have hA : A.Finite := (Set.finite_singleton _).union (finite_occurring_dilations S hS hb)
  obtain ⟨B, hB⟩ := (hA.image natDegree).exists_le
  apply finite_of_eventual_factor_bound B 0
  intro k hg R hR hI hd hlarge
  have hm : R ∈ A := by
    rcases hcover k hg R hR hI hd with he | ⟨Q, hQ, L, he⟩
    · exact Or.inl he
    · right
      apply Set.mem_iUnion.mpr
      refine ⟨Q, Set.mem_iUnion.mpr ⟨hQ, ?_⟩⟩
      refine ⟨L, ?_, he.symm⟩
      exact ⟨k, hg, by rwa [← he]⟩
  have hbound := hB R.natDegree ⟨R, hm, rfl⟩
  omega

/-- If the original set were infinite, every proposed finite collection of
such even-degree dilation families would miss an irreducible candidate
factor other than X+1. This is a necessary condition, not a disproof. -/
theorem infinite_forces_escape_from_even_dilation_families
    (hinf : ¬ {n | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite)
    (S : Set ℤ[X]) (hS : S.Finite)
    (hb : ∀ Q ∈ S, Q.Monic ∧ Irreducible Q ∧ Q.coeff 0 = 1 ∧ Even Q.natDegree) :
    ∃ k : ℕ, Nat.digits 3 (2^k) ⊆ [0, 1] ∧ ∃ R : ℤ[X], R.Monic ∧
      Irreducible R ∧ R ∣ digitPoly (Nat.digits 3 (2^k)) ∧ R ≠ X+1 ∧
      ∀ Q ∈ S, ∀ L : ℕ, R ≠ expand ℤ L Q := by
  by_contra hh
  push_neg at hh
  apply hinf
  apply finite_of_finite_even_dilation_cover S hS hb
  intro k hg R hR hI hd
  by_cases he : R = X+1
  · exact Or.inl he
  · exact Or.inr (hh k hg R hR hI hd he)

#print axioms finite_candidate_dilation_spacings
#print axioms finite_of_finite_even_dilation_cover
#print axioms infinite_forces_escape_from_even_dilation_families
end Erdos406DilatedFactors
