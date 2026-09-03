import Submission.PolynomialPrimePowerSquares
import Submission.NewmanDilatedFactors

/-! Local square-root approximation removes the even-degree restriction
from the fixed-shape dilation results. A finite covering family remains
an explicit unproved hypothesis, so these results do not settle Erdős406. -/
namespace Erdos406AllDilations
open Polynomial Erdos406LocalRunge Erdos406PatternDilations
  Erdos406DilatedFactors Erdos406ReciprocalFlip Erdos406Cyclotomic
  Erdos406FactorParity Erdos406EventualFactorBound

/-- For a fixed normalized monic nonsquare polynomial, only finitely many
ternary power inputs can give a power of two. -/
theorem finite_power_dilations (P : ℤ[X]) (hm : P.Monic)
    (h0 : P.coeff 0 = 1) (hns : ¬ IsSquare P) :
    {L : ℕ | ∃ k : ℕ, P.eval ((3 : ℤ)^L) = (2 : ℤ)^k}.Finite := by
  have hf := finite_ternary_square_values P hm h0 hns
  apply ((Set.finite_singleton 0).union hf).subset
  intro L hL
  by_cases hz : L = 0
  · exact Or.inl hz
  obtain ⟨k, hk⟩ := hL
  obtain ⟨r, hr⟩ := even_power_exponent_at_ternary_base P h0 L k (by omega) hk
  right
  refine ⟨(2 : ℤ)^r, ?_⟩
  rw [hk, hr, pow_add]

/-- All spacings are covered, including odd spacings of odd-degree patterns. -/
theorem finite_pattern_dilations (P : ℤ[X]) (hP : Binary P) (hm : P.Monic)
    (h0 : P.coeff 0 = 1) (hD : 0 < P.natDegree) :
    {L : ℕ | ∃ k : ℕ, P.eval ((3 : ℤ)^L) = (2 : ℤ)^k}.Finite :=
  finite_power_dilations P hm h0 (normalized_binary_not_square P hP h0 hD)

/-- The parent candidate may vary; only the base irreducible factor is fixed. -/
theorem finite_candidate_dilation_spacings (Q : ℤ[X]) (hm : Q.Monic)
    (hI : Irreducible Q) (h0 : Q.coeff 0 = 1) :
    (dilationSpacings Q).Finite := by
  have hf := finite_power_dilations Q hm h0 (irreducible_not_square Q hI)
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

/-- A finite set of fixed irreducible base shapes gives only finitely many
of their dilations that occur in candidates. No degree parity is assumed. -/
theorem finite_occurring_dilations (S : Set ℤ[X]) (hS : S.Finite)
    (hb : ∀ Q ∈ S, Q.Monic ∧ Irreducible Q ∧ Q.coeff 0 = 1) :
    (⋃ Q ∈ S, (fun L => expand ℤ L Q) '' dilationSpacings Q).Finite := by
  apply hS.biUnion
  intro Q hQ
  obtain ⟨hm, hI, h0⟩ := hb Q hQ
  exact (finite_candidate_dilation_spacings Q hm hI h0).image _

/-- CONDITIONAL finiteness: the existence of a finite covering family of
base shapes is a hypothesis, not a result of this theorem. -/
theorem finite_of_finite_dilation_cover (S : Set ℤ[X]) (hS : S.Finite)
    (hb : ∀ Q ∈ S, Q.Monic ∧ Irreducible Q ∧ Q.coeff 0 = 1)
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

/-- An infinite original set would require irreducible factors escaping
every finite collection of fixed dilation families. -/
theorem infinite_forces_escape_from_dilation_families
    (hinf : ¬ {n | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite)
    (S : Set ℤ[X]) (hS : S.Finite)
    (hb : ∀ Q ∈ S, Q.Monic ∧ Irreducible Q ∧ Q.coeff 0 = 1) :
    ∃ k : ℕ, Nat.digits 3 (2^k) ⊆ [0, 1] ∧ ∃ R : ℤ[X], R.Monic ∧
      Irreducible R ∧ R ∣ digitPoly (Nat.digits 3 (2^k)) ∧ R ≠ X+1 ∧
      ∀ Q ∈ S, ∀ L : ℕ, R ≠ expand ℤ L Q := by
  by_contra hh
  push_neg at hh
  apply hinf
  apply finite_of_finite_dilation_cover S hS hb
  intro k hg R hR hI hd
  by_cases he : R = X+1
  · exact Or.inl he
  · exact Or.inr (hh k hg R hR hI hd he)

#print axioms finite_pattern_dilations
#print axioms finite_candidate_dilation_spacings
#print axioms finite_of_finite_dilation_cover
#print axioms infinite_forces_escape_from_dilation_families
end Erdos406AllDilations
