import FormalConjecturesUtil
import Submission.IrrationalSequenceDiagnostic

/-! An infinite family of nonzero integer quadratics can encode ANY
integer-valued optimization function exactly. Bounded degree alone cannot
replace fixed finiteness in the rational-exponent certificate criterion.
This is not a counterexample to the graph conjecture. -/
open Filter Asymptotics MvPolynomial
namespace Erdos713QuadraticEncoding

noncomputable def exclusion (a b : ℕ) : MvPolynomial (Fin 2) ℤ :=
  (X 0-C (a : ℤ))^2+(X 1-C (b : ℤ))^2-C 1

noncomputable def evalR (P : MvPolynomial (Fin 2) ℤ) (x y : ℝ) : ℝ :=
  MvPolynomial.eval₂ (Int.castRingHom ℝ) ![x,y] P

lemma eval_exclusion (a b : ℕ) (x y : ℝ) :
    evalR (exclusion a b) x y = (x-a)^2+(y-b)^2-1 := by
  simp [evalR,exclusion]

lemma exclusion_degree (a b : ℕ) : (exclusion a b).totalDegree ≤ 2 := by
  have h0 := totalDegree_sub (X (0 : Fin 2) : MvPolynomial (Fin 2) ℤ) (C (a : ℤ))
  have h1 := totalDegree_sub (X (1 : Fin 2) : MvPolynomial (Fin 2) ℤ) (C (b : ℤ))
  have hp0 := totalDegree_pow (X (0 : Fin 2)-C (a : ℤ)) 2
  have hp1 := totalDegree_pow (X (1 : Fin 2)-C (b : ℤ)) 2
  have ha := totalDegree_add ((X (0 : Fin 2)-C (a : ℤ))^2) ((X 1-C (b : ℤ))^2)
  have hs := totalDegree_sub ((X (0 : Fin 2)-C (a : ℤ))^2+(X 1-C (b : ℤ))^2) (C (1 : ℤ))
  simp only [totalDegree_X,totalDegree_C] at h0 h1 hs
  change _ ≤ 2
  unfold exclusion
  omega

lemma exclusion_ne_zero (a b : ℕ) : exclusion a b ≠ 0 := by
  intro h
  have hh := eval_exclusion a b a b
  rw [h] at hh
  norm_num [evalR] at hh

lemma square_separation {n a : ℕ} (hna : n ≠ a) : (1 : ℝ) ≤ ((n : ℝ)-a)^2 := by
  have hi : (n : ℤ)-(a : ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hna)
  have hp := sq_pos_of_ne_zero hi
  have hp' : (1 : ℤ) ≤ ((n : ℤ)-(a : ℤ))^2 := by omega
  exact_mod_cast hp'

lemma feasible_exclusion_iff (a b n m : ℕ) :
    0 ≤ evalR (exclusion a b) n m ↔ n ≠ a ∨ m ≠ b := by
  rw [eval_exclusion]
  constructor
  · intro h
    by_contra hh
    push_neg at hh
    obtain ⟨rfl,rfl⟩ := hh
    norm_num at h
  · rintro (hn | hm)
    · have hh := square_separation hn
      nlinarith [sq_nonneg ((m : ℝ)-b)]
    · have hh := square_separation hm
      nlinarith [sq_nonneg ((n : ℝ)-a)]

/-- A nonzero, degree-at-most-two, integer-coefficient relaxation.
Its index type is NOT required to be finite. -/
def HasQuadraticRelaxation (f : ℕ → ℕ) : Prop :=
  ∃ I : Type, ∃ P : I → MvPolynomial (Fin 2) ℤ,
    (∀ i, (P i).totalDegree ≤ 2 ∧ P i ≠ 0) ∧
    ∀ n m : ℕ, (∀ i, 0 ≤ evalR (P i) n m) ↔ m ≤ f n

lemma universal_encoding (f : ℕ → ℕ) : HasQuadraticRelaxation f := by
  refine ⟨{p : ℕ × ℕ // f p.1 < p.2},fun p => exclusion p.val.1 p.val.2,
    fun p => ⟨exclusion_degree _ _,exclusion_ne_zero _ _⟩,?_⟩
  intro n m
  constructor
  · intro hh
    by_contra hm
    have hb : f n < m := by omega
    have hbad := hh ⟨(n,m),hb⟩
    simp only [eval_exclusion,sub_self,zero_pow (by decide : 2 ≠ 0),add_zero,zero_sub] at hbad
    norm_num at hbad
  · intro hm p
    apply (feasible_exclusion_iff _ _ _ _).mpr
    by_contra hh
    push_neg at hh
    obtain ⟨hn,hmb⟩ := hh
    have hb := p.property
    rw [←hn,←hmb] at hb
    omega

/-- For any fixed finite subset of these exclusions, eventually EVERY
integer m is feasible. The quantifiers cannot be interchanged. -/
lemma finite_subfamily_vacuous (S : Finset (ℕ × ℕ)) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, ∀ p ∈ S, 0 ≤ evalR (exclusion p.1 p.2) n m := by
  filter_upwards [eventually_gt_atTop (S.sup Prod.fst)] with n hn m p hp
  apply (feasible_exclusion_iff _ _ _ _).mpr
  exact Or.inl (ne_of_gt ((Finset.le_sup hp).trans_lt hn))

/-- This is the negation of an AUXILIARY bounded-degree rationality
principle, not the negation of the original graph conjecture. -/
theorem not_bounded_degree_rationality :
    ¬ ∀ (f : ℕ → ℕ) (α c : ℝ), α ∈ Set.Ico 1 2 → 0 < c →
      (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n : ℕ => c*(n : ℝ)^α) →
      HasQuadraticRelaxation f → α ∈ Set.range ((↑) : ℚ → ℝ) := by
  intro h
  have hb := Erdos713IrrationalSequenceDiagnostic.index_bounds
  have hi := h Erdos713IrrationalSequenceDiagnostic.seq
    Erdos713IrrationalSequenceDiagnostic.index 1 ⟨by linarith,by linarith⟩ (by norm_num)
    (by simpa using Erdos713IrrationalSequenceDiagnostic.seq_asymptotic)
    (universal_encoding _)
  exact Erdos713IrrationalSequenceDiagnostic.index_irrational hi

#print axioms exclusion_degree
#print axioms universal_encoding
#print axioms finite_subfamily_vacuous
#print axioms not_bounded_degree_rationality
end Erdos713QuadraticEncoding
