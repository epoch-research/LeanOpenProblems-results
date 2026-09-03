import Submission.GapReduction

/-!
A conditional multiplicative-grid route with a surviving point at the origin.
The nonzero-residue hypothesis is essential to this proposal: the construction
in ProductGridObstruction uses zero residues and does not refute this premise.
No uniform nonzero-grid bound is established here.
-/
namespace Erdos970.NonzeroProductGrid
open IncrementReduction

/-- Explicitly unproved grid premise. All forbidden classes avoid the origin. -/
def GridBound (C : ℕ) : Prop :=
  ∀ k : ℕ, 0 < k → ∀ P : Finset ℕ,
    (∀ p ∈ P, p.Prime) → P.card ≤ k → ∀ r : ℕ → ℕ,
    (∀ p ∈ P, ¬0 ≡ r p [MOD p]) →
    ∃ x y : ℕ, 0 < x ∧ x ≤ C*k ∧ 0 < y ∧ y ≤ C*k ∧
      ∀ p ∈ P, ¬x*y ≡ r p [MOD p]

/-- A grid witness is a positive surviving displacement, not merely a survivor
at zero. This is what permits the next-gap reduction. -/
theorem next_bound_of_grid {C k : ℕ} (h : GridBound C) (hk : 0 < k)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPk : P.card ≤ k) :
    PrimeSetNextBound P ((C*k)^2) := by
  intro r hr
  obtain ⟨x,y,hx,hxC,hy,hyC,hxy⟩ := h k hk P hP hPk r hr
  refine ⟨x*y, Nat.mul_pos hx hy, ?_, hxy⟩
  simpa only [pow_two] using Nat.mul_le_mul hxC hyC

/-- The surviving-origin premise can be used for arbitrary intervals through
the already proved equivalence with next-gap bounds. -/
theorem jacobsthalBound_of_grid {C k : ℕ} (h : GridBound C) (hk : 0 < k) :
    IsJacobsthalBound k ((C*k)^2) := by
  by_contra hbad
  obtain ⟨P,hP,hPk,r,hcover⟩ :=
    (not_isJacobsthalBound_iff_cover k ((C*k)^2)).mp hbad
  have hb := primeSetBound_of_next hP (next_bound_of_grid h hk P hP hPk)
  obtain ⟨i,hi,havoid⟩ := hb r
  obtain ⟨p,hp,hip⟩ := hcover i hi
  exact havoid p hp hip

/-- CONDITIONAL: a fixed linear-side nonzero grid bound would settle the
unchanged conjecture. The grid premise remains a hypothesis. -/
theorem quadratic_bound_of_grid {C : ℕ} (hC : 0 < C) (h : GridBound C) :
    ∃ A > (0 : ℝ), ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤ A*k^2 := by
  refine ⟨(C : ℝ)^2, pow_pos (by exact_mod_cast hC) 2, fun k hk => ?_⟩
  have hh := (jacobsthalFunction_le_iff k ((C*k)^2)).mpr (jacobsthalBound_of_grid h hk)
  have hhR : (jacobsthalFunction k : ℝ) ≤ ((C*k)^2 : ℕ) := by exact_mod_cast hh
  simpa only [Nat.cast_pow,Nat.cast_mul,mul_pow] using hhR

#print axioms next_bound_of_grid
#print axioms jacobsthalBound_of_grid
#print axioms quadratic_bound_of_grid
end Erdos970.NonzeroProductGrid
