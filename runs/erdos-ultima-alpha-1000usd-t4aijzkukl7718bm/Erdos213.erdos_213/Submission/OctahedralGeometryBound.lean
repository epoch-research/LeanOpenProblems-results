import Submission.OctahedralGeometry
import Submission.OctahedralBounds
import Mathlib.Tactic.Linarith

/-! A restricted algebraic orbit bound. This is not a bound for arbitrary
integral-distance configurations and does not settle Erdős 213. -/
namespace Erdos213.OctahedralGeometry
open OctahedralLocal

lemma norm_zero_iff (a b c : ℤ) (i j : Fin 48) :
    normSq a b c i j = 0 ↔ point a b c i = point a b c j := by
  constructor
  · intro h
    unfold normSq at h
    have h0 : (point a b c i 0-point a b c j 0)^2 = 0 := by
      nlinarith [sq_nonneg (point a b c i 1-point a b c j 1),
        sq_nonneg (point a b c i 2-point a b c j 2)]
    have h1 : (point a b c i 1-point a b c j 1)^2 = 0 := by
      nlinarith [sq_nonneg (point a b c i 0-point a b c j 0),
        sq_nonneg (point a b c i 2-point a b c j 2)]
    have h2 : (point a b c i 2-point a b c j 2)^2 = 0 := by
      nlinarith [sq_nonneg (point a b c i 0-point a b c j 0),
        sq_nonneg (point a b c i 1-point a b c j 1)]
    funext k
    fin_cases k
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h0)
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h1)
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h2)
  · intro h
    simp only [normSq,h,sub_self,zero_pow (by norm_num : (2 : ℕ) ≠ 0),add_zero]

lemma square_code_of_square_norm (a b c : ℤ) (i j : Fin 48)
    (hne : point a b c i ≠ point a b c j) (hs : IsSquare (normSq a b c i j)) :
    IsSquare (intCodeValue a b c (edgeCode i j)) := by
  have hf : squareFactor a b c i j ≠ 0 := by
    intro hh
    apply hne
    apply (norm_zero_iff a b c i j).mp
    simp [norm_factor,hh]
  have hfQ : (squareFactor a b c i j : ℚ) ≠ 0 := by exact_mod_cast hf
  apply Rat.isSquare_intCast_iff.mp
  have hd := (Rat.isSquare_intCast_iff.mpr hs).div
    (IsSquare.sq (squareFactor a b c i j : ℚ))
  rw [norm_factor] at hd
  push_cast at hd
  simpa [hfQ] using hd

/-- For primitive integer coordinates with nonzero face forms, a subset of
the 48 signed permutations with distinct points and square integer chord
norms has at most eight labels. No general-position assumption is needed. -/
lemma orbit_square_norm_bound (a b c : ℤ)
    (hp : TetrahedralArithmetic.Primitive a b c)
    (hn : ∀ k : Fin 3, forms a b c (faceIndex k) ≠ 0)
    (T : Finset (Fin 48))
    (hi : Set.InjOn (point a b c) (T : Set (Fin 48)))
    (hs : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → IsSquare (normSq a b c i j)) :
    T.card ≤ 8 := by
  apply normalized_squareclass_one_bound a b c hp hn T
  intro i hit j hjt hij
  exact square_code_of_square_norm a b c i j (fun he => hij (hi hit hjt he))
    (hs i hit j hjt hij)

#print axioms square_code_of_square_norm
#print axioms orbit_square_norm_bound
end Erdos213.OctahedralGeometry
