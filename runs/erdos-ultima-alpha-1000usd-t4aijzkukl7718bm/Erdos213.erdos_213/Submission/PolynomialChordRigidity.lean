import Submission.PolynomialTwoAnchors

/-! Uniform polynomial parametrizations of rational-distance sets are
collinear. This does not address sparse parameter sets or n-dependent paths. -/
namespace Erdos213.PolynomialChordRigidity
open Polynomial PolynomialTwoAnchors
noncomputable section
set_option maxHeartbeats 2000000

def sqNorm (D : ℚ) (x y : ℚ[X]) : ℚ[X] := x^2+C D*y^2

lemma rotation_norm (D a b : ℚ) (x y : ℚ[X]) :
    sqNorm D (C a*x+C (D*b)*y) (C a*y-C b*x) =
      C (a^2+D*b^2)*sqNorm D x y := by
  simp only [sqNorm,map_add,map_mul,map_pow]
  ring

lemma scale_norm (D c : ℚ) (x y : ℚ[X]) :
    sqNorm D (C c*x) (C c*y) = (C c)^2*sqNorm D x y := by
  dsimp [sqNorm]
  ring

lemma cross_zero_of_anchor_squares (D a b α : ℚ) (hD : 0 < D)
    (hab : a ≠ 0 ∨ b ≠ 0) (hL : IsSquare (a^2+D*b^2))
    (x y : ℚ[X]) (hx : x.eval α=0) (hy : y.eval α=0)
    (h0 : IsSquare (sqNorm D x y))
    (h1 : IsSquare (sqNorm D (x-C a) (y-C b))) : C a*y-C b*x=0 := by
  let L := a^2+D*b^2
  have hLpos : 0 < L := by rcases hab with ha | hb <;> dsimp [L] <;> positivity
  have hL0 := ne_of_gt hLpos
  let R := C a*x+C (D*b)*y
  let S := C a*y-C b*x
  let r := C L⁻¹*R
  let s := C L⁻¹*S
  have hcancel : (C L⁻¹ : ℚ[X])*C L=1 := by rw [← map_mul,inv_mul_cancel₀ hL0,map_one]
  have hr : IsSquare (sqNorm D r s) := by
    dsimp [r,s,R,S]
    rw [scale_norm,rotation_norm]
    exact (IsSquare.sq (C L⁻¹)).mul ((hL.map C).mul h0)
  have hR : C a*(x-C a)+C (D*b)*(y-C b)=R-C L := by
    dsimp [R,L]
    simp only [map_add,map_mul,map_pow]
    ring
  have hS : C a*(y-C b)-C b*(x-C a)=S := by dsimp [S]; ring
  have hr1 : r-1=C L⁻¹*(C a*(x-C a)+C (D*b)*(y-C b)) := by
    rw [hR]
    dsimp [r]
    linear_combination hcancel
  have hs1 : s=C L⁻¹*(C a*(y-C b)-C b*(x-C a)) := by rw [hS]
  have hr' : IsSquare (sqNorm D (r-1) s) := by
    rw [hr1,hs1,scale_norm,rotation_norm]
    exact (IsSquare.sq (C L⁻¹)).mul ((hL.map C).mul h1)
  have hs0 : s.eval α=0 := by simp [s,S,hx,hy]
  have hs : s=0 := by
    rcases rational_two_anchor_classification r s D hD hr hr' with hh | ⟨_,hh⟩
    · exact hh
    · have he := eq_C_of_natDegree_eq_zero hh
      have hc : s.coeff 0=0 := by rw [he,eval_C] at hs0; exact hs0
      rw [he,hc,map_zero]
  exact (mul_eq_zero.mp hs).resolve_left (C_ne_zero.mpr (inv_ne_zero hL0))

lemma exists_different_tail_value (p : ℚ[X]) (hp : p.natDegree ≠ 0) (N : ℤ) :
    ∃ n : ℤ, N ≤ n ∧ p.eval (n : ℚ) ≠ p.eval (N : ℚ) := by
  have hf : p-C (p.eval (N : ℚ)) ≠ 0 := by
    intro h
    have he := congrArg natDegree (sub_eq_zero.mp h)
    exact hp (by simpa only [natDegree_C] using he)
  obtain ⟨M,hM⟩ := exists_max_root (p-C (p.eval (N : ℚ))) hf
  obtain ⟨n,hn⟩ := exists_int_gt (max M (N : ℚ))
  have hnM : M < (n : ℚ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hnN : (N : ℚ) < n := lt_of_le_of_lt (le_max_right _ _) hn
  refine ⟨n,?_,?_⟩
  · have hN : N < n := by exact_mod_cast hnN
    omega
  · intro hh
    have he : (p-C (p.eval (N : ℚ))).eval (n : ℚ)=0 := by simp [hh]
    exact (not_le_of_gt hnM) (hM _ he)

lemma fixed_anchor_line (D : ℚ) (hD : 0 < D) (x y : ℚ[X]) (N a b : ℤ)
    (ha : N ≤ a) (hb : N ≤ b)
    (hne : x.eval (b : ℚ)-x.eval (a : ℚ) ≠ 0 ∨
      y.eval (b : ℚ)-y.eval (a : ℚ) ≠ 0)
    (hint : ∀ m n : ℤ, N ≤ m → N ≤ n →
      IsSquare ((x.eval (m : ℚ)-x.eval (n : ℚ))^2+
        D*(y.eval (m : ℚ)-y.eval (n : ℚ))^2)) :
    C (x.eval (b : ℚ)-x.eval (a : ℚ))*(y-C (y.eval (a : ℚ)))-
      C (y.eval (b : ℚ)-y.eval (a : ℚ))*(x-C (x.eval (a : ℚ)))=0 := by
  apply cross_zero_of_anchor_squares D _ _ (a : ℚ) hD hne
  · convert hint a b ha hb using 1 <;> ring
  · simp
  · simp
  · apply PolynomialSquareValues.isSquare_of_eventually_int_eval
    refine ⟨N,?_⟩
    intro n hn
    simpa only [sqNorm,eval_add,eval_mul,eval_pow,eval_C,eval_sub] using hint n a hn ha
  · apply PolynomialSquareValues.isSquare_of_eventually_int_eval
    refine ⟨N,?_⟩
    intro n hn
    simp only [sqNorm,eval_add,eval_mul,eval_pow,eval_C,eval_sub]
    convert hint n b hn hb using 1 <;> ring

lemma determinant_zero_of_fixed_line (x y : ℚ → ℚ) (a b c d : ℚ)
    (hab : a ≠ 0 ∨ b ≠ 0)
    (h : ∀ t, a*(y t-d)-b*(x t-c)=0) (s t u : ℚ) :
    (x t-x s)*(y u-y s)-(y t-y s)*(x u-x s)=0 := by
  rcases hab with ha | hb
  · have hh : a*((x t-x s)*(y u-y s)-(y t-y s)*(x u-x s))=0 := by
      linear_combination (x t-x s)*(h u-h s)-(x u-x s)*(h t-h s)
    exact (mul_eq_zero.mp hh).resolve_left ha
  · have hh : b*((x t-x s)*(y u-y s)-(y t-y s)*(x u-x s))=0 := by
      linear_combination (y t-y s)*(h u-h s)-(y u-y s)*(h t-h s)
    exact (mul_eq_zero.mp hh).resolve_left hb

/-- A single rational polynomial path whose values at every sufficiently
large integer have pairwise rational distances is collinear at ALL rational
parameter values. There is no degree bound. -/
theorem all_chords_collinear (D : ℚ) (hD : 0 < D) (x y : ℚ[X])
    (hint : ∃ N : ℤ, ∀ m n : ℤ, N ≤ m → N ≤ n →
      IsSquare ((x.eval (m : ℚ)-x.eval (n : ℚ))^2+
        D*(y.eval (m : ℚ)-y.eval (n : ℚ))^2)) (s t u : ℚ) :
    (x.eval t-x.eval s)*(y.eval u-y.eval s)-
      (y.eval t-y.eval s)*(x.eval u-x.eval s)=0 := by
  by_cases hc : x.natDegree=0 ∧ y.natDegree=0
  · rw [eq_C_of_natDegree_eq_zero hc.1,eq_C_of_natDegree_eq_zero hc.2]
    simp
  obtain ⟨N,hN⟩ := hint
  have hchoose : ∃ n : ℤ, N ≤ n ∧
      (x.eval (n : ℚ)-x.eval (N : ℚ) ≠ 0 ∨ y.eval (n : ℚ)-y.eval (N : ℚ) ≠ 0) := by
    by_cases hx : x.natDegree=0
    · have hy : y.natDegree ≠ 0 := fun h => hc ⟨hx,h⟩
      obtain ⟨n,hn,he⟩ := exists_different_tail_value y hy N
      exact ⟨n,hn,Or.inr (sub_ne_zero.mpr he)⟩
    · obtain ⟨n,hn,he⟩ := exists_different_tail_value x hx N
      exact ⟨n,hn,Or.inl (sub_ne_zero.mpr he)⟩
  obtain ⟨n,hn,hne⟩ := hchoose
  have hp := fixed_anchor_line D hD x y N N n le_rfl hn hne hN
  apply determinant_zero_of_fixed_line (fun t => x.eval t) (fun t => y.eval t)
    (x.eval (n : ℚ)-x.eval (N : ℚ)) (y.eval (n : ℚ)-y.eval (N : ℚ))
    (x.eval (N : ℚ)) (y.eval (N : ℚ)) hne _ s t u
  intro k
  have hk := congrArg (Polynomial.eval k) hp
  simpa only [eval_sub,eval_mul,eval_C,eval_zero] using hk

#print axioms cross_zero_of_anchor_squares
#print axioms all_chords_collinear
end
end Erdos213.PolynomialChordRigidity
