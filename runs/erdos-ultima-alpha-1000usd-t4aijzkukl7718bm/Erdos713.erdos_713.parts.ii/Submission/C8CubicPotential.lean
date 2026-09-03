import FormalConjecturesUtil
import Submission.C8GeneralQuadratic

/-! A construction diagnostic: every polynomial potential of total degree at most
three in the four-coordinate incidence ansatz admits an octagon over the rationals.
This is not a disproof of the rational-exponent conjecture. -/

open SimpleGraph
namespace Erdos713C8Quadratic

lemma octagon_of_mixed_difference (Q : ℚ → ℚ → ℚ) (a b t : ℚ) (ht : t ≠ 0)
    (hQ : Q (a+2) (b-t) - Q (a+1) (b-t) - Q (a+1) b + Q a b = 0) : Octagon Q := by
  let p : Fin 4 → Vertex :=
    ![(0, ![-b,0,0]), (-t, ![-a*t-b,-b*t,-t*Q a b]),
      (0, ![t-b,-t^2,t*(Q (a+1) (b-t)-Q a b)]),
      (-t, ![-(a+1)*t-b,-b*t,-t*Q (a+1) b])]
  let l : Fin 4 → Vertex :=
    ![(a, ![b,0,0]), (a+1, ![b-t,t^2,t*(Q a b-Q (a+1) (b-t))]),
      (a+2, ![b-t,t^2,t*(Q a b-Q (a+1) (b-t))]), (a+1, ![b,0,0])]
  refine ⟨p,l,?_,?_,?_,?_⟩
  · intro i j hij
    have hx := congrArg (fun v : Vertex => v.1) hij
    have hy := congrArg (fun v : Vertex => v.2 0) hij
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; apply ht; dsimp [p] at hx hy; linarith)
  · intro i j hij
    have ha := congrArg (fun v : Vertex => v.1) hij
    have hb := congrArg (fun v : Vertex => v.2 0) hij
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; apply ht; dsimp [l] at ha hb; linarith)
  · intro i
    fin_cases i <;> dsimp [Inc,p,l]
    all_goals refine ⟨?_,?_,?_⟩
    all_goals ring
  · intro i
    fin_cases i <;> dsimp [Inc,p,l]
    all_goals refine ⟨?_,?_,?_⟩
    all_goals solve | ring | linear_combination t*hQ

abbrev cubic (A B C D E F G H I J : ℚ) (a b : ℚ) : ℚ :=
  A*a^3+B*a^2*b+C*a*b^2+D*b^3+E*a^2+F*a*b+G*b^2+H*a+I*b+J

lemma cubic_mixed_difference (A B C D E F G H I J a b t : ℚ) :
    cubic A B C D E F G H I J (a+2) (b-t) -
      cubic A B C D E F G H I J (a+1) (b-t) -
      cubic A B C D E F G H I J (a+1) b +
      cubic A B C D E F G H I J a b =
    (6*A-2*B*t)*a+(2*B-2*C*t)*b+(6*A-3*B*t+C*t^2+2*E-F*t) := by
  dsimp [cubic]
  ring

lemma cubic_octagon_of_nonzero (A B C D E F G H I J : ℚ)
    (h : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) : Octagon (cubic A B C D E F G H I J) := by
  have ht : ∃ t : ℚ, t ≠ 0 ∧ (6*A-2*B*t ≠ 0 ∨ 2*B-2*C*t ≠ 0) := by
    by_cases hA : 6*A-2*B ≠ 0
    · exact ⟨1, by norm_num, Or.inl (by simpa using hA)⟩
    by_cases hB : 2*B-2*C ≠ 0
    · exact ⟨1, by norm_num, Or.inr (by simpa using hB)⟩
    refine ⟨2, by norm_num, Or.inl ?_⟩
    intro he
    push_neg at hA hB
    rcases h with h | h | h
    · apply h; linarith
    · apply h; linarith
    · apply h; linarith
  obtain ⟨t, ht, hL | hM⟩ := ht
  · apply octagon_of_mixed_difference (cubic A B C D E F G H I J)
      (-(6*A-3*B*t+C*t^2+2*E-F*t)/(6*A-2*B*t)) 0 t ht
    rw [cubic_mixed_difference]
    simp only [mul_zero, add_zero, mul_div_cancel₀ _ hL, neg_add_cancel]
  · apply octagon_of_mixed_difference (cubic A B C D E F G H I J)
      0 (-(6*A-3*B*t+C*t^2+2*E-F*t)/(2*B-2*C*t)) t ht
    rw [cubic_mixed_difference]
    simp only [mul_zero, zero_add, mul_div_cancel₀ _ hM, neg_add_cancel]

lemma cubic_octagon (A B C D E F G H I J : ℚ) :
    Octagon (cubic A B C D E F G H I J) := by
  by_cases h : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0
  · exact cubic_octagon_of_nonzero A B C D E F G H I J h
  push_neg at h
  rcases h with ⟨rfl,rfl,rfl⟩
  by_cases hD : D = 0
  · subst D
    have he : cubic 0 0 0 0 E F G H I J =
        (fun a b => E*a^2+F*a*b+G*b^2+H*a+I*b+J) := by
      funext a b
      simp [cubic]
    rw [he]
    exact quadratic_octagon E F G H I J
  apply shift_octagon 1 (Q := cubic D (3*D) (3*D) D (E+F+G) (F+2*G) G (H+I) I J)
  · intro a b
    dsimp [cubic]
    ring
  · exact cubic_octagon_of_nonzero _ _ _ _ _ _ _ _ _ _ (Or.inl hD)

lemma contains_cubic (A B C D E F G H I J : ℚ) :
    cycleGraph 8 ⊑ graph (cubic A B C D E F G H I J) :=
  contains_of_octagon (cubic_octagon A B C D E F G H I J)

#print axioms cubic_octagon
#print axioms contains_cubic
end Erdos713C8Quadratic
