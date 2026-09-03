import FormalConjecturesUtil

/-! Exact metric reduction for a central Pascal nine-point candidate.
No arithmetic parameter satisfying all nine square conditions is asserted,
and no general-position conclusion or settlement of Erdős 213 is claimed. -/
open EuclideanGeometry
namespace Erdos213.HyperbolaPascal
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
abbrev QPoint := ℚ × ℚ

def normSq (N : ℚ) (p q : QPoint) : ℚ := (p.1-q.1)^2+N*(p.2-q.2)^2

def point (b c : ℚ) : Fin 9 → QPoint :=
  ![(1,1),(-1,-1),(b,1/b),(-b,-1/b),(c,1/c),(-c,-1/c),(0,0),
    ((b*c-b-2*c)/(c+1),-(2*b+c-1)/(b*(c+1))),
    (-(b*c-b-2*c)/(c+1),(2*b+c-1)/(b*(c+1)))]

/-- The six old and three new cleared norm conditions. -/
def condition (N b c : ℚ) : Fin 9 → ℚ :=
  ![1+N,b^2+N,c^2+N,b^4+N,b^2*c^2+N,c^4+N,
    b^2*(b*c-b-3*c-1)^2+N*(b*c+3*b+c-1)^2,
    b^2*c^2*(b*c-b-c^2-3*c)^2+N*(3*b*c+b+c^2-c)^2,
    b^2*(b*c-b-2*c)^2+N*(2*b+c-1)^2]

private def factorIndex : Fin 9 → Fin 9 → Fin 9 :=
  !![0,0,1,1,2,2,0,6,1;
     0,0,1,1,2,2,0,1,6;
     1,1,0,3,4,4,3,1,4;
     1,1,3,0,4,4,3,4,1;
     2,2,4,4,0,5,5,7,4;
     2,2,4,4,5,0,5,4,7;
     0,0,3,3,5,5,0,8,8;
     6,1,1,4,7,4,8,0,8;
     1,6,4,1,4,7,8,8,0]

private def coefficient (b c : ℚ) : Fin 9 → Fin 9 → ℚ :=
  !![0,2,(b - 1)/b,(b + 1)/b,(c - 1)/c,(c + 1)/c,1,1/(b*(c + 1)),(b - 1)*(c - 1)/(b*(c + 1));
     -2,0,-(b + 1)/b,-(b - 1)/b,-(c + 1)/c,-(c - 1)/c,-1,-(b - 1)*(c - 1)/(b*(c + 1)),-1/(b*(c + 1));
     -(b - 1)/b,(b + 1)/b,0,2/b,-(b - c)/(b*c),(b + c)/(b*c),1/b,2*(b + c)/(b*(c + 1)),-2*(b - 1)/(b*(c + 1));
     -(b + 1)/b,(b - 1)/b,-2/b,0,-(b + c)/(b*c),(b - c)/(b*c),-1/b,2*(b - 1)/(b*(c + 1)),-2*(b + c)/(b*(c + 1));
     -(c - 1)/c,(c + 1)/c,(b - c)/(b*c),(b + c)/(b*c),0,2/c,1/c,1/(b*c*(c + 1)),-(b + c)*(c - 1)/(b*c*(c + 1));
     -(c + 1)/c,(c - 1)/c,-(b + c)/(b*c),-(b - c)/(b*c),-2/c,0,-1/c,(b + c)*(c - 1)/(b*c*(c + 1)),-1/(b*c*(c + 1));
     -1,1,-1/b,1/b,-1/c,1/c,0,1/(b*(c + 1)),-1/(b*(c + 1));
     -1/(b*(c + 1)),(b - 1)*(c - 1)/(b*(c + 1)),-2*(b + c)/(b*(c + 1)),-2*(b - 1)/(b*(c + 1)),-1/(b*c*(c + 1)),-(b + c)*(c - 1)/(b*c*(c + 1)),-1/(b*(c + 1)),0,-2/(b*(c + 1));
     -(b - 1)*(c - 1)/(b*(c + 1)),1/(b*(c + 1)),2*(b - 1)/(b*(c + 1)),2*(b + c)/(b*(c + 1)),(b + c)*(c - 1)/(b*c*(c + 1)),1/(b*c*(c + 1)),1/(b*(c + 1)),2/(b*(c + 1)),0]

lemma norm_factorization (N b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0)
    (hc1 : c+1 ≠ 0) (i j : Fin 9) :
    normSq N (point b c i) (point b c j) =
      (coefficient b c i j)^2 * condition N b c (factorIndex i j) := by
  have h0 : condition N b c 0 = 1+N := by rfl
  have h1 : condition N b c 1 = b^2+N := by rfl
  have h2 : condition N b c 2 = c^2+N := by rfl
  have h3 : condition N b c 3 = b^4+N := by rfl
  have h4 : condition N b c 4 = b^2*c^2+N := by rfl
  have h5 : condition N b c 5 = c^4+N := by rfl
  have h6 : condition N b c 6 = b^2*(b*c-b-3*c-1)^2+N*(b*c+3*b+c-1)^2 := by rfl
  have h7 : condition N b c 7 = b^2*c^2*(b*c-b-c^2-3*c)^2+N*(3*b*c+b+c^2-c)^2 := by rfl
  have h8 : condition N b c 8 = b^2*(b*c-b-2*c)^2+N*(2*b+c-1)^2 := by rfl
  fin_cases i <;> fin_cases j
  all_goals norm_num [point,normSq,coefficient,factorIndex,Matrix.cons_val_succ,Matrix.cons_val_succ']
  all_goals simp only [h0,h1,h2,h3,h4,h5,h6,h7,h8]
  all_goals field_simp
  all_goals ring

lemma all_norms_square (N b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hc1 : c+1 ≠ 0)
    (h : ∀ k, IsSquare (condition N b c k)) (i j : Fin 9) :
    IsSquare (normSq N (point b c i) (point b c j)) := by
  rw [norm_factorization N b c hb hc hc1]
  exact (IsSquare.sq _).mul (h _)

private lemma square_of_nonzero_factor (r f : ℚ) (hr : r ≠ 0)
    (h : IsSquare (r^2*f)) : IsSquare f := by
  have hh := h.div (IsSquare.sq r)
  simpa only [mul_div_cancel_left₀ _ (pow_ne_zero 2 hr)] using hh

lemma all_conditions_square (N b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0)
    (hc1 : c+1 ≠ 0) (hb1 : b ≠ 1) (hc2 : c ≠ 1) (hbc : b ≠ c)
    (h : ∀ i j, IsSquare (normSq N (point b c i) (point b c j))) :
    ∀ k, IsSquare (condition N b c k) := by
  have hb' : b-1 ≠ 0 := sub_ne_zero.mpr hb1
  have hc' : c-1 ≠ 0 := sub_ne_zero.mpr hc2
  have hbc' : b-c ≠ 0 := sub_ne_zero.mpr hbc
  have e0 := h 0 6
  rw [norm_factorization N b c hb hc hc1] at e0
  change IsSquare ((1)^2 * condition N b c 0) at e0
  have q0 : IsSquare (condition N b c 0) := square_of_nonzero_factor _ _ (by
    norm_num) e0
  have e1 := h 0 2
  rw [norm_factorization N b c hb hc hc1] at e1
  change IsSquare (((b - 1)/b)^2 * condition N b c 1) at e1
  have q1 : IsSquare (condition N b c 1) := square_of_nonzero_factor _ _ (by
    apply_rules [div_ne_zero, mul_ne_zero, neg_ne_zero.mpr, hb, hc, hc1, hb', hc', hbc'] <;> norm_num) e1
  have e2 := h 0 4
  rw [norm_factorization N b c hb hc hc1] at e2
  change IsSquare (((c - 1)/c)^2 * condition N b c 2) at e2
  have q2 : IsSquare (condition N b c 2) := square_of_nonzero_factor _ _ (by
    apply_rules [div_ne_zero, mul_ne_zero, neg_ne_zero.mpr, hb, hc, hc1, hb', hc', hbc'] <;> norm_num) e2
  have e3 := h 2 6
  rw [norm_factorization N b c hb hc hc1] at e3
  change IsSquare ((1/b)^2 * condition N b c 3) at e3
  have q3 : IsSquare (condition N b c 3) := square_of_nonzero_factor _ _ (by
    apply_rules [div_ne_zero, mul_ne_zero, neg_ne_zero.mpr, hb, hc, hc1, hb', hc', hbc'] <;> norm_num) e3
  have e4 := h 2 4
  rw [norm_factorization N b c hb hc hc1] at e4
  change IsSquare ((-(b - c)/(b*c))^2 * condition N b c 4) at e4
  have q4 : IsSquare (condition N b c 4) := square_of_nonzero_factor _ _ (by
    apply_rules [div_ne_zero, mul_ne_zero, neg_ne_zero.mpr, hb, hc, hc1, hb', hc', hbc'] <;> norm_num) e4
  have e5 := h 4 6
  rw [norm_factorization N b c hb hc hc1] at e5
  change IsSquare ((1/c)^2 * condition N b c 5) at e5
  have q5 : IsSquare (condition N b c 5) := square_of_nonzero_factor _ _ (by
    apply_rules [div_ne_zero, mul_ne_zero, neg_ne_zero.mpr, hb, hc, hc1, hb', hc', hbc'] <;> norm_num) e5
  have e6 := h 0 7
  rw [norm_factorization N b c hb hc hc1] at e6
  change IsSquare ((1/(b*(c + 1)))^2 * condition N b c 6) at e6
  have q6 : IsSquare (condition N b c 6) := square_of_nonzero_factor _ _ (by
    apply_rules [div_ne_zero, mul_ne_zero, neg_ne_zero.mpr, hb, hc, hc1, hb', hc', hbc'] <;> norm_num) e6
  have e7 := h 4 7
  rw [norm_factorization N b c hb hc hc1] at e7
  change IsSquare ((1/(b*c*(c + 1)))^2 * condition N b c 7) at e7
  have q7 : IsSquare (condition N b c 7) := square_of_nonzero_factor _ _ (by
    apply_rules [div_ne_zero, mul_ne_zero, neg_ne_zero.mpr, hb, hc, hc1, hb', hc', hbc'] <;> norm_num) e7
  have e8 := h 6 7
  rw [norm_factorization N b c hb hc hc1] at e8
  change IsSquare ((1/(b*(c + 1)))^2 * condition N b c 8) at e8
  have q8 : IsSquare (condition N b c 8) := square_of_nonzero_factor _ _ (by
    apply_rules [div_ne_zero, mul_ne_zero, neg_ne_zero.mpr, hb, hc, hc1, hb', hc', hbc'] <;> norm_num) e8
  intro k
  fin_cases k <;> first
    | exact q0
    | exact q1
    | exact q2
    | exact q3
    | exact q4
    | exact q5
    | exact q6
    | exact q7
    | exact q8

lemma all_norms_square_iff (N b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0)
    (hc1 : c+1 ≠ 0) (hb1 : b ≠ 1) (hc2 : c ≠ 1) (hbc : b ≠ c) :
    (∀ i j, IsSquare (normSq N (point b c i) (point b c j))) ↔
      (∀ k, IsSquare (condition N b c k)) :=
  ⟨all_conditions_square N b c hb hc hc1 hb1 hc2 hbc,
    all_norms_square N b c hb hc hc1⟩

noncomputable def embed (N : ℚ) (p : QPoint) : ℝ² :=
  !₂[(p.1 : ℝ),(p.2 : ℝ)*Real.sqrt (N : ℝ)]

lemma embed_dist_sq (N : ℚ) (hN : 0 ≤ N) (p q : QPoint) :
    dist (embed N p) (embed N q)^2 = (normSq N p q : ℝ) := by
  have hn : 0 ≤ (N : ℝ) := by exact_mod_cast hN
  simp only [EuclideanSpace.dist_sq_eq,Fin.sum_univ_two,Real.dist_eq,embed,
    Matrix.cons_val_zero,Matrix.cons_val_one,normSq]
  push_cast
  rw [sq_abs,sq_abs]
  linear_combination ((p.2 : ℝ)-q.2)^2*(Real.sq_sqrt hn)

lemma rational_distance_iff (N : ℚ) (hN : 0 ≤ N) (p q : QPoint) :
    dist (embed N p) (embed N q) ∈ Set.range ((↑) : ℚ → ℝ) ↔
      IsSquare (normSq N p q) := by
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨r,?_⟩
    have hh := embed_dist_sq N hN p q
    rw [← hr] at hh
    apply Rat.cast_injective (α := ℝ)
    push_cast
    nlinarith only [hh]
  · rintro ⟨r,hr⟩
    refine ⟨|r|,?_⟩
    have hh := embed_dist_sq N hN p q
    rw [hr] at hh
    push_cast at hh
    rw [Rat.cast_abs]
    nlinarith [sq_abs (r : ℝ),abs_nonneg (r : ℝ),
      dist_nonneg (x := embed N p) (y := embed N q)]

/-- An exact nine-condition metric criterion, not a parameter-existence claim. -/
theorem nine_rational_iff (N b c : ℚ) (hN : 0 ≤ N) (hb : b ≠ 0) (hc : c ≠ 0)
    (hc1 : c+1 ≠ 0) (hb1 : b ≠ 1) (hc2 : c ≠ 1) (hbc : b ≠ c) :
    (∀ i j, dist (embed N (point b c i)) (embed N (point b c j))
      ∈ Set.range ((↑) : ℚ → ℝ)) ↔ (∀ k, IsSquare (condition N b c k)) := by
  simp only [rational_distance_iff N hN]
  exact all_norms_square_iff N b c hb hc hc1 hb1 hc2 hbc

/-- A positive metric control, but with repeated points. It is not a
nine-point witness: the extra point is an old hyperbola point. -/
lemma positive_degenerate_metric_control :
    (∀ k, IsSquare (condition (105/16) 2 (-2) k)) ∧
      point 2 (-2) 7 = point 2 (-2) 2 := by
  constructor
  · intro k
    fin_cases k <;> norm_num [condition,Matrix.cons_val_succ,Matrix.cons_val_succ']
  · change ((2*(-2)-2-2*(-2))/((-2)+1),-(2*2+(-2)-1)/(2*((-2)+1))) =
      ((2 : ℚ),1/2)
    norm_num

lemma pascal_chord_equations (b c : ℚ) (hb : b ≠ 0) (hc1 : c+1 ≠ 0) :
    (point b c 7).1-b*(point b c 7).2=b-1 ∧
    (point b c 7).1+b*c*(point b c 7).2=-b-c := by
  change (b*c-b-2*c)/(c+1)-b*(-(2*b+c-1)/(b*(c+1)))=b-1 ∧
    (b*c-b-2*c)/(c+1)+b*c*(-(2*b+c-1)/(b*(c+1)))=-b-c
  constructor <;> field_simp <;> ring

lemma central_triple_collinear (N b c : ℚ) :
    Collinear ℝ {embed N (point b c 6),embed N (point b c 0),embed N (point b c 1)} := by
  have hz : embed N (point b c 6) = 0 := by
    have hq : point b c 6 = ((0 : ℚ),0) := rfl
    simp [hq,embed]
  have hn : embed N (point b c 1) = -embed N (point b c 0) := by
    ext i
    fin_cases i <;> simp [embed,point]
  rw [hz,hn,collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨0,embed N (point b c 0),?_⟩
  rintro p (rfl | rfl | hp)
  · exact ⟨0,by simp⟩
  · exact ⟨1,by simp⟩
  · have hp' := Set.mem_singleton_iff.mp hp
    subst p
    exact ⟨-1,by simp⟩

/-- The nine-term candidate must be used as a weak source for inversion;
it is never itself a general-position set. -/
lemma nine_not_general_position (N b c : ℚ) :
    ¬NonTrilinear (Set.range (fun i => embed N (point b c i))) := by
  have hq6 : point b c 6 = ((0 : ℚ),0) := rfl
  have hq0 : point b c 0 = ((1 : ℚ),1) := rfl
  have hq1 : point b c 1 = ((-1 : ℚ),-1) := rfl
  intro h
  apply h ⟨6,rfl⟩ ⟨0,rfl⟩ ⟨1,rfl⟩ ?_ ?_ ?_ (central_triple_collinear N b c)
  all_goals intro he
  all_goals have hx := congrArg (fun p : ℝ² => p 0) he
  all_goals norm_num [embed,hq6,hq0,hq1] at hx

#print axioms positive_degenerate_metric_control
#print axioms pascal_chord_equations
#print axioms central_triple_collinear
#print axioms nine_not_general_position

#print axioms norm_factorization
#print axioms all_norms_square_iff
#print axioms embed_dist_sq
#print axioms rational_distance_iff
#print axioms nine_rational_iff
end Erdos213.HyperbolaPascal
