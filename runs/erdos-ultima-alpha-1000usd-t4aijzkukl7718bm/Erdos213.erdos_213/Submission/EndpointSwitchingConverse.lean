import Submission.EndpointSwitching

/-! Exact algebraic endpoint-switching criterion. The converse produces
abstract positive real endpoint weights, not an inversion center. -/
namespace Erdos213.EndpointSwitching

variable {ι : Type*}

/-- A common rational square class for triangle products suffices for abstract
positive real endpoint reweighting. It does not assert planar realization of
the resulting rational edge lengths. -/
theorem realWeightedRational_of_triangle_class (N : ι → ι → ℚ)
    (hsym : ∀ i j, N i j = N j i)
    (hpos : ∀ i j, i ≠ j → 0 < N i j)
    (a : ι) (T : ℚ) (hT : 0 < T)
    (hclass : ∀ i j, a ≠ i → a ≠ j → i ≠ j →
      IsSquare (N a i*N a j*N i j*T)) : RealWeightedRational N := by
  classical
  let v : ℝ := Real.sqrt (T : ℝ)
  have hv : 0 < v := Real.sqrt_pos.mpr (by exact_mod_cast hT)
  have hv0 : v ≠ 0 := ne_of_gt hv
  have hv2 : v^2 = (T : ℝ) := Real.sq_sqrt (by exact_mod_cast hT.le)
  let s : ι → ℝ := fun i => if i=a then v else 1/(v*(N a i : ℝ))
  refine ⟨s,?_,?_⟩
  · intro i
    by_cases hi : i=a
    · simpa [s,hi] using hv
    · have hn : (0 : ℝ) < N a i := by exact_mod_cast hpos a i (Ne.symm hi)
      simp only [s,if_neg hi]
      exact one_div_pos.mpr (mul_pos hv hn)
  · intro i j hij
    by_cases hi : i=a
    · subst i
      have hn : (N a j : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (hpos a j hij)
      refine ⟨1,?_⟩
      simp only [s,if_pos rfl,if_neg (Ne.symm hij),Rat.cast_one]
      field_simp
    by_cases hj : j=a
    · subst j
      have hn : (N a i : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (hpos a i (Ne.symm hij))
      refine ⟨1,?_⟩
      simp only [s,if_pos rfl,if_neg hi,Rat.cast_one]
      rw [hsym i a]
      field_simp
    · obtain ⟨r,hr⟩ := hclass i j (Ne.symm hi) (Ne.symm hj) hij
      have hni : (N a i : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (hpos a i (Ne.symm hi))
      have hnj : (N a j : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (hpos a j (Ne.symm hj))
      have ht0 : (T : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hT
      have hr' : (r : ℝ)^2 = (N a i : ℝ)*N a j*N i j*T := by
        exact_mod_cast (show r^2 = N a i*N a j*N i j*T by simpa only [pow_two] using hr.symm)
      refine ⟨r/(T*N a i*N a j),?_⟩
      simp only [s,if_neg hi,if_neg hj,Rat.cast_div,Rat.cast_mul]
      rw [div_pow,hr']
      field_simp
      rw [hv2]

/-- Necessary and sufficient criterion for abstract positive real weights.
Symmetry and positivity are explicit, as for squared distances of distinct
points. Geometric realizability of the weights is a separate problem. -/
theorem realWeightedRational_iff_triangle_class (N : ι → ι → ℚ)
    (hsym : ∀ i j, N i j = N j i)
    (hpos : ∀ i j, i ≠ j → 0 < N i j)
    {a b c : ι} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    RealWeightedRational N ↔
    ∀ i j, a ≠ i → a ≠ j → i ≠ j →
      IsSquare (N a i*N a j*N i j*(N a b*N a c*N b c)) := by
  constructor
  · intro h i j hai haj hij
    exact triangle_product_square N h hab hac hbc hai haj hij
      (fun u v huv => ne_of_gt (hpos u v huv))
  · intro h
    exact realWeightedRational_of_triangle_class N hsym hpos a
      (N a b*N a c*N b c)
      (mul_pos (mul_pos (hpos a b hab) (hpos a c hac)) (hpos b c hbc)) h

/-- Arbitrary endpoint reweighting need not preserve even the triangle
inequality. In particular, not every choice of weights comes from inversion. -/
lemma weighted_triangle_control :
    (∃ s : Fin 3 → ℚ, (∀ i, 0 < s i) ∧
      s 0*s 1=100^2 ∧ s 0*s 2=10^2 ∧ s 1*s 2=10^2) ∧
    ¬ ∃ p : Fin 3 → ℂ, dist (p 0) (p 1)=100 ∧
      dist (p 0) (p 2)=10 ∧ dist (p 1) (p 2)=10 := by
  constructor
  · let s : Fin 3 → ℚ := fun i => if i.val=2 then 1 else 100
    refine ⟨s,?_,by norm_num [s],by norm_num [s],by norm_num [s]⟩
    intro i
    dsimp [s]
    split_ifs <;> norm_num
  · rintro ⟨p,h01,h02,h12⟩
    have ht := dist_triangle (p 0) (p 2) (p 1)
    rw [h01,h02,dist_comm (p 2) (p 1),h12] at ht
    norm_num at ht

#print axioms realWeightedRational_of_triangle_class
#print axioms realWeightedRational_iff_triangle_class
#print axioms weighted_triangle_control

end Erdos213.EndpointSwitching
