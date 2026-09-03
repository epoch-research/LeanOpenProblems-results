import Submission.AxisGlobalRankObstruction

/-! The concrete geometric control attached to the complete normalized rank
obstruction. Its distances are integral, but it is NOT in general position. -/
namespace Erdos213.AxisRankGeometry
open EuclideanGeometry AxisRankObstruction AxisGlobalRankObstruction
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def point (i : Fin 8) : ℂ :=
  (points i 0 : ℂ)+(points i 1 : ℂ)*Complex.I

lemma distances_nonneg : ∀ i j : Fin 8, 0≤distances i j := by
  decide +kernel

lemma point_dist_sq (i j : Fin 8) :
    dist (point i) (point j)^2=(distances i j : ℝ)^2 := by
  rw [dist_eq_norm,← Complex.normSq_eq_norm_sq]
  simp only [point,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.intCast_re,Complex.intCast_im,Complex.I_re,Complex.I_im,
    mul_zero,mul_one,zero_add,add_zero,sub_zero]
  have hh := distances_correct i j
  simp only [pow_two] at hh ⊢
  exact_mod_cast hh

lemma point_dist (i j : Fin 8) : dist (point i) (point j)=(distances i j : ℝ) := by
  have h := point_dist_sq i j
  have hn : (0 : ℝ)≤distances i j := by exact_mod_cast distances_nonneg i j
  nlinarith [dist_nonneg (x := point i) (y := point j)]

lemma points_injective : Function.Injective points := by
  decide +kernel

lemma point_injective : Function.Injective point := by
  intro i j h
  have hx := congrArg Complex.re h
  have hy := congrArg Complex.im h
  simp only [point,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.intCast_re,Complex.intCast_im,Complex.I_re,Complex.I_im,
    mul_zero,mul_one,zero_add,add_zero,sub_zero] at hx hy
  apply points_injective
  funext k
  fin_cases k
  · exact_mod_cast hx
  · exact_mod_cast hy

/-- An actual eight-point integral-distance metric underlies the obstruction. -/
theorem integral_control : (Set.range point).Finite ∧ (Set.range point).ncard=8 ∧
    ∀ i j, dist (point i) (point j)∈Set.range ((↑) : ℤ → ℝ) := by
  refine ⟨Set.finite_range _,?_,?_⟩
  · rw [Set.ncard_range_of_injective point_injective]
    simp
  · intro i j
    exact ⟨distances i j,(point_dist i j).symm⟩

lemma first_three_collinear : Collinear ℝ ({point 0,point 1,point 2} : Set ℂ) := by
  rw [collinear_iff_of_mem (by simp : point 0∈({point 0,point 1,point 2} : Set ℂ))]
  refine ⟨1,?_⟩
  intro p hp
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0,by norm_num [point,points,Matrix.cons_val]⟩
  · exact ⟨952,by norm_num [point,points,Matrix.cons_val]⟩
  · refine ⟨1800,?_⟩
    have hx : points (2 : Fin 8) 0=1800 := by decide +kernel
    have hy : points (2 : Fin 8) 1=0 := by decide +kernel
    simp only [point,hx,hy]
    norm_num [points]

/-- The rank control cannot itself serve as a witness to Erdős 213. -/
theorem not_general_position : ¬NonTrilinear (Set.range point) := by
  intro h
  have h01 : point 0≠point 1 :=
    fun e => (show (0 : Fin 8)≠1 by decide) (point_injective e)
  have h12 : point 1≠point 2 :=
    fun e => (show (1 : Fin 8)≠2 by decide) (point_injective e)
  have h02 : point 0≠point 2 :=
    fun e => (show (0 : Fin 8)≠2 by decide) (point_injective e)
  exact h (Set.mem_range_self 0) (Set.mem_range_self 1) (Set.mem_range_self 2)
    h01 h12 h02 first_three_collinear

/-- The seven old finite vertices, followed by the new finite vertex.
The remaining index `Sum.inl 7` is infinity. -/
def finiteIndex : Fin 8 → Fin 8 ⊕ Fin 1 :=
  ![Sum.inl 0,Sum.inl 1,Sum.inl 2,Sum.inl 3,Sum.inl 4,Sum.inl 5,Sum.inl 6,Sum.inr 0]

lemma sign_sq (b : Bool) : (sign b : ℚ)^2=1 := by
  cases b <;> norm_num [sign]

/-- Every encoded finite matrix entry has the prescribed distance magnitude. -/
theorem encoded_lengths (s : Fin 21 → Bool) (t : Fin 7 → Bool) (i j : Fin 8) :
    (normalizedMatrix s t (finiteIndex i) (finiteIndex j))^2=(distances i j : ℚ)^2 := by
  fin_cases i <;> fin_cases j
  · change ((0 : ℤ) : ℚ)^2=(((0 : ℤ) : ℚ))^2
    norm_num
  · change ((952*sign (s 0) : ℤ) : ℚ)^2=(((952 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((1800*sign (s 1) : ℤ) : ℚ)^2=(((1800 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((3536*sign (s 2) : ℤ) : ℚ)^2=(((3536 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((960*sign (s 3) : ℤ) : ℚ)^2=(((960 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((1785*sign (s 4) : ℤ) : ℚ)^2=(((1785 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((6630*sign (s 5) : ℤ) : ℚ)^2=(((6630 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((952*sign (t 0) : ℤ) : ℚ)^2=(((952 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((-(952*sign (s 0)) : ℤ) : ℚ)^2=(((952 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((0 : ℤ) : ℚ)^2=(((0 : ℤ) : ℚ))^2
    norm_num
  · change ((848*sign (s 6) : ℤ) : ℚ)^2=(((848 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((2584*sign (s 7) : ℤ) : ℚ)^2=(((2584 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((1352*sign (s 8) : ℤ) : ℚ)^2=(((1352 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((2023*sign (s 9) : ℤ) : ℚ)^2=(((2023 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((6698*sign (s 10) : ℤ) : ℚ)^2=(((6698 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((1904*sign (t 1) : ℤ) : ℚ)^2=(((1904 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((-(1800*sign (s 1)) : ℤ) : ℚ)^2=(((1800 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((-(848*sign (s 6)) : ℤ) : ℚ)^2=(((848 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((0 : ℤ) : ℚ)^2=(((0 : ℤ) : ℚ))^2
    norm_num
  · change ((1736*sign (s 11) : ℤ) : ℚ)^2=(((1736 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((2040*sign (s 12) : ℤ) : ℚ)^2=(((2040 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((2535*sign (s 13) : ℤ) : ℚ)^2=(((2535 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((6870*sign (s 14) : ℤ) : ℚ)^2=(((6870 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((2752*sign (t 2) : ℤ) : ℚ)^2=(((2752 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((-(3536*sign (s 2)) : ℤ) : ℚ)^2=(((3536 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((-(2584*sign (s 7)) : ℤ) : ℚ)^2=(((2584 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((-(1736*sign (s 11)) : ℤ) : ℚ)^2=(((1736 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((0 : ℤ) : ℚ)^2=(((0 : ℤ) : ℚ))^2
    norm_num
  · change ((3664*sign (s 15) : ℤ) : ℚ)^2=(((3664 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((3961*sign (s 16) : ℤ) : ℚ)^2=(((3961 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((7514*sign (s 17) : ℤ) : ℚ)^2=(((7514 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((4488*sign (t 3) : ℤ) : ℚ)^2=(((4488 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((-(960*sign (s 3)) : ℤ) : ℚ)^2=(((960 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((-(1352*sign (s 8)) : ℤ) : ℚ)^2=(((1352 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((-(2040*sign (s 12)) : ℤ) : ℚ)^2=(((2040 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((-(3664*sign (s 15)) : ℤ) : ℚ)^2=(((3664 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((0 : ℤ) : ℚ)^2=(((0 : ℤ) : ℚ))^2
    norm_num
  · change ((825*sign (s 18) : ℤ) : ℚ)^2=(((825 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((5670*sign (s 19) : ℤ) : ℚ)^2=(((5670 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((1352*sign (t 4) : ℤ) : ℚ)^2=(((1352 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((-(1785*sign (s 4)) : ℤ) : ℚ)^2=(((1785 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((-(2023*sign (s 9)) : ℤ) : ℚ)^2=(((2023 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((-(2535*sign (s 13)) : ℤ) : ℚ)^2=(((2535 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((-(3961*sign (s 16)) : ℤ) : ℚ)^2=(((3961 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((-(825*sign (s 18)) : ℤ) : ℚ)^2=(((825 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((0 : ℤ) : ℚ)^2=(((0 : ℤ) : ℚ))^2
    norm_num
  · change ((4845*sign (s 20) : ℤ) : ℚ)^2=(((4845 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((2023*sign (t 5) : ℤ) : ℚ)^2=(((2023 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((-(6630*sign (s 5)) : ℤ) : ℚ)^2=(((6630 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((-(6698*sign (s 10)) : ℤ) : ℚ)^2=(((6698 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((-(6870*sign (s 14)) : ℤ) : ℚ)^2=(((6870 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((-(7514*sign (s 17)) : ℤ) : ℚ)^2=(((7514 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((-(5670*sign (s 19)) : ℤ) : ℚ)^2=(((5670 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((-(4845*sign (s 20)) : ℤ) : ℚ)^2=(((4845 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change ((0 : ℤ) : ℚ)^2=(((0 : ℤ) : ℚ))^2
    norm_num
  · change ((6698*sign (t 6) : ℤ) : ℚ)^2=(((6698 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change (-((952*sign (t 0) : ℤ) : ℚ))^2=(((952 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change (-((1904*sign (t 1) : ℤ) : ℚ))^2=(((1904 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change (-((2752*sign (t 2) : ℤ) : ℚ))^2=(((2752 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change (-((4488*sign (t 3) : ℤ) : ℚ))^2=(((4488 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change (-((1352*sign (t 4) : ℤ) : ℚ))^2=(((1352 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change (-((2023*sign (t 5) : ℤ) : ℚ))^2=(((2023 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change (-((6698*sign (t 6) : ℤ) : ℚ))^2=(((6698 : ℤ) : ℚ))^2
    simp [mul_pow,sign_sq]
  · change (0 : ℚ)^2=(((0 : ℤ) : ℚ))^2
    norm_num

/-- The finite-to-infinity entries are normalized to one, including the new vertex. -/
theorem encoded_infinity (s : Fin 21 → Bool) (t : Fin 7 → Bool) (i : Fin 8) :
    normalizedMatrix s t (finiteIndex i) (Sum.inl 7)=1 := by
  fin_cases i
  · change ((1 : ℤ) : ℚ)=1
    norm_num
  · change ((1 : ℤ) : ℚ)=1
    norm_num
  · change ((1 : ℤ) : ℚ)=1
    norm_num
  · change ((1 : ℤ) : ℚ)=1
    norm_num
  · change ((1 : ℤ) : ℚ)=1
    norm_num
  · change ((1 : ℤ) : ℚ)=1
    norm_num
  · change ((1 : ℤ) : ℚ)=1
    norm_num
  · change -(((-1 : ℤ) : ℚ))=1
    norm_num

/-- The full nine-by-nine encoding is alternating. -/
theorem encoded_alternating (s : Fin 21 → Bool) (t : Fin 7 → Bool)
    (i j : Fin 8 ⊕ Fin 1) :
    normalizedMatrix s t i j= -normalizedMatrix s t j i := by
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i <;> fin_cases j <;>
      simp [normalizedMatrix,KernelRankAugmentation.augmented,AxisBaseCompleteness.template]
  · simp [normalizedMatrix,KernelRankAugmentation.augmented]
  · simp [normalizedMatrix,KernelRankAugmentation.augmented]
  · simp [normalizedMatrix,KernelRankAugmentation.augmented]

/-- No choice of signs in the complete normalized augmented encoding has
rank at most six. This is not a negation of the general-position conjecture. -/
theorem no_rank_six_signing : ¬∃ s t, (normalizedMatrix s t).rank≤6 := by
  rintro ⟨s,t,h⟩
  exact (not_lt_of_ge h) (normalized_rank_gt_six s t)

#print axioms encoded_alternating
#print axioms encoded_lengths
#print axioms encoded_infinity
#print axioms integral_control
#print axioms not_general_position
#print axioms no_rank_six_signing
end Erdos213.AxisRankGeometry
