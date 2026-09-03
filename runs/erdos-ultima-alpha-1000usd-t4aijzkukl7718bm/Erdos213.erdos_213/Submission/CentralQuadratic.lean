import FormalConjecturesUtil

/-! The general central-six quadratic seven-point metric construction.
This does not assert general position of the output and does not settle
Erdős 213. The six additional geometric conditions are audited separately. -/

namespace Erdos213.CentralQuadratic
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

/-- A complex number whose usual Euclidean norm is rational. -/
def RationalNorm (z : ℂ) : Prop := ‖z‖ ∈ Set.range ((↑) : ℚ → ℝ)

lemma RationalNorm.mul {z w : ℂ} (hz : RationalNorm z) (hw : RationalNorm w) :
    RationalNorm (z*w) := by
  obtain ⟨a,ha⟩ := hz
  obtain ⟨b,hb⟩ := hw
  exact ⟨a*b,by simp [ha,hb]⟩

lemma RationalNorm.int (a : ℤ) : RationalNorm (a : ℂ) := by
  refine ⟨(a.natAbs : ℚ),?_⟩
  simp

lemma RationalNorm.neg {z : ℂ} (hz : RationalNorm z) : RationalNorm (-z) := by
  simpa [RationalNorm] using hz

lemma RationalNorm.two_mul_iff (z : ℂ) : RationalNorm (2*z) ↔ RationalNorm z := by
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨r/2,?_⟩
    norm_num [norm_mul] at hr ⊢
    linarith
  · intro hz
    exact (RationalNorm.int 2).mul hz

/-- The nine complex factors whose norms are required by the construction. -/
def factors {R : Type*} [CommRing R] (u v w : R) : Fin 9 → R :=
  ![u,v,w,u+v,u-v,u+w,u-w,v+w,v-w]

/-- The seven output points. -/
def point {R : Type*} [CommRing R] (u v w : R) : Fin 7 → R :=
  ![0,u^2-v^2,u^2-w^2,(u+v)*(u+w),(u+v)*(u-w),(u-v)*(u+w),(u-v)*(u-w)]

private def coefficient : Fin 7 → Fin 7 → ℤ :=
  !![0,1,1,1,1,1,1;
     0,0,1,1,1,-1,-1;
     0,0,0,1,1,-1,-1;
     0,0,0,0,-2,-2,-2;
     0,0,0,0,0,-2,-2;
     0,0,0,0,0,0,-2;
     0,0,0,0,0,0,0]

private def leftFactor : Fin 7 → Fin 7 → Fin 9 :=
  !![0,4,6,3,3,4,4;
     0,0,8,3,3,4,4;
     0,0,0,5,6,5,6;
     0,0,0,0,2,1,0;
     0,0,0,0,0,0,1;
     0,0,0,0,0,0,2;
     0,0,0,0,0,0,0]

private def rightFactor : Fin 7 → Fin 7 → Fin 9 :=
  !![0,3,5,5,6,5,6;
     0,0,7,7,8,8,7;
     0,0,0,7,8,8,7;
     0,0,0,0,3,5,7;
     0,0,0,0,0,8,6;
     0,0,0,0,0,0,4;
     0,0,0,0,0,0,0]

/-- All 21 differences factor over the original nine linear forms. -/
lemma difference_factorization {R : Type*} [CommRing R] (u v w : R)
    (i j : Fin 7) (hij : i < j) :
    point u v w j-point u v w i =
      (coefficient i j : R)*factors u v w (leftFactor i j)*factors u v w (rightFactor i j) := by
  have h0 : factors u v w 0 = u := rfl
  have h1 : factors u v w 1 = v := rfl
  have h2 : factors u v w 2 = w := rfl
  have h3 : factors u v w 3 = u+v := rfl
  have h4 : factors u v w 4 = u-v := rfl
  have h5 : factors u v w 5 = u+w := rfl
  have h6 : factors u v w 6 = u-w := rfl
  have h7 : factors u v w 7 = v+w := rfl
  have h8 : factors u v w 8 = v-w := rfl
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals norm_num [point,coefficient,leftFactor,rightFactor,Matrix.cons_val_succ]
  all_goals simp only [h0,h1,h2,h3,h4,h5,h6,h7,h8]
  all_goals ring

private lemma coefficient_ne_zero : ∀ i j : Fin 7, i < j → coefficient i j ≠ 0 := by decide

lemma point_difference_rational (u v w : ℂ)
    (h : ∀ k, RationalNorm (factors u v w k)) (i j : Fin 7) (hij : i < j) :
    RationalNorm (point u v w j-point u v w i) := by
  rw [difference_factorization u v w i j hij]
  exact ((RationalNorm.int _).mul (h _)).mul (h _)

lemma point_rational_distances (u v w : ℂ)
    (h : ∀ k, RationalNorm (factors u v w k)) (i j : Fin 7) :
    dist (point u v w i) (point u v w j) ∈ Set.range ((↑) : ℚ → ℝ) := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [dist_comm,dist_eq_norm]
    exact point_difference_rational u v w h i j hij
  · exact ⟨0,by simp⟩
  · rw [dist_eq_norm]
    exact point_difference_rational u v w h j i hji

lemma point_difference_ne_zero {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (u v w : R) (h : ∀ k, factors u v w k ≠ 0)
    (i j : Fin 7) (hij : i < j) : point u v w j-point u v w i ≠ 0 := by
  rw [difference_factorization u v w i j hij]
  exact mul_ne_zero (mul_ne_zero (by exact_mod_cast coefficient_ne_zero i j hij) (h _)) (h _)

lemma point_injective {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (u v w : R) (h : ∀ k, factors u v w k ≠ 0) : Function.Injective (point u v w) := by
  intro i j he
  rcases lt_trichotomy i j with hij | heq | hji
  · exact False.elim (point_difference_ne_zero u v w h i j hij (sub_eq_zero.mpr he.symm))
  · exact heq
  · exact False.elim (point_difference_ne_zero u v w h j i hji (sub_eq_zero.mpr he))

/-- The central input, before applying the quadratic construction. -/
def source {R : Type*} [CommRing R] (u v w : R) : Fin 6 → R := ![u,-u,v,-v,w,-w]

/-- Distinctness of the six source points supplies every nonvanishing factor. -/
lemma source_factors_ne_zero {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (u v w : R) (h : Function.Injective (source u v w)) :
    ∀ k, factors u v w k ≠ 0 := by
  have hu : u ≠ 0 := by
    intro he
    have hh : source u v w 0 = source u v w 1 := by simp [source,he]
    have hn := congrArg Fin.val (h hh)
    norm_num at hn
  have hv : v ≠ 0 := by
    intro he
    have hh : source u v w 2 = source u v w 3 := by
      change v = -v
      simp [he]
    have hn := congrArg Fin.val (h hh)
    norm_num at hn
  have hw : w ≠ 0 := by
    intro he
    have hh : source u v w 4 = source u v w 5 := by
      change w = -w
      simp [he]
    have hn := congrArg Fin.val (h hh)
    norm_num at hn
  have huv : u-v ≠ 0 := by
    intro he
    have hh : source u v w 0 = source u v w 2 := sub_eq_zero.mp he
    have hn := congrArg Fin.val (h hh)
    norm_num at hn
  have hupv : u+v ≠ 0 := by
    intro he
    have hh : source u v w 0 = source u v w 3 := eq_neg_of_add_eq_zero_left he
    have hn := congrArg Fin.val (h hh)
    norm_num at hn
  have huw : u-w ≠ 0 := by
    intro he
    have hh : source u v w 0 = source u v w 4 := sub_eq_zero.mp he
    have hn := congrArg Fin.val (h hh)
    norm_num at hn
  have hupw : u+w ≠ 0 := by
    intro he
    have hh : source u v w 0 = source u v w 5 := eq_neg_of_add_eq_zero_left he
    have hn := congrArg Fin.val (h hh)
    norm_num at hn
  have hvw : v-w ≠ 0 := by
    intro he
    have hh : source u v w 2 = source u v w 4 := sub_eq_zero.mp he
    have hn := congrArg Fin.val (h hh)
    norm_num at hn
  have hvpw : v+w ≠ 0 := by
    intro he
    have hh : source u v w 2 = source u v w 5 := eq_neg_of_add_eq_zero_left he
    have hn := congrArg Fin.val (h hh)
    norm_num at hn
  intro k
  fin_cases k <;> first
    | simpa [factors] using hu
    | simpa [factors] using hv
    | simpa [factors] using hw
    | simpa [factors] using hupv
    | simpa [factors] using huv
    | simpa [factors] using hupw
    | simpa [factors] using huw
    | simpa [factors] using hvpw
    | simpa [factors] using hvw

/-- Rational distances on the central source give all nine rational norms. -/
lemma source_factors_rational (u v w : ℂ)
    (h : ∀ i j, dist (source u v w i) (source u v w j) ∈ Set.range ((↑) : ℚ → ℝ)) :
    ∀ k, RationalNorm (factors u v w k) := by
  have hu : RationalNorm u := by
    apply (RationalNorm.two_mul_iff u).mp
    have hh := h 0 1
    simpa [RationalNorm,source,dist_eq_norm,two_mul] using hh
  have hv : RationalNorm v := by
    apply (RationalNorm.two_mul_iff v).mp
    have hh := h 2 3
    change ‖v-(-v)‖ ∈ Set.range ((↑) : ℚ → ℝ) at hh
    simpa [RationalNorm,two_mul] using hh
  have hw : RationalNorm w := by
    apply (RationalNorm.two_mul_iff w).mp
    have hh := h 4 5
    change ‖w-(-w)‖ ∈ Set.range ((↑) : ℚ → ℝ) at hh
    simpa [RationalNorm,two_mul] using hh
  have huv : RationalNorm (u-v) := h 0 2
  have hupv : RationalNorm (u+v) := by
    have hh := h 0 3
    change ‖u-(-v)‖ ∈ Set.range ((↑) : ℚ → ℝ) at hh
    simpa [RationalNorm] using hh
  have huw : RationalNorm (u-w) := h 0 4
  have hupw : RationalNorm (u+w) := by
    have hh := h 0 5
    change ‖u-(-w)‖ ∈ Set.range ((↑) : ℚ → ℝ) at hh
    simpa [RationalNorm] using hh
  have hvw : RationalNorm (v-w) := h 2 4
  have hvpw : RationalNorm (v+w) := by
    have hh := h 2 5
    change ‖v-(-w)‖ ∈ Set.range ((↑) : ℚ → ℝ) at hh
    simpa [RationalNorm] using hh
  intro k
  fin_cases k <;> first
    | simpa [factors] using hu
    | simpa [factors] using hv
    | simpa [factors] using hw
    | simpa [factors] using hupv
    | simpa [factors] using huv
    | simpa [factors] using hupw
    | simpa [factors] using huw
    | simpa [factors] using hvpw
    | simpa [factors] using hvw

/-- The full metric/cardinality conclusion, with no general-position assertion. -/
theorem central_six_to_seven (u v w : ℂ)
    (hinj : Function.Injective (source u v w))
    (h : ∀ i j, dist (source u v w i) (source u v w j) ∈ Set.range ((↑) : ℚ → ℝ)) :
    (Set.range (point u v w)).Finite ∧ (Set.range (point u v w)).ncard=7 ∧
      (Set.range (point u v w)).Pairwise
        (fun p q => dist p q ∈ Set.range ((↑) : ℚ → ℝ)) := by
  refine ⟨Set.finite_range _,?_,?_⟩
  · rw [Set.ncard_range_of_injective (point_injective u v w (source_factors_ne_zero u v w hinj))]
    simp
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _
    exact point_rational_distances u v w (source_factors_rational u v w h) i j

#print axioms difference_factorization
#print axioms point_rational_distances
#print axioms point_injective
#print axioms source_factors_ne_zero
#print axioms source_factors_rational
#print axioms central_six_to_seven
end Erdos213.CentralQuadratic
