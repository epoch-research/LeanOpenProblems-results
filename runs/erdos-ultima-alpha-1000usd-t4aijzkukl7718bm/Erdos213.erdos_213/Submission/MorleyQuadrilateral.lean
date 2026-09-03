import FormalConjecturesUtil

/-! A two-square criterion and an exceptional rational Morley parameter.
This proves a four-point positive control, not the unrestricted conjecture. -/
open EuclideanGeometry
namespace Erdos213.MorleyQuadrilateral
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def IntegralGP (n : ℕ) : Prop := ∃ S : Set ℝ², S.Finite ∧ S.ncard=n ∧
  NonTrilinear S ∧
  (∀ Q : Set ℝ², Q ⊆ S ∧ Q.ncard=4 → ¬ Cospherical Q) ∧
  (S.Pairwise fun a b => dist a b ∈ Set.range Int.cast)

private lemma collinear_det_zero {a b c : ℝ²} (h : Collinear ℝ {a, b, c}) :
    (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) = 0 := by
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (by simp : a ∈ ({a,b,c} : Set ℝ²))).mp h
  obtain ⟨r, hr⟩ := hv b (by simp)
  obtain ⟨s, hs⟩ := hv c (by simp)
  subst b c
  simp
  ring

private lemma p4_dist_sq (a b : ℝ²) :
    dist a b ^ 2 = (a 0 - b 0)^2 + (a 1 - b 1)^2 := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq]

private def det3 {R : Type*} [CommRing R] (a b c d e f g h i : R) : R :=
  a*(e*i-f*h) - b*(d*i-f*g) + c*(d*h-e*g)

private noncomputable def latticePoint (D : ℕ) (x y : ℤ) : ℝ² := !₂[(x : ℝ), (y : ℝ)*Real.sqrt D]

private def latticeNorm (D : ℕ) (x y x' y' : ℤ) : ℤ :=
  (x-x')^2 + (D : ℤ)*(y-y')^2

private def latticeTriangle (x y : Fin n → ℤ) (i j k : Fin n) : ℤ :=
  (x j-x i)*(y k-y i) - (y j-y i)*(x k-x i)

private def latticeCircle (D : ℕ) (x y : Fin n → ℤ) (i j k l : Fin n) : ℤ :=
  det3 (x j-x i) (y j-y i) (latticeNorm D (x i) (y i) (x j) (y j))
    (x k-x i) (y k-y i) (latticeNorm D (x i) (y i) (x k) (y k))
    (x l-x i) (y l-y i) (latticeNorm D (x i) (y i) (x l) (y l))

private lemma latticePoint_dist_sq (D : ℕ) (x y x' y' : ℤ) :
    dist (latticePoint D x y) (latticePoint D x' y')^2 = (latticeNorm D x y x' y' : ℝ) := by
  rw [p4_dist_sq]
  simp only [latticePoint, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    latticeNorm]
  push_cast
  linear_combination ((y : ℝ)-y')^2 * (Real.sq_sqrt (show 0 ≤ (D : ℝ) by positivity))

private lemma lattice_not_collinear {D : ℕ} (hD : 0 < D) {x y : Fin n → ℤ}
    {i j k : Fin n} (ht : latticeTriangle x y i j k ≠ 0) :
    ¬Collinear ℝ {latticePoint D (x i) (y i), latticePoint D (x j) (y j),
      latticePoint D (x k) (y k)} := by
  intro h
  have hz := collinear_det_zero h
  have hz' : (latticeTriangle x y i j k : ℝ) * Real.sqrt D = 0 := by
    convert hz using 1
    simp [latticePoint, latticeTriangle]
    ring
  have hn : (latticeTriangle x y i j k : ℝ) ≠ 0 := by exact_mod_cast ht
  exact (mul_ne_zero hn (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hD))) hz'

private lemma cospherical_det_zero {a b c d : ℝ²} (h : Cospherical {a,b,c,d}) :
    det3 (b 0-a 0) (b 1-a 1) (dist a b^2)
      (c 0-a 0) (c 1-a 1) (dist a c^2)
      (d 0-a 0) (d 1-a 1) (dist a d^2) = 0 := by
  obtain ⟨o,r,h⟩ := h
  have ha := congrArg (fun z : ℝ => z^2) (h a (by simp))
  have hb := congrArg (fun z : ℝ => z^2) (h b (by simp))
  have hc := congrArg (fun z : ℝ => z^2) (h c (by simp))
  have hd := congrArg (fun z : ℝ => z^2) (h d (by simp))
  simp only [p4_dist_sq] at ha hb hc hd ⊢
  unfold det3
  linear_combination
    ((c 0-a 0)*(d 1-a 1)-(d 0-a 0)*(c 1-a 1)) * (hb-ha) +
    ((d 0-a 0)*(b 1-a 1)-(b 0-a 0)*(d 1-a 1)) * (hc-ha) +
    ((b 0-a 0)*(c 1-a 1)-(c 0-a 0)*(b 1-a 1)) * (hd-ha)

private lemma lattice_not_cospherical {D : ℕ} (hD : 0 < D) {x y : Fin n → ℤ}
    {i j k l : Fin n} (ht : latticeCircle D x y i j k l ≠ 0) :
    ¬Cospherical {latticePoint D (x i) (y i), latticePoint D (x j) (y j),
      latticePoint D (x k) (y k), latticePoint D (x l) (y l)} := by
  intro h
  have hz := cospherical_det_zero h
  simp only [latticePoint_dist_sq] at hz
  have hz' : (latticeCircle D x y i j k l : ℝ) * Real.sqrt D = 0 := by
    convert hz using 1
    simp [latticePoint, latticeCircle, det3]
    ring
  have hn : (latticeCircle D x y i j k l : ℝ) ≠ 0 := by exact_mod_cast ht
  exact (mul_ne_zero hn (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hD))) hz'

private lemma integral_configuration_certificate (D n : ℕ) (hD : 0 < D)
    (x y : Fin n → ℤ) (d : Fin n → Fin n → ℕ)
    (hinj : Function.Injective x)
    (htri : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → latticeTriangle x y i j k ≠ 0)
    (hcirc : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      latticeCircle D x y i j k l ≠ 0)
    (hdist : ∀ i j, latticeNorm D (x i) (y i) (x j) (y j) = (d i j : ℤ)^2) :
    IntegralGP n := by
  let p : Fin n → ℝ² := fun i => latticePoint D (x i) (y i)
  have hp : Function.Injective p := by
    intro i j hij
    apply hinj
    have he := congrArg (fun z : ℝ² => z 0) hij
    change (x i : ℝ) = (x j : ℝ) at he
    exact_mod_cast he
  refine ⟨Set.range p, Set.finite_range _, ?_, ?_, ?_, ?_⟩
  · rw [Set.ncard_range_of_injective hp]
    simp
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _ ⟨k,rfl⟩ hij hjk hik
    exact lattice_not_collinear hD (htri i j k (fun he => hij (he ▸ rfl))
      (fun he => hjk (he ▸ rfl)) (fun he => hik (he ▸ rfl)))
  · intro Q hQ hcos
    obtain ⟨a,b,c,e,hab,hac,hae,hbc,hbe,hce,hset⟩ := Set.ncard_eq_four.mp hQ.2
    subst Q
    obtain ⟨i,rfl⟩ := hQ.1 (by simp : a ∈ ({a,b,c,e} : Set ℝ²))
    obtain ⟨j,rfl⟩ := hQ.1 (by simp : b ∈ ({p i,b,c,e} : Set ℝ²))
    obtain ⟨k,rfl⟩ := hQ.1 (by simp : c ∈ ({p i,p j,c,e} : Set ℝ²))
    obtain ⟨l,rfl⟩ := hQ.1 (by simp : e ∈ ({p i,p j,p k,e} : Set ℝ²))
    exact lattice_not_cospherical hD (hcirc i j k l
      (fun he => hab (he ▸ rfl)) (fun he => hac (he ▸ rfl))
      (fun he => hae (he ▸ rfl)) (fun he => hbc (he ▸ rfl))
      (fun he => hbe (he ▸ rfl)) (fun he => hce (he ▸ rfl))) hcos
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _
    refine ⟨(d i j : ℤ), ?_⟩
    have he := latticePoint_dist_sq D (x i) (y i) (x j) (y j)
    rw [hdist] at he
    push_cast at he ⊢
    change (d i j : ℝ) = dist (latticePoint D (x i) (y i)) (latticePoint D (x j) (y j))
    nlinarith [dist_nonneg (x := latticePoint D (x i) (y i)) (y := latticePoint D (x j) (y j)),
      Nat.cast_nonneg (α := ℝ) (d i j)]


abbrev QPoint := ℚ × ℚ
def quad (k : ℚ) : Fin 4 → QPoint :=
  ![(-1,0),(1,0),((k^2+3)/(6*(k+1)),-(k-1)*(k+3)/(6*(k+1))),(0,1/k)]
lemma quad0 (k : ℚ) : quad k 0 = (-1,0) := rfl
lemma quad1 (k : ℚ) : quad k 1 = (1,0) := rfl
lemma quad2 (k : ℚ) : quad k 2 = ((k^2+3)/(6*(k+1)),-(k-1)*(k+3)/(6*(k+1))) := rfl
lemma quad3 (k : ℚ) : quad k 3 = (0,1/k) := rfl

def normSq (p q : QPoint) : ℚ := (p.1-q.1)^2+3*(p.2-q.2)^2
noncomputable def embed (p : QPoint) : ℝ² := !₂[(p.1 : ℝ),(p.2 : ℝ)*Real.sqrt 3]

lemma embed_dist_sq (p q : QPoint) : dist (embed p) (embed q)^2 = (normSq p q : ℝ) := by
  rw [p4_dist_sq]
  simp only [embed,PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,normSq]
  push_cast
  linear_combination ((p.2 : ℝ)-q.2)^2 * (Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num))

lemma rational_distance_iff (p q : QPoint) :
    dist (embed p) (embed q) ∈ Set.range ((↑) : ℚ → ℝ) ↔ IsSquare (normSq p q) := by
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨r,?_⟩
    have h := embed_dist_sq p q
    rw [← hr] at h
    exact_mod_cast (by nlinarith [h] : (normSq p q : ℝ) = (r : ℝ)*(r : ℝ))
  · rintro ⟨r,hr⟩
    refine ⟨|r|,?_⟩
    rw [Rat.cast_abs]
    have h := embed_dist_sq p q
    have hh : (normSq p q : ℝ) = (r : ℝ)*(r : ℝ) := by exact_mod_cast hr
    nlinarith [h,hh,abs_nonneg (r : ℝ),sq_abs (r : ℝ),dist_nonneg (x := embed p) (y := embed q)]

def condition (k : ℚ) : Fin 3 → ℚ := ![1,k^2+3,k^2+3*k+3]
private def factorIndex : Fin 4 → Fin 4 → Fin 3 :=
  !![0,0,1,1;0,0,0,1;1,0,0,2;1,1,2,0]
private def coefficient (k : ℚ) : Fin 4 → Fin 4 → ℚ :=
  !![0,2,(k+3)/(3*(k+1)),1/k;
     2,0,(k^2+3)/(3*(k+1)),1/k;
     (k+3)/(3*(k+1)),(k^2+3)/(3*(k+1)),0,(k^2+3)/(3*k*(k+1));
     1/k,1/k,(k^2+3)/(3*k*(k+1)),0]

lemma norm_factorization (k : ℚ) (hk : k ≠ 0) (hk1 : k+1 ≠ 0) (i j : Fin 4) :
    normSq (quad k i) (quad k j) = (coefficient k i j)^2 * condition k (factorIndex i j) := by
  have h0 : condition k 0 = 1 := rfl
  have h1 : condition k 1 = k^2+3 := rfl
  have h2 : condition k 2 = k^2+3*k+3 := rfl
  fin_cases i <;> fin_cases j
  all_goals norm_num [quad,normSq,coefficient,factorIndex,Matrix.cons_val_succ,Matrix.cons_val_succ']
  all_goals simp only [h0,h1,h2]
  all_goals field_simp
  all_goals ring

private lemma strip_square_factor (a f : ℚ) (ha : a ≠ 0) (h : IsSquare (a^2*f)) : IsSquare f := by
  have hh := h.div (IsSquare.sq a)
  simpa only [mul_div_cancel_left₀ _ (pow_ne_zero 2 ha)] using hh

/-- All six distances are rational exactly when these two quadratic values are squares. -/
lemma metric_iff (k : ℚ) (hk : k ≠ 0) (hk1 : k+1 ≠ 0) :
    (∀ i j : Fin 4, dist (embed (quad k i)) (embed (quad k j)) ∈ Set.range ((↑) : ℚ → ℝ)) ↔
      IsSquare (k^2+3) ∧ IsSquare (k^2+3*k+3) := by
  constructor
  · intro h
    have h03 := (rational_distance_iff _ _).mp (h 0 3)
    rw [norm_factorization k hk hk1] at h03
    change IsSquare ((1/k)^2*(k^2+3)) at h03
    have h23 := (rational_distance_iff _ _).mp (h 2 3)
    rw [norm_factorization k hk hk1] at h23
    change IsSquare (((k^2+3)/(3*k*(k+1)))^2*(k^2+3*k+3)) at h23
    refine ⟨strip_square_factor _ _ (one_div_ne_zero hk) h03,?_⟩
    apply strip_square_factor _ _ _ h23
    apply div_ne_zero
    · nlinarith [sq_nonneg k]
    · exact mul_ne_zero (mul_ne_zero (by norm_num) hk) hk1
  · rintro ⟨hF,hG⟩ i j
    apply (rational_distance_iff _ _).mpr
    rw [norm_factorization k hk hk1]
    apply (IsSquare.sq _).mul
    have hc : ∀ l : Fin 3, IsSquare (condition k l) := by
      intro l
      fin_cases l
      · exact ⟨1,by norm_num [condition]⟩
      · exact hF
      · exact hG
    exact hc _

def triangle (a b c : QPoint) : ℚ := (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1)
def circle (a b c d : QPoint) : ℚ :=
  det3 (b.1-a.1) (b.2-a.2) (normSq a b)
    (c.1-a.1) (c.2-a.2) (normSq a c) (d.1-a.1) (d.2-a.2) (normSq a d)

lemma determinant_formulas (k : ℚ) (hk : k ≠ 0) (hk1 : k+1 ≠ 0) :
    triangle (quad k 0) (quad k 1) (quad k 2) = -(k-1)*(k+3)/(3*(k+1)) ∧
    triangle (quad k 0) (quad k 1) (quad k 3) = 2/k ∧
    triangle (quad k 0) (quad k 2) (quad k 3) = (k+3)*(k^2+3)/(6*k*(k+1)) ∧
    triangle (quad k 1) (quad k 2) (quad k 3) = -(k^2+3)/(6*k) ∧
    circle (quad k 0) (quad k 1) (quad k 2) (quad k 3) =
      (k+3)*(k^2+3)^2/(9*k^2*(k+1)^2) := by
  repeat' constructor
  all_goals simp only [quad0,quad1,quad2,quad3]
  all_goals dsimp [triangle,circle,det3,normSq]
  all_goals field_simp
  all_goals ring

def quartic (t : ℚ) : ℚ := t^4-2*t^3+2/3*t^2+2/3*t+1/9
def parameter (t : ℚ) : ℚ := (1-3*t^2)/(2*t)

lemma parameter_identities (t : ℚ) (ht : t ≠ 0) :
    (parameter t)^2+3 = ((1+3*t^2)/(2*t))^2 ∧
    (parameter t)^2+3*parameter t+3 = (3/(2*t))^2*quartic t := by
  constructor <;> dsimp [parameter,quartic] <;> field_simp <;> ring

lemma quartic_to_squares (t : ℚ) (ht : t ≠ 0) (h : IsSquare (quartic t)) :
    IsSquare ((parameter t)^2+3) ∧ IsSquare ((parameter t)^2+3*parameter t+3) := by
  rw [(parameter_identities t ht).1,(parameter_identities t ht).2]
  exact ⟨IsSquare.sq _,(IsSquare.sq _).mul h⟩

lemma tangent_identity (t : ℚ) :
    (1/3+t-t^2/2)^2-quartic t = t^3*(1-3*t/4) := by
  unfold quartic
  ring

lemma exceptional_parameter : parameter (4/3) = -13/8 ∧ IsSquare (quartic (4/3)) := by
  constructor
  · norm_num [parameter]
  · exact ⟨7/9,by norm_num [quartic]⟩

private def X : Fin 4 → ℤ := ![-3120,3120,-4693,0]
private def Y : Fin 4 → ℤ := ![0,0,-3003,-1920]
private def lengths : Fin 4 → Fin 4 → ℕ :=
  !![0,6240,5434,4560;6240,0,9386,4560;5434,9386,0,5054;4560,4560,5054,0]

lemma scaled_quad_coordinates (i : Fin 4) :
    ((X i : ℚ),(Y i : ℚ)) = (3120*(quad (-13/8) i).1,3120*(quad (-13/8) i).2) := by
  fin_cases i <;> norm_num [X,Y,quad,Matrix.cons_val_succ,Matrix.cons_val_succ']

/-- The exceptional square condition gives an actual integral GP quadrilateral. -/
lemma exceptional_integral_configuration : IntegralGP 4 := by
  apply integral_configuration_certificate 3 4 (by norm_num) X Y lengths
  · decide
  · decide
  · decide
  · decide

#print axioms metric_iff
#print axioms determinant_formulas
#print axioms quartic_to_squares
#print axioms tangent_identity
#print axioms exceptional_parameter
#print axioms scaled_quad_coordinates
#print axioms exceptional_integral_configuration
end Erdos213.MorleyQuadrilateral
