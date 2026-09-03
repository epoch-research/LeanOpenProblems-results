import Submission.CircumcenterScale
import Submission.EndpointSwitching

/-! Four vertices and their four opposite triangle circumcenters.
Only four new square conditions are needed for all mixed distances to be
rational. Their simultaneous satisfaction and general position are not asserted. -/
namespace Erdos213.MixedCircumcenters
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
noncomputable section

abbrev V := ℚ × ℚ
def norm (u : V) : ℚ := u.1^2+u.2^2
def sqDist (a b : V) : ℚ := norm (a-b)
def det (u v : V) : ℚ := u.1*v.2-u.2*v.1
def area (a b c : V) : ℚ := det (b-a) (c-a)
def center (a b c : V) : V := a+
  ((norm (b-a)*(c-a).2-norm (c-a)*(b-a).2)/(2*area a b c),
   (norm (c-a)*(b-a).1-norm (b-a)*(c-a).1)/(2*area a b c))

lemma sqDist_comm (a b : V) : sqDist a b=sqDist b a := by
  dsimp [sqDist,norm]; ring
lemma sqDist_self (a : V) : sqDist a a=0 := by simp [sqDist,norm]
lemma sqDist_ne_zero {a b : V} (h : a≠b) : sqDist a b≠0 := by
  intro hz
  have hx : a.1=b.1 := by dsimp [sqDist,norm] at hz; nlinarith [sq_nonneg (a.2-b.2)]
  have hy : a.2=b.2 := by dsimp [sqDist,norm] at hz; nlinarith [sq_nonneg (a.1-b.1)]
  exact h (Prod.ext hx hy)

lemma center_incidence {a b c : V} (ha : area a b c≠0) :
    sqDist (center a b c) a=sqDist (center a b c) b ∧
    sqDist (center a b c) a=sqDist (center a b c) c := by
  constructor <;> dsimp [sqDist,norm,center]
  all_goals field_simp
  all_goals dsimp [area,det,norm]; ring

lemma center_radius {a b c : V} (ha : area a b c≠0) :
    sqDist (center a b c) a=
      sqDist a b*sqDist a c*sqDist b c/(2*area a b c)^2 := by
  dsimp [sqDist,norm,center]
  field_simp
  dsimp [area,det,norm]
  ring

lemma center_radius_square {a b c : V} (ha : area a b c≠0)
    (hab : IsSquare (sqDist a b)) (hac : IsSquare (sqDist a c))
    (hbc : IsSquare (sqDist b c)) : IsSquare (sqDist (center a b c) a) := by
  rw [center_radius ha]
  exact (hab.mul hac |>.mul hbc).div (IsSquare.sq _)

lemma shared_bisector_square {a b o p : V} (hab : a≠b)
    (hedge : IsSquare (sqDist a b))
    (ho : sqDist o a=sqDist o b) (hp : sqDist p a=sqDist p b) :
    IsSquare (sqDist o p) := by
  obtain ⟨r,hr⟩ := hedge
  have hr0 : r≠0 := by intro hz; apply sqDist_ne_zero hab; rw [hr,hz]; ring
  have hh := CircumcenterScale.shared_bisectors_isSquare 1 a.1 a.2 b.1 b.2
    o.1 o.2 p.1 p.2 r hr0
    (by dsimp [sqDist,norm] at hr; nlinarith only [hr])
    (by simpa [sqDist,norm] using ho)
    (by simpa [sqDist,norm] using hp)
  simpa [sqDist,norm] using hh

def opposite : Fin 4 → Fin 3 → Fin 4 :=
  !![1,2,3;0,2,3;0,1,3;0,1,2]
def centers (p : Fin 4 → V) (i : Fin 4) : V :=
  center (p (opposite i 0)) (p (opposite i 1)) (p (opposite i 2))
def Noncollinear (p : Fin 4 → V) : Prop :=
  ∀ i, area (p (opposite i 0)) (p (opposite i 1)) (p (opposite i 2))≠0

def mixed (p : Fin 4 → V) : (Fin 4 ⊕ Fin 4) → V := Sum.elim p (centers p)

lemma opposite_neq : ∀ i : Fin 4, ∀ j : Fin 3, opposite i j≠i := by decide
lemma opposite_mem : ∀ i j : Fin 4, j≠i → ∃ k : Fin 3, opposite i k=j := by decide
lemma shared_indices : ∀ i j : Fin 4, i≠j →
    ∃ k l : Fin 4, k≠l ∧ k≠i ∧ k≠j ∧ l≠i ∧ l≠j := by decide

lemma centers_incidence {p : Fin 4 → V} (h : Noncollinear p)
    (i : Fin 4) (j k : Fin 3) :
    sqDist (centers p i) (p (opposite i j))=sqDist (centers p i) (p (opposite i k)) := by
  obtain ⟨h01,h02⟩ := center_incidence (h i)
  change sqDist (centers p i) (p (opposite i 0))=sqDist (centers p i) (p (opposite i 1)) at h01
  change sqDist (centers p i) (p (opposite i 0))=sqDist (centers p i) (p (opposite i 2)) at h02
  fin_cases j <;> fin_cases k <;> first | rfl | exact h01 | exact h01.symm | exact h02 | exact h02.symm | exact h01.symm.trans h02 | exact h02.symm.trans h01

lemma centers_incidence_of_ne {p : Fin 4 → V} (h : Noncollinear p)
    {i j k : Fin 4} (hj : j≠i) (hk : k≠i) :
    sqDist (centers p i) (p j)=sqDist (centers p i) (p k) := by
  obtain ⟨a,rfl⟩ := opposite_mem i j hj
  obtain ⟨b,rfl⟩ := opposite_mem i k hk
  exact centers_incidence h i a b

lemma cross_square {p : Fin 4 → V} (h : Noncollinear p)
    (hsq : ∀ i j, IsSquare (sqDist (p i) (p j))) {i j : Fin 4} (hij : i≠j) :
    IsSquare (sqDist (p i) (centers p j)) := by
  rw [sqDist_comm,centers_incidence_of_ne h hij (opposite_neq j 0)]
  exact center_radius_square (h j) (hsq _ _) (hsq _ _) (hsq _ _)

lemma centers_square {p : Fin 4 → V} (h : Noncollinear p)
    (hinj : Function.Injective p) (hsq : ∀ i j, IsSquare (sqDist (p i) (p j)))
    (i j : Fin 4) : IsSquare (sqDist (centers p i) (centers p j)) := by
  by_cases hij : i=j
  · subst j; rw [sqDist_self]; exact IsSquare.zero
  · obtain ⟨k,l,hkl,hki,hkj,hli,hlj⟩ := shared_indices i j hij
    exact shared_bisector_square (fun hh => hkl (hinj hh)) (hsq k l)
      (centers_incidence_of_ne h hki hli) (centers_incidence_of_ne h hkj hlj)

/-- The original six square distances and just four opposite-center square
conditions are exactly the arithmetic conditions on the whole mixed octad. -/
theorem mixed_squares_iff {p : Fin 4 → V} (h : Noncollinear p) (hinj : Function.Injective p) :
    (∀ i j, IsSquare (sqDist (mixed p i) (mixed p j))) ↔
      (∀ i j, IsSquare (sqDist (p i) (p j))) ∧
      (∀ i, IsSquare (sqDist (p i) (centers p i))) := by
  constructor
  · intro H
    exact ⟨fun i j => H (Sum.inl i) (Sum.inl j),fun i => H (Sum.inl i) (Sum.inr i)⟩
  · rintro ⟨hsq,hop⟩ (i|i) (j|j)
    · exact hsq i j
    · by_cases hij : i=j
      · subst j; exact hop i
      · exact cross_square h hsq hij
    · rw [sqDist_comm]; by_cases hij : j=i
      · subst j; exact hop i
      · exact cross_square h hsq hij
    · exact centers_square h hinj hsq i j

def plane (p : V) : EuclideanSpace ℝ (Fin 2) := !₂[(p.1 : ℝ),(p.2 : ℝ)]

lemma plane_dist_sq (p q : V) : dist (plane p) (plane q)^2=(sqDist p q : ℝ) := by
  simp [EuclideanSpace.dist_sq_eq,Fin.sum_univ_two,Real.dist_eq,plane,sqDist,norm]

lemma plane_rational_iff (p q : V) :
    dist (plane p) (plane q)∈Set.range ((↑) : ℚ → ℝ) ↔ IsSquare (sqDist p q) := by
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨r,?_⟩
    have he := plane_dist_sq p q
    rw [← hr] at he
    exact_mod_cast (show (sqDist p q : ℝ)=(r : ℝ)*(r : ℝ) by nlinarith only [he])
  · rintro ⟨r,hr⟩
    refine ⟨|r|,?_⟩
    have he := plane_dist_sq p q
    rw [hr] at he
    push_cast at he ⊢
    apply (sq_eq_sq₀ (abs_nonneg _) dist_nonneg).mp
    rw [sq_abs]
    nlinarith only [he]

/-- The criterion concerns actual Euclidean distances, not merely a formal
quadratic form. The only unchecked cross pairs are the opposite pairs. -/
theorem mixed_rational_distances_iff {p : Fin 4 → V} (h : Noncollinear p)
    (hinj : Function.Injective p)
    (hsq : ∀ i j, IsSquare (sqDist (p i) (p j))) :
    (∀ i j, dist (plane (mixed p i)) (plane (mixed p j))∈Set.range ((↑) : ℚ → ℝ)) ↔
      ∀ i, IsSquare (sqDist (p i) (centers p i)) := by
  simp_rw [plane_rational_iff]
  rw [mixed_squares_iff h hinj]
  exact and_iff_right hsq

lemma plane_centers_incidence {p : Fin 4 → V} (h : Noncollinear p)
    {i j k : Fin 4} (hj : j≠i) (hk : k≠i) :
    dist (plane (centers p i)) (plane (p j))=dist (plane (centers p i)) (plane (p k)) := by
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [plane_dist_sq,plane_dist_sq,centers_incidence_of_ne h hj hk]

lemma opposite_injective : ∀ i : Fin 4, Function.Injective (opposite i) := by decide

/-- Arbitrary positive real endpoint weights do not repair any of the four
missing edges of a distinct mixed octad. This includes the factors induced
by inversions and common positive real dilations. -/
theorem mixed_weighted_iff {p : Fin 4 → V} (h : Noncollinear p)
    (hinj : Function.Injective (mixed p))
    (hsq : ∀ i j, IsSquare (sqDist (p i) (p j))) :
    EndpointSwitching.RealWeightedRational (fun i j => sqDist (mixed p i) (mixed p j)) ↔
      ∀ i, IsSquare (sqDist (p i) (centers p i)) := by
  have hsource : Function.Injective p := fun _ _ hh => Sum.inl.inj (hinj (show mixed p (Sum.inl _)=mixed p (Sum.inl _) from hh))
  constructor
  · intro H i
    let k := opposite i 0
    let l := opposite i 1
    have hkl : k≠l := fun he => (by decide : (0 : Fin 3)≠1) (opposite_injective i he)
    have hli : l≠i := opposite_neq i 1
    have hN : ∀ u v, u≠v → sqDist (mixed p u) (mixed p v)≠0 :=
      fun u v huv => sqDist_ne_zero (fun hh => huv (hinj hh))
    have hab : (Sum.inl i : Fin 4 ⊕ Fin 4)≠Sum.inr i := by simp
    have hbc : (Sum.inr i : Fin 4 ⊕ Fin 4)≠Sum.inl k := by simp
    have hcd : (Sum.inl k : Fin 4 ⊕ Fin 4)≠Sum.inl l := by simpa using hkl
    have hda : (Sum.inl l : Fin 4 ⊕ Fin 4)≠Sum.inl i := by simpa using hli
    have he := EndpointSwitching.four_edge_square
      (fun u v => sqDist (mixed p u) (mixed p v)) H hab hbc hcd hda
      (hN _ _ hbc) (hN _ _ hda)
    change IsSquare (sqDist (p i) (centers p i)*sqDist (p k) (p l)/
      (sqDist (centers p i) (p k)*sqDist (p l) (p i))) at he
    have hbcsq : IsSquare (sqDist (centers p i) (p k)) := by
      rw [sqDist_comm]
      exact cross_square h hsq (opposite_neq i 0)
    have hh := (he.mul (hbcsq.mul (hsq l i))).div (hsq k l)
    have hbc0 : sqDist (centers p i) (p k)≠0 := hN _ _ hbc
    have hda0 : sqDist (p l) (p i)≠0 := hN _ _ hda
    have hcd0 : sqDist (p k) (p l)≠0 := hN _ _ hcd
    rw [div_mul_cancel₀ _ (mul_ne_zero hbc0 hda0),mul_div_cancel_right₀ _ hcd0] at hh
    exact hh
  · intro hop
    have H := (mixed_squares_iff h hsource).mpr ⟨hsq,hop⟩
    refine ⟨fun _ => 1,fun _ => by norm_num,?_⟩
    intro i j _
    obtain ⟨r,hr⟩ := H i j
    refine ⟨r,?_⟩
    change (r : ℝ)^2=1*1*(sqDist (mixed p i) (mixed p j) : ℝ)
    rw [hr]
    push_cast
    ring

/-- An arbitrary off-set inversion center and positive real scale cannot
remove the four-square arithmetic burden. No rationality of center or scale
is assumed. -/
theorem opposite_squares_of_inverted_rational {p : Fin 4 → V} (h : Noncollinear p)
    (hinj : Function.Injective (mixed p))
    (hsq : ∀ i j, IsSquare (sqDist (p i) (p j)))
    (o : EuclideanSpace ℝ (Fin 2)) (ho : ∀ i, plane (mixed p i)≠o)
    (A : ℝ) (hA : 0<A)
    (hd : ∀ i j, i≠j → A*dist
      (EuclideanGeometry.inversion o 1 (plane (mixed p i)))
      (EuclideanGeometry.inversion o 1 (plane (mixed p j)))∈Set.range ((↑) : ℚ → ℝ)) :
    ∀ i, IsSquare (sqDist (p i) (centers p i)) := by
  apply (mixed_weighted_iff h hinj hsq).mp
  obtain ⟨l,hl,he⟩ := EndpointSwitching.weights_of_inverted_lengths
    (fun i => plane (mixed p i)) o ho A hA hd
  refine ⟨fun i => l i^2,fun i => sq_pos_of_pos (hl i),?_⟩
  intro i j hij
  obtain ⟨r,hr⟩ := he i j hij
  refine ⟨r,?_⟩
  rw [hr,mul_pow,mul_pow,plane_dist_sq]

#print axioms center_radius_square
#print axioms shared_bisector_square
#print axioms mixed_squares_iff
#print axioms mixed_rational_distances_iff
#print axioms plane_centers_incidence
#print axioms mixed_weighted_iff
#print axioms opposite_squares_of_inverted_rational
end
end Erdos213.MixedCircumcenters
