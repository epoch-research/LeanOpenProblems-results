import FormalConjecturesUtil
import Submission.ProductOrientation

/-! The radius/matching control really is in general position, but an edge
has irrational length. It is not an integral or rational-distance GP8. -/
open EuclideanGeometry
namespace Erdos213.ProductOrientationGeometry
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

private def px : Fin 8 → ℤ :=
  ![7151518,-7151518,-15369420,15369420,12211440,-12211440,-38649600,38649600]
private def py : Fin 8 → ℤ :=
  ![0,0,9134125,-9134125,9713088,-9713088,-5277720,5277720]
private def det3 {R : Type*} [CommRing R] (a b c d e f g h i : R) : R :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)
private def norm (i j : Fin 8) : ℤ := (px j-px i)^2+(py j-py i)^2
private def tri (i j k : Fin 8) : ℤ :=
  (px j-px i)*(py k-py i)-(py j-py i)*(px k-px i)
private def circ (i j k l : Fin 8) : ℤ :=
  det3 (px j-px i) (py j-py i) (norm i j)
    (px k-px i) (py k-py i) (norm i k)
    (px l-px i) (py l-py i) (norm i l)

noncomputable def point (i : Fin 8) : ℝ² := !₂[(px i : ℝ),(py i : ℝ)]

lemma normalization (i : Fin 8) :
    ((px i : ℚ)/7151518,(py i : ℚ)/7151518) =
      (![ (1,0),(-1,0),(-9570/4453,11375/8906),(9570/4453,-11375/8906),
        (83640/48983,6048/4453),(-83640/48983,-6048/4453),
        ((-9570/4453)*(83640/48983)-(11375/8906)*(6048/4453),
         (-9570/4453)*(6048/4453)+(11375/8906)*(83640/48983)),
        (-((-9570/4453)*(83640/48983)-(11375/8906)*(6048/4453)),
         -((-9570/4453)*(6048/4453)+(11375/8906)*(83640/48983)))] :
          Fin 8 → ℚ × ℚ) i := by
  fin_cases i <;> norm_num [px,py]

private lemma collinear_det_zero {a b c : ℝ²} (h : Collinear ℝ {a,b,c}) :
    (b 0-a 0)*(c 1-a 1)-(b 1-a 1)*(c 0-a 0)=0 := by
  obtain ⟨v,hv⟩ := (collinear_iff_of_mem (by simp : a ∈ ({a,b,c} : Set ℝ²))).mp h
  obtain ⟨r,hr⟩ := hv b (by simp)
  obtain ⟨s,hs⟩ := hv c (by simp)
  subst b c
  simp
  ring

private lemma dist_sq (a b : ℝ²) :
    dist a b^2=(a 0-b 0)^2+(a 1-b 1)^2 := by
  simp [EuclideanSpace.dist_sq_eq,Fin.sum_univ_two,Real.dist_eq]

private lemma cospherical_det_zero {a b c d : ℝ²} (h : Cospherical {a,b,c,d}) :
    det3 (b 0-a 0) (b 1-a 1) (dist a b^2)
      (c 0-a 0) (c 1-a 1) (dist a c^2)
      (d 0-a 0) (d 1-a 1) (dist a d^2)=0 := by
  obtain ⟨o,r,h⟩ := h
  have ha := congrArg (fun z : ℝ => z^2) (h a (by simp))
  have hb := congrArg (fun z : ℝ => z^2) (h b (by simp))
  have hc := congrArg (fun z : ℝ => z^2) (h c (by simp))
  have hd := congrArg (fun z : ℝ => z^2) (h d (by simp))
  simp only [dist_sq] at ha hb hc hd ⊢
  unfold det3
  linear_combination
    ((c 0-a 0)*(d 1-a 1)-(d 0-a 0)*(c 1-a 1))*(hb-ha)+
    ((d 0-a 0)*(b 1-a 1)-(b 0-a 0)*(d 1-a 1))*(hc-ha)+
    ((b 0-a 0)*(c 1-a 1)-(c 0-a 0)*(b 1-a 1))*(hd-ha)

private lemma all_triangles : ∀ i j k : Fin 8, i ≠ j → j ≠ k → i ≠ k → tri i j k ≠ 0 := by
  decide

private lemma all_circles : ∀ i j k l : Fin 8,
    i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l → circ i j k l ≠ 0 := by
  decide

lemma point_injective : Function.Injective point := by
  have hinj : Function.Injective px := by decide
  intro i j he
  apply hinj
  have h := congrArg (fun z : ℝ² => z 0) he
  change (px i : ℝ)=(px j : ℝ) at h
  exact_mod_cast h

lemma no_collinear (i j k : Fin 8) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ¬ Collinear ℝ {point i,point j,point k} := by
  intro h
  have he := collinear_det_zero h
  have he' : (tri i j k : ℝ)=0 := by
    simpa [tri,point] using he
  exact all_triangles i j k hij hjk hik (by exact_mod_cast he')

lemma point_dist_sq (i j : Fin 8) : dist (point i) (point j)^2=(norm i j : ℝ) := by
  rw [dist_sq]
  simp [point,norm]
  ring

lemma no_cospherical (i j k l : Fin 8)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ¬ Cospherical {point i,point j,point k,point l} := by
  intro h
  have he := cospherical_det_zero h
  simp only [point_dist_sq] at he
  have he' : (circ i j k l : ℝ)=0 := by
    simpa [circ,point,det3] using he
  exact all_circles i j k l hij hik hil hjk hjl hkl (by exact_mod_cast he')

/-- The control has eight points in genuine Euclidean general position.
No assertion about integral or rational distances is included here. -/
theorem general_position_control :
    (Set.range point).Finite ∧ (Set.range point).ncard=8 ∧
    NonTrilinear (Set.range point) ∧
    (∀ Q : Set ℝ², Q ⊆ Set.range point ∧ Q.ncard=4 → ¬ Cospherical Q) := by
  refine ⟨Set.finite_range _,?_,?_,?_⟩
  · rw [Set.ncard_range_of_injective point_injective]
    simp
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _ ⟨k,rfl⟩ hij hjk hik
    exact no_collinear i j k (fun he => hij (he ▸ rfl))
      (fun he => hjk (he ▸ rfl)) (fun he => hik (he ▸ rfl))
  · intro Q hQ hcos
    obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,hset⟩ := Set.ncard_eq_four.mp hQ.2
    subst Q
    obtain ⟨i,rfl⟩ := hQ.1 (by simp : a ∈ ({a,b,c,d} : Set ℝ²))
    obtain ⟨j,rfl⟩ := hQ.1 (by simp : b ∈ ({point i,b,c,d} : Set ℝ²))
    obtain ⟨k,rfl⟩ := hQ.1 (by simp : c ∈ ({point i,point j,c,d} : Set ℝ²))
    obtain ⟨l,rfl⟩ := hQ.1 (by simp : d ∈ ({point i,point j,point k,d} : Set ℝ²))
    exact no_cospherical i j k l
      (fun he => hab (he ▸ rfl)) (fun he => hac (he ▸ rfl))
      (fun he => had (he ▸ rfl)) (fun he => hbc (he ▸ rfl))
      (fun he => hbd (he ▸ rfl)) (fun he => hcd (he ▸ rfl)) hcos

/-- An actual irrational edge prevents this control from being a witness. -/
theorem irrational_edge :
    dist (point 0) (point 2) ∉ Set.range ((↑) : ℚ → ℝ) := by
  rintro ⟨r,hr⟩
  have hn : ¬ IsSquare ((norm 0 2 : ℤ) : ℚ) := by decide +kernel
  apply hn
  refine ⟨r,?_⟩
  have he := point_dist_sq 0 2
  rw [← hr] at he
  have he' : ((norm 0 2 : ℤ) : ℝ)=(r : ℝ)*(r : ℝ) := by nlinarith only [he]
  exact_mod_cast he'

#print axioms normalization
#print axioms general_position_control
#print axioms irrational_edge
end Erdos213.ProductOrientationGeometry
