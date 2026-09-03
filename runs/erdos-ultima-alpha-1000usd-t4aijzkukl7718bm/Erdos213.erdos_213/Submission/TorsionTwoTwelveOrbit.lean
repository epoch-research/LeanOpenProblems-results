import Submission.TorsionTwoTwelveNorm
import FormalConjecturesUtil

/-! A metric obstruction for each four-point torsion orbit. It permits every
rational linear projection y+k*x and every common positive real dilation.
It does not classify arbitrary point configurations, or arbitrary endpoint weights. -/
namespace Erdos213.TorsionTwoTwelve
noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def quadraticPoint (D a b : ℚ) : ℂ :=
  (a : ℂ)+(b : ℂ)*(Real.sqrt (D : ℝ) : ℂ)*Complex.I

lemma quadraticPoint_dist_sq {D : ℚ} (hD : 0≤D) (a b c e : ℚ) :
    dist (quadraticPoint D a b) (quadraticPoint D c e)^2 =
      (((a-c)^2+D*(b-e)^2 : ℚ) : ℝ) := by
  rw [dist_eq_norm,Complex.sq_norm,Complex.normSq_apply]
  simp only [quadraticPoint,Complex.sub_re,Complex.sub_im,Complex.add_re,
    Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.ratCast_re,Complex.ratCast_im,Complex.I_re,Complex.I_im,
    mul_zero,mul_one,zero_mul,zero_add,add_zero,sub_zero,zero_sub]
  push_cast
  have hs := Real.sq_sqrt (show 0≤(D : ℝ) by exact_mod_cast hD)
  linear_combination ((b : ℝ)-e)^2*hs

/-- The four members Q, -Q, conjugate Q, -conjugate Q after projection y+k*x.
The rational coefficients a,b encode the x-coordinate of Q. -/
def projectedOrbit (v : ℚ) (i : Fin 3) (a b k : ℚ) : Fin 4 → ℂ :=
  ![quadraticPoint (characteristic v) (k*a+realPart v i) (k*b+imagCoeff v i),
    quadraticPoint (characteristic v) (k*a-realPart v i) (k*b-imagCoeff v i),
    quadraticPoint (characteristic v) (k*a+realPart v i) (-k*b-imagCoeff v i),
    quadraticPoint (characteristic v) (k*a-realPart v i) (-k*b+imagCoeff v i)]

lemma projected_norm_edges {v : ℚ} (hv : 1<v) (i : Fin 3) (a b k : ℚ) :
    dist (projectedOrbit v i a b k 0) (projectedOrbit v i a b k 1)^2 =
      ((4*ordinateNorm v i : ℚ) : ℝ) ∧
    dist (projectedOrbit v i a b k 2) (projectedOrbit v i a b k 3)^2 =
      ((4*ordinateNorm v i : ℚ) : ℝ) := by
  constructor
  · change dist (quadraticPoint (characteristic v) (k*a+realPart v i) (k*b+imagCoeff v i))
        (quadraticPoint (characteristic v) (k*a-realPart v i) (k*b-imagCoeff v i))^2 = _
    rw [quadraticPoint_dist_sq (characteristic_pos hv).le]
    dsimp [ordinateNorm]
    push_cast
    ring
  · change dist (quadraticPoint (characteristic v) (k*a+realPart v i) (-k*b-imagCoeff v i))
        (quadraticPoint (characteristic v) (k*a-realPart v i) (-k*b+imagCoeff v i))^2 = _
    rw [quadraticPoint_dist_sq (characteristic_pos hv).le]
    dsimp [ordinateNorm]
    push_cast
    ring

lemma projected_conjugate_edges {v : ℚ} (hv : 1<v) (i : Fin 3) (a b k : ℚ) :
    dist (projectedOrbit v i a b k 0) (projectedOrbit v i a b k 2)^2 =
      ((4*characteristic v*(k*b+imagCoeff v i)^2 : ℚ) : ℝ) ∧
    dist (projectedOrbit v i a b k 1) (projectedOrbit v i a b k 3)^2 =
      ((4*characteristic v*(k*b-imagCoeff v i)^2 : ℚ) : ℝ) := by
  constructor
  · change dist (quadraticPoint (characteristic v) (k*a+realPart v i) (k*b+imagCoeff v i))
        (quadraticPoint (characteristic v) (k*a+realPart v i) (-k*b-imagCoeff v i))^2 = _
    rw [quadraticPoint_dist_sq (characteristic_pos hv).le]
    push_cast
    ring
  · change dist (quadraticPoint (characteristic v) (k*a-realPart v i) (k*b-imagCoeff v i))
        (quadraticPoint (characteristic v) (k*a-realPart v i) (-k*b+imagCoeff v i))^2 = _
    rw [quadraticPoint_dist_sq (characteristic_pos hv).le]
    push_cast
    ring

lemma separated_scaled_lengths {v : ℚ} (hv : 1<v) (i : Fin 3)
    (L M scale : ℝ) (r : ℚ) (hscale : 0<scale) (hMpos : 0<M)
    (hL : L^2=((4*ordinateNorm v i : ℚ) : ℝ))
    (hM : M^2=((4*characteristic v*r^2 : ℚ) : ℝ))
    (hLrat : scale*L ∈ Set.range ((↑) : ℚ → ℝ))
    (hMrat : scale*M ∈ Set.range ((↑) : ℚ → ℝ)) : False := by
  obtain ⟨p,hp⟩ := hLrat
  obtain ⟨q,hq⟩ := hMrat
  have hq0 : q≠0 := by
    intro he
    have hz : (0 : ℝ)=scale*M := by simpa [he] using hq
    exact (ne_of_gt (mul_pos hscale hMpos)) hz.symm
  have heR : (ordinateNorm v i : ℝ)*(q : ℝ)^2 =
      (characteristic v : ℝ)*((p*r : ℚ) : ℝ)^2 := by
    push_cast at hL hM ⊢
    rw [hp,hq]
    linear_combination scale^2*((ordinateNorm v i : ℝ)*hM-
      (characteristic v : ℝ)*(r : ℝ)^2*hL)
  have he : ordinateNorm v i*q^2=characteristic v*(p*r)^2 := by
    exact_mod_cast heR
  exact norm_characteristic_separated hv i hq0 he

private lemma three_pair_types : ∀ i j k : Fin 4, i≠j → i≠k → j≠k →
    ((0∈({i,j,k} : Finset (Fin 4)) ∧ 1∈({i,j,k} : Finset (Fin 4))) ∨
     (2∈({i,j,k} : Finset (Fin 4)) ∧ 3∈({i,j,k} : Finset (Fin 4)))) ∧
    ((0∈({i,j,k} : Finset (Fin 4)) ∧ 2∈({i,j,k} : Finset (Fin 4))) ∨
     (1∈({i,j,k} : Finset (Fin 4)) ∧ 3∈({i,j,k} : Finset (Fin 4)))) := by
  decide +kernel

/-- At most two distinct projected points in a four-point orbit can have
pairwise rational distances after one common positive real dilation. -/
theorem projected_orbit_card_le_two {v : ℚ} (hv : 1<v) (i : Fin 3)
    (a b k : ℚ) (scale : ℝ) (hscale : 0<scale) (S : Finset (Fin 4))
    (hinj : Set.InjOn (projectedOrbit v i a b k) (S : Set (Fin 4)))
    (hrat : ∀ j∈S, ∀ l∈S, j≠l →
      scale*dist (projectedOrbit v i a b k j) (projectedOrbit v i a b k l) ∈
        Set.range ((↑) : ℚ → ℝ)) : S.card≤2 := by
  by_contra hcard
  obtain ⟨j,l,m,hj,hl,hm,hjl,hjm,hlm⟩ :=
    Finset.two_lt_card_iff.mp (show 2<S.card by omega)
  have hsub : ({j,l,m} : Finset (Fin 4)) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  obtain ⟨hN,hD⟩ := three_pair_types j l m hjl hjm hlm
  obtain ⟨r,s,hr,hs,hrs,hNorm⟩ : ∃ r s : Fin 4, r∈S ∧ s∈S ∧ r≠s ∧
      dist (projectedOrbit v i a b k r) (projectedOrbit v i a b k s)^2 =
        ((4*ordinateNorm v i : ℚ) : ℝ) := by
    rcases hN with ⟨h0,h1⟩ | ⟨h2,h3⟩
    · exact ⟨0,1,hsub h0,hsub h1,by decide,(projected_norm_edges hv i a b k).1⟩
    · exact ⟨2,3,hsub h2,hsub h3,by decide,(projected_norm_edges hv i a b k).2⟩
  obtain ⟨t,u,c,ht,hu,htu,hConj⟩ : ∃ t u : Fin 4, ∃ c : ℚ, t∈S ∧ u∈S ∧ t≠u ∧
      dist (projectedOrbit v i a b k t) (projectedOrbit v i a b k u)^2 =
        ((4*characteristic v*c^2 : ℚ) : ℝ) := by
    rcases hD with ⟨h0,h2⟩ | ⟨h1,h3⟩
    · exact ⟨0,2,k*b+imagCoeff v i,hsub h0,hsub h2,by decide,
        (projected_conjugate_edges hv i a b k).1⟩
    · exact ⟨1,3,k*b-imagCoeff v i,hsub h1,hsub h3,by decide,
        (projected_conjugate_edges hv i a b k).2⟩
  have hMpos : 0<dist (projectedOrbit v i a b k t) (projectedOrbit v i a b k u) := by
    exact dist_pos.mpr (fun he => htu (hinj ht hu he))
  exact separated_scaled_lengths hv i _ _ scale c hscale hMpos hNorm hConj
    (hrat r hr s hs hrs) (hrat t ht u hu htu)

lemma real_axis_collinear (z w t : ℂ) (hz : z.im=0) (hw : w.im=0) (ht : t.im=0) :
    Collinear ℝ ({z,w,t} : Set ℂ) := by
  rw [collinear_iff_of_mem (by simp : z∈({z,w,t} : Set ℂ))]
  refine ⟨1, ?_⟩
  intro p hp
  have him : p.im=0 := by
    rcases hp with rfl | rfl | rfl <;> assumption
  refine ⟨p.re-z.re, ?_⟩
  apply Complex.ext <;> simp [him,hz]

/-- The entire projected torsion model lies in a real line and three such
four-point orbits. Every finite nontrilinear rational-distance subset, after
an arbitrary common positive real dilation, has at most eight points.
No four-on-a-circle hypothesis is needed for this restricted bound. -/
theorem projected_cloud_card_le_eight {v : ℚ} (hv : 1<v)
    (a b : Fin 3 → ℚ) (k : ℚ) (scale : ℝ) (hscale : 0<scale)
    (S : Finset ℂ)
    (hcover : ∀ z∈S, z.im=0 ∨ ∃ i j, z=projectedOrbit v i (a i) (b i) k j)
    (htri : ∀ z∈S, ∀ w∈S, ∀ t∈S, z≠w → z≠t → w≠t →
      ¬Collinear ℝ ({z,w,t} : Set ℂ))
    (hrat : ∀ z∈S, ∀ w∈S, z≠w → scale*dist z w ∈ Set.range ((↑) : ℚ → ℝ)) :
    S.card≤8 := by
  classical
  let A := S.filter (fun z => z.im=0)
  let B : Fin 3 → Finset ℂ := fun i =>
    S.filter (fun z => z∈Set.range (projectedOrbit v i (a i) (b i) k))
  have hA : A.card≤2 := by
    by_contra hc
    obtain ⟨z,w,t,hz,hw,ht,hzw,hzt,hwt⟩ :=
      Finset.two_lt_card_iff.mp (show 2<A.card by omega)
    obtain ⟨hzS,hzim⟩ := Finset.mem_filter.mp hz
    obtain ⟨hwS,hwim⟩ := Finset.mem_filter.mp hw
    obtain ⟨htS,htim⟩ := Finset.mem_filter.mp ht
    exact htri z hzS w hwS t htS hzw hzt hwt
      (real_axis_collinear z w t hzim hwim htim)
  have hB (i : Fin 3) : (B i).card≤2 := by
    let f := projectedOrbit v i (a i) (b i) k
    have hsurj : Set.SurjOn f Set.univ (B i : Set ℂ) := by
      intro z hz
      obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hz).2
      exact ⟨j,Set.mem_univ _,hj⟩
    obtain ⟨U,-,hinj,he⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
      Set.univ (B i) hsurj
    have hmem (j : Fin 4) (hj : j∈U) : f j∈S := by
      have hz : f j∈B i := by rw [← he]; exact Finset.mem_image_of_mem f hj
      exact (Finset.mem_filter.mp hz).1
    rw [← he,Finset.card_image_of_injOn hinj]
    apply projected_orbit_card_le_two hv i (a i) (b i) k scale hscale U hinj
    intro j hj l hl hjl
    exact hrat (f j) (hmem j hj) (f l) (hmem l hl)
      (fun h => hjl (hinj hj hl h))
  have hsub : S ⊆ A ∪ Finset.univ.biUnion B := by
    intro z hz
    rcases hcover z hz with h | ⟨i,j,h⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz,h⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hz,⟨j,h.symm⟩⟩⟩
  calc
    S.card ≤ (A ∪ Finset.univ.biUnion B).card := Finset.card_le_card hsub
    _ ≤ A.card+(Finset.univ.biUnion B).card := Finset.card_union_le _ _
    _ ≤ A.card+∑ i : Fin 3, (B i).card :=
      Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ 2+∑ _i : Fin 3, 2 := Nat.add_le_add hA (Finset.sum_le_sum (fun i _ => hB i))
    _ = 8 := by norm_num

#print axioms projected_cloud_card_le_eight

#print axioms quadraticPoint_dist_sq
#print axioms separated_scaled_lengths
#print axioms projected_orbit_card_le_two
end
end Erdos213.TorsionTwoTwelve
