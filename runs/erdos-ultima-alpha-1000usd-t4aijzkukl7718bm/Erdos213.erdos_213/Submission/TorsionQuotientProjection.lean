import Submission.TorsionTwoTwelveOrbit
import Submission.IsoscelesCurve

/-! A bound for the quotient projection of the quadratic 2-by-12 torsion model.
The hypotheses below state the coordinate cover explicitly. They do not
assert that arbitrary integral-distance configurations have this cover. -/
namespace Erdos213.TorsionTwoTwelve
noncomputable section
set_option maxHeartbeats 2000000

lemma characteristic_not_square {v : ℚ} (hv : 1<v) :
    ¬ IsSquare (characteristic v) := by
  rintro ⟨w,hw⟩
  have he : (3*v*w)^2=(3*v^2+1)*((3*v^2+1)-1)*((3*v^2+1)-4) := by
    dsimp [characteristic] at hw
    linear_combination -9*v^2*hw
  obtain ⟨hx,_⟩ := (IsoscelesCurve.minus_curve_points _ _).mp he
  have h2 := parameter_sq_gt_one hv
  rcases hx with hx | hx | hx <;> nlinarith

lemma vertical_line_collinear (z w t : ℂ) (hw : w.re=z.re) (ht : t.re=z.re) :
    Collinear ℝ ({z,w,t} : Set ℂ) := by
  rw [collinear_iff_of_mem (by simp : z∈({z,w,t} : Set ℂ))]
  refine ⟨Complex.I,?_⟩
  intro p hp
  have hre : p.re=z.re := by
    rcases hp with rfl | rfl | rfl
    · rfl
    · exact hw
    · exact ht
  refine ⟨p.im-z.im,?_⟩
  apply Complex.ext <;> simp [hre]

lemma incompatible_scaled_directions {D : ℚ} (hD : ¬ IsSquare D)
    (L M scale : ℝ) (r s : ℚ) (hscale : 0<scale) (hLp : 0<L) (hMp : 0<M)
    (hL : L^2=(r : ℝ)^2) (hM : M^2=(D : ℝ)*(s : ℝ)^2)
    (hLrat : scale*L∈Set.range ((↑) : ℚ → ℝ))
    (hMrat : scale*M∈Set.range ((↑) : ℚ → ℝ)) : False := by
  obtain ⟨p,hp⟩ := hLrat
  obtain ⟨q,hq⟩ := hMrat
  have hp0 : p≠0 := by
    intro he
    have hz : (0 : ℝ)=scale*L := by simpa [he] using hp
    exact (ne_of_gt (mul_pos hscale hLp)) hz.symm
  have hs0 : s≠0 := by
    intro he
    rw [he] at hM
    norm_num at hM
    linarith
  have heR : (D : ℝ)*((p*s : ℚ) : ℝ)^2=((q*r : ℚ) : ℝ)^2 := by
    push_cast
    rw [hp,hq]
    linear_combination scale^2*((D : ℝ)*(s : ℝ)^2*hL-(r : ℝ)^2*hM)
  have he : D*(p*s)^2=(q*r)^2 := by exact_mod_cast heR
  apply hD
  refine ⟨q*r/(p*s),?_⟩
  field_simp
  nlinarith only [he]

private lemma quadraticPoint_re (D a b : ℚ) : (quadraticPoint D a b).re=(a : ℝ) := by
  simp [quadraticPoint]

private lemma quadraticPoint_axis_im (D a : ℚ) : (quadraticPoint D a 0).im=0 := by
  simp [quadraticPoint]

/-- A rational horizontal axis and three rational vertical fibers in a
nonsquare characteristic contain at most seven points in any nontrilinear
rational-distance set, even after arbitrary common positive real dilation.
There is no assumption excluding four points on a circle in this theorem. -/
theorem three_vertical_fibers_card_le_seven {D : ℚ} (hDpos : 0<D)
    (hDns : ¬ IsSquare D) (a : Fin 3 → ℚ) (scale : ℝ) (hscale : 0<scale)
    (S : Finset ℂ)
    (hcover : ∀ z∈S, (∃ x : ℚ, z=quadraticPoint D x 0) ∨
      ∃ i : Fin 3, ∃ y : ℚ, z=quadraticPoint D (a i) y)
    (htri : ∀ z∈S, ∀ w∈S, ∀ t∈S, z≠w → z≠t → w≠t →
      ¬Collinear ℝ ({z,w,t} : Set ℂ))
    (hrat : ∀ z∈S, ∀ w∈S, z≠w → scale*dist z w∈Set.range ((↑) : ℚ → ℝ)) :
    S.card≤7 := by
  classical
  let A := S.filter (fun z => ∃ x : ℚ, z=quadraticPoint D x 0)
  let B : Fin 3 → Finset ℂ := fun i =>
    S.filter (fun z => ∃ y : ℚ, z=quadraticPoint D (a i) y)
  have hA : A.card≤2 := by
    by_contra hc
    obtain ⟨z,w,t,hz,hw,ht,hzw,hzt,hwt⟩ :=
      Finset.two_lt_card_iff.mp (show 2<A.card by omega)
    obtain ⟨hzS,x,rfl⟩ := Finset.mem_filter.mp hz
    obtain ⟨hwS,y,rfl⟩ := Finset.mem_filter.mp hw
    obtain ⟨htS,u,rfl⟩ := Finset.mem_filter.mp ht
    exact htri _ hzS _ hwS _ htS hzw hzt hwt
      (real_axis_collinear _ _ _ (quadraticPoint_axis_im _ _)
        (quadraticPoint_axis_im _ _) (quadraticPoint_axis_im _ _))
  have hB (i : Fin 3) : (B i).card≤2 := by
    by_contra hc
    obtain ⟨z,w,t,hz,hw,ht,hzw,hzt,hwt⟩ :=
      Finset.two_lt_card_iff.mp (show 2<(B i).card by omega)
    obtain ⟨hzS,x,rfl⟩ := Finset.mem_filter.mp hz
    obtain ⟨hwS,y,rfl⟩ := Finset.mem_filter.mp hw
    obtain ⟨htS,u,rfl⟩ := Finset.mem_filter.mp ht
    exact htri _ hzS _ hwS _ htS hzw hzt hwt
      (vertical_line_collinear _ _ _ (by simp [quadraticPoint_re])
        (by simp [quadraticPoint_re]))
  have hsub : S ⊆ A ∪ Finset.univ.biUnion B := by
    intro z hz
    rcases hcover z hz with hh | ⟨i,y,hy⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz,hh⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hz,⟨y,hy⟩⟩⟩
  have hcount : S.card ≤ A.card+∑ i : Fin 3, (B i).card := by
    calc
      S.card ≤ (A ∪ Finset.univ.biUnion B).card := Finset.card_le_card hsub
      _ ≤ A.card+(Finset.univ.biUnion B).card := Finset.card_union_le _ _
      _ ≤ A.card+∑ i : Fin 3, (B i).card :=
        Nat.add_le_add_left Finset.card_biUnion_le _
  by_cases hAsmall : A.card≤1
  · calc
      S.card ≤ A.card+∑ i : Fin 3, (B i).card := hcount
      _ ≤ 1+∑ _i : Fin 3, 2 := Nat.add_le_add hAsmall (Finset.sum_le_sum (fun i _ => hB i))
      _ = 7 := by norm_num
  · have hBsmall (i : Fin 3) : (B i).card≤1 := by
      by_contra hc
      obtain ⟨z,w,hz,hw,hzw⟩ := Finset.one_lt_card_iff.mp (show 1<A.card by omega)
      obtain ⟨t,u,ht,hu,htu⟩ := Finset.one_lt_card_iff.mp (show 1<(B i).card by omega)
      obtain ⟨hzS,x,rfl⟩ := Finset.mem_filter.mp hz
      obtain ⟨hwS,y,rfl⟩ := Finset.mem_filter.mp hw
      obtain ⟨htS,b,rfl⟩ := Finset.mem_filter.mp ht
      obtain ⟨huS,c,rfl⟩ := Finset.mem_filter.mp hu
      apply incompatible_scaled_directions hDns _ _ scale (x-y) (b-c) hscale
        (dist_pos.mpr hzw) (dist_pos.mpr htu)
      · rw [quadraticPoint_dist_sq hDpos.le]
        push_cast
        ring
      · rw [quadraticPoint_dist_sq hDpos.le]
        push_cast
        ring
      · exact hrat _ hzS _ hwS hzw
      · exact hrat _ htS _ huS htu
    calc
      S.card ≤ A.card+∑ i : Fin 3, (B i).card := hcount
      _ ≤ 2+∑ _i : Fin 3, 1 := Nat.add_le_add hA (Finset.sum_le_sum (fun i _ => hBsmall i))
      _ ≤ 7 := by norm_num

/-- The quotient projection's four points are all on a single vertical fiber. -/
def quotientOrbit (D a b c k : ℚ) : Fin 4 → ℂ :=
  ![quadraticPoint D (k*a) (k*b+c), quadraticPoint D (k*a) (k*b-c),
    quadraticPoint D (k*a) (-k*b-c), quadraticPoint D (k*a) (-k*b+c)]

theorem quotient_cloud_card_le_seven {v : ℚ} (hv : 1<v)
    (a b c : Fin 3 → ℚ) (k : ℚ) (scale : ℝ) (hscale : 0<scale)
    (S : Finset ℂ)
    (hcover : ∀ z∈S, (∃ x : ℚ, z=quadraticPoint (characteristic v) x 0) ∨
      ∃ i j, z=quotientOrbit (characteristic v) (a i) (b i) (c i) k j)
    (htri : ∀ z∈S, ∀ w∈S, ∀ t∈S, z≠w → z≠t → w≠t →
      ¬Collinear ℝ ({z,w,t} : Set ℂ))
    (hrat : ∀ z∈S, ∀ w∈S, z≠w → scale*dist z w∈Set.range ((↑) : ℚ → ℝ)) :
    S.card≤7 := by
  apply three_vertical_fibers_card_le_seven (characteristic_pos hv)
    (characteristic_not_square hv) (fun i => k*a i) scale hscale S ?_ htri hrat
  intro z hz
  rcases hcover z hz with hh | ⟨i,j,rfl⟩
  · exact Or.inl hh
  · right
    refine ⟨i,?_⟩
    fin_cases j <;> exact ⟨_,rfl⟩

#print axioms characteristic_not_square
#print axioms incompatible_scaled_directions
#print axioms three_vertical_fibers_card_le_seven
#print axioms quotient_cloud_card_le_seven
end
end Erdos213.TorsionTwoTwelve
