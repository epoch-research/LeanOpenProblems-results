import FormalConjecturesUtil

/-!
A local affine-plane diagnostic for the characteristic-three connection set
`N(z)=a^4`. This does not assert biclique freeness or settle Erdős 714.
-/
noncomputable section
set_option maxHeartbeats 2000000
namespace Erdos714CubicQuarticPlane
variable {E : Type*} [Field E] [CharP E 3]

def cubicNorm (σ : E →+* E) (x : E) : E := x*σ x*σ (σ x)

def polar (σ : E →+* E) (u x : E) : E :=
  u*σ u*σ (σ x)+u*σ x*σ (σ u)+x*σ u*σ (σ u)

omit [CharP E 3] in
lemma norm_nonzero (σ : E →+* E) {u : E} (hu : u ≠ 0) : cubicNorm σ u ≠ 0 :=
  mul_ne_zero (mul_ne_zero hu ((map_ne_zero σ).mpr hu))
    ((map_ne_zero σ).mpr ((map_ne_zero σ).mpr hu))

omit [CharP E 3] in
lemma norm_mul (σ : E →+* E) (u v : E) :
    cubicNorm σ (u*v) = cubicNorm σ u*cubicNorm σ v := by
  simp only [cubicNorm,map_mul]
  ring

lemma norm_three (σ : E →+* E) (x u : E) :
    cubicNorm σ (x+u)+cubicNorm σ (x-u)+cubicNorm σ x = -polar σ u x := by
  simp only [cubicNorm,polar,map_add,map_sub]
  have h3 : (3 : E) = 0 := CharP.cast_eq_zero E 3
  linear_combination (x*σ x*σ (σ x)+x*σ u*σ (σ u)+u*σ x*σ (σ u)+u*σ u*σ (σ x))*h3

lemma fourth_three (a b : E) : (a+b)^4+(a-b)^4+a^4 = -b^4 := by
  have h3 : (3 : E) = 0 := CharP.cast_eq_zero E 3
  linear_combination (a^4+4*a^2*b^2+b^4)*h3

omit [CharP E 3] in
lemma polar_add (σ : E →+* E) (u x y : E) :
    polar σ u (x+y) = polar σ u x+polar σ u y := by
  simp only [polar,map_add]
  ring

lemma ratio_fixed (σ : E →+* E) (u v : E) (hu : u ≠ 0)
    (huv : polar σ u v = 0) (hvu : polar σ v u = 0) : σ (v/u) = v/u := by
  simp only [polar] at huv hvu
  let t := v/u
  have hu₁ : σ u ≠ 0 := (map_ne_zero σ).mpr hu
  have hu₂ : σ (σ u) ≠ 0 := (map_ne_zero σ).mpr hu₁
  have hsum : t+σ t+σ (σ t) = 0 := by
    dsimp [t]
    simp only [map_div₀]
    field_simp
    linear_combination huv
  have hpair : t*σ t+t*σ (σ t)+σ t*σ (σ t) = 0 := by
    dsimp [t]
    simp only [map_div₀]
    field_simp
    linear_combination hvu
  have h3 : (3 : E) = 0 := CharP.cast_eq_zero E 3
  have hsquare : (t-σ t)^2 = 0 := by
    linear_combination (t+σ t)*hsum-hpair-(t*σ t)*h3
  exact (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hsquare)).symm

/-- The three elements of the prime subfield, expressed without casts. -/
def Three (s : E) : Prop := s = 0 ∨ s = 1 ∨ s = -1

lemma polar_of_three (σ : E →+* E) (x u a b : E)
    (h0 : cubicNorm σ x = a^4)
    (hp : cubicNorm σ (x+u) = (a+b)^4)
    (hm : cubicNorm σ (x-u) = (a-b)^4) : polar σ u x = b^4 := by
  have h := norm_three σ x u
  rw [h0,hp,hm,fourth_three] at h
  exact neg_injective h.symm

lemma grid_polar (σ : E →+* E) (x u v a b c : E)
    (h : ∀ s t : E, Three s → Three t →
      cubicNorm σ (x+s*u+t*v) = (a+s*b+t*c)^4) :
    polar σ u x = b^4 ∧ polar σ u v = 0 := by
  have ht (t : E) (ht : Three t) : polar σ u (x+t*v) = b^4 := by
    apply polar_of_three σ (x+t*v) u (a+t*c) b
    · simpa only [zero_mul,add_zero,zero_add] using h 0 t (Or.inl rfl) ht
    · convert h 1 t (Or.inr (Or.inl rfl)) ht using 1 <;> congr 1 <;> ring
    · convert h (-1) t (Or.inr (Or.inr rfl)) ht using 1 <;> congr 1 <;> ring
  have h0 : polar σ u x = b^4 := by
    simpa only [zero_mul,add_zero] using ht 0 (Or.inl rfl)
  have h1 : polar σ u (x+v) = b^4 := by
    simpa only [one_mul] using ht 1 (Or.inr (Or.inl rfl))
  rw [polar_add,h0] at h1
  exact ⟨h0,by linear_combination h1⟩

omit [CharP E 3] in
lemma norm_add (σ : E →+* E) (x u : E) :
    cubicNorm σ (x+u) = cubicNorm σ x+polar σ x u+polar σ u x+cubicNorm σ u := by
  simp only [cubicNorm,polar,map_add]
  ring

omit [CharP E 3] in
lemma polar_smul_left (σ : E →+* E) (l u x : E) (hl : σ l = l) :
    polar σ (l*u) x = l^2*polar σ u x := by
  simp only [polar,map_mul,hl]
  ring

omit [CharP E 3] in
lemma polar_smul_right (σ : E →+* E) (l u x : E) (hl : σ l = l) :
    polar σ x (l*u) = l*polar σ x u := by
  simp only [polar,map_mul,hl]
  ring

omit [CharP E 3] in
lemma norm_smul (σ : E →+* E) (l u : E) (hl : σ l = l) :
    cubicNorm σ (l*u) = l^3*cubicNorm σ u := by
  simp only [cubicNorm,map_mul,hl]
  ring

omit [CharP E 3] in
lemma cube_three (l : E) (hl : l^3 = l) : Three l := by
  have h : l*(l-1)*(l+1) = 0 := by linear_combination hl
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h))

lemma quartic_ratios (l b c : E) (hb : b ≠ 0)
    (h1 : c^4 = l^2*b^4) (h2 : (b+c)^4 = (1+l)^2*b^4) :
    Three l ∧ c = l*b := by
  have h3 : (3 : E) = 0 := CharP.cast_eq_zero E 3
  have hcross : b^3*c+b*c^3 = 2*l*b^4 := by
    linear_combination h2-h1-(b^3*c+2*b^2*c^2+b*c^3)*h3
  have hsquare : (b*c*(b^2-c^2))^2 = 0 := by
    linear_combination (b^3*c+b*c^3+2*l*b^4)*hcross - 4*b^4*h1
  have hz : c = 0 ∨ b = c ∨ b = -c := by
    have hp := (mul_eq_zero.mp (eq_zero_of_pow_eq_zero hsquare))
    rcases hp with h | h
    · exact Or.inl ((mul_eq_zero.mp h).resolve_left hb)
    · exact Or.inr (sq_eq_sq_iff_eq_or_eq_neg.mp (sub_eq_zero.mp h))
  have hb4 : b^4 ≠ 0 := pow_ne_zero 4 hb
  rcases hz with rfl | hc | hc
  · have hl : l = 0 := by
      have hh : l^2*b^4 = 0 := by simpa using h1.symm
      exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hh).resolve_right hb4)
    exact ⟨Or.inl hl,by simp [hl]⟩
  · have hl : l = 1 := by
      rw [← hc] at hcross
      have hh : (l-1)*b^4 = 0 := by
        linear_combination hcross+(l*b^4-b^4)*h3
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hb4)
    subst l
    exact ⟨Or.inr (Or.inl rfl),by simpa using hc.symm⟩
  · have hc' : c = -b := by linear_combination hc
    have hl : l = -1 := by
      rw [hc'] at hcross
      have hh : (l+1)*b^4 = 0 := by
        linear_combination hcross+(l*b^4+b^4)*h3
      exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hh).resolve_right hb4)
    subst l
    exact ⟨Or.inr (Or.inr rfl),by simpa using hc'⟩

/-- Nine connection equations force dependence of the two prime-field directions. -/
theorem directions_dependent (σ : E →+* E) (x u v a b c : E)
    (h : ∀ s t : E, Three s → Three t →
      cubicNorm σ (x+s*u+t*v) = (a+s*b+t*c)^4) :
    (u = 0 ∧ b = 0) ∨ ∃ l : E, Three l ∧ v = l*u ∧ c = l*b := by
  obtain ⟨hux,huv⟩ := grid_polar σ x u v a b c h
  have hswap : ∀ s t : E, Three s → Three t →
      cubicNorm σ (x+s*v+t*u) = (a+s*c+t*b)^4 := by
    intro s t hs ht
    convert h t s ht hs using 1 <;> congr 1 <;> ring
  obtain ⟨hvx,hvu⟩ := grid_polar σ x v u a c b hswap
  by_cases hu : u = 0
  · refine Or.inl ⟨hu,?_⟩
    have hb4 : b^4 = 0 := by simpa [hu,polar] using hux.symm
    exact eq_zero_of_pow_eq_zero hb4
  let l := v/u
  have hl : σ l = l := ratio_fixed σ u v hu huv hvu
  have hv : v = l*u := by dsimp [l]; field_simp
  have hcoef1 : c^4 = l^2*b^4 := by
    rw [← hvx,hv,polar_smul_left σ l u x hl,hux]
  have hdiag : polar σ (u+v) x = (b+c)^4 := by
    apply polar_of_three σ x (u+v) a (b+c)
    · simpa only [zero_mul,add_zero] using h 0 0 (Or.inl rfl) (Or.inl rfl)
    · convert h 1 1 (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl)) using 1 <;>
        congr 1 <;> ring
    · convert h (-1) (-1) (Or.inr (Or.inr rfl)) (Or.inr (Or.inr rfl)) using 1 <;>
        congr 1 <;> ring
  have hcoef2 : (b+c)^4 = (1+l)^2*b^4 := by
    have hsum : u+v = (1+l)*u := by rw [hv]; ring
    rw [← hdiag,hsum,polar_smul_left σ (1+l) u x (by simp [hl]),hux]
  by_cases hb : b = 0
  · have hc : c = 0 := by
      apply eq_zero_of_pow_eq_zero (n := 4)
      simpa only [hb,zero_pow (by decide : 4 ≠ 0),mul_zero] using hcoef1
    have h0 : cubicNorm σ x = a^4 := by
      simpa only [zero_mul,add_zero] using h 0 0 (Or.inl rfl) (Or.inl rfl)
    have hpu : cubicNorm σ (x+u) = a^4 := by
      simpa only [hb,one_mul,zero_mul,add_zero] using
        h 1 0 (Or.inr (Or.inl rfl)) (Or.inl rfl)
    have hpv : cubicNorm σ (x+v) = a^4 := by
      simpa only [hc,one_mul,zero_mul,add_zero] using
        h 0 1 (Or.inl rfl) (Or.inr (Or.inl rfl))
    have hux0 : polar σ u x = 0 := by simpa only [hb,zero_pow (by decide : 4 ≠ 0)] using hux
    rw [norm_add,h0,hux0] at hpu
    rw [hv,norm_add,h0,polar_smul_left σ l u x hl,
      polar_smul_right σ l u x hl,norm_smul σ l u hl,hux0] at hpv
    have hl3 : l^3 = l := by
      apply sub_eq_zero.mp
      apply (mul_eq_zero.mp (show cubicNorm σ u*(l^3-l) = 0 from ?_)).resolve_left
        (norm_nonzero σ hu)
      linear_combination hpv-l*hpu
    exact Or.inr ⟨l,cube_three l hl3,hv,by simp [hb,hc]⟩
  · obtain ⟨hl3,hc⟩ := quartic_ratios l b c hb hcoef1 hcoef2
    exact Or.inr ⟨l,hl3,hv,hc⟩

/-- Coordinates of the prime-field grid. -/
def sample (i : Fin 3) : E := ![0,1,-1] i

omit [CharP E 3] in
lemma sample_three (i : Fin 3) : Three (sample (E := E) i) := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

def grid (x u v a b c : E) (p : Fin 3 × Fin 3) : E × E :=
  (x+sample p.1*u+sample p.2*v,a+sample p.1*b+sample p.2*c)

/-- Absence of an affine F3-plane is only a local property; it is not K44-freeness. -/
theorem no_injective_grid (σ : E →+* E) (x u v a b c : E)
    (h : ∀ i j : Fin 3,
      cubicNorm σ (x+sample i*u+sample j*v) = (a+sample i*b+sample j*c)^4) :
    ¬ Function.Injective (grid x u v a b c) := by
  have hh : ∀ s t : E, Three s → Three t →
      cubicNorm σ (x+s*u+t*v) = (a+s*b+t*c)^4 := by
    intro s t hs ht
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl
    · exact h 0 0
    · exact h 0 1
    · exact h 0 2
    · exact h 1 0
    · exact h 1 1
    · exact h 1 2
    · exact h 2 0
    · exact h 2 1
    · exact h 2 2
  intro hinj
  rcases directions_dependent σ x u v a b c hh with ⟨hu,hb⟩ | ⟨l,hl,hv,hc⟩
  · have he : grid x u v a b c (0,0) = grid x u v a b c (1,0) := by
      simp [grid,sample,hu,hb]
    exact (by decide : ((0,0) : Fin 3 × Fin 3) ≠ (1,0)) (hinj he)
  · rcases hl with rfl | rfl | rfl
    · have he : grid x u v a b c (0,0) = grid x u v a b c (0,1) := by
        simp [grid,sample,hv,hc]
      exact (by decide : ((0,0) : Fin 3 × Fin 3) ≠ (0,1)) (hinj he)
    · have he : grid x u v a b c (1,0) = grid x u v a b c (0,1) := by
        simp [grid,sample,hv,hc]
      exact (by decide : ((1,0) : Fin 3 × Fin 3) ≠ (0,1)) (hinj he)
    · have he : grid x u v a b c (0,0) = grid x u v a b c (1,1) := by
        simp [grid,sample,hv,hc]
      exact (by decide : ((0,0) : Fin 3 × Fin 3) ≠ (1,1)) (hinj he)

section ActualNorm
variable {F : Type*} [Field F] [Algebra F E]
  [Fintype F] [Fintype E] [FiniteDimensional F E]

omit [CharP E 3] [Fintype F] [Fintype E] [FiniteDimensional F E] in
lemma map_sample (i : Fin 3) :
    algebraMap F E (sample (E := F) i) = sample (E := E) i := by
  fin_cases i <;> simp [sample]

omit [FiniteDimensional F E] in
/-- The original field-norm connection set contains no affine prime-field plane.
This statement does not exclude general four-by-four sum rectangles. -/
theorem no_injective_actual_norm_grid (hdim : Module.finrank F E = 3)
    (x u v : E) (a b c : F)
    (h : ∀ i j : Fin 3,
      Algebra.norm F (x+sample i*u+sample j*v) =
        (a+sample (E := F) i*b+sample (E := F) j*c)^4) :
    ¬ Function.Injective (fun p : Fin 3 × Fin 3 =>
      (x+sample p.1*u+sample p.2*v,
       a+sample (E := F) p.1*b+sample (E := F) p.2*c)) := by
  let σ : E →+* E := (FiniteField.frobeniusAlgHom F E).toRingHom
  have hN (z : E) : algebraMap F E (Algebra.norm F z) = cubicNorm σ z := by
    change algebraMap F E (Algebra.norm F z) =
      z*(z^Fintype.card F)*((z^Fintype.card F)^Fintype.card F)
    rw [FiniteField.algebraMap_norm_eq_prod_pow F E z,hdim]
    simp only [Finset.prod_range_succ,Finset.prod_range_zero,pow_zero,pow_one,one_mul,
      Nat.card_eq_fintype_card,← pow_mul,pow_two]
  have he (i j : Fin 3) :
      cubicNorm σ (x+sample i*u+sample j*v) =
        (algebraMap F E a+sample i*algebraMap F E b+sample j*algebraMap F E c)^4 := by
    rw [← hN,h i j,map_pow,map_add,map_add,map_mul,map_mul,map_sample,map_sample]
  intro hinj
  apply no_injective_grid σ x u v (algebraMap F E a) (algebraMap F E b)
    (algebraMap F E c) he
  intro p q hpq
  apply hinj
  apply Prod.ext
  · exact congrArg (fun z : E × E => z.1) hpq
  · apply (algebraMap F E).injective
    simpa only [map_add,map_mul,map_sample,grid] using congrArg Prod.snd hpq

end ActualNorm

#print axioms ratio_fixed
#print axioms quartic_ratios
#print axioms directions_dependent
#print axioms no_injective_grid
#print axioms no_injective_actual_norm_grid

end Erdos714CubicQuarticPlane
