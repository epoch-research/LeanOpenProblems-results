import Submission.QuadraticRigidity
import Submission.SquaredBimedians

/-! A low-degree varying-characteristic obstruction. The hypotheses are square
identities in the rational-function field, not distance conditions at a single
specialization. This does not settle Erdős 213. -/
namespace Erdos213.VaryingMetricAffine
open Polynomial EuclideanGeometry
noncomputable section
set_option maxHeartbeats 3000000

/-- The vertical coefficient is constant; its metric weight varies with `t`. -/
def point (a b c t : ℝ) : ℂ := ⟨a+b*t,c*Real.sqrt t⟩

def chordPolynomial (a b c : ℝ) : ℝ[X] :=
  QuadraticRigidity.quad (b^2) (2*a*b+c^2) (a^2)

lemma chord_type (a b c : ℝ)
    (h : IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (chordPolynomial a b c))) :
    c = 0 ∨ 4*a*b+c^2 = 0 := by
  have hd := QuadraticRigidity.discr_zero_of_ratFunc_square h
  change (2*a*b+c^2)^2-4*b^2*a^2=0 at hd
  have hf : c^2*(4*a*b+c^2)=0 := by linear_combination hd
  rcases mul_eq_zero.mp hf with hc | hn
  · exact Or.inl (sq_eq_zero_iff.mp hc)
  · exact Or.inr hn

lemma chord_eval (a b c t : ℝ) (ht : 0 ≤ t) :
    (chordPolynomial a b c).eval t = ‖point a b c t‖^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp only [point,chordPolynomial,QuadraticRigidity.quad,eval_add,eval_mul,
    eval_C,eval_pow,eval_X]
  linear_combination -c^2*(Real.sq_sqrt ht)

/-- Two nonzero null vectors with null difference have zero projected area. -/
lemma null_cross (a b c d e f t : ℝ)
    (hc : c ≠ 0) (hf : f ≠ 0)
    (h1 : 4*a*b+c^2=0) (h2 : 4*d*e+f^2=0)
    (h3 : 4*(d-a)*(e-b)+(f-c)^2=0) :
    (a+b*t)*f-c*(d+e*t)=0 := by
  have ha : a ≠ 0 := by
    intro hz
    rw [hz] at h1
    simp only [mul_zero,zero_mul,zero_add] at h1
    exact hc (sq_eq_zero_iff.mp h1)
  have hd : d ≠ 0 := by
    intro hz
    rw [hz] at h2
    simp only [mul_zero,zero_mul,zero_add] at h2
    exact hf (sq_eq_zero_iff.mp h2)
  have hs : (a*f-d*c)^2=0 := by
    linear_combination a*d*h3+a*(a-d)*h2+d*(d-a)*h1
  have hfc : a*f-d*c=0 := sq_eq_zero_iff.mp hs
  have hbe : a*e-d*b=0 := by
    have hp : (4*a*d)*(a*e-d*b)=0 := by
      linear_combination a^2*h2-d^2*h1-(a*f+d*c)*hfc
    exact (mul_eq_zero.mp hp).resolve_left
      (mul_ne_zero (mul_ne_zero (by norm_num) ha) hd)
  apply (mul_eq_zero.mp (show a*((a+b*t)*f-c*(d+e*t))=0 by
    linear_combination (a+b*t)*hfc-c*t*hbe)).resolve_left ha

lemma null_triangle_collinear (a b c : Fin 3 → ℝ)
    (hc01 : c 1 ≠ c 0) (hc02 : c 2 ≠ c 0)
    (h01 : 4*(a 1-a 0)*(b 1-b 0)+(c 1-c 0)^2=0)
    (h02 : 4*(a 2-a 0)*(b 2-b 0)+(c 2-c 0)^2=0)
    (h12 : 4*(a 2-a 1)*(b 2-b 1)+(c 2-c 1)^2=0) (t : ℝ) :
    Collinear ℝ {point (a 0) (b 0) (c 0) t,point (a 1) (b 1) (c 1) t,
      point (a 2) (b 2) (c 2) t} := by
  apply SquaredBimedians.collinear_of_cross
  have h := null_cross (a 1-a 0) (b 1-b 0) (c 1-c 0)
    (a 2-a 0) (b 2-b 0) (c 2-c 0) t
    (sub_ne_zero.mpr hc01) (sub_ne_zero.mpr hc02) h01 h02
    (by simpa only [sub_sub_sub_cancel_right] using h12)
  dsimp [SquaredBimedians.cross,point]
  linear_combination Real.sqrt t*h

lemma horizontal_collinear (a b c : Fin 3 → ℝ)
    (h01 : c 0=c 1) (h12 : c 1=c 2) (t : ℝ) :
    Collinear ℝ {point (a 0) (b 0) (c 0) t,point (a 1) (b 1) (c 1) t,
      point (a 2) (b 2) (c 2) t} := by
  apply SquaredBimedians.collinear_of_cross
  simp [SquaredBimedians.cross,point,h01,h12]

/-- Two distinct points on each of two translated rectangular hyperbolas have
matching coordinate sums. The hypotheses include all noncollision conditions. -/
lemma hyperbola_midpoint (x y u v r s K : ℝ) (hK : K ≠ 0)
    (hxy : x ≠ 0 ∨ y ≠ 0) (huvrs : u ≠ r ∨ v ≠ s)
    (h1 : u*v=K) (h2 : r*s=K)
    (h3 : (u-x)*(v-y)=K) (h4 : (r-x)*(s-y)=K) :
    u+r=x ∧ v+s=y := by
  have hu : u ≠ 0 := by intro hz; apply hK; simpa [hz] using h1.symm
  have hv : v ≠ 0 := by intro hz; apply hK; simpa [hz] using h1.symm
  have hl : u*y+v*x-x*y=0 := by linear_combination h1-h3
  have hr : r*y+s*x-x*y=0 := by linear_combination h2-h4
  have hx : x ≠ 0 := by
    intro hz
    have hy : y=0 := (mul_eq_zero.mp (show u*y=0 by simpa [hz] using hl)).resolve_left hu
    exact hxy.elim (fun h => h hz) (fun h => h hy)
  have hy : y ≠ 0 := by
    intro hz
    have hx0 : x=0 := (mul_eq_zero.mp (show v*x=0 by simpa [hz] using hl)).resolve_left hv
    exact hx hx0
  have hur : u-r ≠ 0 := by
    intro hz
    have he : u=r := sub_eq_zero.mp hz
    have hvs : v=s := by
      apply mul_left_cancel₀ hu
      simpa [he] using h1.trans h2.symm
    exact huvrs.elim (fun h => h he) (fun h => h hvs)
  have hsum : u+r=x := by
    have hp : y*(u-r)*(u+r-x)=0 := by
      linear_combination u*hl-r*hr-x*(h1-h2)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (mul_ne_zero hy hur))
  refine ⟨hsum,?_⟩
  have hp : x*(v+s-y)=0 := by linear_combination hl+hr-y*hsum
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hx)


private lemma complex_dist_sq (z w : ℂ) :
    dist z w ^ 2 = (z.re-w.re)^2+(z.im-w.im)^2 := by
  rw [dist_eq_norm,Complex.sq_norm,Complex.normSq_apply]
  simp [pow_two]

lemma chord_distance_sq (a b c d e f t : ℝ) (ht : 0 ≤ t) :
    dist (point a b c t) (point d e f t)^2 =
      (chordPolynomial (a-d) (b-e) (c-f)).eval t := by
  rw [complex_dist_sq]
  simp only [point,chordPolynomial,QuadraticRigidity.quad,eval_add,eval_mul,
    eval_C,eval_pow,eval_X]
  linear_combination (c-f)^2*(Real.sq_sqrt ht)


/-- Two horizontal pairs with a shared horizontal midpoint are cyclic when
their heights differ. No distinctness within each pair is needed. -/
lemma horizontal_pairs_cospherical (z₀ z₁ z₂ z₃ : ℂ)
    (hl : z₀.im=z₁.im) (hu : z₂.im=z₃.im)
    (hx : z₀.re+z₁.re=z₂.re+z₃.re) (hy : z₂.im ≠ z₀.im) :
    Cospherical ({z₀,z₁,z₂,z₃} : Set ℂ) := by
  let m : ℝ := (z₀.re+z₁.re)/2
  let n : ℝ := ((z₂.re-m)^2+z₂.im^2-(z₀.re-m)^2-z₀.im^2)/(2*(z₂.im-z₀.im))
  let o : ℂ := ⟨m,n⟩
  have hn : 2*(z₂.im-z₀.im)*n =
      (z₂.re-m)^2+z₂.im^2-(z₀.re-m)^2-z₀.im^2 := by
    dsimp [n]
    field_simp [sub_ne_zero.mpr hy]
  have hm : 2*m=z₀.re+z₁.re := by dsimp [m]; ring
  have hs₁ : (z₁.re-m)^2=(z₀.re-m)^2 := by
    linear_combination (z₀.re-z₁.re)*hm
  have hs₃ : (z₃.re-m)^2=(z₂.re-m)^2 := by
    linear_combination (z₂.re-z₃.re)*hm+(z₂.re-z₃.re)*hx
  refine ⟨o,dist z₀ o,?_⟩
  rintro z (rfl | rfl | rfl | rfl)
  · rfl
  all_goals
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    simp only [complex_dist_sq]
    dsimp [o]
    try simp only [←hl,←hu]
    nlinarith

lemma two_plus_two (a b c : Fin 4 → ℝ) (t : ℝ) (ht : 0 < t)
    (hc01 : c 0=c 1) (hc23 : c 2=c 3) (hc20 : c 2 ≠ c 0)
    (hp01 : point (a 0) (b 0) (c 0) t ≠ point (a 1) (b 1) (c 1) t)
    (hp23 : point (a 2) (b 2) (c 2) t ≠ point (a 3) (b 3) (c 3) t)
    (hnull : ∀ i j, c i ≠ c j →
      4*(a i-a j)*(b i-b j)+(c i-c j)^2=0) :
    Cospherical ({point (a 0) (b 0) (c 0) t,point (a 1) (b 1) (c 1) t,
      point (a 2) (b 2) (c 2) t,point (a 3) (b 3) (c 3) t} : Set ℂ) := by
  have hK : -(c 2-c 0)^2/4 ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (sub_ne_zero.mpr hc20))) (by norm_num)
  have hxy : a 1-a 0 ≠ 0 ∨ b 1-b 0 ≠ 0 := by
    by_contra! h
    apply hp01
    apply Complex.ext <;> dsimp [point]
    · linear_combination -h.1-t*h.2
    · rw [hc01]
  have huvrs : a 2-a 0 ≠ a 3-a 0 ∨ b 2-b 0 ≠ b 3-b 0 := by
    by_contra! h
    apply hp23
    apply Complex.ext <;> dsimp [point]
    · linear_combination h.1+t*h.2
    · rw [hc23]
  have h20 := hnull 2 0 hc20
  have h30 := hnull 3 0 (by simpa [←hc23] using hc20)
  have h21 := hnull 2 1 (by simpa [←hc01] using hc20)
  have h31 := hnull 3 1 (by simpa [←hc01,←hc23] using hc20)
  rw [←hc01] at h21
  rw [←hc23] at h30
  rw [←hc01,←hc23] at h31
  obtain ⟨hx,hy⟩ := hyperbola_midpoint (a 1-a 0) (b 1-b 0)
    (a 2-a 0) (b 2-b 0) (a 3-a 0) (b 3-b 0) (-(c 2-c 0)^2/4)
    hK hxy huvrs (by linarith only [h20]) (by linarith only [h30])
    (by simp only [sub_sub_sub_cancel_right]; linarith only [h21])
    (by simp only [sub_sub_sub_cancel_right]; linarith only [h31])
  apply horizontal_pairs_cospherical
  · dsimp [point]; rw [hc01]
  · dsimp [point]; rw [hc23]
  · dsimp [point]; linear_combination -hx-t*hy
  · dsimp [point]
    exact (mul_left_inj' (Real.sqrt_ne_zero'.mpr ht)).not.mpr hc20

/-- Four colors with no monochromatic or rainbow triple split into two pairs. -/
lemma four_colors (c : Fin 4 → ℝ)
    (h : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ¬ ((c i=c j ∧ c j=c k) ∨ (c i ≠ c j ∧ c i ≠ c k ∧ c j ≠ c k))) :
    (c 0=c 1 ∧ c 2=c 3 ∧ c 2 ≠ c 0) ∨
    (c 0=c 2 ∧ c 1=c 3 ∧ c 1 ≠ c 0) ∨
    (c 0=c 3 ∧ c 1=c 2 ∧ c 1 ≠ c 0) := by
  have h012 := h 0 1 2 (by decide) (by decide) (by decide)
  have h013 := h 0 1 3 (by decide) (by decide) (by decide)
  have h023 := h 0 2 3 (by decide) (by decide) (by decide)
  have h123 := h 1 2 3 (by decide) (by decide) (by decide)
  clear h
  grind

lemma colored_triangle (a b c : Fin 4 → ℝ) (t : ℝ)
    (hnull : ∀ i j, c i ≠ c j →
      4*(a i-a j)*(b i-b j)+(c i-c j)^2=0)
    (i j k : Fin 4)
    (hc : (c i=c j ∧ c j=c k) ∨ (c i ≠ c j ∧ c i ≠ c k ∧ c j ≠ c k)) :
    Collinear ℝ {point (a i) (b i) (c i) t,point (a j) (b j) (c j) t,
      point (a k) (b k) (c k) t} := by
  rcases hc with hc | hc
  · exact horizontal_collinear ![a i,a j,a k] ![b i,b j,b k] ![c i,c j,c k]
      hc.1 hc.2 t
  · exact null_triangle_collinear ![a i,a j,a k] ![b i,b j,b k] ![c i,c j,c k]
      hc.1.symm hc.2.1.symm (hnull j i hc.1.symm) (hnull k i hc.2.1.symm)
      (hnull k j hc.2.2.symm) t

/-- With no collinear indexed triple, four such motions are cospherical.
The square conditions are imposed as identities in `ℝ(t)`. -/
theorem four_motion_cospherical (a b c : Fin 4 → ℝ) (t : ℝ) (ht : 0 < t)
    (hsq : ∀ i j, i ≠ j → IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (chordPolynomial (a i-a j) (b i-b j) (c i-c j))))
    (hp : Function.Injective (fun i => point (a i) (b i) (c i) t))
    (htri : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ¬ Collinear ℝ {point (a i) (b i) (c i) t,point (a j) (b j) (c j) t,
        point (a k) (b k) (c k) t}) :
    Cospherical ({point (a 0) (b 0) (c 0) t,point (a 1) (b 1) (c 1) t,
      point (a 2) (b 2) (c 2) t,point (a 3) (b 3) (c 3) t} : Set ℂ) := by
  have hnull (i j : Fin 4) (hc : c i ≠ c j) :
      4*(a i-a j)*(b i-b j)+(c i-c j)^2=0 := by
    exact (chord_type _ _ _ (hsq i j (fun h => hc (congrArg c h)))).resolve_left
      (sub_ne_zero.mpr hc)
  have hcolor (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      ¬ ((c i=c j ∧ c j=c k) ∨ (c i ≠ c j ∧ c i ≠ c k ∧ c j ≠ c k)) :=
    fun hc => htri i j k hij hik hjk (colored_triangle a b c t hnull i j k hc)
  rcases four_colors c hcolor with hc | hc | hc
  · exact two_plus_two a b c t ht hc.1 hc.2.1 hc.2.2
      (hp.ne (by decide)) (hp.ne (by decide)) hnull
  · let e : Fin 4 → Fin 4 := ![0,2,1,3]
    have hh := two_plus_two (a ∘ e) (b ∘ e) (c ∘ e) t ht hc.1 hc.2.1 hc.2.2
      (hp.ne (by decide : (0 : Fin 4) ≠ 2))
      (hp.ne (by decide : (1 : Fin 4) ≠ 3)) (fun i j h => hnull (e i) (e j) h)
    refine Cospherical.subset ?_ hh
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz ⊢
    dsimp [e,Function.comp_def]
    tauto
  · let e : Fin 4 → Fin 4 := ![0,3,1,2]
    have hh := two_plus_two (a ∘ e) (b ∘ e) (c ∘ e) t ht hc.1 hc.2.1 hc.2.2
      (hp.ne (by decide : (0 : Fin 4) ≠ 3))
      (hp.ne (by decide : (1 : Fin 4) ≠ 2)) (fun i j h => hnull (e i) (e j) h)
    refine Cospherical.subset ?_ hh
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz ⊢
    dsimp [e,Function.comp_def]
    tauto

lemma range_four (p : Fin 4 → ℂ) : Set.range p = {p 0,p 1,p 2,p 3} := by
  ext z
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩

/-- No positive specialization has four distinct points in general position. -/
theorem no_four_general_position (a b c : Fin 4 → ℝ) (t : ℝ) (ht : 0 < t)
    (hsq : ∀ i j, i ≠ j → IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (chordPolynomial (a i-a j) (b i-b j) (c i-c j)))) :
    ¬ (Function.Injective (fun i => point (a i) (b i) (c i) t) ∧
      NonTrilinear (Set.range (fun i => point (a i) (b i) (c i) t)) ∧
      ¬ Cospherical (Set.range (fun i => point (a i) (b i) (c i) t))) := by
  rintro ⟨hp,htri,hcirc⟩
  apply hcirc
  rw [range_four]
  apply four_motion_cospherical a b c t ht hsq hp
  intro i j k hij hik hjk
  exact htri (Set.mem_range_self i) (Set.mem_range_self j) (Set.mem_range_self k)
    (hp.ne hij) (hp.ne hjk) (hp.ne hik)

lemma chord_square_of_type (a b c : ℝ) (h : c=0 ∨ 4*a*b+c^2=0) :
    IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (chordPolynomial a b c)) := by
  apply (QuadraticRigidity.isSquare_ratFunc_iff _).mpr
  rcases h with h | h
  · subst c
    refine ⟨C b*X+C a,?_⟩
    simp only [chordPolynomial,QuadraticRigidity.quad,map_add,map_mul,map_pow,map_ofNat,map_zero]
    ring
  · have he : 2*a*b+c^2 = -(2*a*b) := by linarith only [h]
    refine ⟨C b*X-C a,?_⟩
    simp only [chordPolynomial,QuadraticRigidity.quad,he,map_neg,map_mul,map_pow,map_ofNat]
    ring

private def controlA : Fin 4 → ℝ := ![0,1,9/8,-1/8]
private def controlB : Fin 4 → ℝ := ![0,1,-1/8,9/8]
private def controlC : Fin 4 → ℝ := ![0,0,3/4,3/4]

lemma control_square_identities (i j : Fin 4) :
    IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (chordPolynomial (controlA i-controlA j) (controlB i-controlB j)
        (controlC i-controlC j))) := by
  apply chord_square_of_type
  fin_cases i <;> fin_cases j <;> norm_num [controlA,controlB,controlC]

private def control : Fin 4 → ℂ := fun i =>
  ⟨(![0,5,5/8,35/8] : Fin 4 → ℝ) i,(![0,0,3/2,3/2] : Fin 4 → ℝ) i⟩

lemma control_specialization (i : Fin 4) :
    point (controlA i) (controlB i) (controlC i) 4 = control i := by
  fin_cases i <;> apply Complex.ext <;>
    norm_num [point,controlA,controlB,controlC,control]

private lemma collinear_cross_zero (z₀ z₁ z₂ : ℂ)
    (h : Collinear ℝ {z₀,z₁,z₂}) : SquaredBimedians.cross (z₁-z₀) (z₂-z₀)=0 := by
  obtain ⟨v,hv⟩ := (collinear_iff_of_mem (by simp : z₀∈({z₀,z₁,z₂} : Set ℂ))).mp h
  obtain ⟨r,hr⟩ := hv z₁ (by simp)
  obtain ⟨s,hs⟩ := hv z₂ (by simp)
  subst z₁ z₂
  simp [SquaredBimedians.cross]
  ring

lemma control_injective : Function.Injective control := by
  intro i j hij
  have hx := congrArg Complex.re hij
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [control] at hx

lemma control_nontrilinear : NonTrilinear (Set.range control) := by
  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _ ⟨k,rfl⟩ hij hjk hik hcol
  have hz := collinear_cross_zero _ _ _ hcol
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [control,SquaredBimedians.cross] at *

lemma control_cospherical : Cospherical (Set.range control) := by
  refine ⟨(⟨5/2,-31/192⟩ : ℂ),481/192,?_⟩
  rintro z ⟨i,rfl⟩
  apply (sq_eq_sq₀ dist_nonneg (by norm_num : (0 : ℝ) ≤ 481/192)).mp
  rw [complex_dist_sq]
  fin_cases i <;> norm_num [control]

/-- The circle alternative is necessary even with four distinct points and no
collinear triple; this is not a general-position configuration. -/
lemma cyclic_control :
    (∀ i j : Fin 4, IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (chordPolynomial (controlA i-controlA j) (controlB i-controlB j)
        (controlC i-controlC j)))) ∧
    Function.Injective (fun i => point (controlA i) (controlB i) (controlC i) 4) ∧
    NonTrilinear (Set.range (fun i => point (controlA i) (controlB i) (controlC i) 4)) ∧
    Cospherical (Set.range (fun i => point (controlA i) (controlB i) (controlC i) 4)) := by
  simp only [control_specialization]
  exact ⟨control_square_identities,control_injective,control_nontrilinear,control_cospherical⟩

/-- One edge of the known characteristic-2002 heptad is square at its
specialization but is not a rational-function square. Thus the universal
hypothesis above cannot be inferred from that finite configuration. -/
lemma seven_edge_specialization_control :
    IsSquare ((chordPolynomial 19079044 0 54168).eval 2002) ∧
    ¬ IsSquare (algebraMap ℝ[X] (RatFunc ℝ) (chordPolynomial 19079044 0 54168)) := by
  constructor
  · refine ⟨19232372,?_⟩
    norm_num [chordPolynomial,QuadraticRigidity.quad]
  · intro h
    rcases chord_type 19079044 0 54168 h with h | h <;> norm_num at h

#print axioms seven_edge_specialization_control
#print axioms cyclic_control
#print axioms chord_type
#print axioms hyperbola_midpoint
#print axioms four_motion_cospherical
#print axioms no_four_general_position
#print axioms control_square_identities

end
end Erdos213.VaryingMetricAffine
