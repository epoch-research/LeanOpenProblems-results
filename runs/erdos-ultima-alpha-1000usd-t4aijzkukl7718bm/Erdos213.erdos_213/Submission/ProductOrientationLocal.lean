import FormalConjecturesUtil
import Submission.ProductOrientation

/-! A modulo-19 obstruction to the ENTIRE fixed-radius matching family
R=5/2, S=24/11. This is not an obstruction to arbitrary product inputs or
arbitrary integral point sets. Homogenization and descent handle denominators. -/
namespace Erdos213.ProductOrientationLocal
open ProductNormMatching ProductOrientation
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

abbrev F := ZMod 19
instance : Fact (Nat.Prime 19) := ⟨by norm_num⟩

lemma anisotropic : ∀ x y : F, x^2+y^2=0 → x=0 ∧ y=0 := by decide

lemma first_star_axis : ∀ t x y : F,
    4*(x^2+y^2)=25*t^2 →
    IsSquare ((x-t)^2+y^2) → IsSquare ((x+t)^2+y^2) → y=0 := by
  decide +kernel

lemma second_star_zero : ∀ t w : F,
    121*w^2=576*t^2 → IsSquare (t^2+w^2) → t=0 := by
  decide +kernel

-- Coordinates are t,x,y,z,w,a,b,c,d. The final four entries are anchor lengths.
def equations {R : Type*} [CommRing R] (j : Fin 9 → R) : Fin 7 → R :=
  ![4*((j 1)^2+(j 2)^2)-25*(j 0)^2,
    121*((j 3)^2+(j 4)^2)-576*(j 0)^2,
    (j 5)^2-(j 1-j 0)^2-(j 2)^2,
    (j 6)^2-(j 1+j 0)^2-(j 2)^2,
    (j 7)^2-(j 3-j 0)^2-(j 4)^2,
    (j 8)^2-(j 3+j 0)^2-(j 4)^2,
    9555*(j 1)*(j 3)+20213*(j 2)*(j 4)]

lemma equations_scale {R : Type*} [CommRing R] (j : Fin 9 → R) (c : R) :
    equations (fun i => c*j i)=fun i => c^2*equations j i := by
  ext i
  fin_cases i <;> dsimp [equations] <;> ring

lemma equations_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (j : Fin 9 → R) :
    equations (fun i => f (j i))=fun i => f (equations j i) := by
  ext i
  fin_cases i <;> dsimp [equations] <;> simp only [map_sub,map_add,map_mul,map_pow,map_ofNat]

/-- Every homogeneous solution over F_19 is zero, including the hyperplane
at infinity t=0. No general-position condition is used. -/
theorem residue_zero (j : Fin 9 → F) (h : equations j=0) : j=0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  have h6 := congrFun h 6
  dsimp [equations] at h0 h1 h2 h3 h4 h5 h6
  have hr : 4*((j 1)^2+(j 2)^2)=25*(j 0)^2 := sub_eq_zero.mp h0
  have hs : 121*((j 3)^2+(j 4)^2)=576*(j 0)^2 := sub_eq_zero.mp h1
  have hm : IsSquare ((j 1-j 0)^2+(j 2)^2) := by
    refine ⟨j 5,?_⟩
    linear_combination -h2
  have hp : IsSquare ((j 1+j 0)^2+(j 2)^2) := by
    refine ⟨j 6,?_⟩
    linear_combination -h3
  have hy := first_star_axis (j 0) (j 1) (j 2) hr hm hp
  have ht : j 0=0 := by
    by_cases hx : j 1=0
    · rw [hx,hy] at hr
      norm_num at hr
      exact hr.resolve_left (by decide : (25 : F) ≠ 0)
    · have hz : j 3=0 := by
        rw [hy] at h6
        simp only [mul_zero,zero_mul,add_zero] at h6
        exact (mul_eq_zero.mp h6).resolve_left (mul_ne_zero (by decide : (9555 : F) ≠ 0) hx)
      have hc : IsSquare ((j 0)^2+(j 4)^2) := by
        refine ⟨j 7,?_⟩
        rw [hz] at h4
        linear_combination -h4
      apply second_star_zero (j 0) (j 4) ?_ hc
      simpa [hz] using hs
  have hx : j 1=0 := by
    rw [ht,hy] at hr
    norm_num at hr
    exact hr.resolve_left (by decide : (4 : F) ≠ 0)
  have hzw : j 3=0 ∧ j 4=0 := by
    apply anisotropic
    rw [ht] at hs
    norm_num at hs
    exact hs.resolve_left (by decide : (121 : F) ≠ 0)
  have ha : j 5=0 := by
    rw [ht,hx,hy] at h2
    simpa using h2
  have hb : j 6=0 := by
    rw [ht,hx,hy] at h3
    simpa using h3
  have hc : j 7=0 := by
    rw [ht,hzw.1,hzw.2] at h4
    simpa using h4
  have hd : j 8=0 := by
    rw [ht,hzw.1,hzw.2] at h5
    simpa using h5
  ext i
  fin_cases i <;> simp_all

lemma integral_divisible (j : Fin 9 → ℤ) (h : equations j=0) :
    ∀ i, (19 : ℤ) ∣ j i := by
  have hc : equations (fun i => (j i : F))=0 := by
    change equations (fun i => (Int.castRingHom F) (j i))=0
    rw [equations_map,h]
    rfl
  have hz := residue_zero _ hc
  intro i
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (j i) 19).mp (congrFun hz i)

private lemma descent_zero {ι : Type*} (P : (ι → ℤ) → Prop) (p : ℕ) (hp : 1<p)
    (hdiv : ∀ j, P j → ∃ k, P k ∧ j=fun i => (p : ℤ)*k i)
    (j : ι → ℤ) (hj : P j) : j=0 := by
  ext i
  have hc : ∀ N : ℕ, ∀ k : ι → ℤ, (k i).natAbs=N → P k → k i=0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro k hkN hk
      obtain ⟨l,hl,hkl⟩ := hdiv k hk
      by_cases hi : l i=0
      · rw [hkl]; simp [hi]
      have hlpos : 0<(l i).natAbs := Int.natAbs_pos.mpr hi
      have hn : (l i).natAbs<N := by
        rw [hkl] at hkN
        simp only [Int.natAbs_mul,Int.natAbs_natCast] at hkN
        nlinarith
      exact (hi (ih _ hn l rfl hl)).elim
  exact hc _ j rfl hj

lemma integral_zero (j : Fin 9 → ℤ) (h : equations j=0) : j=0 := by
  apply descent_zero (fun k => equations k=0) 19 (by norm_num) _ j h
  intro k hk
  choose l hl using integral_divisible k hk
  have he : k=fun i => (19 : ℤ)*l i := funext hl
  refine ⟨l,?_,he⟩
  rw [he,equations_scale] at hk
  ext i
  have hc := congrFun hk i
  exact (mul_eq_zero.mp hc).resolve_left (pow_ne_zero _ (by norm_num))

lemma rational_zero (j : Fin 9 → ℚ) (h : equations j=0) : j=0 := by
  obtain ⟨b,hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) j
  change ∀ i, ∃ k : ℤ, (k : ℚ)=(b : ℤ) • j i at hb
  choose k hk using hb
  have he : (fun i => (k i : ℚ))=fun i => ((b : ℤ) : ℚ)*j i := by
    ext i
    simpa only [zsmul_eq_mul] using hk i
  have hc : equations (fun i => (k i : ℚ))=0 := by
    rw [he,equations_scale,h]
    ext i
    simp
  have hi : equations k=0 := by
    change equations (fun i => (Int.castRingHom ℚ) (k i))=0 at hc
    rw [equations_map] at hc
    ext i
    have hh := congrFun hc i
    change ((equations k i : ℤ) : ℚ)=0 at hh
    exact_mod_cast hh
  have hz := integral_zero k hi
  have hb0 : (b : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.property
  ext i
  have hh := congrFun he i
  rw [hz] at hh
  have hbQ : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hb0
  exact (mul_eq_zero.mp hh.symm).resolve_left hbQ

/-- The fixed radii cannot support the two three-anchor inputs with this
same-sign matching, for ANY rational proportionality factor q. -/
theorem fixed_radii_no_matching {x y z w q : ℚ}
    (hr : radius 1 x y=(5/2 : ℚ)^2) (hs : radius 1 z w=(24/11 : ℚ)^2)
    (hb : SquareInput 1 x y) (hc : SquareInput 1 z w)
    (hm : Matching 1 x y z w q) : False := by
  obtain ⟨a,ha⟩ := hb.2.1
  obtain ⟨b,hb'⟩ := hb.2.2
  obtain ⟨c,hc'⟩ := hc.2.1
  obtain ⟨d,hd⟩ := hc.2.2
  have ho := matching_orthogonal hm
  dsimp [jRe,jIm] at ho
  rw [hr,hs] at ho
  let j : Fin 9 → ℚ := ![1,x,y,z,w,a,b,c,d]
  have he : equations j=0 := by
    ext i
    fin_cases i
    · dsimp [equations,j]
      dsimp [radius] at hr
      linear_combination 4*hr
    · dsimp [equations,j]
      dsimp [radius] at hs
      linear_combination 121*hs
    · dsimp [equations,j]
      dsimp [minusNorm] at ha
      linear_combination -ha
    · dsimp [equations,j]
      dsimp [plusNorm] at hb'
      linear_combination -hb'
    · dsimp [equations,j]
      dsimp [minusNorm] at hc'
      linear_combination -hc'
    · dsimp [equations,j]
      dsimp [plusNorm] at hd
      linear_combination -hd
    · dsimp [equations,j]
      linear_combination 484*ho
  have hz := congrFun (rational_zero j he) 0
  norm_num [j] at hz

/-- No rational point anywhere on the orientation fiber can satisfy both
three-anchor inputs. This is stronger than testing one elliptic point. -/
theorem no_full_orientation_input {e u v : ℚ} (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hu : u^2=e^2+9555^2) (hv : v^2=e^2+20213^2)
    (hb : SquareInput 1 (bx e u) (byCoord u))
    (hc : SquareInput 1 (cx v) (cy e v)) : False :=
  fixed_radii_no_matching (first_radius hu0 hu) (second_radius hv0 hv)
    hb hc (orientation_matching hu0 hv0 hu hv)

lemma anchor_product_nonzero {D x y : ℚ} (hD : 0<D)
    (hr0 : radius D x y ≠ 0) (hr1 : radius D x y ≠ 1) :
    radius D x y*minusNorm D x y*plusNorm D x y ≠ 0 := by
  have hterm : 0≤D*y^2 := mul_nonneg hD.le (sq_nonneg y)
  have hm : minusNorm D x y ≠ 0 := by
    intro hz
    dsimp [minusNorm] at hz
    have hx : x=1 := by nlinarith only [hz,hterm,sq_nonneg (x-1)]
    apply hr1
    dsimp [radius]
    rw [hx] at hz ⊢
    nlinarith only [hz]
  have hp : plusNorm D x y ≠ 0 := by
    intro hz
    dsimp [plusNorm] at hz
    have hx : x= -1 := by nlinarith only [hz,hterm,sq_nonneg (x+1)]
    apply hr1
    dsimp [radius]
    rw [hx] at hz ⊢
    nlinarith only [hz]
  exact mul_ne_zero (mul_ne_zero hr0 hm) hp

lemma characteristic_norms (d x y : ℚ) :
    radius 1 x (d*y)=radius (d*d) x y ∧
    minusNorm 1 x (d*y)=minusNorm (d*d) x y ∧
    plusNorm 1 x (d*y)=plusNorm (d*d) x y := by
  dsimp [radius,minusNorm,plusNorm]
  constructor
  · ring
  constructor <;> ring

lemma characteristic_square_input {d x y : ℚ} (h : SquareInput (d*d) x y) :
    SquareInput 1 x (d*y) := by
  unfold SquareInput
  rw [(characteristic_norms d x y).1,(characteristic_norms d x y).2.1,
    (characteristic_norms d x y).2.2]
  exact h

lemma characteristic_matching {d x y z w q : ℚ}
    (h : Matching (d*d) x y z w q) : Matching 1 x (d*y) z (d*w) q := by
  unfold Matching at h ⊢
  rw [(characteristic_norms d x y).1,(characteristic_norms d z w).1]
  constructor
  · convert h.1 using 1 <;> ring
  · convert h.2 using 1 <;> ring

/-- The obstruction also excludes every positive rational characteristic,
not just D=1: the existing matching theorem first forces D to be a square. -/
theorem no_positive_characteristic_lift {D x y z w q : ℚ} (hD : 0<D)
    (hr : radius D x y=(5/2 : ℚ)^2) (hs : radius D z w=(24/11 : ℚ)^2)
    (hb : SquareInput D x y) (hc : SquareInput D z w)
    (hm : Matching D x y z w q) : False := by
  have hb0 := anchor_product_nonzero hD
    (by rw [hr]; norm_num) (by rw [hr]; norm_num)
  have hc0 := anchor_product_nonzero hD
    (by rw [hs]; norm_num) (by rw [hs]; norm_num)
  obtain ⟨d,hd⟩ := matching_forces_square_characteristic hb hc hb0 hc0 hm
  subst D
  apply fixed_radii_no_matching (x := x) (y := d*y) (z := z) (w := d*w)
    ?_ ?_ (characteristic_square_input hb) (characteristic_square_input hc)
    (characteristic_matching hm)
  · rw [(characteristic_norms d x y).1]
    exact hr
  · rw [(characteristic_norms d z w).1]
    exact hs

#print axioms no_positive_characteristic_lift
#print axioms first_star_axis
#print axioms second_star_zero
#print axioms residue_zero
#print axioms rational_zero
#print axioms fixed_radii_no_matching
#print axioms no_full_orientation_input
end Erdos213.ProductOrientationLocal
