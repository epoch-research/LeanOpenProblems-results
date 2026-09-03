import Submission.CubeCollisionGrowth

/-!
A family of strict cubic collisions whose middle roots lie at arbitrarily
separated multiplicative scales. These auxiliary arithmetic results are not
a proof or disproof of the positive-density conjecture.
-/
set_option maxHeartbeats 1000000

namespace Erdos1206.SeparatedConicFamily
open Finset Filter
open scoped Classical
open PrimitiveCollisionMass CubeCollisionGrowth

def A (r u v : ℤ) : ℤ := (r^6-1)*u^2-6*r^3*u*v-3*v^2
def B (r u v : ℤ) : ℤ := (r^6-1)*u^2+6*r^3*u*v-3*v^2
def C (r u v : ℤ) : ℤ := r*(r^6-1)*u^2-6*r*u*v+3*r*v^2
def D (r u v : ℤ) : ℤ := r*(r^6-1)*u^2+6*r*u*v+3*r*v^2

lemma identity (r u v : ℤ) : A r u v ^ 3 + D r u v ^ 3 = B r u v ^ 3 + C r u v ^ 3 := by
  dsimp [A,B,C,D]
  ring

lemma inverse_identities (r u v : ℤ) :
    C r u v + D r u v-r*(A r u v+B r u v) = 12*r*v^2 ∧
    D r u v-C r u v = 12*r*u*v := by
  dsimp [A,B,C,D]
  constructor <;> ring

lemma ordered_and_separated {r u v : ℤ} (hr : 3 ≤ r) (hv : 0 < v) (hvu : v ≤ u) :
    0 < A r u v ∧ A r u v < B r u v ∧ B r u v < C r u v ∧
      C r u v < D r u v ∧ r*B r u v < 2*C r u v := by
  have hu : 0 < u := hv.trans_le hvu
  have hR : 27 ≤ r^3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℤ) ≤ 3) hr 3]
  have hR6 : r^6 = (r^3)^2 := by ring
  have hcoef : 0 < r^6-6*r^3-13 := by rw [hR6]; nlinarith
  have huv : 0 < u*v := mul_pos hu hv
  have hvu' : u*v ≤ u^2 := by nlinarith
  have hv2 : v^2 ≤ u^2 := by nlinarith
  have hu2 : 0 < u^2 := sq_pos_of_pos hu
  have hRA : 6*r^3*(u*v) ≤ 6*r^3*u^2 :=
    mul_le_mul_of_nonneg_left hvu' (by positivity)
  have hA : 0 < A r u v := by
    have hh := mul_pos hcoef hu2
    dsimp [A]
    nlinarith
  have hAB : A r u v < B r u v := by
    have hh := mul_pos (show 0 < 12*r^3 by positivity) huv
    dsimp [A,B]
    nlinarith
  have hsep : r*B r u v < 2*C r u v := by
    have hh := mul_pos hcoef hu2
    have hmul := mul_le_mul_of_nonneg_left hvu' (show 0 ≤ 6*r^3+12 by positivity)
    have hp : 0 < (r^6-1)*u^2-(6*r^3+12)*u*v+9*v^2 := by
      nlinarith [sq_nonneg v]
    have hp' := mul_pos (show 0 < r by omega) hp
    dsimp [B,C]
    nlinarith only [hp']
  have hB : 0 < B r u v := hA.trans hAB
  have hBC : B r u v < C r u v := by nlinarith
  have hCD : C r u v < D r u v := by
    have hh := mul_pos (show 0 < 12*r by omega) huv
    dsimp [C,D]
    nlinarith
  exact ⟨hA,hAB,hBC,hCD,hsep⟩

lemma height_bound {r u v : ℤ} (hr : 3 ≤ r) (hv : 0 < v) (hvu : v ≤ u) :
    D r u v ≤ r*(r^6+8)*u^2 := by
  have hu : 0 < u := hv.trans_le hvu
  have hvu' : u*v ≤ u^2 := by nlinarith
  have hv2 : v^2 ≤ u^2 := by nlinarith
  have h₁ := mul_le_mul_of_nonneg_left hvu' (show 0 ≤ 6*r by omega)
  have h₂ := mul_le_mul_of_nonneg_left hv2 (show 0 ≤ 3*r by omega)
  dsimp [D]
  nlinarith


/-- Divide a strict positive integer collision by its four-coordinate gcd. -/
lemma normalize_collision {a b c d : ℕ} (ha : 0<a) (hab : a<b) (hbc : b<c)
    (hcd : c<d) (hid : a^3+d^3=b^3+c^3) :
    ∃ e : Collision, ∃ g : ℕ, 0<g ∧
      a=g*e.val.1 ∧ b=g*e.val.2.1 ∧ c=g*e.val.2.2.1 ∧ d=g*e.val.2.2.2 := by
  let g := Nat.gcd (Nat.gcd a b) (Nat.gcd c d)
  have hg : 0<g := Nat.gcd_pos_of_pos_left _ (Nat.gcd_pos_of_pos_left _ ha)
  have hga : g ∣ a := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have hgb : g ∣ b := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have hgc : g ∣ c := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  have hgd : g ∣ d := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  obtain ⟨a',ha'⟩ := hga
  obtain ⟨b',hb'⟩ := hgb
  obtain ⟨c',hc'⟩ := hgc
  obtain ⟨d',hd'⟩ := hgd
  have hprim : Nat.gcd (Nat.gcd a' b') (Nat.gcd c' d') = 1 := by
    have hh : g = g * Nat.gcd (Nat.gcd a' b') (Nat.gcd c' d') := by
      conv_lhs => dsimp [g]; rw [ha',hb',hc',hd',Nat.gcd_mul_left,Nat.gcd_mul_left,Nat.gcd_mul_left]
    exact (Nat.eq_of_mul_eq_mul_left hg (by simpa using hh)).symm
  have heq : a'^3+d'^3=b'^3+c'^3 := by
    rw [ha',hb',hc',hd',mul_pow,mul_pow,mul_pow,mul_pow,← mul_add,← mul_add] at hid
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hg _) hid
  refine ⟨⟨(a',b',c',d'), ?_, ?_, ?_, ?_, heq, hprim⟩,g,hg,ha',hb',hc',hd'⟩
  · rw [ha'] at ha
    exact Nat.pos_of_mul_pos_left ha
  · rw [ha',hb'] at hab
    exact (Nat.mul_lt_mul_left hg).mp hab
  · rw [hb',hc'] at hbc
    exact (Nat.mul_lt_mul_left hg).mp hbc
  · rw [hc',hd'] at hcd
    exact (Nat.mul_lt_mul_left hg).mp hcd

lemma family_normalization {r u v : ℕ} (hr : 3≤r) (hv : 0<v) (hvu : v≤u) :
    ∃ e : Collision, ∃ g : ℕ, 0<g ∧
      A r u v=(g:ℤ)*e.val.1 ∧ B r u v=(g:ℤ)*e.val.2.1 ∧
      C r u v=(g:ℤ)*e.val.2.2.1 ∧ D r u v=(g:ℤ)*e.val.2.2.2 := by
  obtain ⟨ha,hab,hbc,hcd,_⟩ := ordered_and_separated (r := (r:ℤ)) (u := (u:ℤ)) (v := (v:ℤ))
    (by exact_mod_cast hr) (by exact_mod_cast hv) (by exact_mod_cast hvu)
  have hna : ((A r u v).toNat:ℤ)=A r u v := Int.toNat_of_nonneg ha.le
  have hnb : ((B r u v).toNat:ℤ)=B r u v := Int.toNat_of_nonneg (ha.trans hab).le
  have hnc : ((C r u v).toNat:ℤ)=C r u v := Int.toNat_of_nonneg (ha.trans (hab.trans hbc)).le
  have hnd : ((D r u v).toNat:ℤ)=D r u v := Int.toNat_of_nonneg (ha.trans (hab.trans (hbc.trans hcd))).le
  obtain ⟨e,g,hg,h₁,h₂,h₃,h₄⟩ := normalize_collision
    (a := (A r u v).toNat) (b := (B r u v).toNat) (c := (C r u v).toNat)
    (d := (D r u v).toNat)
    (by exact_mod_cast (hna ▸ ha))
    (by exact_mod_cast (show ((A r u v).toNat:ℤ)<(B r u v).toNat by simpa only [hna,hnb] using hab))
    (by exact_mod_cast (show ((B r u v).toNat:ℤ)<(C r u v).toNat by simpa only [hnb,hnc] using hbc))
    (by exact_mod_cast (show ((C r u v).toNat:ℤ)<(D r u v).toNat by simpa only [hnc,hnd] using hcd))
    (by exact_mod_cast (show ((A r u v).toNat:ℤ)^3+(D r u v).toNat^3=
        (B r u v).toNat^3+(C r u v).toNat^3 by
      simpa only [hna,hnb,hnc,hnd] using identity (r:ℤ) u v))
  refine ⟨e,g,hg,?_,?_,?_,?_⟩
  · rw [← hna]; exact_mod_cast h₁
  · rw [← hnb]; exact_mod_cast h₂
  · rw [← hnc]; exact_mod_cast h₃
  · rw [← hnd]; exact_mod_cast h₄

abbrev Index := (p : PrimitiveCollisionMass.LargePrime) × Fin (p.val-1)

noncomputable def point (r : ℕ) (hr : 3≤r) (x : Index) : Collision :=
  (family_normalization (r := r) (u := x.1.val) (v := x.2.val+1)
    hr (by omega) (by have := x.2.isLt; omega)).choose

lemma point_certificate (r : ℕ) (hr : 3≤r) (x : Index) :
    ∃ g : ℕ, 0<g ∧
      A r x.1.val (x.2.val+1)=(g:ℤ)*(point r hr x).val.1 ∧
      B r x.1.val (x.2.val+1)=(g:ℤ)*(point r hr x).val.2.1 ∧
      C r x.1.val (x.2.val+1)=(g:ℤ)*(point r hr x).val.2.2.1 ∧
      D r x.1.val (x.2.val+1)=(g:ℤ)*(point r hr x).val.2.2.2 :=
  (family_normalization (r := r) (u := x.1.val) (v := x.2.val+1)
    hr (by omega) (by have := x.2.isLt; omega)).choose_spec

lemma point_ratio (r : ℕ) (hr : 3≤r) (x : Index) :
    (x.1.val:ℤ) * ((point r hr x).val.2.2.1 + (point r hr x).val.2.2.2 -
      r*((point r hr x).val.1 + (point r hr x).val.2.1)) =
    (x.2.val+1:ℕ) * ((point r hr x).val.2.2.2 - (point r hr x).val.2.2.1 : ℤ) := by
  obtain ⟨g,hg,ha,hb,hc,hd⟩ := point_certificate r hr x
  obtain ⟨hi,hj⟩ := inverse_identities (r:ℤ) x.1.val (x.2.val+1)
  simp only [ha,hb,hc,hd] at hi hj
  have hi' := congrArg (fun z:ℤ => (x.1.val:ℤ)*z) hi
  have hj' := congrArg (fun z:ℤ => ((x.2.val+1:ℕ):ℤ)*z) hj
  apply mul_left_cancel₀ (by exact_mod_cast (show g≠0 by omega) : (g:ℤ)≠0)
  push_cast at hi' hj' ⊢
  nlinarith only [hi',hj']

lemma point_injective (r : ℕ) (hr : 3≤r) : Function.Injective (point r hr) := by
  intro x y hxy
  have hx := point_ratio r hr x
  have hy := point_ratio r hr y
  rw [hxy] at hx
  have hx' := congrArg (fun z:ℤ => (y.1.val:ℤ)*z) hx
  have hy' := congrArg (fun z:ℤ => (x.1.val:ℤ)*z) hy
  have hdel : (0:ℤ) < (point r hr y).val.2.2.2 - (point r hr y).val.2.2.1 := by
    have := (point r hr y).property.2.2.2.1
    omega
  have heZ : (y.1.val:ℤ)*(x.2.val+1:ℕ)=(x.1.val:ℤ)*(y.2.val+1:ℕ) := by
    apply mul_right_cancel₀ hdel.ne'
    nlinarith only [hx',hy']
  have he : y.1.val*(x.2.val+1)=x.1.val*(y.2.val+1) := by exact_mod_cast heZ
  have hxv : x.2.val+1<x.1.val := by have := x.2.isLt; omega
  have hd : x.1.val ∣ y.1.val := by
    have hh : x.1.val ∣ y.1.val*(x.2.val+1) := he ▸ dvd_mul_right x.1.val (y.2.val+1)
    exact (x.1.property.1.dvd_mul.mp hh).resolve_right (by
      intro hd
      have := Nat.le_of_dvd (by omega : 0<x.2.val+1) hd
      omega)
  have hp : x.1.val=y.1.val := (Nat.prime_dvd_prime_iff_eq x.1.property.1 y.1.property.1).mp hd
  have hv : x.2.val=y.2.val := by
    have he' := he.trans (congrArg (fun z => z*(y.2.val+1)) hp)
    have := Nat.eq_of_mul_eq_mul_left y.1.property.1.pos he'
    omega
  cases x with | mk p j =>
    cases y with | mk q l =>
      have hpq : p=q := Subtype.ext hp
      subst q
      have hjl : j=l := Fin.ext hv
      subst l
      rfl

lemma point_height_bound (r : ℕ) (hr : 3≤r) (x : Index) :
    (point r hr x).val.2.2.2 ≤ r*(r^6+8)*x.1.val^2 := by
  obtain ⟨g,hg,ha,hb,hc,hd⟩ := point_certificate r hr x
  have hv : (0:ℤ)<(x.2.val+1:ℕ) := by positivity
  have hvu : ((x.2.val+1:ℕ):ℤ)≤x.1.val := by have := x.2.isLt; omega
  have hh := height_bound (r := (r:ℤ)) (by exact_mod_cast hr) hv hvu
  push_cast at hh
  rw [hd] at hh
  have hmul : (point r hr x).val.2.2.2 ≤ g*(point r hr x).val.2.2.2 :=
    Nat.le_mul_of_pos_left _ hg
  have hbnd : g*(point r hr x).val.2.2.2 ≤ r*(r^6+8)*x.1.val^2 := by exact_mod_cast hh
  exact hmul.trans hbnd


lemma point_separated (K : ℕ) (x : Index) :
    K*(point (2*K+3) (by omega) x).val.2.1 <
      (point (2*K+3) (by omega) x).val.2.2.1 := by
  let r := 2*K+3
  have hr : 3≤r := by dsimp [r]; omega
  obtain ⟨g,hg,ha,hb,hc,hd⟩ := point_certificate r hr x
  have hh := (ordered_and_separated (r := (r:ℤ)) (u := x.1.val) (v := x.2.val+1)
    (by exact_mod_cast hr) (by positivity) (by have := x.2.isLt; omega)).2.2.2.2
  rw [hb,hc] at hh
  have hgZ : (0:ℤ)<g := by exact_mod_cast hg
  have hs : (r:ℤ)*(point r hr x).val.2.1 < 2*(point r hr x).val.2.2.1 := by
    apply (mul_lt_mul_iff_right₀ hgZ).mp
    nlinarith only [hh]
  have hbp : 0<(point r hr x).val.2.1 :=
    (point r hr x).property.1.trans (point r hr x).property.2.1
  have hbpZ : (0:ℤ)<(point r hr x).val.2.1 := by exact_mod_cast hbp
  have hrZ : (r:ℤ)=2*K+3 := by simp [r]
  change K*(point r hr x).val.2.1 < (point r hr x).val.2.2.1
  have hz : (K:ℤ)*(point r hr x).val.2.1 < (point r hr x).val.2.2.1 := by
    rw [hrZ] at hs
    nlinarith
  exact_mod_cast hz

abbrev SeparatedCollision (K : ℕ) :=
  {e : Collision // K*e.val.2.1 < e.val.2.2.1}

noncomputable def separatedPoint (K : ℕ) (x : Index) : SeparatedCollision K :=
  ⟨point (2*K+3) (by omega) x, point_separated K x⟩

lemma separatedPoint_injective (K : ℕ) : Function.Injective (separatedPoint K) := by
  intro x y he
  exact point_injective (2*K+3) (by omega) (congrArg Subtype.val he)

lemma index_reciprocals_not_summable (r : ℕ) (hr : 3≤r) :
    ¬ Summable (fun x : Index => (1:ℝ)/(point r hr x).val.2.2.2) := by
  let L : ℝ := r*(r^6+8)
  have hL : 0<L := by dsimp [L]; positivity
  have hblock (p : PrimitiveCollisionMass.LargePrime) :
      1/(2*L*(p.val:ℝ)) ≤ ∑ j : Fin (p.val-1), (1:ℝ)/(point r hr ⟨p,j⟩).val.2.2.2 := by
    have hp : (0:ℝ)<p.val := by exact_mod_cast p.property.1.pos
    have hpc : (p.val:ℝ) ≤ 2*(p.val-1:ℕ) := by
      exact_mod_cast (show p.val ≤ 2*(p.val-1) by have := p.property.2; omega)
    calc
      _ ≤ ((p.val-1:ℕ):ℝ)/(L*(p.val:ℝ)^2) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        have hh := mul_le_mul_of_nonneg_right hpc (show 0≤L*(p.val:ℝ) by positivity)
        nlinarith
      _ = ∑ _j : Fin (p.val-1), (1:ℝ)/(L*(p.val:ℝ)^2) := by simp [div_eq_mul_inv]
      _ ≤ _ := by
        apply sum_le_sum
        intro j hj
        have hb : ((point r hr ⟨p,j⟩).val.2.2.2:ℝ) ≤ L*(p.val:ℝ)^2 := by
          dsimp [L]
          exact_mod_cast point_height_bound r hr ⟨p,j⟩
        have hd : (0:ℝ)<(point r hr ⟨p,j⟩).val.2.2.2 := by
          exact_mod_cast primitive_height_pos (point r hr ⟨p,j⟩)
        exact one_div_le_one_div_of_le hd hb
  intro hs
  have hblocks := ((summable_sigma_of_nonneg
    (fun x : Index => (by positivity : (0:ℝ)≤1/(point r hr x).val.2.2.2))).mp hs).2
  have hsum : Summable (fun p : PrimitiveCollisionMass.LargePrime =>
      ∑ j : Fin (p.val-1), (1:ℝ)/(point r hr ⟨p,j⟩).val.2.2.2) := by
    simpa only [tsum_fintype] using hblocks
  have hsmall : Summable (fun p : PrimitiveCollisionMass.LargePrime => 1/(2*L*(p.val:ℝ))) :=
    hsum.of_nonneg_of_le (fun _ => by positivity) hblock
  apply PrimitiveCollisionMass.large_prime_reciprocals_not_summable
  convert hsmall.mul_left (2*L) using 1
  funext p
  have hp : (p.val:ℝ)≠0 := by exact_mod_cast p.property.1.ne_zero
  field_simp

/-- Arbitrarily separated middle-root scales still have divergent primitive
reciprocal-height mass. -/
theorem separated_reciprocals_not_summable (K : ℕ) :
    ¬ Summable (fun e : SeparatedCollision K => (1:ℝ)/e.val.val.2.2.2) := by
  intro hs
  have hh := hs.comp_injective (separatedPoint_injective K)
  exact index_reciprocals_not_summable (2*K+3) (by omega) hh

noncomputable def separatedCollisionsUpTo (K N : ℕ) : Finset Quad :=
  (collisionsUpTo N).filter (fun x => K*x.2.1 < x.2.2.1)

lemma finite_separated_dilate_count {K : ℕ} (F : Finset (SeparatedCollision K)) (N : ℕ) :
    ∑ e ∈ F, N/e.val.val.2.2.2 ≤ (separatedCollisionsUpTo K N).card := by
  let S := F.sigma (fun e => Icc 1 (N/e.val.val.2.2.2))
  let f : ((e : SeparatedCollision K) × ℕ) → Quad := fun z => dilate z.2 z.1.val.val
  have hf : Set.InjOn f (S : Set ((e : SeparatedCollision K) × ℕ)) := by
    intro x hx y hy hxy
    have hqx : 0<x.2 := (mem_Icc.mp (mem_sigma.mp hx).2).1
    obtain ⟨he,hq⟩ := primitive_dilate_injective hqx hxy
    have he' : x.1=y.1 := Subtype.ext he
    cases x with | mk e q =>
      cases y with | mk e' q' =>
        dsimp only at he' hq
        subst e' q'
        rfl
  have hsub : S.image f ⊆ separatedCollisionsUpTo K N := by
    intro x hx
    obtain ⟨⟨e,q⟩,hz,rfl⟩ := mem_image.mp hx
    have hq := mem_Icc.mp (mem_sigma.mp hz).2
    apply mem_filter.mpr
    constructor
    · apply dilate_mem_collisionsUpTo e.val hq.1
      exact (Nat.mul_le_mul_right _ hq.2).trans (Nat.div_mul_le_self N _)
    · have hh := Nat.mul_lt_mul_of_pos_left e.property hq.1
      simpa only [f,dilate,Nat.mul_left_comm] using hh
  have hh := card_le_card hsub
  rw [card_image_of_injOn hf] at hh
  simpa [S,card_sigma] using hh

lemma finite_separated_reciprocal_bound {K : ℕ} (F : Finset (SeparatedCollision K)) (N : ℕ) :
    (N:ℝ)*(∑ e ∈ F, (1:ℝ)/e.val.val.2.2.2) ≤
      ((separatedCollisionsUpTo K N).card:ℝ)+F.card := by
  have hterm (e : SeparatedCollision K) :
      (N:ℝ)/e.val.val.2.2.2 ≤ ((N/e.val.val.2.2.2:ℕ):ℝ)+1 := by
    have he : (0:ℝ)<e.val.val.2.2.2 := by exact_mod_cast primitive_height_pos e.val
    apply (div_le_iff₀ he).mpr
    have hh := Nat.lt_mul_div_succ N (primitive_height_pos e.val)
    have hh' : (N:ℝ)<e.val.val.2.2.2*(((N/e.val.val.2.2.2:ℕ):ℝ)+1) := by exact_mod_cast hh
    nlinarith
  have hc : (∑ e ∈ F, ((N/e.val.val.2.2.2:ℕ):ℝ)) ≤
      ((separatedCollisionsUpTo K N).card:ℝ) := by exact_mod_cast finite_separated_dilate_count F N
  calc
    _ = ∑ e ∈ F, (N:ℝ)/e.val.val.2.2.2 := by simp [mul_sum,div_eq_mul_inv]
    _ ≤ ∑ e ∈ F, (((N/e.val.val.2.2.2:ℕ):ℝ)+1) := sum_le_sum fun e _ => hterm e
    _ = (∑ e ∈ F, ((N/e.val.val.2.2.2:ℕ):ℝ))+F.card := by simp [sum_add_distrib]
    _ ≤ _ := by linarith

/-- Even after requiring `K*b<c` in the ordered collision `a<b<c<d`,
no linear full-prefix collision bound is possible. This does not give an
independence-density bound. -/
theorem separated_collision_count_superlinear (K : ℕ) (C : ℝ) :
    ∃ M : ℕ, ∀ N ≥ M, C*N < ((separatedCollisionsUpTo K N).card:ℝ) := by
  have hF : ∃ F : Finset (SeparatedCollision K),
      C+1 < ∑ e ∈ F, (1:ℝ)/e.val.val.2.2.2 := by
    by_contra! h
    exact separated_reciprocals_not_summable K (summable_of_sum_le (fun _ => by positivity) h)
  obtain ⟨F,hF⟩ := hF
  refine ⟨F.card+1,fun N hN => ?_⟩
  have hNpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hFN : (F.card:ℝ)≤N := by exact_mod_cast (show F.card≤N by omega)
  have hm := mul_lt_mul_of_pos_left hF hNpos
  have hb := finite_separated_reciprocal_bound F N
  nlinarith

#print axioms separated_reciprocals_not_summable
#print axioms separated_collision_count_superlinear
end Erdos1206.SeparatedConicFamily
