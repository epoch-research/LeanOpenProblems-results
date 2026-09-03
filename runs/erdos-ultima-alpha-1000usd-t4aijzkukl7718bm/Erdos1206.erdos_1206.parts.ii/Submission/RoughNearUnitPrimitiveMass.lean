import Submission.RoughNearUnitConicFamily
import Submission.RoughCollisionNormalization
import Submission.PrimeBlockMass

/-!
Primitive collisions with every root coprime to a prescribed modulus, still
having gap ratios arbitrarily close to one and divergent reciprocal height
mass. This is a counting result, not a density or independence conclusion.
-/
namespace Erdos1206.RoughNearUnitPrimitiveMass
open RoughNearUnitConicFamily
open PrimitiveCollisionMass (Collision)

abbrev modulus (Q : ℕ) := 18*Q
def center (Q H : ℕ) : ℕ := 12*modulus Q*(H+1)+1
abbrev Index (Q : ℕ) := PrimeBlockMass.Index (modulus Q)
def numerator (Q : ℕ) (x : Index Q) : ℕ := 1+modulus Q*x.2.val.val
def paramS (Q H : ℕ) (x : Index Q) : ℕ := numerator Q x+12*center Q H*modulus Q*x.1.val
def paramT (Q : ℕ) (x : Index Q) : ℕ := modulus Q*x.1.val

def raw (F : ℤ → ℤ → ℤ → ℤ → ℤ) (Q H : ℕ) (x : Index Q) : ℤ :=
  F (center Q H) (modulus Q) (paramS Q H x) (paramT Q x)

lemma center_bound (Q H : ℕ) : 12*modulus Q ≤ center Q H := by
  dsimp [center]
  nlinarith

lemma raw_ordered (Q H : ℕ) (hQ : 0<Q) (x : Index Q) :
    0<raw A Q H x ∧ raw A Q H x<raw B Q H x ∧
    raw B Q H x<raw C Q H x ∧ raw C Q H x<raw D Q H x := by
  have hL : (1:ℤ) ≤ modulus Q := by dsimp [modulus]; omega
  have hm : 12*(modulus Q:ℤ) ≤ center Q H := by exact_mod_cast center_bound Q H
  have ht : (0:ℤ)<paramT Q x := by
    dsimp [paramT,modulus]
    exact_mod_cast Nat.mul_pos (by omega : 0<18*Q) x.1.property.1.pos
  have hh := ordered_int hL hm (u := (numerator Q x:ℤ)) (by positivity) ht
  simpa only [raw,paramS,paramT,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,mul_assoc] using hh

lemma raw_congruences (Q H : ℕ) (x : Index Q) :
    ((modulus Q:ℤ) ∣ raw A Q H x-18) ∧ ((modulus Q:ℤ) ∣ raw B Q H x-18) ∧
    ((modulus Q:ℤ) ∣ raw C Q H x-18) ∧ ((modulus Q:ℤ) ∣ raw D Q H x-18) := by
  have hm : 1+(18*(Q:ℤ))*(12*(H+1):ℕ)=(center Q H:ℤ) := by
    dsimp [center,modulus]
    ring
  have hs : 1+(18*(Q:ℤ))*(x.2.val.val+12*center Q H*x.1.val:ℕ)=(paramS Q H x:ℤ) := by
    dsimp [paramS,numerator,modulus]
    ring
  have hh := eighteen_congruences Q (12*(H+1)) (x.2.val.val+12*center Q H*x.1.val) x.1.val
  dsimp only at hh
  rw [hm,hs] at hh
  simpa only [raw,paramT,modulus,Nat.cast_mul,Nat.cast_ofNat] using hh

private lemma family_lift (Q H : ℕ) (hQ : 0<Q) (x : Index Q) :
    ∃ e : Collision, ∃ g : ℕ, 0<g ∧
      raw A Q H x=(18*g:ℤ)*e.val.1 ∧ raw B Q H x=(18*g:ℤ)*e.val.2.1 ∧
      raw C Q H x=(18*g:ℤ)*e.val.2.2.1 ∧ raw D Q H x=(18*g:ℤ)*e.val.2.2.2 ∧
      Nat.Coprime e.val.1 Q ∧ Nat.Coprime e.val.2.1 Q ∧
      Nat.Coprime e.val.2.2.1 Q ∧ Nat.Coprime e.val.2.2.2 Q := by
  obtain ⟨ha,hab,hbc,hcd⟩ := raw_ordered Q H hQ x
  obtain ⟨hA,hB,hC,hD⟩ := raw_congruences Q H x
  exact RoughCollisionNormalization.primitive_lift_coprime ha hab hbc hcd
    (identity _ _ _ _) hA hB hC hD

noncomputable def collision (Q H : ℕ) (hQ : 0<Q) (x : Index Q) : Collision :=
  (family_lift Q H hQ x).choose
noncomputable def scale (Q H : ℕ) (hQ : 0<Q) (x : Index Q) : ℕ :=
  (family_lift Q H hQ x).choose_spec.choose

lemma scale_spec (Q H : ℕ) (hQ : 0<Q) (x : Index Q) :
    0<scale Q H hQ x ∧
      raw A Q H x=(18*scale Q H hQ x:ℤ)*(collision Q H hQ x).val.1 ∧
      raw B Q H x=(18*scale Q H hQ x:ℤ)*(collision Q H hQ x).val.2.1 ∧
      raw C Q H x=(18*scale Q H hQ x:ℤ)*(collision Q H hQ x).val.2.2.1 ∧
      raw D Q H x=(18*scale Q H hQ x:ℤ)*(collision Q H hQ x).val.2.2.2 ∧
      Nat.Coprime (collision Q H hQ x).val.1 Q ∧ Nat.Coprime (collision Q H hQ x).val.2.1 Q ∧
      Nat.Coprime (collision Q H hQ x).val.2.2.1 Q ∧ Nat.Coprime (collision Q H hQ x).val.2.2.2 Q :=
  (family_lift Q H hQ x).choose_spec.choose_spec

lemma collision_injective (Q H : ℕ) (hQ : 0<Q) : Function.Injective (collision Q H hQ) := by
  intro x y he
  obtain ⟨hg,hA,hB,hC,hD,hcop⟩ := scale_spec Q H hQ x
  obtain ⟨hg',hA',hB',hC',hD',hcop'⟩ := scale_spec Q H hQ y
  have hrel (F : ℤ → ℤ → ℤ → ℤ → ℤ) (j : ℕ)
      (hx : raw F Q H x=(18*scale Q H hQ x:ℤ)*j)
      (hy : raw F Q H y=(18*scale Q H hQ y:ℤ)*j) :
      (scale Q H hQ y:ℤ)*raw F Q H x=(scale Q H hQ x:ℤ)*raw F Q H y := by
    rw [hx,hy]; ring
  have hAe := hrel A _ hA (by simpa [he] using hA')
  have hBe := hrel B _ hB (by simpa [he] using hB')
  have hCe := hrel C _ hC (by simpa [he] using hC')
  have hL : (0:ℚ)< modulus Q := by dsimp [modulus]; positivity
  have hm : 12*(modulus Q:ℚ) ≤ center Q H := by exact_mod_cast center_bound Q H
  have ht : (paramT Q x:ℚ) ≠ 0 := by
    have hh : 0<paramT Q x := Nat.mul_pos (by dsimp [modulus]; omega) x.1.property.1.pos
    exact_mod_cast hh.ne'
  have hh := projective_parameter hL hm
    (s := (paramS Q H x:ℚ)) (t := (paramT Q x:ℚ))
    (s' := (paramS Q H y:ℚ)) (t' := (paramT Q y:ℚ))
    (r := (scale Q H hQ y:ℚ)) (r' := (scale Q H hQ x:ℚ))
    (by exact_mod_cast hg'.ne') ht
    (by simp only [raw,A,U,RoughNearUnitConicFamily.norm,den] at hAe ⊢; exact_mod_cast hAe)
    (by simp only [raw,B,V,RoughNearUnitConicFamily.norm,den] at hBe ⊢; exact_mod_cast hBe)
    (by simp only [raw,C,U,RoughNearUnitConicFamily.norm,den] at hCe ⊢; exact_mod_cast hCe)
  have hratio : numerator Q x*y.1.val=numerator Q y*x.1.val := by
    have hQeq : (modulus Q:ℚ)*((numerator Q x:ℚ)*y.1.val-(numerator Q y:ℚ)*x.1.val)=0 := by
      simp only [paramS,paramT,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hh
      simp only [modulus,Nat.cast_mul,Nat.cast_ofNat]
      linear_combination hh
    have heq := sub_eq_zero.mp ((mul_eq_zero.mp hQeq).resolve_left hL.ne')
    exact_mod_cast heq
  have hpdiv : x.1.val ∣ y.1.val := by
    have hh : x.1.val ∣ numerator Q x*y.1.val := by rw [hratio]; exact dvd_mul_left _ _
    exact (x.1.property.1.dvd_mul.mp hh).resolve_left x.2.property
  have hp : x.1.val=y.1.val := (Nat.prime_dvd_prime_iff_eq x.1.property.1 y.1.property.1).mp hpdiv
  have hu : numerator Q x=numerator Q y := by
    have hh := (congrArg (fun p : ℕ => numerator Q x*p) hp).trans hratio
    exact Nat.eq_of_mul_eq_mul_right x.1.property.1.pos hh
  have hj : x.2.val.val=y.2.val.val := by
    dsimp [numerator] at hu
    have hh : modulus Q*x.2.val.val=modulus Q*y.2.val.val := by omega
    exact Nat.eq_of_mul_eq_mul_left (by dsimp [modulus]; omega) hh
  cases x with
  | mk p i =>
    cases y with
    | mk q j =>
      have hp' : p=q := Subtype.ext hp
      subst q
      have hij : i=j := Subtype.ext (Fin.ext hj)
      subst j
      rfl

lemma near_unit_gap (Q H : ℕ) (hQ : 0<Q) (x : Index Q) :
    H*((collision Q H hQ x).val.2.1-(collision Q H hQ x).val.1) <
      (H+1)*((collision Q H hQ x).val.2.2.2-(collision Q H hQ x).val.2.2.1) := by
  obtain ⟨hg,hA,hB,hC,hD,hcop⟩ := scale_spec Q H hQ x
  have ht : 0<paramT Q x := Nat.mul_pos (by dsimp [modulus]; omega) x.1.property.1.pos
  have hh := outside_compact_gap H (modulus Q) (numerator Q x) (paramT Q x)
    (by dsimp [modulus]; omega) ht
  dsimp only at hh
  have hm : (12*(modulus Q:ℤ)*(H+1)+1)=(center Q H:ℤ) := by simp [center]
  have hs : (numerator Q x:ℤ)+12*(center Q H:ℤ)*(paramT Q x:ℤ)=(paramS Q H x:ℤ) := by
    dsimp [paramS,paramT]
    ring
  rw [hm,hs] at hh
  change (H:ℤ)*(raw B Q H x-raw A Q H x) < (H+1)*(raw D Q H x-raw C Q H x) at hh
  rw [hA,hB,hC,hD,← mul_sub,← mul_sub] at hh
  have hgI : (0:ℤ)<18*scale Q H hQ x := by positivity
  have he := (collision Q H hQ x).property
  have hh' : (H:ℤ)*((collision Q H hQ x).val.2.1-(collision Q H hQ x).val.1) <
      (H+1)*((collision Q H hQ x).val.2.2.2-(collision Q H hQ x).val.2.2.1) := by
    nlinarith only [hh,hgI]
  rw [← Nat.cast_sub he.2.1.le,← Nat.cast_sub he.2.2.2.1.le] at hh'
  exact_mod_cast hh'

lemma numerator_bound (Q : ℕ) (x : Index Q) :
    numerator Q x ≤ (modulus Q+1)*x.1.val := by
  have hj : x.2.val.val < x.1.val := x.2.val.isLt.trans_le (Nat.div_le_self _ _)
  have hp := x.1.property.1.pos
  dsimp [numerator]
  nlinarith

lemma normalized_height_bound (Q H : ℕ) (hQ : 0<Q) :
    ∃ K : ℝ, 0<K ∧ ∀ x : Index Q,
      ((collision Q H hQ x).val.2.2.2:ℝ) ≤ K*(x.1.val:ℝ)^2 := by
  let L : ℝ := modulus Q
  let m : ℝ := center Q H
  let K : ℝ := D m L (L+1+12*m*L) L
  have hL : 1≤L := by dsimp [L,modulus]; norm_cast; omega
  have hL0 : 0<L := by linarith
  have hm : 12*L ≤ m := by
    dsimp [L,m]
    exact_mod_cast center_bound Q H
  have hm0 : 0 < m := by linarith
  have hK : 0<K := by
    have ho := ordered_real hL hm (u := L+1) (by linarith) hL0
    exact ((ho.1.trans ho.2.1).trans ho.2.2.1).trans ho.2.2.2
  refine ⟨K,hK,fun x => ?_⟩
  let p : ℝ := x.1.val
  let u : ℝ := numerator Q x
  have hp : 0<p := by dsimp [p]; exact_mod_cast x.1.property.1.pos
  have hu : 0≤u := Nat.cast_nonneg _
  have hup : u ≤ (L+1)*p := by
    have hh := numerator_bound Q x
    dsimp [u,L,p]
    exact_mod_cast hh
  have hn : 0≤RoughNearUnitConicFamily.norm m L := by
    dsimp [RoughNearUnitConicFamily.norm]
    nlinarith [sq_nonneg (2*m-3*L)]
  have hc₁ : 0≤ m-L := by linarith
  have hc₂ : 0≤6*m-10*L := by linarith
  have hupper : D m L (u+12*m*L*p) (L*p) ≤ D m L ((L+1)*p+12*m*L*p) (L*p) := by
    dsimp [D,V,den]
    gcongr
  have hdeq : D m L ((L+1)*p+12*m*L*p) (L*p)=K*p^2 := by
    dsimp [K,D,V,RoughNearUnitConicFamily.norm,den]
    ring
  obtain ⟨hg,hA,hB,hC,hD,hcop⟩ := scale_spec Q H hQ x
  have hD' : D m L (u+12*m*L*p) (L*p)=
      (18*scale Q H hQ x:ℝ)*(collision Q H hQ x).val.2.2.2 := by
    dsimp [m,L,u,p]
    simp only [raw,paramS,paramT,D,V,RoughNearUnitConicFamily.norm,den,
      Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hD ⊢
    exact_mod_cast hD
  have hg1 : (1:ℝ) ≤ 18*scale Q H hQ x := by exact_mod_cast (show 1≤18*scale Q H hQ x by omega)
  calc
    _ ≤ (18*scale Q H hQ x:ℝ)*(collision Q H hQ x).val.2.2.2 := by
      have hh := mul_le_mul_of_nonneg_right hg1
        (Nat.cast_nonneg (collision Q H hQ x).val.2.2.2)
      simpa only [one_mul] using hh
    _ = _ := hD'.symm
    _ ≤ _ := hupper
    _ = _ := hdeq

lemma index_mass_not_summable (Q H : ℕ) (hQ : 0<Q) :
    ¬ Summable (fun x : Index Q => (1:ℝ)/(collision Q H hQ x).val.2.2.2) := by
  obtain ⟨K,hK,hbound⟩ := normalized_height_bound Q H hQ
  apply PrimeBlockMass.good_height_not_summable (modulus Q) _ _ K hK hbound
  intro x
  have he := (collision Q H hQ x).property
  exact ((he.1.trans he.2.1).trans he.2.2.1).trans he.2.2.2.1

/-- The small-gap residual source, now with all four roots coprime to Q. -/
abbrev Residual (Q H : ℕ) := {e : Collision //
  H*(e.val.2.1-e.val.1) < (H+1)*(e.val.2.2.2-e.val.2.2.1) ∧
  Nat.Coprime e.val.1 Q ∧ Nat.Coprime e.val.2.1 Q ∧
  Nat.Coprime e.val.2.2.1 Q ∧ Nat.Coprime e.val.2.2.2 Q}

/-- No fixed finite-prime sieve restores per-collision reciprocal summability
outside a compact gap interval. This does not rule out reusable covers. -/
theorem residual_reciprocal_heights_not_summable (Q H : ℕ) (hQ : 0<Q) :
    ¬ Summable (fun e : Residual Q H => (1:ℝ)/e.val.val.2.2.2) := by
  intro hs
  let f : Index Q → Residual Q H := fun x => ⟨collision Q H hQ x,
    near_unit_gap Q H hQ x,(scale_spec Q H hQ x).2.2.2.2.2⟩
  have hf : Function.Injective f := by
    intro x y he
    have hh : (f x).val=(f y).val := congrArg (fun e : Residual Q H => e.val) he
    exact collision_injective Q H hQ hh
  have hcomp := hs.comp_injective hf
  exact index_mass_not_summable Q H hQ hcomp

#print axioms raw_congruences
#print axioms collision_injective
#print axioms near_unit_gap
#print axioms normalized_height_bound
#print axioms index_mass_not_summable
#print axioms residual_reciprocal_heights_not_summable
end Erdos1206.RoughNearUnitPrimitiveMass
