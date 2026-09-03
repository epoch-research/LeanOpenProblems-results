import Submission.NearUnitConicFamily
import Submission.PrimitiveCollisionMass

/-! Distinct primitive collisions have divergent reciprocal height mass even
below any fixed compact gap-ratio cutoff. This concerns per-collision cost,
not reusable divisor covers or the original density conjecture. -/
namespace Erdos1206.NearUnitPrimitiveMass
open NearUnitConicFamily
open PrimitiveCollisionMass (Collision Index index_t_lt LargePrime large_prime_reciprocals_not_summable)

lemma primitive_lift {a b c d : ℤ}
    (ha : 0<a) (hab : a<b) (hbc : b<c) (hcd : c<d)
    (he : a^3+d^3=b^3+c^3) :
    ∃ e : Collision, ∃ g : ℕ, 0<g ∧
      a=(g:ℤ)*e.val.1 ∧ b=(g:ℤ)*e.val.2.1 ∧
      c=(g:ℤ)*e.val.2.2.1 ∧ d=(g:ℤ)*e.val.2.2.2 := by
  let a₀ := a.toNat
  let b₀ := b.toNat
  let c₀ := c.toNat
  let d₀ := d.toNat
  have ha₀ : (a₀:ℤ)=a := Int.toNat_of_nonneg ha.le
  have hb₀ : (b₀:ℤ)=b := Int.toNat_of_nonneg (ha.trans hab).le
  have hc₀ : (c₀:ℤ)=c := Int.toNat_of_nonneg ((ha.trans hab).trans hbc).le
  have hd₀ : (d₀:ℤ)=d := Int.toNat_of_nonneg (((ha.trans hab).trans hbc).trans hcd).le
  have ha₀pos : 0<a₀ := by omega
  let g := Nat.gcd (Nat.gcd a₀ b₀) (Nat.gcd c₀ d₀)
  have hg : 0<g := Nat.gcd_pos_of_pos_left _ (Nat.gcd_pos_of_pos_left _ ha₀pos)
  have hga : g ∣ a₀ := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have hgb : g ∣ b₀ := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have hgc : g ∣ c₀ := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  have hgd : g ∣ d₀ := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  obtain ⟨a',ha'⟩ := hga
  obtain ⟨b',hb'⟩ := hgb
  obtain ⟨c',hc'⟩ := hgc
  obtain ⟨d',hd'⟩ := hgd
  have haI : a=(g:ℤ)*a' := by rw [← ha₀,ha']; simp
  have hbI : b=(g:ℤ)*b' := by rw [← hb₀,hb']; simp
  have hcI : c=(g:ℤ)*c' := by rw [← hc₀,hc']; simp
  have hdI : d=(g:ℤ)*d' := by rw [← hd₀,hd']; simp
  have hgI : (0:ℤ)<g := by exact_mod_cast hg
  have hapos : 0<a' := by
    have hh := ha
    rw [haI] at hh
    have hh' := pos_of_mul_pos_right hh hgI.le
    exact_mod_cast hh'
  have hab' : a'<b' := by
    rw [haI,hbI] at hab
    exact_mod_cast (mul_lt_mul_iff_right₀ hgI).mp hab
  have hbc' : b'<c' := by
    rw [hbI,hcI] at hbc
    exact_mod_cast (mul_lt_mul_iff_right₀ hgI).mp hbc
  have hcd' : c'<d' := by
    rw [hcI,hdI] at hcd
    exact_mod_cast (mul_lt_mul_iff_right₀ hgI).mp hcd
  have he' : a'^3+d'^3=b'^3+c'^3 := by
    rw [haI,hbI,hcI,hdI] at he
    simp only [mul_pow,← mul_add] at he
    exact_mod_cast mul_left_cancel₀ (pow_ne_zero 3 hgI.ne') he
  have hp : Nat.gcd (Nat.gcd a' b') (Nat.gcd c' d')=1 := by
    have hh : g*1=g*Nat.gcd (Nat.gcd a' b') (Nat.gcd c' d') := by
      calc
        _ = Nat.gcd (Nat.gcd a₀ b₀) (Nat.gcd c₀ d₀) := by simp [g]
        _ = _ := by rw [ha',hb',hc',hd',Nat.gcd_mul_left,Nat.gcd_mul_left,Nat.gcd_mul_left]
    exact (Nat.eq_of_mul_eq_mul_left hg hh).symm
  exact ⟨⟨(a',b',c',d'),hapos,hab',hbc',hcd',he',hp⟩,g,hg,haI,hbI,hcI,hdI⟩

private lemma family_lift (k : ℕ) (x : Index) :
    ∃ e : Collision, ∃ g : ℕ, 0<g ∧
      A ((k:ℤ)+12) (6*x.2.val+1+12*((k:ℤ)+12)*x.1.val) x.1.val=(g:ℤ)*e.val.1 ∧
      B ((k:ℤ)+12) (6*x.2.val+1+12*((k:ℤ)+12)*x.1.val) x.1.val=(g:ℤ)*e.val.2.1 ∧
      C ((k:ℤ)+12) (6*x.2.val+1+12*((k:ℤ)+12)*x.1.val) x.1.val=(g:ℤ)*e.val.2.2.1 ∧
      D ((k:ℤ)+12) (6*x.2.val+1+12*((k:ℤ)+12)*x.1.val) x.1.val=(g:ℤ)*e.val.2.2.2 := by
  have hord := ordered k (6*x.2.val+1) x.1.val x.1.property.1.pos
  push_cast at hord
  exact primitive_lift hord.1 hord.2.1 hord.2.2.1 hord.2.2.2 (identity _ _ _)

noncomputable def collision (k : ℕ) (x : Index) : Collision := (family_lift k x).choose
noncomputable def scale (k : ℕ) (x : Index) : ℕ := (family_lift k x).choose_spec.choose

lemma scale_spec (k : ℕ) (x : Index) :
    0<scale k x ∧
      A ((k:ℤ)+12) (6*x.2.val+1+12*((k:ℤ)+12)*x.1.val) x.1.val=(scale k x:ℤ)*(collision k x).val.1 ∧
      B ((k:ℤ)+12) (6*x.2.val+1+12*((k:ℤ)+12)*x.1.val) x.1.val=(scale k x:ℤ)*(collision k x).val.2.1 ∧
      C ((k:ℤ)+12) (6*x.2.val+1+12*((k:ℤ)+12)*x.1.val) x.1.val=(scale k x:ℤ)*(collision k x).val.2.2.1 ∧
      D ((k:ℤ)+12) (6*x.2.val+1+12*((k:ℤ)+12)*x.1.val) x.1.val=(scale k x:ℤ)*(collision k x).val.2.2.2 :=
  (family_lift k x).choose_spec.choose_spec

/-- Common-factor cancellation does not merge distinct prime-denominator
parameters. No bound on the cancellation factor is assumed. -/
theorem collision_injective (k : ℕ) : Function.Injective (collision k) := by
  intro x y he
  obtain ⟨hg,hA,hB,hC,hD⟩ := scale_spec k x
  obtain ⟨hg',hA',hB',hC',hD'⟩ := scale_spec k y
  have hrel (F : ℤ → ℤ → ℤ → ℤ) (j : ℕ)
      (hx : F ((k:ℤ)+12) (6*x.2.val+1+12*((k:ℤ)+12)*x.1.val) x.1.val=(scale k x:ℤ)*j)
      (hy : F ((k:ℤ)+12) (6*y.2.val+1+12*((k:ℤ)+12)*y.1.val) y.1.val=(scale k y:ℤ)*j) :
      (scale k y:ℤ)*F ((k:ℤ)+12) (6*x.2.val+1+12*((k:ℤ)+12)*x.1.val) x.1.val=
        (scale k x:ℤ)*F ((k:ℤ)+12) (6*y.2.val+1+12*((k:ℤ)+12)*y.1.val) y.1.val := by
    rw [hx,hy]; ring
  have hAeq := hrel A _ hA (by simpa [he] using hA')
  have hBeq := hrel B _ hB (by simpa [he] using hB')
  have hCeq := hrel C _ hC (by simpa [he] using hC')
  have hh := projective_parameter (m := (k:ℚ)+12)
    (r := (scale k y:ℚ)) (r' := (scale k x:ℚ))
    (s := 6*x.2.val+1+12*((k:ℚ)+12)*x.1.val) (t := (x.1.val:ℚ))
    (s' := 6*y.2.val+1+12*((k:ℚ)+12)*y.1.val) (t' := (y.1.val:ℚ))
    (by have hk : (0:ℚ) ≤ k := Nat.cast_nonneg k; linarith) (by exact_mod_cast hg'.ne') (by exact_mod_cast x.1.property.1.ne_zero)
    (by simp only [A,U,NearUnitConicFamily.norm,den] at hAeq ⊢; exact_mod_cast hAeq)
    (by simp only [B,V,NearUnitConicFamily.norm,den] at hBeq ⊢; exact_mod_cast hBeq)
    (by simp only [C,U,NearUnitConicFamily.norm,den] at hCeq ⊢; exact_mod_cast hCeq)
  have hratio : (6*x.2.val+1)*y.1.val=(6*y.2.val+1)*x.1.val := by
    have hQ : (6*(x.2.val:ℚ)+1)*y.1.val=(6*(y.2.val:ℚ)+1)*x.1.val := by
      linear_combination hh
    exact_mod_cast hQ
  have hpdiv : x.1.val ∣ y.1.val := by
    have hh : x.1.val ∣ (6*x.2.val+1)*y.1.val := by rw [hratio]; exact dvd_mul_left _ _
    rcases x.1.property.1.dvd_mul.mp hh with h | h
    · have hb := index_t_lt x
      have hh := Nat.le_of_dvd (by omega : 0<6*x.2.val+1) h
      omega
    · exact h
  have hp : x.1.val=y.1.val := (Nat.prime_dvd_prime_iff_eq x.1.property.1 y.1.property.1).mp hpdiv
  have hj : x.2.val=y.2.val := by
    have heq := (congrArg (fun p : ℕ => (6*x.2.val+1)*p) hp).trans hratio
    have hh := Nat.eq_of_mul_eq_mul_right x.1.property.1.pos heq
    omega
  cases x with
  | mk p i =>
    cases y with
    | mk q j =>
      have hp' : p=q := Subtype.ext hp
      subst q
      have hij : i=j := Fin.ext hj
      subst j
      rfl

lemma near_unit_gap (H : ℕ) (x : Index) :
    H*((collision (12*H) x).val.2.1-(collision (12*H) x).val.1) <
      (H+1)*((collision (12*H) x).val.2.2.2-(collision (12*H) x).val.2.2.1) := by
  obtain ⟨hg,hA,hB,hC,hD⟩ := scale_spec (12*H) x
  have hh := outside_compact_gap H (6*x.2.val+1) x.1.val x.1.property.1.pos
  dsimp only at hh
  push_cast at hA hB hC hD hh
  rw [hA,hB,hC,hD] at hh
  have hgI : (0:ℤ)<scale (12*H) x := by exact_mod_cast hg
  have he := (collision (12*H) x).property
  have hlow := he.2.1.le
  have hupp := he.2.2.2.1.le
  rw [← mul_sub,← mul_sub] at hh
  have hh' : (H:ℤ)*((collision (12*H) x).val.2.1-(collision (12*H) x).val.1) <
      (H+1)*((collision (12*H) x).val.2.2.2-(collision (12*H) x).val.2.2.1) := by
    nlinarith only [hh,hgI]
  rw [← Nat.cast_sub hlow,← Nat.cast_sub hupp] at hh'
  exact_mod_cast hh'

/-- A quadratic upper height bound is retained after normalization. -/
lemma normalized_height_bound (k : ℕ) : ∃ K : ℝ, 0<K ∧ ∀ x : Index,
    ((collision k x).val.2.2.2:ℝ) ≤ K*(x.1.val:ℝ)^2 := by
  let K : ℝ := D ((k:ℝ)+12) (1+12*((k:ℝ)+12)) 1
  have hord := ordered k 1 1 (by decide)
  have hKD : (0:ℤ) < D ((k:ℤ)+12) (1+12*((k:ℤ)+12)) 1 := by
    simpa using ((hord.1.trans hord.2.1).trans hord.2.2.1).trans hord.2.2.2
  have hK : 0<K := by
    dsimp [K,D,V,NearUnitConicFamily.norm,den]
    simp only [D,V,NearUnitConicFamily.norm,den] at hKD
    exact_mod_cast hKD
  refine ⟨K,hK,fun x => ?_⟩
  let p := x.1.val
  let u := 6*x.2.val+1
  have hup : (u:ℝ) ≤ p := by exact_mod_cast (index_t_lt x).le
  have hu0 : (0:ℝ) ≤ u := Nat.cast_nonneg u
  have hp0 : (0:ℝ) ≤ p := Nat.cast_nonneg p
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hupper : D ((k:ℝ)+12) ((u:ℝ)+12*((k:ℝ)+12)*p) p ≤
      D ((k:ℝ)+12) ((p:ℝ)+12*((k:ℝ)+12)*p) p := by
    have hn : (0:ℝ) ≤ NearUnitConicFamily.norm ((k:ℝ)+12) := by
      dsimp [NearUnitConicFamily.norm]
      nlinarith
    have hc₁ : (0:ℝ) ≤ (k:ℝ)+12-1 := by linarith
    have hc₂ : (0:ℝ) ≤ 6*((k:ℝ)+12)-10 := by linarith
    dsimp [D,V,den]
    gcongr
  have hdeq : D ((k:ℝ)+12) ((p:ℝ)+12*((k:ℝ)+12)*p) p=K*(p:ℝ)^2 := by
    dsimp [K,D,V,NearUnitConicFamily.norm,den]
    ring
  obtain ⟨hg,hA,hB,hC,hD⟩ := scale_spec k x
  have hD' : D ((k:ℝ)+12) ((u:ℝ)+12*((k:ℝ)+12)*p) p=
      (scale k x:ℝ)*(collision k x).val.2.2.2 := by
    dsimp [u,p]
    simp only [D,V,NearUnitConicFamily.norm,den] at hD ⊢
    exact_mod_cast hD
  have hg1 : (1:ℝ) ≤ scale k x := by exact_mod_cast hg
  calc
    _ ≤ (scale k x:ℝ)*(collision k x).val.2.2.2 := by
      have hh := mul_le_mul_of_nonneg_right hg1
        (Nat.cast_nonneg (collision k x).val.2.2.2)
      simpa only [one_mul] using hh
    _ = _ := hD'.symm
    _ ≤ _ := hupper
    _ = _ := hdeq

lemma index_mass_not_summable (k : ℕ) :
    ¬ Summable (fun x : Index => (1:ℝ)/(collision k x).val.2.2.2) := by
  intro hs
  obtain ⟨K,hK,hbound⟩ := normalized_height_bound k
  let block : LargePrime → ℝ := fun p => ∑ j : Fin (p.val/12),
    (1:ℝ)/(collision k (⟨p,j⟩:Index)).val.2.2.2
  have hblocks := ((summable_sigma_of_nonneg
    (fun x : Index => (by positivity : (0:ℝ) ≤ 1/(collision k x).val.2.2.2))).mp hs).2
  have hsum : Summable block := by simpa only [block,tsum_fintype] using hblocks
  have hlower (p : LargePrime) : (1:ℝ)/(24*K*p.val) ≤ block p := by
    have hp : (0:ℝ)<p.val := by exact_mod_cast p.property.1.pos
    have hc : (p.val:ℝ) ≤ 24*(p.val/12:ℕ) := by
      exact_mod_cast (show p.val ≤ 24*(p.val/12) by have := p.property.2; omega)
    calc
      _ ≤ ((p.val/12:ℕ):ℝ)/(K*(p.val:ℝ)^2) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith [mul_le_mul_of_nonneg_right hc (show (0:ℝ) ≤ K*p.val by positivity)]
      _ = ∑ _j : Fin (p.val/12), (1:ℝ)/(K*(p.val:ℝ)^2) := by simp [div_eq_mul_inv]
      _ ≤ block p := by
        apply Finset.sum_le_sum
        intro j hj
        have he := (collision k (⟨p,j⟩:Index)).property
        have hp' : 0 < (collision k (⟨p,j⟩:Index)).val.2.2.2 :=
          ((he.1.trans he.2.1).trans he.2.2.1).trans he.2.2.2.1
        exact one_div_le_one_div_of_le (by exact_mod_cast hp') (hbound _)
  have hsmall : Summable (fun p : LargePrime => (1:ℝ)/(24*K*p.val)) :=
    hsum.of_nonneg_of_le (fun _ => by positivity) hlower
  apply large_prime_reciprocals_not_summable
  convert hsmall.mul_left (24*K) using 1
  funext p
  have hp : (p.val:ℝ) ≠ 0 := by exact_mod_cast p.property.1.ne_zero
  field_simp

/-- The residual primitive collisions with gap ratio below `1+1/H`. -/
abbrev Residual (H : ℕ) := {e : Collision //
  H*(e.val.2.1-e.val.1) < (H+1)*(e.val.2.2.2-e.val.2.2.1)}

/-- Removing any compact gap interval still leaves divergent per-collision
reciprocal height mass. Reusable divisors or colorings are NOT ruled out. -/
theorem residual_reciprocal_heights_not_summable (H : ℕ) :
    ¬ Summable (fun e : Residual H => (1:ℝ)/e.val.val.2.2.2) := by
  intro hs
  let f : Index → Residual H := fun x => ⟨collision (12*H) x,near_unit_gap H x⟩
  have hf : Function.Injective f := by
    intro x y he
    have hh : (f x).val=(f y).val := congrArg (fun e : Residual H => e.val) he
    exact collision_injective (12*H) hh
  have hcomp := hs.comp_injective hf
  exact index_mass_not_summable (12*H) hcomp

#print axioms collision_injective
#print axioms near_unit_gap
#print axioms normalized_height_bound
#print axioms index_mass_not_summable
#print axioms residual_reciprocal_heights_not_summable
end Erdos1206.NearUnitPrimitiveMass
