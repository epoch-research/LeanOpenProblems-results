import FormalConjecturesUtil

/-! An elementary fourth-moment route to a Kloosterman-sum bound over a
finite field. This module does not assert a prime-factor density theorem. -/
namespace Erdos371.Kloosterman
open Finset

section Algebra
variable {F : Type*} [Field F]

lemma inverse_pair_collision (x y z w : Fˣ)
    (hs : (x:F)+(y:F)=(z:F)+(w:F))
    (hi : (x:F)⁻¹+(y:F)⁻¹=(z:F)⁻¹+(w:F)⁻¹)
    (hn : (x:F)+(y:F)≠0) :
    (z=x ∧ w=y) ∨ (z=y ∧ w=x) := by
  have hprod : (x:F)*(y:F)=(z:F)*(w:F) := by
    rw [inv_add_inv (Units.ne_zero x) (Units.ne_zero y),
      inv_add_inv (Units.ne_zero z) (Units.ne_zero w),← hs] at hi
    simp only [div_eq_mul_inv] at hi
    exact inv_injective (mul_left_cancel₀ hn hi)
  have hroot : ((z:F)-(x:F))*((z:F)-(y:F))=0 := by
    linear_combination -(z:F)*hs+hprod
  rcases mul_eq_zero.mp hroot with hz | hz
  · have hz' : z=x := Units.ext (sub_eq_zero.mp hz)
    subst z
    exact Or.inl ⟨rfl,Units.ext (by linear_combination -hs)⟩
  · have hz' : z=y := Units.ext (sub_eq_zero.mp hz)
    subst z
    exact Or.inr ⟨rfl,Units.ext (by linear_combination -hs)⟩

lemma units_add_eq_zero_iff (x y : Fˣ) : (x:F)+(y:F)=0 ↔ y= -x := by
  constructor
  · intro h
    apply Units.ext
    change (y:F)= -(x:F)
    linear_combination h
  · intro h
    subst y
    simp
end Algebra

section Energy
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def collisionCount (x y : Fˣ) : ℕ :=
  (univ.filter fun zw : Fˣ×Fˣ =>
    (x:F)+(y:F)=(zw.1:F)+(zw.2:F) ∧
    (x:F)⁻¹+(y:F)⁻¹=(zw.1:F)⁻¹+(zw.2:F)⁻¹).card

lemma collisionCount_nonzero (x y : Fˣ) (hn : (x:F)+(y:F)≠0) :
    collisionCount x y≤2 := by
  classical
  have hsub : (univ.filter fun zw : Fˣ×Fˣ =>
      (x:F)+(y:F)=(zw.1:F)+(zw.2:F) ∧
      (x:F)⁻¹+(y:F)⁻¹=(zw.1:F)⁻¹+(zw.2:F)⁻¹) ⊆ {(x,y),(y,x)} := by
    intro zw hz
    have hh := (mem_filter.mp hz).2
    rcases inverse_pair_collision x y zw.1 zw.2 hh.1 hh.2 hn with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · simp [h1,h2,Prod.ext_iff]
    · simp [h1,h2,Prod.ext_iff]
  exact (card_le_card hsub).trans ((card_insert_le _ _).trans (by simp))

lemma collisionCount_zero (x y : Fˣ) (hz : (x:F)+(y:F)=0) :
    collisionCount x y≤Fintype.card Fˣ := by
  classical
  unfold collisionCount
  apply (card_le_card_of_injOn (t := (univ : Finset Fˣ)) Prod.fst
    (by intro a ha; simp) ?_).trans_eq card_univ
  intro a ha b hb he
  have ha' := (mem_filter.mp ha).2.1
  have hb' := (mem_filter.mp hb).2.1
  have ha'' : a.2= -a.1 := (units_add_eq_zero_iff _ _).mp (ha'.symm.trans hz)
  have hb'' : b.2= -b.1 := (units_add_eq_zero_iff _ _).mp (hb'.symm.trans hz)
  exact Prod.ext he (by simpa only [ha'',hb''] using congrArg Neg.neg he)

/-- The inverse curve has additive energy at most three times the square
of its cardinality. The zero-sum fibers are counted separately. -/
theorem inverse_curve_energy_bound :
    (∑ x : Fˣ, ∑ y : Fˣ, collisionCount x y) ≤ 3*(Fintype.card Fˣ)^2 := by
  classical
  have ht (x y : Fˣ) : collisionCount x y≤2+(if (x:F)+(y:F)=0 then Fintype.card Fˣ else 0) := by
    by_cases h : (x:F)+(y:F)=0
    · rw [if_pos h]; exact (collisionCount_zero x y h).trans (by omega)
    · rw [if_neg h,add_zero]; exact collisionCount_nonzero x y h
  calc
    _ ≤ ∑ x : Fˣ, ∑ y : Fˣ, (2+(if (x:F)+(y:F)=0 then Fintype.card Fˣ else 0)) :=
      sum_le_sum fun x _ => sum_le_sum fun y _ => ht x y
    _ = _ := by
      simp only [sum_add_distrib,units_add_eq_zero_iff,sum_ite_eq',mem_univ,if_true,
        sum_const,card_univ,smul_eq_mul]
      ring
end Energy

section Fourier
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (ψ : AddChar F ℂ)

lemma character_orthogonality (hψ : ψ.IsPrimitive) (u v : F) :
    (∑ a : F, ∑ b : F, ψ (a*u+b*v)) =
      if u=0 ∧ v=0 then (Fintype.card F : ℂ)^2 else 0 := by
  classical
  simp only [AddChar.map_add_eq_mul,← mul_sum,← sum_mul,AddChar.sum_mulShift _ hψ]
  split_ifs <;> simp_all [sq]

omit [DecidableEq F] in
lemma norm_square_sum_character {ι : Type*} [Fintype ι] (h : ι → F) :
    ((‖∑ x, ψ (h x)‖^2 : ℝ) : ℂ) =
      ∑ x : ι, ∑ y : ι, ψ (h x-h y) := by
  rw [Complex.sq_norm,← Complex.mul_conj,map_sum,sum_mul_sum]
  apply sum_congr rfl
  intro x hx
  apply sum_congr rfl
  intro y hy
  rw [sub_eq_add_neg,AddChar.map_add_eq_mul,AddChar.map_neg_eq_conj]

set_option maxHeartbeats 2000000 in
/-- Orthogonality for an arbitrary finite parametrized curve in F squared. -/
theorem curve_parseval {ι : Type*} [Fintype ι] (hψ : ψ.IsPrimitive)
    (f g : ι → F) :
    (∑ a : F, ∑ b : F, ‖∑ x : ι, ψ (a*f x+b*g x)‖^2) =
      (Fintype.card F : ℝ)^2 *
        (∑ x : ι, ∑ y : ι, if f x=f y ∧ g x=g y then (1 : ℝ) else 0) := by
  classical
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum,Complex.ofReal_mul]
  simp_rw [norm_square_sum_character]
  have hp (a b : F) (x y : ι) :
      ψ ((a*f x+b*g x)-(a*f y+b*g y)) = ψ (a*(f x-f y)+b*(g x-g y)) := by
    congr 1; ring
  simp_rw [hp]
  have hs : (∑ a : F, ∑ b : F, ∑ x : ι, ∑ y : ι, ψ (a*(f x-f y)+b*(g x-g y))) =
      ∑ x : ι, ∑ y : ι, ∑ a : F, ∑ b : F, ψ (a*(f x-f y)+b*(g x-g y)) := by
    simpa only [Fintype.sum_prod_type] using
      (sum_comm (s := (univ : Finset (F×F))) (t := (univ : Finset (ι×ι)))
        (f := fun ab xy => ψ (ab.1*(f xy.1-f xy.2)+ab.2*(g xy.1-g xy.2))))
  rw [hs]
  simp_rw [character_orthogonality ψ hψ,sub_eq_zero]
  push_cast
  simp only [mul_sum]
  apply sum_congr rfl
  intro x hx
  apply sum_congr rfl
  intro y hy
  split_ifs <;> simp_all
end Fourier

section Kloosterman
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def kloostermanSum (ψ : AddChar F ℂ) (a b : F) : ℂ :=
  ∑ x : Fˣ, ψ (a*(x:F)+b*(x:F)⁻¹)

lemma kloostermanSum_square (ψ : AddChar F ℂ) (a b : F) :
    (kloostermanSum ψ a b)^2 =
      ∑ xy : Fˣ×Fˣ, ψ (a*((xy.1:F)+(xy.2:F))+b*((xy.1:F)⁻¹+(xy.2:F)⁻¹)) := by
  rw [pow_two,kloostermanSum,sum_mul_sum,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro x hx
  apply sum_congr rfl
  intro y hy
  rw [← AddChar.map_add_eq_mul]
  congr 1; ring

lemma kloosterman_norm_fourth (ψ : AddChar F ℂ) (a b : F) :
    ‖kloostermanSum ψ a b‖^4 =
      ‖∑ xy : Fˣ×Fˣ, ψ (a*((xy.1:F)+(xy.2:F))+b*((xy.1:F)⁻¹+(xy.2:F)⁻¹))‖^2 := by
  rw [← kloostermanSum_square,norm_pow]
  ring

/-- The complete fourth moment is the additive energy of the inverse curve. -/
theorem kloosterman_fourth_moment (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    (∑ a : F, ∑ b : F, ‖kloostermanSum ψ a b‖^4) =
      (Fintype.card F : ℝ)^2 * (∑ x : Fˣ, ∑ y : Fˣ, (collisionCount x y : ℝ)) := by
  simp_rw [kloosterman_norm_fourth]
  rw [curve_parseval ψ hψ]
  congr 1
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro x hx
  apply sum_congr rfl
  intro y hy
  simp only [collisionCount,sum_boole]

lemma kloosterman_fourth_moment_bound (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    (∑ a : F, ∑ b : F, ‖kloostermanSum ψ a b‖^4) ≤
      3*(Fintype.card F : ℝ)^2*(Fintype.card Fˣ : ℝ)^2 := by
  rw [kloosterman_fourth_moment ψ hψ]
  have he : (∑ x : Fˣ, ∑ y : Fˣ, (collisionCount x y : ℝ))≤3*(Fintype.card Fˣ : ℝ)^2 := by
    exact_mod_cast (inverse_curve_energy_bound (F := F))
  calc
    _ ≤ (Fintype.card F : ℝ)^2*(3*(Fintype.card Fˣ : ℝ)^2) :=
      mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = _ := by ring

/-- Multiplicative change of variables gives a full orbit of equal Fourier
coefficients. This orbit is what turns the complete fourth moment into a
pointwise estimate. -/
lemma kloostermanSum_scale (ψ : AddChar F ℂ) (a b : F) (t : Fˣ) :
    kloostermanSum ψ (a*(t:F)) (b/(t:F))=kloostermanSum ψ a b := by
  unfold kloostermanSum
  apply Fintype.sum_equiv (Equiv.mulLeft t)
  intro x
  change ψ ((a*(t:F))*(x:F)+(b/(t:F))*(x:F)⁻¹) =
    ψ (a*((t:F)*(x:F))+b*((t:F)*(x:F))⁻¹)
  simp only [mul_inv_rev,div_eq_mul_inv]
  congr 1; ring

lemma kloosterman_orbit_lower (ψ : AddChar F ℂ) (a b : F) (ha : a≠0) :
    (Fintype.card Fˣ : ℝ)*‖kloostermanSum ψ a b‖^4 ≤
      ∑ c : F, ∑ d : F, ‖kloostermanSum ψ c d‖^4 := by
  classical
  let orb : Fˣ → F×F := fun t => (a*(t:F),b/(t:F))
  have hinj : Function.Injective orb := by
    intro t u he
    apply Units.ext
    exact mul_left_cancel₀ ha (congrArg Prod.fst he)
  have hsub : (univ.image orb) ⊆ (univ : Finset (F×F)) := subset_univ _
  have hb := sum_le_sum_of_subset_of_nonneg (f := fun cd : F×F => ‖kloostermanSum ψ cd.1 cd.2‖^4)
    hsub (by intros; positivity)
  rw [sum_image hinj.injOn,Fintype.sum_prod_type] at hb
  simpa only [orb,kloostermanSum_scale,sum_const,card_univ,nsmul_eq_mul] using hb

/-- Elementary Kloosterman bound, obtained without the Weil bound.
The nontrivial saving is a fourth power bounded by O(q cubed). -/
theorem kloosterman_norm_fourth_le (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (a b : F) (ha : a≠0) :
    ‖kloostermanSum ψ a b‖^4 ≤ 3*(Fintype.card F : ℝ)^3 := by
  have hm : (0 : ℝ)<Fintype.card Fˣ := by exact_mod_cast (Fintype.card_pos (α := Fˣ))
  have h := (kloosterman_orbit_lower ψ a b ha).trans (kloosterman_fourth_moment_bound ψ hψ)
  have hdiv : ‖kloostermanSum ψ a b‖^4 ≤ 3*(Fintype.card F : ℝ)^2*(Fintype.card Fˣ : ℝ) := by
    nlinarith
  have hcard : (Fintype.card Fˣ : ℝ)≤Fintype.card F := by
    exact_mod_cast Fintype.card_le_of_injective (fun x : Fˣ => (x:F)) Units.val_injective
  calc
    _ ≤ 3*(Fintype.card F : ℝ)^2*(Fintype.card Fˣ : ℝ) := hdiv
    _ ≤ 3*(Fintype.card F : ℝ)^2*(Fintype.card F : ℝ) := by gcongr
    _ = _ := by ring
lemma kloostermanSum_swap (ψ : AddChar F ℂ) (a b : F) :
    kloostermanSum ψ a b=kloostermanSum ψ b a := by
  unfold kloostermanSum
  apply Fintype.sum_equiv (Equiv.inv Fˣ)
  intro x
  change ψ (a*(x:F)+b*(x:F)⁻¹)=ψ (b*((x⁻¹:Fˣ):F)+a*((x⁻¹:Fˣ):F)⁻¹)
  simp only [Units.val_inv_eq_inv_val,inv_inv,add_comm]

lemma kloosterman_norm_fourth_le_nonzero (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (a b : F) (hab : a≠0 ∨ b≠0) :
    ‖kloostermanSum ψ a b‖^4 ≤ 3*(Fintype.card F : ℝ)^3 := by
  rcases hab with ha | hb
  · exact kloosterman_norm_fourth_le ψ hψ a b ha
  · rw [kloostermanSum_swap]
    exact kloosterman_norm_fourth_le ψ hψ b a hb

lemma kloosterman_norm_bound (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (a b : F) (hab : a≠0 ∨ b≠0) :
    ‖kloostermanSum ψ a b‖ ≤ Real.sqrt (Real.sqrt (3*(Fintype.card F : ℝ)^3)) := by
  apply Real.le_sqrt_of_sq_le
  apply Real.le_sqrt_of_sq_le
  simpa only [← pow_mul] using kloosterman_norm_fourth_le_nonzero ψ hψ a b hab

/-- Uniform normalized cancellation at every nonzero Fourier frequency.
The right side tends to zero with the cardinality of the field. -/
theorem kloosterman_normalized_bound (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (a b : F) (hab : a≠0 ∨ b≠0) :
    ‖kloostermanSum ψ a b‖ / Fintype.card F ≤
      Real.sqrt (Real.sqrt (3/(Fintype.card F : ℝ))) := by
  have hq : (0 : ℝ)<Fintype.card F := by exact_mod_cast (Fintype.card_pos (α := F))
  have h := kloosterman_norm_fourth_le_nonzero ψ hψ a b hab
  apply Real.le_sqrt_of_sq_le
  apply Real.le_sqrt_of_sq_le
  rw [← pow_mul,div_pow]
  apply (div_le_iff₀ (pow_pos hq 4)).mpr
  convert h using 1
  field_simp

/-- Specialization to the standard prime-modulus additive character. -/
theorem prime_kloosterman_normalized_bound (p : ℕ) [Fact p.Prime]
    (a b : ZMod p) (hab : a≠0 ∨ b≠0) :
    ‖kloostermanSum ZMod.stdAddChar a b‖/(p : ℝ) ≤
      Real.sqrt (Real.sqrt (3/(p : ℝ))) := by
  simpa only [ZMod.card] using kloosterman_normalized_bound ZMod.stdAddChar
    (ZMod.isPrimitive_stdAddChar p) a b hab

open Filter in
/-- The saving is uniform in the moving nonzero frequencies along any
sequence of prime moduli tending to infinity. -/
theorem prime_kloosterman_normalized_tendsto (p : ℕ → ℕ)
    [∀ n, Fact (p n).Prime] (hp : Tendsto p atTop atTop)
    (a b : (n : ℕ) → ZMod (p n)) (hab : ∀ n, a n≠0 ∨ b n≠0) :
    Tendsto (fun n => ‖kloostermanSum ZMod.stdAddChar (a n) (b n)‖/(p n : ℝ))
      atTop (nhds 0) := by
  have ht := (((tendsto_const_div_atTop_nhds_zero_nat (3 : ℝ)).comp hp).sqrt).sqrt
  simp only [Real.sqrt_zero] at ht
  exact squeeze_zero (fun n => by positivity)
    (fun n => prime_kloosterman_normalized_bound (p n) (a n) (b n) (hab n)) ht

end Kloosterman

#print axioms inverse_curve_energy_bound
#print axioms curve_parseval
#print axioms kloosterman_fourth_moment
#print axioms kloosterman_norm_fourth_le
#print axioms kloosterman_normalized_bound
#print axioms prime_kloosterman_normalized_bound
#print axioms prime_kloosterman_normalized_tendsto

end Erdos371.Kloosterman
