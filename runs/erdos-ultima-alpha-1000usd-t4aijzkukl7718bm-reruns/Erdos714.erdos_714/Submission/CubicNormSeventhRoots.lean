import Submission.EqualRowCubicNorm

/-!
Seventh roots of unity give a constant-norm K44 in cubic extensions whenever
q is 2 or 4 modulo 7. Therefore EVERY nonempty scalar weight law has a copy
in these fields. This is a construction obstruction, not a disproof of Erdős714.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714CubicNormSeventhRoots
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]

omit [Fintype E] in
lemma cyclotomic_identity (ζ : E) (hζ : IsPrimitiveRoot ζ 7) :
    (1+ζ)*(1+ζ^2)*(1+ζ^4)=1 := by
  calc
    _ = (∑ i ∈ range 7, ζ^i)+ζ^7 := by simp only [sum_range_succ,sum_range_zero]; ring
    _ = _ := by rw [hζ.geom_sum_eq_zero (by decide),hζ.pow_eq_one,zero_add]

lemma norm_root (hd : Module.finrank F E=3)
    (hq : Fintype.card F%7=2 ∨ Fintype.card F%7=4)
    (ζ : E) (hζ : IsPrimitiveRoot ζ 7) : Algebra.norm F ζ=1 := by
  apply (algebraMap F E).injective
  rw [FiniteField.algebraMap_norm_eq_pow_sum,hd,map_one]
  simp only [sum_range_succ,sum_range_zero,pow_zero,pow_one,zero_add,Nat.card_eq_fintype_card]
  rw [pow_eq_pow_mod _ hζ.pow_eq_one]
  rcases hq with hq | hq <;> norm_num [Nat.add_mod,Nat.pow_mod,hq]

lemma norm_one_add_root (hd : Module.finrank F E=3)
    (hq : Fintype.card F%7=2 ∨ Fintype.card F%7=4)
    (ζ : E) (hζ : IsPrimitiveRoot ζ 7) : Algebra.norm F (1+ζ)=1 := by
  have hpow (x : E) : (1+x)^Fintype.card F=1+x^Fintype.card F := by
    simpa only [FiniteField.frobeniusAlgHom_apply,map_one] using
      (FiniteField.frobeniusAlgHom F E).map_add 1 x
  have hpow2 : (1+ζ)^(Fintype.card F^2)=1+ζ^(Fintype.card F^2) := by
    rw [pow_two,pow_mul,hpow,hpow,←pow_mul]
  apply (algebraMap F E).injective
  rw [FiniteField.algebraMap_norm_eq_prod_pow,hd,map_one]
  simp only [prod_range_succ,prod_range_zero,pow_zero,pow_one,one_mul,Nat.card_eq_fintype_card]
  rw [hpow,hpow2,pow_eq_pow_mod (Fintype.card F) hζ.pow_eq_one,
    pow_eq_pow_mod (Fintype.card F^2) hζ.pow_eq_one]
  rcases hq with hq | hq
  · simpa only [hq,Nat.pow_mod,Nat.reducePow,Nat.reduceMod] using cyclotomic_identity ζ hζ
  · have h := cyclotomic_identity ζ hζ
    simpa only [hq,Nat.pow_mod,Nat.reducePow,Nat.reduceMod,mul_right_comm] using h

lemma norm_power_sum (hd : Module.finrank F E=3)
    (hq : Fintype.card F%7=2 ∨ Fintype.card F%7=4)
    (ζ : E) (hζ : IsPrimitiveRoot ζ 7) (i j : ℕ) (hij : i < j) (hj : j < 7) :
    Algebra.norm F (ζ^i+ζ^j)=1 := by
  have hk0 : 0 < j-i := Nat.sub_pos_of_lt hij
  have hk7 : j-i < 7 := (Nat.sub_le j i).trans_lt hj
  have hcop : (j-i).Coprime 7 := by
    apply Nat.Coprime.symm
    exact (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 7)).mpr
      (Nat.not_dvd_of_pos_of_lt hk0 hk7)
  have he : ζ^i+ζ^j=ζ^i*(1+ζ^(j-i)) := by
    rw [mul_add,mul_one,←pow_add,Nat.add_sub_of_le hij.le]
  rw [he,map_mul,map_pow,norm_root hd hq ζ hζ,
    norm_one_add_root hd hq _ (hζ.pow_of_coprime _ hcop),one_pow,one_mul]

lemma exists_root (hd : Module.finrank F E=3)
    (hq : Fintype.card F%7=2 ∨ Fintype.card F%7=4) :
    ∃ ζ : E, IsPrimitiveRoot ζ 7 := by
  have hcard : Fintype.card E=Fintype.card F^3 := by
    rw [Module.card_eq_pow_finrank (K := F),hd]
  have hrem : (Fintype.card F^3)%7=1 := by
    rcases hq with h | h <;> norm_num [Nat.pow_mod,h]
  have hdvd : 7 ∣ Fintype.card Eˣ := by
    rw [Fintype.card_units,hcard]
    have he := Nat.mod_add_div (Fintype.card F^3) 7
    apply Nat.dvd_iff_mod_eq_zero.mpr
    omega
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card (G := Eˣ) 7 hdvd
  refine ⟨u,IsPrimitiveRoot.coe_units_iff.mpr ?_⟩
  simpa only [hu] using IsPrimitiveRoot.orderOf u

def left (ζ : E) (i : Fin 4) : E := ζ^(i : ℕ)
def right (ζ : E) (j : Fin 4) : E := if j=0 then 0 else ζ^((j : ℕ)+3)

omit [Fintype E] in
lemma left_injective (ζ : E) (hζ : IsPrimitiveRoot ζ 7) : Function.Injective (left ζ) := by
  intro i j he
  apply Fin.ext
  exact hζ.pow_inj (by omega) (by omega) he

omit [Fintype E] in
lemma right_injective (ζ : E) (hζ : IsPrimitiveRoot ζ 7) : Function.Injective (right ζ) := by
  intro i j he
  have hz : ζ ≠ 0 := hζ.ne_zero (by decide)
  by_cases hi : i=0
  · subst i
    by_cases hj : j=0
    · exact hj.symm
    · have hh : ζ^((j : ℕ)+3)=0 := by simpa [right,hj] using he.symm
      exact False.elim (pow_ne_zero _ hz hh)
  · by_cases hj : j=0
    · subst j
      have hh : ζ^((i : ℕ)+3)=0 := by simpa [right,hi] using he
      exact False.elim (pow_ne_zero _ hz hh)
    · have hp : (i : ℕ)+3=(j : ℕ)+3 := hζ.pow_inj (by omega) (by omega) (by simpa [right,hi,hj] using he)
      apply Fin.ext
      omega

lemma constant_edges (hd : Module.finrank F E=3)
    (hq : Fintype.card F%7=2 ∨ Fintype.card F%7=4)
    (ζ : E) (hζ : IsPrimitiveRoot ζ 7) (i j : Fin 4) :
    Algebra.norm F (left ζ i+right ζ j)=1 := by
  by_cases hj : j=0
  · subst j
    simp [right,left,norm_root hd hq ζ hζ]
  · have hj0 : 0 < (j : ℕ) := by have := j.isLt; have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h); omega
    simp only [right,if_neg hj,left]
    exact norm_power_sum hd hq ζ hζ _ _ (by omega) (by omega)

/-- A constant norm, independent of both endpoints, with four distinct points
on each side. No scalar-weight availability is assumed. -/
theorem exists_constant_rectangle (hd : Module.finrank F E=3)
    (hq : Fintype.card F%7=2 ∨ Fintype.card F%7=4) :
    ∃ L R : Fin 4 ↪ E, ∀ i j, Algebra.norm F (L i+R j)=1 := by
  obtain ⟨ζ,hζ⟩ := exists_root hd hq
  exact ⟨⟨left ζ,left_injective ζ hζ⟩,⟨right ζ,right_injective ζ hζ⟩,constant_edges hd hq ζ hζ⟩

/-- Any prescribed nonzero norm value is obtained by a single scaling. -/
theorem exists_constant_value (hd : Module.finrank F E=3)
    (hq : Fintype.card F%7=2 ∨ Fintype.card F%7=4) (d : F) (hd0 : d ≠ 0) :
    ∃ L R : Fin 4 ↪ E, ∀ i j, Algebra.norm F (L i+R j)=d := by
  obtain ⟨L,R,h⟩ := exists_constant_rectangle hd hq
  obtain ⟨z,hz⟩ := FiniteField.norm_surjective F E d
  have hz0 : z ≠ 0 := Algebra.norm_ne_zero_iff.mp (by rwa [hz])
  let L' : Fin 4 ↪ E := ⟨fun i => z*L i,fun i j he => L.injective (mul_left_cancel₀ hz0 he)⟩
  let R' : Fin 4 ↪ E := ⟨fun i => z*R i,fun i j he => R.injective (mul_left_cancel₀ hz0 he)⟩
  refine ⟨L',R',?_⟩
  intro i j
  change Algebra.norm F (z*L i+z*R j)=d
  rw [←mul_add,map_mul,hz,h,mul_one]

/-- In these fields a single allowed nonzero weight pair already forces K44. -/
theorem not_free_of_nonzero_value (hd : Module.finrank F E=3)
    (hq : Fintype.card F%7=2 ∨ Fintype.card F%7=4)
    {A D : Type*} (W : A → D → F) (a : A) (b : D) (hw : W a b ≠ 0) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (Erdos714EqualRowCubicNorm.graph (E := E) W) := by
  obtain ⟨L,R,h⟩ := exists_constant_value hd hq (W a b) hw
  let l : Fin 4 ↪ E × A := ⟨fun i => (L i,a),fun i j he => L.injective (congrArg Prod.fst he)⟩
  let r : Fin 4 ↪ E × D := ⟨fun j => (R j,b),fun i j he => R.injective (congrArg Prod.fst he)⟩
  have he (i j : Fin 4) : (Erdos714EqualRowCubicNorm.graph (E := E) W).Adj (.inl (l i)) (.inr (r j)) :=
    ⟨h i j,hw⟩
  intro hf
  apply hf
  refine ⟨⟨⟨l.sumMap r,?_⟩,(l.sumMap r).injective⟩⟩
  intro x y hxy
  cases x with
  | inl i => cases y with
    | inl j => simp at hxy
    | inr j => exact he i j
  | inr i => cases y with
    | inr j => simp at hxy
    | inl j => exact he j i

/-- The full point-coordinate model is free exactly when its weight law allows
no nonzero edges at all. Arbitrary label types and repeated values are allowed. -/
theorem free_iff_zero (hd : Module.finrank F E=3)
    (hq : Fintype.card F%7=2 ∨ Fintype.card F%7=4)
    {A D : Type*} (W : A → D → F) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Free (Erdos714EqualRowCubicNorm.graph (E := E) W) ↔
      ∀ a b, W a b=0 := by
  constructor
  · intro hf a b
    by_contra hw
    exact not_free_of_nonzero_value hd hq W a b hw hf
  · intro hw
    have hno (x y : (E × A) ⊕ (E × D)) :
        ¬ (Erdos714EqualRowCubicNorm.graph W).Adj x y := by
      cases x <;> cases y <;> simp [Erdos714EqualRowCubicNorm.graph,hw]
    rintro ⟨c⟩
    exact hno _ _ (c.toHom.map_adj (show (completeBipartiteGraph (Fin 4) (Fin 4)).Adj (.inl 0) (.inr 0) by simp))

#print axioms norm_root
#print axioms norm_one_add_root
#print axioms exists_root
#print axioms exists_constant_rectangle
#print axioms exists_constant_value
#print axioms not_free_of_nonzero_value
#print axioms free_iff_zero
end Erdos714CubicNormSeventhRoots
