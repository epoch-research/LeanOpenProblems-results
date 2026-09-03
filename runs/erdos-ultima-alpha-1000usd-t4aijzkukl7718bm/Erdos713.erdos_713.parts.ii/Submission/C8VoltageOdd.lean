import FormalConjecturesUtil
import Submission.C8Voltage

/-! The last-coordinate compression obstruction in odd characteristic. -/

open SimpleGraph Finset
namespace Erdos713C8VoltageOdd

section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev D (x : F) := x*(x^2-1)

def ConstantClass (c : ℤ) : Prop :=
  ∀ x : F, x ≠ 0 → x-1 ≠ 0 → x+1 ≠ 0 → quadraticChar F (D x) = c

lemma triple_value {c : ℤ} (hC : ConstantClass (F := F) c)
    (x h : F) (hh : h ≠ 0) (hx : x ≠ 0) (hm : x-h ≠ 0) (hp : x+h ≠ 0) :
    quadraticChar F (x*(x-h)*(x+h)) = quadraticChar F h * c := by
  have hsub : x/h-1 = (x-h)/h := by field_simp
  have hadd : x/h+1 = (x+h)/h := by field_simp
  have hcx := hC (x/h) (div_ne_zero hx hh)
    (hsub ▸ div_ne_zero hm hh) (hadd ▸ div_ne_zero hp hh)
  have heq : x*(x-h)*(x+h) = h^3 * D (x/h) := by
    dsimp only [D]
    field_simp
    ring
  rw [heq,map_mul,map_pow,hcx]
  have hqh := quadraticChar_sq_one hh
  rw [show quadraticChar F h ^ 3 = quadraticChar F h ^ 2 * quadraticChar F h by ring,
    hqh,one_mul]

lemma four_step {c : ℤ} (hC : ConstantClass (F := F) c) (x h : F) (hh : h ≠ 0)
    (h0 : x ≠ 0) (h1 : x+h ≠ 0) (h2 : x+2*h ≠ 0) (h3 : x+3*h ≠ 0) :
    quadraticChar F x = quadraticChar F (x+3*h) := by
  have he1 : quadraticChar F (x*(x+h)*(x+2*h)) = quadraticChar F h*c := by
    have hh' := triple_value hC (x+h) h hh h1 (by simpa using h0)
      (by convert h2 using 1 <;> ring)
    convert hh' using 1
    congr 1
    ring
  have he2 : quadraticChar F ((x+h)*(x+2*h)*(x+3*h)) = quadraticChar F h*c := by
    have hh' := triple_value hC (x+2*h) h hh h2
      (by convert h1 using 1 <;> ring) (by convert h3 using 1 <;> ring)
    convert hh' using 1
    congr 1
    ring
  have he := he1.trans he2.symm
  simp only [map_mul] at he
  have hn : quadraticChar F (x+h)*quadraticChar F (x+2*h) ≠ 0 :=
    mul_ne_zero (mt quadraticChar_eq_zero_iff.mp h1) (mt quadraticChar_eq_zero_iff.mp h2)
  apply mul_right_cancel₀ hn
  linear_combination he

lemma value_eq_of_avoids_two {c : ℤ} (hC : ConstantClass (F := F) c)
    (hThree : (3 : F) ≠ 0) (x y : F) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : 2*x+y ≠ 0) (hyx : x+2*y ≠ 0) : quadraticChar F x = quadraticChar F y := by
  by_cases heq : x = y
  · rw [heq]
  let h : F := (y-x)/3
  have hh : h ≠ 0 := div_ne_zero (sub_ne_zero.mpr (Ne.symm heq)) hThree
  have he1 : x+h = (2*x+y)/3 := by dsimp [h]; field_simp; ring
  have he2 : x+2*h = (x+2*y)/3 := by dsimp [h]; field_simp; ring
  have he3 : x+3*h = y := by dsimp [h]; field_simp; ring
  have hv := four_step hC x h hh hx (he1 ▸ div_ne_zero hxy hThree)
    (he2 ▸ div_ne_zero hyx hThree) (he3 ▸ hy)
  rwa [he3] at hv

lemma not_constant_of_three_ne_zero (hF : ringChar F ≠ 2) (hCard : 5 < Fintype.card F)
    (hThree : (3 : F) ≠ 0) (c : ℤ) : ¬ ConstantClass (F := F) c := by
  classical
  intro hC
  obtain ⟨a,ha⟩ := quadraticChar_exists_neg_one hF
  have ha0 : a ≠ 0 := by intro hh; subst a; norm_num [quadraticChar_zero] at ha
  have hTwo : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  let S : Finset F := {0,-2,-1/2,-2*a,-a/2}
  have hS : S.card ≤ 5 := by
    simpa [S] using List.toFinset_card_le [0,-2,-1/2,-2*a,-a/2]
  obtain ⟨z,_,hz⟩ := exists_mem_notMem_of_card_lt_card
    (s := S) (t := univ) (by simpa only [card_univ] using hS.trans_lt hCard)
  simp only [S,mem_insert,mem_singleton,not_or] at hz
  have he1 : quadraticChar F 1 = quadraticChar F z := by
    apply value_eq_of_avoids_two hC hThree 1 z one_ne_zero hz.1
    · intro hh
      apply hz.2.1
      linear_combination hh
    · intro hh
      apply hz.2.2.1
      apply (eq_div_iff hTwo).mpr
      linear_combination hh
  have he2 : quadraticChar F z = quadraticChar F a := by
    apply value_eq_of_avoids_two hC hThree z a hz.1 ha0
    · intro hh
      apply hz.2.2.2.2
      apply (eq_div_iff hTwo).mpr
      linear_combination hh
    · intro hh
      apply hz.2.2.2.1
      linear_combination hh
  have he := he1.trans he2
  rw [map_one,ha] at he
  norm_num at he


lemma D_ne_zero {x : F} (hx : x ≠ 0) (hm : x-1 ≠ 0) (hp : x+1 ≠ 0) : D x ≠ 0 := by
  rw [show D x = x*(x-1)*(x+1) by dsimp [D]; ring]
  exact mul_ne_zero (mul_ne_zero hx hm) hp

lemma good_of_D_ne_zero {x : F} (hx : D x ≠ 0) :
    x ≠ 0 ∧ x-1 ≠ 0 ∧ x+1 ≠ 0 := by
  rw [show D x = x*(x-1)*(x+1) by dsimp [D]; ring] at hx
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hx).1).1,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hx).1).2, (mul_ne_zero_iff.mp hx).2⟩

lemma not_constant_char_three [CharP F 3] (hCard : 9 < Fintype.card F)
    (c : ℤ) : ¬ ConstantClass (F := F) c := by
  classical
  intro hC
  have hF : ringChar F ≠ 2 := by rw [ringChar.eq F 3]; decide
  obtain ⟨a,ha⟩ := quadraticChar_exists_neg_one hF
  have ha0 : a ≠ 0 := by intro hh; subst a; norm_num [quadraticChar_zero] at ha
  let ℓ : F →+ F := (frobenius F 3).toAddMonoidHom - AddMonoidHom.id F
  have hlD (x : F) : ℓ x = D x := by simp [ℓ, frobenius_def, D]; ring
  have hClass (x : F) (hx : ℓ x ≠ 0) : quadraticChar F (ℓ x) = c := by
    rw [hlD] at hx ⊢
    obtain ⟨hx,hm,hp⟩ := good_of_D_ne_zero hx
    exact hC x hx hm hp
  let S : Finset F := {0,1,-1}
  have hRoot (x : F) (hx : ℓ x = 0) : x ∈ S := by
    rw [hlD,show D x = x*(x-1)*(x+1) by dsimp [D]; ring] at hx
    rcases mul_eq_zero.mp hx with hx | hx
    · rcases mul_eq_zero.mp hx with hx | hx
      · simp [S,hx]
      · simp [S,sub_eq_zero.mp hx]
    · have hx' : x = -1 := by linear_combination hx
      simp [S,hx']
  let L : (F × F) →+ F :=
    ℓ.comp (AddMonoidHom.fst F F) - (AddMonoidHom.mulLeft a).comp (ℓ.comp (AddMonoidHom.snd F F))
  have hKer (z : L.ker) : z.1.1 ∈ S ∧ z.1.2 ∈ S := by
    have he : ℓ z.1.1 = a * ℓ z.1.2 := sub_eq_zero.mp z.property
    have hy : ℓ z.1.2 = 0 := by
      by_contra hy
      have hx : ℓ z.1.1 ≠ 0 := by rw [he]; exact mul_ne_zero ha0 hy
      have hc2 : c^2 = 1 := by rw [← hClass _ hy]; exact quadraticChar_sq_one hy
      have hec : c = -c := by
        calc
          c = quadraticChar F (ℓ z.1.1) := (hClass _ hx).symm
          _ = quadraticChar F a * quadraticChar F (ℓ z.1.2) := by rw [he,map_mul]
          _ = -c := by rw [ha,hClass _ hy]; ring
      nlinarith
    exact ⟨hRoot _ (by rw [he,hy,mul_zero]),hRoot _ hy⟩
  have hS : S.card ≤ 3 := by simpa [S] using List.toFinset_card_le ([0,1,-1] : List F)
  letI : Fintype L.ker := Fintype.ofFinite _
  letI : Fintype L.range := Fintype.ofFinite _
  let g : L.ker → S × S := fun z => (⟨z.1.1,(hKer z).1⟩,⟨z.1.2,(hKer z).2⟩)
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z : S × S => z.1.1) hxy)
      (congrArg (fun z : S × S => z.2.1) hxy)
  have hK : Fintype.card L.ker ≤ 9 := by
    have hh := Fintype.card_le_of_injective g hg
    simp only [Fintype.card_prod,Fintype.card_coe] at hh
    nlinarith
  have hR : Fintype.card L.range ≤ Fintype.card F := Fintype.card_subtype_le _
  have hCount := L.ker.card_mul_index
  rw [AddSubgroup.index_ker] at hCount
  simp only [Nat.card_eq_fintype_card,Fintype.card_prod] at hCount
  nlinarith [Fintype.card_pos (α := F)]

lemma not_constant_large (hF : ringChar F ≠ 2) (hCard : 9 < Fintype.card F)
    (c : ℤ) : ¬ ConstantClass (F := F) c := by
  by_cases hThree : (3 : F) = 0
  · letI : CharP F 3 := (CharP.charP_iff_prime_eq_zero (by decide : Nat.Prime 3)).mpr hThree
    exact not_constant_char_three hCard c
  · exact not_constant_of_three_ne_zero hF (by omega) hThree c


lemma exists_D_class (hF : ringChar F ≠ 2) (hCard : 9 < Fintype.card F)
    (w : F) (hw : w ≠ 0) :
    ∃ x : F, x ≠ 0 ∧ x-1 ≠ 0 ∧ x+1 ≠ 0 ∧ quadraticChar F (D x) = quadraticChar F w := by
  by_contra hn
  have hC : ConstantClass (F := F) (-quadraticChar F w) := by
    intro x hx hm hp
    have hh : quadraticChar F (D x) ≠ quadraticChar F w := by
      intro heq
      exact hn ⟨x,hx,hm,hp,heq⟩
    rcases quadraticChar_dichotomy (D_ne_zero hx hm hp) with hc | hc <;>
      rcases quadraticChar_dichotomy hw with hwc | hwc <;> simp_all
  exact not_constant_large hF hCard _ hC

lemma every_nonzero_is_voltage (hF : ringChar F ≠ 2) (hCard : 9 < Fintype.card F)
    (w : F) (hw : w ≠ 0) :
    ∃ x z : F, x ≠ 0 ∧ x-1 ≠ 0 ∧ x+1 ≠ 0 ∧ z ≠ 0 ∧ D x * z^2 = w := by
  obtain ⟨x,hx,hm,hp,hClass⟩ := exists_D_class hF hCard w hw
  have hD := D_ne_zero hx hm hp
  have hSq : IsSquare (w * D x) := by
    apply (quadraticChar_one_iff_isSquare (mul_ne_zero hw hD)).mp
    rw [map_mul,hClass]
    simpa only [pow_two] using quadraticChar_sq_one hw
  obtain ⟨a,ha⟩ := hSq
  have ha0 : a ≠ 0 := by
    intro hh
    rw [hh,mul_zero] at ha
    exact mul_ne_zero hw hD ha
  refine ⟨x,a/D x,hx,hm,hp,div_ne_zero ha0 hD,?_⟩
  generalize ht : D x = t at *
  field_simp [hD]
  linear_combination -ha

lemma noninjective_contains_odd {A : Type*} [AddCommGroup A]
    (hF : ringChar F ≠ 2) (hCard : 9 < Fintype.card F)
    (f : F →+ A) (hf : ¬ Function.Injective f) :
    cycleGraph 8 ⊑ Erdos713C8Voltage.graph f := by
  have hKernel : ∃ w : F, w ≠ 0 ∧ f w = 0 := by
    by_contra hn
    apply hf
    intro x y hxy
    apply sub_eq_zero.mp
    by_contra hne
    apply hn
    refine ⟨x-y,hne,?_⟩
    rw [map_sub,hxy,sub_self]
  obtain ⟨w,hw,hfw⟩ := hKernel
  obtain ⟨x,z,hx,hm,hp,hz,he⟩ := every_nonzero_is_voltage hF hCard w hw
  apply Erdos713C8Voltage.contains_of_voltage f x 1 z hx one_ne_zero hz hm hp
  simpa only [mul_one,one_pow,D,he] using hfw

lemma noninjective_contains_large {A : Type*} [AddCommGroup A]
    (hCard : 9 < Fintype.card F) (f : F →+ A) (hf : ¬ Function.Injective f) :
    cycleGraph 8 ⊑ Erdos713C8Voltage.graph f := by
  by_cases hF : ringChar F = 2
  · letI : CharP F 2 := hF ▸ inferInstanceAs (CharP F (ringChar F))
    exact Erdos713C8Voltage.noninjective_contains_char_two f hf (by omega)
  · exact noninjective_contains_odd hF hCard f hf

#print axioms not_constant_large
#print axioms noninjective_contains_large

end
end Erdos713C8VoltageOdd
