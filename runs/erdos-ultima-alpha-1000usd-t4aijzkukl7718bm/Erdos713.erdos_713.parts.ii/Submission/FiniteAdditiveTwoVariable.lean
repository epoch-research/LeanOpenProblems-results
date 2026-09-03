import FormalConjecturesUtil

/-! Elementary surjectivity and nonzero-coordinate lemmas for finite
characteristic-two fields. These are auxiliary algebraic results. -/
namespace Erdos713FiniteAdditiveTwoVariable
variable {K : Type*} [Field K]
set_option maxHeartbeats 2000000

lemma nonzero_first [Finite K] (P Q : K →+ K) (hQ : ∃ z, Q z ≠ 0)
    (hF : Function.Surjective (fun v : K × K => P v.1 + Q v.2)) (w : K) :
    ∃ h z : K, h ≠ 0 ∧ P h + Q z = w := by
  obtain ⟨⟨h,z⟩,he⟩ := hF w
  by_cases hh : h ≠ 0
  · exact ⟨h,z,hh,he⟩
  have hh : h = 0 := not_ne_iff.mp hh
  subst h
  have he : Q z = w := by simpa using he
  by_cases hP : Function.Injective P
  · obtain ⟨v,hv⟩ := hQ
    obtain ⟨u,hu⟩ := Finite.surjective_of_injective hP (-Q v)
    have hu0 : u ≠ 0 := by
      intro h
      rw [h,map_zero] at hu
      exact hv (neg_eq_zero.mp hu.symm)
    refine ⟨u,z+v,hu0,?_⟩
    rw [map_add,hu,he]
    ring
  · obtain ⟨x,y,hxy,hne⟩ := Function.not_injective_iff.mp hP
    refine ⟨x-y,z,sub_ne_zero.mpr hne,?_⟩
    rw [map_sub,hxy,sub_self,zero_add,he]

lemma square_surjective [Finite K] [CharP K 2] :
    Function.Surjective (fun x : K => x^2) :=
  Finite.surjective_of_injective (frobenius_inj K 2)

lemma fourth_surjective [Finite K] [CharP K 2] :
    Function.Surjective (fun x : K => x^4) := by
  intro w
  obtain ⟨a,ha⟩ := square_surjective w
  obtain ⟨b,hb⟩ := square_surjective a
  dsimp only at ha hb
  exact ⟨b,by calc b^4 = (b^2)^2 := by ring
                  _ = w := by rw [hb,ha]⟩

abbrev determinant (A B C δ : K) := δ^4*A^3+B^6*C^4*(A+C^2)

/-- Cancellation eliminates the quartic and linear terms simultaneously.
No trace or classification of finite fields is needed. -/
lemma quartic_pair_surjective [Finite K] [CharP K 2] (A B C δ : K)
    (hdet : determinant A B C δ ≠ 0) :
    Function.Surjective (fun v : K × K => A*v.1^4+B*C*v.1^2+
      v.2^4+B*v.2^2+δ*v.2) := by
  intro w
  by_cases hA : A = 0
  · have hBC : B*C ≠ 0 := by
      intro h
      rcases mul_eq_zero.mp h with h | h <;> simp [determinant,hA,h] at hdet
    obtain ⟨h,hh⟩ := square_surjective (w/(B*C))
    refine ⟨(h,0),?_⟩
    simp only [hA,zero_mul,zero_pow (by decide : 4 ≠ 0),
      zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero,zero_add,hh]
    exact mul_div_cancel₀ w hBC
  obtain ⟨a,ha⟩ := square_surjective A
  dsimp only at ha
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha; exact hA ha.symm
  by_cases hBC : B*C = 0
  · obtain ⟨h,hh⟩ := fourth_surjective (w/A)
    refine ⟨(h,0),?_⟩
    simp only [hBC,zero_mul,zero_pow (by decide : 4 ≠ 0),
      zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero,hh]
    exact mul_div_cancel₀ w hA
  have hB : B ≠ 0 := (mul_ne_zero_iff.mp hBC).1
  have hC : C ≠ 0 := (mul_ne_zero_iff.mp hBC).2
  let L := A*(δ/(B*C))^2+B*C/a+B
  have hLid : L^2*(A*B^4*C^4) = determinant A B C δ := by
    dsimp [L,determinant]
    rw [← ha]
    rw [CharTwo.add_sq,CharTwo.add_sq]
    field_simp
    ring
  have hL : L ≠ 0 := by
    intro he
    rw [he,zero_pow (by decide : 2 ≠ 0),zero_mul] at hLid
    exact hdet hLid.symm
  obtain ⟨z,hz⟩ := square_surjective (w/L)
  obtain ⟨h,hh⟩ := square_surjective (z^2/a+δ/(B*C)*z)
  dsimp only at hh hz
  refine ⟨(h,z),?_⟩
  change A*h^4+B*C*h^2+z^4+B*z^2+δ*z = w
  have h4 : h^4 = (h^2)^2 := by ring
  calc
    _ = L*z^2 := by
      rw [h4,hh,CharTwo.add_sq]
      dsimp [L]
      rw [← ha]
      field_simp
      ring_nf
      reduce_mod_char!
    _ = w := by rw [hz]; exact mul_div_cancel₀ w hL

lemma fourth_add [CharP K 2] (x y : K) : (x+y)^4 = x^4+y^4 := by
  have h (z : K) : z^4 = (z^2)^2 := by ring
  simp only [h,CharTwo.add_sq]

/-- Above four field elements, a solution can be required to have a nonzero
first coordinate. This avoids any appeal to asymptotic or numerical counting. -/
lemma quartic_pair_solve_nonzero [Fintype K] [CharP K 2] (A B C δ w : K)
    (hdet : determinant A B C δ ≠ 0) (hq : 4 < Fintype.card K) :
    ∃ h z : K, h ≠ 0 ∧ A*h^4+B*C*h^2+z^4+B*z^2+δ*z = w := by
  let P : K →+ K :=
    { toFun := fun x => A*x^4+B*C*x^2
      map_zero' := by simp
      map_add' := by intro x y; rw [fourth_add,CharTwo.add_sq]; ring }
  let Q : K →+ K :=
    { toFun := fun z => z^4+B*z^2+δ*z
      map_zero' := by simp
      map_add' := by intro x y; rw [fourth_add,CharTwo.add_sq]; ring }
  have hQ : ∃ z, Q z ≠ 0 := by
    let p : Polynomial K := Polynomial.X^4+Polynomial.C B*Polynomial.X^2+
      Polynomial.C δ*Polynomial.X
    have hd : p.natDegree = 4 := by dsimp [p]; compute_degree <;> norm_num
    have hp : p ≠ 0 := by
      intro he
      rw [he,Polynomial.natDegree_zero] at hd
      omega
    by_contra! he
    apply hp
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p Function.injective_id
    · intro z
      simpa [p,Q] using he z
    · omega
  have hF : Function.Surjective (fun v : K × K => P v.1+Q v.2) := by
    simpa only [P,Q,AddMonoidHom.coe_mk,ZeroHom.coe_mk,add_assoc] using
      quartic_pair_surjective A B C δ hdet
  obtain ⟨h,z,hh,he⟩ := nonzero_first P Q hQ hF w
  exact ⟨h,z,hh,by simpa only [P,Q,AddMonoidHom.coe_mk,ZeroHom.coe_mk,add_assoc] using he⟩

#print axioms nonzero_first
#print axioms quartic_pair_surjective
#print axioms quartic_pair_solve_nonzero
end Erdos713FiniteAdditiveTwoVariable
