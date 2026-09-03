import FormalConjecturesUtil

/-! Independent finite control for the direct prefix search. This repeated
cover CONTAINS modulus3 and cannot instantiate the no-three lifting input. -/
namespace Erdos7TwofoldPrefixControl
set_option autoImplicit false
set_option maxHeartbeats 1500000

def modulus : Fin 14 → ℕ := ![3,3,5,5,7,7,35,35,21,21,15,15,105,105]
def residue : Fin 14 → ℤ := ![0,1,0,1,0,1,17,32,5,20,8,14,2,2]

lemma finite_data :
    (∀ i,1 < modulus i ∧ Odd (modulus i) ∧ modulus i ∣ 105) ∧
    (∀ r : Fin 105,∃ i,(modulus i : ℤ) ∣ (r.val : ℤ)-residue i) ∧
    (∀ i,(Finset.univ.filter (fun j => modulus j=modulus i)).card ≤ 2) := by
  decide +kernel

theorem covers (x : ℤ) : ∃ i,(modulus i : ℤ) ∣ x-residue i := by
  have h0 := Int.emod_nonneg x (by norm_num : (105 : ℤ) ≠ 0)
  have hlt := Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 105)
  let r : Fin 105 := ⟨(x%105).toNat,by omega⟩
  have hr : (r.val : ℤ)=x%105 := Int.toNat_of_nonneg h0
  obtain ⟨i,hi⟩ := finite_data.2.1 r
  have hd : (modulus i : ℤ) ∣ 105 := by exact_mod_cast (finite_data.1 i).2.2
  have hx : (105 : ℤ) ∣ x-x%105 := Int.dvd_self_sub_emod
  have hh := (hd.trans hx).add hi
  rw [hr] at hh
  refine ⟨i,?_⟩
  convert hh using 1 <;> ring

theorem not_no_three : ¬ (∀ i,¬ 3 ∣ modulus i) := by
  intro h
  exact h 0 (by decide)

theorem not_injective : ¬ Function.Injective modulus := by
  intro h
  have he : (0 : Fin 14)=1 := h (by rfl)
  exact (by decide : (0 : Fin 14) ≠ 1) he

#print axioms covers
#print axioms not_no_three
#print axioms not_injective
end Erdos7TwofoldPrefixControl
