import FormalConjecturesUtil

/-! A kernel-checked EVEN control for the free-pure-power construction search.
This is not a witness for the odd covering-system conjecture. -/
namespace Erdos7FreePureControl

def modulus : Fin 5 → ℤ := ![2,3,4,6,12]
def residue : Fin 5 → ℤ := ![0,0,1,1,11]

lemma distinct_moduli : Function.Injective modulus := by decide +kernel
lemma positive_moduli : ∀ i, 1 < modulus i := by decide +kernel
lemma divides_period : ∀ i, modulus i ∣ 12 := by decide +kernel
lemma finite_cover : ∀ r : Fin 12, ∃ i : Fin 5, modulus i ∣ (r.val : ℤ)-residue i := by
  decide +kernel

theorem covers (z : ℤ) : ∃ i, modulus i ∣ z-residue i := by
  have h0 : 0 ≤ z % 12 := Int.emod_nonneg z (by norm_num)
  have hlt : z % 12 < 12 := Int.emod_lt_of_pos z (by norm_num)
  let r : Fin 12 := ⟨(z % 12).toNat, by omega⟩
  have hr : (r.val : ℤ) = z % 12 := by
    dsimp [r]
    exact Int.toNat_of_nonneg h0
  obtain ⟨i, hi⟩ := finite_cover r
  have hz : (12 : ℤ) ∣ z-z%12 := ⟨z/12, by omega⟩
  refine ⟨i, ?_⟩
  have hh := dvd_add ((divides_period i).trans hz) hi
  rw [hr] at hh
  convert hh using 1; ring

lemma even_control : Even (modulus 0) := by decide +kernel

#print axioms distinct_moduli
#print axioms covers
#print axioms even_control
end Erdos7FreePureControl
