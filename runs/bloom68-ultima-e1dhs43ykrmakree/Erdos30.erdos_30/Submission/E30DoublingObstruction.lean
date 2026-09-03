import FormalConjecturesUtil

/-! A limited obstruction to the canonical field-extension cut, not a settlement. -/
namespace Erdos30Research

theorem doubling_closed_canonical_cut_not_sidon {S : Finset ℕ} {v : ℕ}
    (hne : S.Nonempty) (hz : 0 ∉ S) (hbox : ∀ x ∈ S, x < v)
    (hdouble : ∀ x ∈ S, (2 * x) % v ∈ S) :
    ¬ IsSidon ((insert 0 S : Finset ℕ) : Set ℕ) := by
  let a := S.min' hne
  have ha : a ∈ S := Finset.min'_mem S hne
  have hap : 0 < a := by
    by_contra h
    have : a = 0 := by omega
    exact hz (this ▸ ha)
  have hav : a < v := hbox a ha
  have hm : a ≤ (2 * a) % v := Finset.min'_le S _ (hdouble a ha)
  have hd : 2 * a < v := by
    by_contra h
    have hr : (2 * a) % v = 2 * a - v := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hr] at hm
    omega
  have hda : 2 * a ∈ S := by
    simpa only [Nat.mod_eq_of_lt hd] using hdouble a ha
  intro hs
  have he := hs 0 (by simp) a (Finset.mem_insert_of_mem ha)
    (2 * a) (Finset.mem_insert_of_mem hda) a (Finset.mem_insert_of_mem ha) (by omega)
  rcases he with he | he <;> omega

#print axioms doubling_closed_canonical_cut_not_sidon
end Erdos30Research
