import Submission.FinitePaletteCompactness

/-! A finite ordinary Ramsey graph for triangles and any fixed finite palette. -/

open SimpleGraph Set Filter
open Erdos595FinitePalette
namespace Erdos595FiniteFolkmanRamsey

lemma complete_nat_no_coloring (C : Type) [Finite C] :
    ¬HasColoring (⊤ : SimpleGraph ℕ) C := by
  rintro ⟨c,hc⟩
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  have ht : ∀ n : ℕ, {m | n < m} ∈ U :=
    fun n => Nat.hyperfilter_le_atTop (Filter.eventually_gt_atTop n)
  have hex : ∀ n : ℕ, ∃ z : C, {m | c s(n,m) = z} ∈ U := by
    intro n
    apply Ultrafilter.eventually_exists_iff.mp
    exact Filter.Eventually.of_forall (fun m => ⟨c s(n,m),rfl⟩)
  choose k hk using hex
  have hz : ∃ z : C, {n | k n = z} ∈ U := by
    apply Ultrafilter.eventually_exists_iff.mp
    exact Filter.Eventually.of_forall (fun n => ⟨k n,rfl⟩)
  obtain ⟨z,hz⟩ := hz
  obtain ⟨a,ha⟩ := Ultrafilter.nonempty_of_mem hz
  obtain ⟨b,hb,hab,hcb⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem hz (Filter.inter_mem (ht a) (hk a)))
  obtain ⟨d,hbd,hcd,hcbd⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem (ht b) (Filter.inter_mem (hk a) (hk b)))
  change a < b at hab
  change b < d at hbd
  apply hc a b d (by change a ≠ b; omega) (by change a ≠ d; omega) (by change b ≠ d; omega)
  exact ⟨hcb.trans hcd.symm,hcb.trans (ha.trans (hb.symm.trans hcbd.symm))⟩

/-- Finite-palette compactness reflects a finite triangle Ramsey witness. -/
theorem finite_ramsey (C : Type) [Finite C] [Nonempty C] :
    ∃ (R : Type) (_ : Finite R) (K : SimpleGraph R), ¬HasColoring K C := by
  have hex : ∃ S : Finset ℕ, ¬HasColoring ((⊤ : SimpleGraph ℕ).induce (S : Set ℕ)) C := by
    by_contra! hn
    exact complete_nat_no_coloring C (compactness _ hn)
  obtain ⟨S,hS⟩ := hex
  exact ⟨S,inferInstance,(⊤ : SimpleGraph ℕ).induce (S : Set ℕ),hS⟩

#print axioms finite_ramsey
end Erdos595FiniteFolkmanRamsey
