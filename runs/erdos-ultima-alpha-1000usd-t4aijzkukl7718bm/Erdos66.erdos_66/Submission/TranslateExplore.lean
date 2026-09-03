import Submission.Explore

/-! Exact translation formulas for natural-number representation counts. -/
namespace Erdos66Translate
open AdditiveCombinatorics
open scoped Classical

def shift (A : Set ℕ) (M : ℕ) : Set ℕ := (fun a ↦ a + M) '' A

lemma shift_finite {A : Set ℕ} (hA : A.Finite) (M : ℕ) : (shift A M).Finite :=
  hA.image _

lemma shift_ge (A : Set ℕ) (M : ℕ) {x : ℕ} (hx : x ∈ shift A M) : M ≤ x := by
  obtain ⟨a, ha, rfl⟩ := hx
  dsimp
  omega

lemma shift_lt {A : Set ℕ} {M L x : ℕ} (hA : A ⊆ Set.Iio L) (hx : x ∈ shift A M) : x < L + M := by
  obtain ⟨a, ha, rfl⟩ := hx
  have hh := hA ha
  change a < L at hh
  dsimp
  omega

lemma sumRep_shift (A : Set ℕ) (M n : ℕ) :
    sumRep (shift A M) (n + 2 * M) = sumRep A n := by
  rw [sumRep_def, sumRep_def]
  symm
  apply Finset.card_bij (fun ab _ ↦ (ab.1 + M, ab.2 + M))
  · intro ab hab
    obtain ⟨hs, ha, hb⟩ := Finset.mem_filter.mp hab
    have hs' := Finset.mem_antidiagonal.mp hs
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_antidiagonal.mpr (by dsimp; omega),
      ⟨ab.1, ha, rfl⟩, ⟨ab.2, hb, rfl⟩⟩
  · intro ab hab cd hcd he
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    apply Prod.ext <;> dsimp at h₁ h₂ <;> omega
  · intro xy hxy
    obtain ⟨hs, hx, hy⟩ := Finset.mem_filter.mp hxy
    have hs' := Finset.mem_antidiagonal.mp hs
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr ?_, ha, hb⟩,
      Prod.ext hax hby⟩
    dsimp at hax hby ⊢
    omega

lemma sumRep_shift_zero (A : Set ℕ) {M n : ℕ} (hn : n < 2 * M) : sumRep (shift A M) n = 0 := by
  rw [sumRep_def, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro ab hab hm
  have hs := Finset.mem_antidiagonal.mp hab
  have ha := shift_ge A M hm.1
  have hb := shift_ge A M hm.2
  omega

lemma sumRep_shift_eq_sub (A : Set ℕ) {M n : ℕ} (hn : 2 * M ≤ n) :
    sumRep (shift A M) n = sumRep A (n - 2 * M) := by
  simpa only [Nat.sub_add_cancel hn] using sumRep_shift A M (n - 2 * M)

end Erdos66Translate
