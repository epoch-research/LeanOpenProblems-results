import FormalConjecturesUtil

/-! Fibers of an antitone finite-range profile are disjoint integer intervals.
This permits arbitrarily many original profile changes to be grouped by height. -/
namespace Erdos66MonotoneIntervalFibers
open scoped Classical
set_option maxHeartbeats 1800000

lemma exists_fiber_interval (M : ℕ) (f : ℕ → ℕ)
    (hf : ∀ x y, x ≤ y → y<M → f y ≤ f x) (j : ℕ) :
    ∃ a b : ℕ, a ≤ b ∧ b ≤ M ∧ (a<b ∨ a=0 ∧ b=0) ∧ ∀ x, a ≤ x ∧ x<b ↔ x<M ∧ f x=j := by
  let S := (Finset.range M).filter (fun x ↦ f x=j)
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    let d := S.max' hS
    have ha : a∈S := Finset.min'_mem _ _
    have hd : d∈S := Finset.max'_mem _ _
    have haM : a<M := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hdM : d<M := Finset.mem_range.mp (Finset.mem_filter.mp hd).1
    have hfa : f a=j := (Finset.mem_filter.mp ha).2
    have hfd : f d=j := (Finset.mem_filter.mp hd).2
    have had : a ≤ d := Finset.min'_le _ _ hd
    refine ⟨a,d+1,by omega,by omega,Or.inl (by omega),fun x ↦ ?_⟩
    constructor
    · rintro ⟨hax,hxd⟩
      have hxM : x<M := by omega
      have h1 := hf a x hax hxM
      have h2 := hf x d (by omega) hdM
      exact ⟨hxM,by omega⟩
    · rintro ⟨hxM,hfx⟩
      have hx : x∈S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxM,hfx⟩
      have hl := Finset.min'_le _ _ hx
      have hu := Finset.le_max' _ _ hx
      exact ⟨hl,by dsimp [d]; omega⟩
  · refine ⟨0,0,le_rfl,Nat.zero_le _,Or.inr ⟨rfl,rfl⟩,fun x ↦ ?_⟩
    have hn : ¬(x<M ∧ f x=j) := by
      rintro ⟨hx,hj⟩
      exact hS ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hx,hj⟩⟩
    simp [hn]

/-- The number of resulting intervals is the number of quantized heights,
not the number of points or changes of the original profile. -/
theorem exists_interval_fibers (M J : ℕ) (f : ℕ → ℕ)
    (hf : ∀ x y, x ≤ y → y<M → f y ≤ f x) :
    ∃ a b : Fin J → ℕ,
      (∀ j, a j ≤ b j ∧ b j ≤ M) ∧
      (∀ j x, a j ≤ x ∧ x<b j ↔ x<M ∧ f x=j.val) ∧
      ∀ i j, i ≠ j → b i ≤ a j ∨ b j ≤ a i := by
  have hh : ∀ j : Fin J, ∃ a b : ℕ, a ≤ b ∧ b ≤ M ∧ (a<b ∨ a=0 ∧ b=0) ∧
      ∀ x, a ≤ x ∧ x<b ↔ x<M ∧ f x=j.val :=
    fun j ↦ exists_fiber_interval M f hf j.val
  choose a b hab hb hnonempty hmem using hh
  refine ⟨a,b,fun j ↦ ⟨hab j,hb j⟩,hmem,?_⟩
  intro i j hij
  by_contra hh
  have hij' : a j<b i := by omega
  have hji' : a i<b j := by omega
  let x := max (a i) (a j)
  have hia : a i<b i := by rcases hnonempty i with hh | ⟨ha,hb⟩ <;> omega
  have hja : a j<b j := by rcases hnonempty j with hh | ⟨ha,hb⟩ <;> omega
  have hxi : a i ≤ x ∧ x<b i := ⟨le_max_left _ _,max_lt hia hij'⟩
  have hxj : a j ≤ x ∧ x<b j := ⟨le_max_right _ _,max_lt hji' hja⟩
  have hi := (hmem i x).mp hxi
  have hj := (hmem j x).mp hxj
  exact hij (Fin.ext (by omega))

end Erdos66MonotoneIntervalFibers
