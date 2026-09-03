import FormalConjecturesUtil

/-! Reciprocal summability is preserved by finitely many integral dilations.
Consequently bounded normalization cannot collapse divergent distinct-value
reciprocal mass into a summable set. -/
namespace Erdos1206.FiniteDilationMass
open Finset
open scoped Classical

lemma subset_summable {S T : Set ℕ} (hST : S⊆T)
    (hs : Summable (fun n : ℕ => if n∈T then (1:ℝ)/n else 0)) :
    Summable (fun n : ℕ => if n∈S then (1:ℝ)/n else 0) := by
  apply hs.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
  intro n
  by_cases hn : n∈S
  · simp [hn,hST hn]
  · simp only [if_neg hn]
    split_ifs <;> positivity

lemma dilation_summable {B : Set ℕ}
    (hs : Summable (fun n : ℕ => if n∈B then (1:ℝ)/n else 0))
    (g : ℕ) (hg : 0 < g) :
    Summable (fun n : ℕ => if n∈(fun n => g*n) '' B then (1:ℝ)/n else 0) := by
  have hi : Function.Injective (fun n : ℕ => g*n) := mul_right_injective₀ hg.ne'
  apply (hi.summable_iff ?_).mp
  · convert hs.mul_left ((g:ℝ)⁻¹) using 1
    funext n
    dsimp only [Function.comp_apply]
    have he : g*n∈(fun n => g*n) '' B ↔ n∈B := hi.mem_set_image
    simp only [he]
    by_cases hn : n∈B
    · simp only [if_pos hn,Nat.cast_mul,one_div,mul_inv_rev]
      ring
    · simp [hn]
  · intro n hn
    have hh : n∉(fun n => g*n) '' B := by
      rintro ⟨b,hb,rfl⟩
      exact hn ⟨b,rfl⟩
    simp [hh]

def multiples (B : Set ℕ) (G : ℕ) : Set ℕ :=
  {n | ∃ g∈Icc 1 G, n∈(fun n => g*n) '' B}

lemma multiples_summable {B : Set ℕ}
    (hs : Summable (fun n : ℕ => if n∈B then (1:ℝ)/n else 0)) (G : ℕ) :
    Summable (fun n : ℕ => if n∈multiples B G then (1:ℝ)/n else 0) := by
  have hh : Summable (fun n : ℕ => ∑g∈Icc 1 G,
      if n∈(fun n => g*n) '' B then (1:ℝ)/n else 0) :=
    summable_sum (fun g hg => dilation_summable hs g (mem_Icc.mp hg).1)
  apply hh.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
  intro n
  by_cases hn : n∈multiples B G
  · rw [if_pos hn]
    obtain ⟨g,hg,he⟩ := hn
    have hh := single_le_sum (s := Icc 1 G)
      (f := fun g => if n∈(fun n => g*n) '' B then (1:ℝ)/n else 0)
      (fun g _ => by dsimp only; split_ifs <;> positivity) hg
    simpa only [if_pos he] using hh
  · rw [if_neg hn]
    exact sum_nonneg (fun g _ => by split_ifs <;> positivity)

lemma image_not_summable_of_bounded_normalization {α : Type*}
    (f h : α → ℕ) (G : ℕ)
    (hn : ∀ x, ∃ g∈Icc 1 G, f x=g*h x)
    (hf : ¬ Summable (fun n : ℕ => if n∈Set.range f then (1:ℝ)/n else 0)) :
    ¬ Summable (fun n : ℕ => if n∈Set.range h then (1:ℝ)/n else 0) := by
  intro hs
  apply hf
  apply subset_summable (T := multiples (Set.range h) G) ?_ (multiples_summable hs G)
  rintro n ⟨x,rfl⟩
  obtain ⟨g,hg,he⟩ := hn x
  exact ⟨g,hg,h x,⟨x,rfl⟩,he.symm⟩

#print axioms multiples_summable
#print axioms image_not_summable_of_bounded_normalization
end Erdos1206.FiniteDilationMass
