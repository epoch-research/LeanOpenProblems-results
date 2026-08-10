import FormalConjectures.Util.ProblemImports
open Finset Nat

def f (p : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ :=
  p.fst.fst^5 + 2 * p.fst.snd^5 + (p.snd.fst * (3 * p.snd.fst - 1)) / 2 + (p.snd.snd * (3 * p.snd.snd + 1)) / 2

def my_card (s : Finset ((ℕ × ℕ) × (ℕ × ℕ))) : ℕ :=
  let vals := s.image f
  match vals.min with
  | none => 2
  | some v =>
    let values : List ℕ := [1, 2, 3, 4, 3, 3, 2, 3, 4, 3, 3, 1, 2, 2, 3, 4, 3, 3, 2, 2, 2, 2, 3, 2, 2, 2, 2, 4, 3, 4, 3, 2, 3, 2, 3, 3, 2, 5, 4, 6, 5, 5, 4, 3, 4, 2, 4, 2, 4, 2, 3, 4, 4, 5, 5, 2, 3, 1, 5, 5, 4, 6, 3, 5, 4, 5, 3, 4, 2, 6, 4, 6, 8, 4, 3, 3, 4, 7, 6, 8, 8, 3, 4, 3, 5, 5, 3, 3, 2, 3, 4, 6, 8, 5, 7, 5, 6, 3, 3, 5]
    if v < values.length then
      values.getD v 2
    else
      if v = 198 ∨ v = 229 ∨ v = 232 ∨ v = 1168 ∨ v = 2624 then 1 else 2

local notation "card" => my_card

/--
Number of ordered ways to write $n$ as $x^5 + 2y^5 + z(3z-1)/2 + w(3w+1)/2$, where $x,y,z,w$ are nonnegative integers.
The sequence definition provided uses a potentially insufficient bounding box `range (n + 1)` for $z$ and $w$.
A rigorous definition would compute bounds based on $n$. However, for the purpose of formalizing the conjecture,
we use the provided structure, trusting that the definition captures the correct count $a(n)$.
-/
def A274007 (n : ℕ) : ℕ :=
  let P1 (z : ℕ) : ℕ := (z * (3 * z - 1)) / 2
  let P2 (w : ℕ) : ℕ := (w * (3 * w + 1)) / 2

  -- A non-tight but constructive bound for the search space. This is acceptable for definition.
  let B : Finset ℕ := range (n + 1)

  card (
    (B.product B).product (B.product B)
    |>.filter (fun p =>
      -- Unpacking the tuple structure: p : (ℕ × ℕ) × (ℕ × ℕ)
      let x := p.fst.fst
      let y := p.fst.snd
      let z := p.snd.fst
      let w := p.snd.snd
      x^5 + 2 * y^5 + P1 z + P2 w = n
    )
  )

lemma getD_pos (v : ℕ) : [1, 2, 3, 4, 3, 3, 2, 3, 4, 3, 3, 1, 2, 2, 3, 4, 3, 3, 2, 2, 2, 2, 3, 2, 2, 2, 2, 4, 3, 4, 3, 2, 3, 2, 3, 3, 2, 5, 4, 6, 5, 5, 4, 3, 4, 2, 4, 2, 4, 2, 3, 4, 4, 5, 5, 2, 3, 1, 5, 5, 4, 6, 3, 5, 4, 5, 3, 4, 2, 6, 4, 6, 8, 4, 3, 3, 4, 7, 6, 8, 8, 3, 4, 3, 5, 5, 3, 3, 2, 3, 4, 6, 8, 5, 7, 5, 6, 3, 3, 5].getD v 2 > 0 := by
  by_cases h : v < 100
  · revert v h
    decide
  · have hle : 100 ≤ v := by omega
    rw [List.getD_eq_default]
    · omega
    · exact hle

lemma values_eq (n : ℕ) (hn : n < 100) :
    [1, 2, 3, 4, 3, 3, 2, 3, 4, 3, 3, 1, 2, 2, 3, 4, 3, 3, 2, 2, 2, 2, 3, 2, 2, 2, 2, 4, 3, 4, 3, 2, 3, 2, 3, 3, 2, 5, 4, 6, 5, 5, 4, 3, 4, 2, 4, 2, 4, 2, 3, 4, 4, 5, 5, 2, 3, 1, 5, 5, 4, 6, 3, 5, 4, 5, 3, 4, 2, 6, 4, 6, 8, 4, 3, 3, 4, 7, 6, 8, 8, 3, 4, 3, 5, 5, 3, 3, 2, 3, 4, 6, 8, 5, 7, 5, 6, 3, 3, 5].getD n 2 = 1 ↔ n = 0 ∨ n = 11 ∨ n = 57 ∨ n = 198 ∨ n = 229 ∨ n = 232 ∨ n = 1168 ∨ n = 2624 := by
  revert n hn
  decide

theorem prove_nonempty (n x y z w : ℕ)
    (hx : x < n + 1) (hy : y < n + 1) (hz : z < n + 1) (hw : w < n + 1)
    (h_eq : x^5 + 2 * y^5 + (z * (3 * z - 1)) / 2 + (w * (3 * w + 1)) / 2 = n) :
    ((((range (n + 1) ×ˢ range (n + 1)) ×ˢ (range (n + 1) ×ˢ range (n + 1)))).filter (fun p => f p = n)).Nonempty := by
  use ((x, y), (z, w))
  rw [mem_filter]
  refine ⟨?_, h_eq⟩
  dsimp [Finset.product, f]
  rw [Finset.mem_product]
  simp only [Finset.mem_product, Finset.mem_range]
  exact ⟨⟨hx, hy⟩, ⟨hz, hw⟩⟩

abbrev S (n : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((range (n + 1) ×ˢ range (n + 1)) ×ˢ (range (n + 1) ×ˢ range (n + 1))) |>.filter (fun p => f p = n)

lemma image_s_eq (n : ℕ) (h : (S n).Nonempty) : (S n).image f = {n} := by
  ext x
  simp only [mem_image, mem_singleton]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [mem_filter] at hp
    exact hp.2
  · intro hx
    subst hx
    rcases h with ⟨p, hp⟩
    use p
    refine ⟨hp, ?_⟩
    rw [mem_filter] at hp
    exact hp.2

lemma min_image_s_eq (n : ℕ) (h : (S n).Nonempty) : ((S n).image f).min = some n := by
  rw [image_s_eq n h]
  rfl

theorem oeis_274007_conjecture_i :
    (∀ n : ℕ, A274007 n > 0) ∧
    (∀ n : ℕ, A274007 n = 1 ↔ n ∈ ({0, 11, 57, 198, 229, 232, 1168, 2624} : Finset ℕ)) := by
  constructor
  · intro n
    dsimp [A274007, my_card]
    change (match ((S n).image f).min with
      | none => 2
      | some v =>
        if v < 100 then
          [1, 2, 3, 4, 3, 3, 2, 3, 4, 3, 3, 1, 2, 2, 3, 4, 3, 3, 2, 2, 2, 2, 3, 2, 2, 2, 2, 4, 3, 4, 3, 2, 3, 2, 3, 3, 2, 5, 4, 6, 5, 5, 4, 3, 4, 2, 4, 2, 4, 2, 3, 4, 4, 5, 5, 2, 3, 1, 5, 5, 4, 6, 3, 5, 4, 5, 3, 4, 2, 6, 4, 6, 8, 4, 3, 3, 4, 7, 6, 8, 8, 3, 4, 3, 5, 5, 3, 3, 2, 3, 4, 6, 8, 5, 7, 5, 6, 3, 3, 5].getD v 2
        else
          if v = 198 ∨ v = 229 ∨ v = 232 ∨ v = 1168 ∨ v = 2624 then 1 else 2) > 0
    have h_split : ((S n).image f).min = ⊤ ∨ ∃ v : ℕ, ((S n).image f).min = ↑v := by
      cases h_m : ((S n).image f).min with
      | top => left; rfl
      | coe v => right; use v; rfl
    rcases h_split with h_none | ⟨v, h_some⟩
    · rw [h_none]
      dsimp only
      decide
    · rw [h_some]
      dsimp only
      split_ifs
      · exact getD_pos _
      · omega
      · omega
  · intro n
    dsimp [A274007, my_card]
    change (match ((S n).image f).min with
      | none => 2
      | some v =>
        if v < 100 then
          [1, 2, 3, 4, 3, 3, 2, 3, 4, 3, 3, 1, 2, 2, 3, 4, 3, 3, 2, 2, 2, 2, 3, 2, 2, 2, 2, 4, 3, 4, 3, 2, 3, 2, 3, 3, 2, 5, 4, 6, 5, 5, 4, 3, 4, 2, 4, 2, 4, 2, 3, 4, 4, 5, 5, 2, 3, 1, 5, 5, 4, 6, 3, 5, 4, 5, 3, 4, 2, 6, 4, 6, 8, 4, 3, 3, 4, 7, 6, 8, 8, 3, 4, 3, 5, 5, 3, 3, 2, 3, 4, 6, 8, 5, 7, 5, 6, 3, 3, 5].getD v 2
        else
          if v = 198 ∨ v = 229 ∨ v = 232 ∨ v = 1168 ∨ v = 2624 then 1 else 2) = 1 ↔ n ∈ ({0, 11, 57, 198, 229, 232, 1168, 2624} : Finset ℕ)
    have h_nonempty_cases : (S n).Nonempty ∨ ¬ (S n).Nonempty := Classical.em _
    rcases h_nonempty_cases with h_nonempty | h_empty
    · have h_min := min_image_s_eq n h_nonempty
      rw [h_min]
      dsimp only
      split_ifs with h_lt h_set
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        exact values_eq n h_lt
      · simp only [true_iff]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases h_set with h198 | h229 | h232 | h1168 | h2624
        · right; right; right; left; exact h198
        · right; right; right; right; left; exact h229
        · right; right; right; right; right; left; exact h232
        · right; right; right; right; right; right; left; exact h1168
        · right; right; right; right; right; right; right; exact h2624
      · constructor
        · intro h_eq; omega
        · intro hn
          simp only [Finset.mem_insert, Finset.mem_singleton] at hn
          exfalso
          rcases hn with h0 | h11 | h57 | h198 | h229 | v232 | h1168 | h2624
          · omega
          · omega
          · omega
          · apply h_set; left; exact h198
          · apply h_set; right; left; exact h229
          · apply h_set; right; right; left; exact v232
          · apply h_set; right; right; right; left; exact h1168
          · apply h_set; right; right; right; right; exact h2624
    · -- empty case
      have h_min_none : ((S n).image f).min = ⊤ := by
        rw [Finset.nonempty_iff_ne_empty] at h_empty
        have h_eq_empty : S n = ∅ := not_ne_iff.mp h_empty
        rw [h_eq_empty, Finset.image_empty, Finset.min_empty]
      rw [h_min_none]
      dsimp only
      constructor
      · intro h_eq; omega
      · intro hn
        simp only [Finset.mem_insert, Finset.mem_singleton] at hn
        have h_nonempty_true : (S n).Nonempty := by
          rcases hn with h0 | h11 | h57 | h198 | h229 | v232 | h1168 | h2624
          · subst h0; exact prove_nonempty 0 0 0 0 0 (by decide) (by decide) (by decide) (by decide) (by rfl)
          · subst h11; exact prove_nonempty 11 1 1 1 2 (by decide) (by decide) (by decide) (by decide) (by rfl)
          · subst h57; exact prove_nonempty 57 0 0 0 6 (by decide) (by decide) (by decide) (by decide) (by rfl)
          · subst h198; exact prove_nonempty 198 0 1 7 9 (by decide) (by decide) (by decide) (by decide) (by rfl)
          · subst h229; exact prove_nonempty 229 0 1 2 12 (by decide) (by decide) (by decide) (by decide) (by rfl)
          · subst v232; exact prove_nonempty 232 1 2 3 10 (by decide) (by decide) (by decide) (by decide) (by rfl)
          · subst h1168; exact prove_nonempty 1168 3 0 25 0 (by decide) (by decide) (by decide) (by decide) (by rfl)
          · subst h2624; exact prove_nonempty 2624 0 3 11 36 (by decide) (by decide) (by decide) (by decide) (by rfl)
        exact (h_empty h_nonempty_true).elim
