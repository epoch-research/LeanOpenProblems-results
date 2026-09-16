import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  let L := n.choose 2 + 1
  let R := (n + 1).choose 2
  let is_composite (k : ℕ) : Prop := 1 < k ∧ ¬ k.Prime
  (Icc L R).filter is_composite |>.prod id

lemma prod_image_dvd_prod (s : Finset ℕ) (t : Finset ℕ) (f : ℕ → ℕ)
  (h_inj : Set.InjOn f ↑s)
  (h_sub : s.image f ⊆ t) :
  (∏ x ∈ s, f x) ∣ (∏ x ∈ t, x) := by
  have H : (∏ x ∈ s.image f, x) = ∏ x ∈ s, f x := by
    exact prod_image h_inj
  rw [← H]
  exact prod_dvd_prod_of_subset (s.image f) t id h_sub

lemma disproof_aux (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
  let n := p * (p - 2)
  n > 1 ∧ ¬ (a (n - 1) ∣ a n) := by
  intro n
  have h_p2 : p - 2 ≥ 3 := by omega
  have h1 : n > 1 := by dsimp [n]; nlinarith
  refine ⟨h1, ?_⟩
  intro hdvd
  sorry
