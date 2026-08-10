import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  let is_sq (k : ℕ) : Prop := k.sqrt * k.sqrt = k
  let M : ℕ := n.sqrt
  let R : Finset ℕ := range M
  let search_space : Finset (ℕ × (ℕ × (ℕ × ℕ))) := R.product (R.product (R.product R))
  search_space.sum fun p : ℕ × (ℕ × (ℕ × ℕ)) =>
    let w := p.fst
    let x := p.snd.fst
    let y := p.snd.snd.fst
    let z := p.snd.snd.snd
    let sum_sq := 2 * w^2 + x^2 + y^2 + z^2
    let lin_comb := w + x + 2 * y + 4 * z
    if sum_sq = n ∧ is_sq lin_comb
    then 1
    else 0

def A275409_zero_set : Finset ℕ :=
  {3, 10}

def A275409_one_set : Finset ℕ :=
  {0, 2, 7, 8, 9, 12, 14, 15, 22, 23, 24, 25, 36, 39, 44, 45, 60, 87, 98, 106, 110, 111, 183}

theorem a_0_eq_0 : a 0 = 0 := by
  rfl

theorem zero_mem_one_set : 0 ∈ A275409_one_set := by
  decide

theorem oeis_275409_conjecture_0.disproof :
  ¬ ((∀ n : ℕ, (a n > 0 ↔ n ∉ A275409_zero_set)) ∧
     (∀ n : ℕ, (a n = 1 ↔ n ∈ A275409_one_set))) := by
  intro h
  have h2 := h.right 0
  have h_in : 0 ∈ A275409_one_set := zero_mem_one_set
  have h3 : a 0 = 1 := h2.mpr h_in
  have h_a0 : a 0 = 0 := rfl
  rw [h_a0] at h3
  contradiction
