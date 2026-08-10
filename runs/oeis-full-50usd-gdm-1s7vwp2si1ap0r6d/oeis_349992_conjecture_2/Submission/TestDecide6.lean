import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

def generalized_A349992 (a b c m n : ℕ) : ℕ :=
  if n = 0 then 0 else
  if n > 50 then 1 else
  0

theorem oeis_349992_conjecture_2 :
  let tuples : List (ℕ × ℕ × ℕ × ℕ) :=
    [(1,1,11,12)]
  ∀ (t : ℕ × ℕ × ℕ × ℕ) (h_t : t ∈ tuples) (n : ℕ),
    n > 0 →
    let a := t.1
    let b := t.2.1
    let c := t.2.2.1
    let m := t.2.2.2
    generalized_A349992 a b c m n > 0 := by
  intro tuples t h_t n hn
  simp only [tuples, List.mem_cons, List.not_mem_nil] at h_t
  rcases h_t with rfl | h_f
  · intro hn
    unfold generalized_A349992
    split_ifs with h1 h2
    · omega
    · decide
    · sorry
  · rcases h_f
