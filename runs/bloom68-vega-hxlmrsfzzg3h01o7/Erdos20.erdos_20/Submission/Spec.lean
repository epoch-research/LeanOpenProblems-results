import FormalConjecturesUtil

/-!
# Erdős Problem 20

*References:*
* [erdosproblems.com/20](https://www.erdosproblems.com/20)
* [Wikipedia](https://en.wikipedia.org/wiki/Sunflower_(mathematics))
* [ErRa60] Erdős, Paul and Rado, Richard. Intersection theorems for systems of sets.
  J. London Math. Soc. 35 (1960), 85--90.

-/
namespace Erdos20

/--
Let $f(n,k)$ be minimal such that every $F$ family of $n$-uniform sets with $|F| \ge f(n,k)$
contains a $k$-sunflower.
-/
noncomputable def f (n k : ℕ) : ℕ :=
  sInf {m | ∀ {α : Type}, ∀ (F : Set (Set α)),
    ((∀ f ∈ F, f.ncard = n) ∧ m ≤ F.ncard) → ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S}

/--
Is it true that $f(n,k) < c_k^n$ for some constant $c_k>0$ and for all $n > 0$?
-/
theorem erdos_20 : ∃ (c : ℕ → ℕ), ∀ n k, n > 0 → f n k < (c k) ^ n := by
  sorry

-- TODO(firsching): add the various known bounds as variants.

end Erdos20

theorem Erdos20.erdos_20.disproof : ¬ (type_of% @Erdos20.erdos_20) := sorry
