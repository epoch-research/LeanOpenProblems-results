import FormalConjectures.Util.ProblemImports

open Finset Nat

-- Let's define the periodic property we want to prove.
def eventually_periodic {α : Type*} (f : ℕ → α) (P : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f (n + P) = f n

lemma pow_eventually_periodic_unit (k : ℕ) [NeZero k] (g : (ZMod k)ˣ) :
    (g : ZMod k) ^ totient k = 1 := by
  have h := ZMod.pow_totient g
  exact Units.ext_iff.mp h

lemma pow_eventually_periodic_unit' (k : ℕ) [NeZero k] (g : (ZMod k)ˣ) :
    eventually_periodic (fun n => (g : ZMod k) ^ n) (totient k) := by
  use 0
  intro n hn
  dsimp only
  rw [pow_add, pow_eventually_periodic_unit k g, mul_one]
