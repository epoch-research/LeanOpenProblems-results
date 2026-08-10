import FormalConjectures.Util.ProblemImports
open Nat
set_option maxRecDepth 100000
def Pred (n : ℕ) (p : ℕ × ℕ × ℕ) : Prop :=
  p.1 ^ 2 + p.2.1 * (2 * p.2.1 + 1) + p.2.2 * (p.2.2 + 1) / 2 = n ∧
    (Nat.Prime p.2.2 ∨ Nat.Prime (p.2.2 + 1))
instance (n : ℕ) (p : ℕ × ℕ × ℕ) : Decidable (Pred n p) := by unfold Pred; infer_instance
def box (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (n+1)) ×ˢ (Finset.range (n+1)) ×ˢ (Finset.range (n+1))
-- a(30)=1, box 30 = 31^3 = 29791 triples (comparable scale to tight box for n=1344)
example : ((box 30).filter (Pred 30)).card = 1 := by decide
