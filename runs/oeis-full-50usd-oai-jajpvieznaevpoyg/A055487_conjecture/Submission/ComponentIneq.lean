import FormalConjectures.Util.ProblemImports
open Nat

lemma prime_pow_ge_totient_component_succ {r a : ℕ} (hr : Nat.Prime r) (ha : 0 < a) :
    r ^ a ≥ r ^ (a - 1) * (r - 1) + 1 := by
  cases a with
  | zero => omega
  | succ b =>
    cases b with
    | zero =>
      simp [hr.pos]
    | succ c =>
      -- r^(c+2) = r^(c+1)*(r-1) + r^(c+1)
      have hpowpos : 1 ≤ r ^ (c + 1) := Nat.one_le_pow _ _ (by exact hr.one_le)
      calc
        r ^ (Nat.succ (Nat.succ c)) = r ^ (c + 1) * r := by
          rfl
        _ = r ^ (c + 1) * ((r - 1) + 1) := by rw [Nat.sub_add_cancel hr.one_le]
        _ = r ^ (c + 1) * (r - 1) + r ^ (c + 1) := by rw [mul_add, mul_one]
        _ ≥ r ^ (c + 1) * (r - 1) + 1 := by omega
