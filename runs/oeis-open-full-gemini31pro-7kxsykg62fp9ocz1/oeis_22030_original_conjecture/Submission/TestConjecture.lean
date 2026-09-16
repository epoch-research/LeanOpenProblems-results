import FormalConjectures.Util.ProblemImports
import Submission.Spec

def C : ℕ → ℤ
| 0 => 4
| 1 => 16
| 2 => 63
| (n + 3) => 4 * C (n + 2) - C n

def C_nat (n : ℕ) : ℕ := (C n).toNat

lemma C_nat_div_eq (n : ℕ) : (C_nat (n + 1)^2 + C_nat n - 1) / C_nat n - 1 = C_nat (n + 2) := sorry
lemma C_nat_0 : C_nat 0 = 4 := by rfl
lemma C_nat_1 : C_nat 1 = 16 := by rfl

theorem A022030_eq_C_nat (n : ℕ) : A022030_original n = C_nat n := by
  induction' n using Nat.strong_induction_on with n ih
  match n with
  | 0 =>
    rw [A022030_original]
    dsimp
    exact C_nat_0
  | 1 =>
    rw [A022030_original]
    dsimp
    exact C_nat_1
  | m + 2 =>
    rw [A022030_original]
    dsimp
    have hm0 : ¬ (m + 2 = 0) := by omega
    have hm1 : ¬ (m + 2 = 1) := by omega
    rw [dif_neg hm0, dif_neg hm1]
    have ih1 : A022030_original (m + 1) = C_nat (m + 1) := ih (m + 1) (by omega)
    have ih2 : A022030_original m = C_nat m := ih m (by omega)
    -- the definition uses let, we might need to dsimp
    sorry
