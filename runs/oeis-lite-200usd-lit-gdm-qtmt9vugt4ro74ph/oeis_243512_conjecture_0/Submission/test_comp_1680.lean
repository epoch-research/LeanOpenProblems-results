import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000

open Nat ArithmeticFunction Rat

theorem sigma_one_mul_coprime (a b : ℕ) (h : Coprime a b) :
    sigma 1 (a * b) = sigma 1 a * sigma 1 b := by
  exact isMultiplicative_sigma.map_mul_of_coprime h

def A243473_val (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let r : Rat := (sigma 1 i : Rat) / i
    (r.num - (r.den : ℤ)).toNat

theorem test_1680 : A243473_val 624606909696 = 1680 := by
  unfold A243473_val
  have h_ne : ¬ 624606909696 = 0 := by decide
  rw [if_neg h_ne]
  have h_dec : 624606909696 = 256 * (81 * (7 * (1331 * (53 * 61)))) := by rfl
  have h_cop1 : Coprime 256 (81 * (7 * (1331 * (53 * 61)))) := by decide
  have h_cop2 : Coprime 81 (7 * (1331 * (53 * 61))) := by decide
  have h_cop3 : Coprime 7 (1331 * (53 * 61)) := by decide
  have h_cop4 : Coprime 1331 (53 * 61) := by decide
  have h_cop5 : Coprime 53 61 := by decide
  have h_sig : sigma 1 624606909696 = 2424503321856 := by
    rw [h_dec]
    rw [sigma_one_mul_coprime 256 (81 * (7 * (1331 * (53 * 61)))) h_cop1]
    rw [sigma_one_mul_coprime 81 (7 * (1331 * (53 * 61))) h_cop2]
    rw [sigma_one_mul_coprime 7 (1331 * (53 * 61)) h_cop3]
    rw [sigma_one_mul_coprime 1331 (53 * 61) h_cop4]
    rw [sigma_one_mul_coprime 53 61 h_cop5]
    rfl
  rw [h_sig]
  norm_num
  rfl
