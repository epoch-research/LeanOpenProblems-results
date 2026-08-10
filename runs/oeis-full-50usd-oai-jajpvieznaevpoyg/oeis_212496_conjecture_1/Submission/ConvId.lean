import FormalConjectures.Util.ProblemImports

open BigOperators Finset Nat Real
open scoped ArithmeticFunction.Omega

/-- original definitions -/
def omega_mult (k : ℕ) : ℕ := k.factorization.sum (fun _ e => e)

def c (n : ℕ) : ℤ := if ((n : ℤ) - (omega_mult n : ℤ)) % 2 = 0 then -1 else 1

def liouv (n : ℕ) : ℤ := if omega_mult n % 2 = 0 then 1 else -1

lemma omega_mult_eq_cardFactors (n : ℕ) : omega_mult n = ArithmeticFunction.cardFactors n := by
  unfold omega_mult
  rw [ArithmeticFunction.cardFactors_eq_sum_factorization]

lemma if_parity_mul (a b : ℕ) :
    (if (a + b) % 2 = 0 then (1 : ℤ) else -1) =
      (if a % 2 = 0 then (1 : ℤ) else -1) * (if b % 2 = 0 then (1 : ℤ) else -1) := by
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb] <;> omega

lemma liouv_mul (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    liouv (m*n) = liouv m * liouv n := by
  unfold liouv
  rw [omega_mult_eq_cardFactors, omega_mult_eq_cardFactors, omega_mult_eq_cardFactors]
  rw [ArithmeticFunction.cardFactors_mul hm hn]
  exact if_parity_mul _ _

lemma omega_mult_two_mul (n : ℕ) (hn : n ≠ 0) : omega_mult (2*n) = omega_mult n + 1 := by
  rw [omega_mult_eq_cardFactors, omega_mult_eq_cardFactors]
  rw [show 2*n = n*2 by omega]
  rw [ArithmeticFunction.cardFactors_mul hn (by norm_num : (2:ℕ) ≠ 0)]
  rw [ArithmeticFunction.cardFactors_apply_prime (by norm_num : Nat.Prime 2)]

lemma liouv_two_mul (n : ℕ) (hn : n ≠ 0) : liouv (2*n) = - liouv n := by
  unfold liouv
  rw [omega_mult_two_mul n hn]
  have h : (omega_mult n + 1) % 2 = 0 ↔ omega_mult n % 2 ≠ 0 := by omega
  by_cases hp : omega_mult n % 2 = 0 <;> simp [hp, h]

lemma c_eq (n : ℕ) : c n = (if n % 2 = 0 then (- liouv n) else liouv n) := by
  unfold c liouv
  by_cases hn : n % 2 = 0
  · have hnz : ((n : ℤ) % 2 = 0) := by exact_mod_cast hn
    have hiff : (((n : ℤ) - (omega_mult n : ℤ)) % 2 = 0) ↔ ((omega_mult n : ℤ) % 2 = 0) := by
      omega
    by_cases ho : omega_mult n % 2 = 0
    · have hoz : ((omega_mult n : ℤ) % 2 = 0) := by exact_mod_cast ho
      simp [hn, hiff, ho, hoz]
    · have hoz : ¬ ((omega_mult n : ℤ) % 2 = 0) := by
        intro h; exact ho (by exact_mod_cast h)
      simp [hn, hiff, ho, hoz]
  · have hnz : ((n : ℤ) % 2 ≠ 0) := by
      intro h; exact hn (by exact_mod_cast h)
    have hiff : (((n : ℤ) - (omega_mult n : ℤ)) % 2 = 0) ↔ ¬ ((omega_mult n : ℤ) % 2 = 0) := by
      omega
    by_cases ho : omega_mult n % 2 = 0
    · have hoz : ((omega_mult n : ℤ) % 2 = 0) := by exact_mod_cast ho
      simp [hn, hiff, ho, hoz]
    · have hoz : ¬ ((omega_mult n : ℤ) % 2 = 0) := by
        intro h; exact ho (by exact_mod_cast h)
      simp [hn, hiff, ho, hoz]
