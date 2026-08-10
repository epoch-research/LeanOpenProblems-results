import FormalConjectures.Util.ProblemImports
open BigOperators Finset Nat Real
open scoped ArithmeticFunction.Omega

def omega_mult (k : ℕ) : ℕ := k.factorization.sum (fun _ e => e)

lemma omega_mult_eq_cardFactors (n : ℕ) : omega_mult n = ArithmeticFunction.cardFactors n := by
  unfold omega_mult
  rw [ArithmeticFunction.cardFactors_eq_sum_factorization]

lemma int_even_sub_iff {a b : ℤ} (ha : a % 2 = 0) : (a - b) % 2 = 0 ↔ b % 2 = 0 := by
  constructor
  · intro h
    have hb : b = a - (a - b) := by ring
    rw [hb, Int.sub_emod, ha, h]
    norm_num
  · intro hb
    rw [Int.sub_emod, ha, hb]
    norm_num

lemma int_odd_sub_iff {a b : ℤ} (ha : a % 2 ≠ 0) : (a - b) % 2 = 0 ↔ b % 2 ≠ 0 := by
  constructor
  · intro h hb
    have hb' : (a - b) % 2 = a % 2 := by rw [Int.sub_emod, hb]; simp
    rw [h] at hb'
    exact ha hb'.symm
  · intro hb
    have ha1 : a % 2 = 1 := by omega
    have hb1 : b % 2 = 1 := by omega
    rw [Int.sub_emod, ha1, hb1]
    norm_num

lemma nat_even_int_iff (n : ℕ) : (n : ℤ) % 2 = 0 ↔ n % 2 = 0 := by
  constructor <;> intro h <;> exact_mod_cast h

lemma sign_split (k : ℕ) :
    (if ((k : ℤ) - (omega_mult k : ℤ)) % 2 = 0 then (1 : ℤ) else -1) =
      if k % 2 = 0 then
        (if omega_mult k % 2 = 0 then (1 : ℤ) else -1)
      else
        (if omega_mult k % 2 = 0 then (-1 : ℤ) else 1) := by
  by_cases hk : k % 2 = 0
  · simp [hk]
    have hkz : (k : ℤ) % 2 = 0 := (nat_even_int_iff k).2 hk
    have heq : (2 ∣ (k : ℤ) - (omega_mult k : ℤ)) ↔ (omega_mult k : ℤ) % 2 = 0 := by
      simpa [Int.dvd_iff_emod_eq_zero] using int_even_sub_iff hkz
    rw [heq]
    by_cases ho : omega_mult k % 2 = 0
    · have hoz : (omega_mult k : ℤ) % 2 = 0 := (nat_even_int_iff (omega_mult k)).2 ho
      simp [ho, hoz]
    · have hoz : (omega_mult k : ℤ) % 2 ≠ 0 := by
        intro h; exact ho ((nat_even_int_iff (omega_mult k)).1 h)
      simp [ho, hoz]
  · simp [hk]
    have hkz : (k : ℤ) % 2 ≠ 0 := by intro h; exact hk ((nat_even_int_iff k).1 h)
    have heq : (2 ∣ (k : ℤ) - (omega_mult k : ℤ)) ↔ (omega_mult k : ℤ) % 2 ≠ 0 := by
      simpa [Int.dvd_iff_emod_eq_zero] using int_odd_sub_iff hkz
    rw [heq]
    by_cases ho : omega_mult k % 2 = 0
    · have hoz : (omega_mult k : ℤ) % 2 = 0 := (nat_even_int_iff (omega_mult k)).2 ho
      simp [ho, hoz]
    · have hoz : (omega_mult k : ℤ) % 2 ≠ 0 := by
        intro h; exact ho ((nat_even_int_iff (omega_mult k)).1 h)
      simp [ho, hoz]
