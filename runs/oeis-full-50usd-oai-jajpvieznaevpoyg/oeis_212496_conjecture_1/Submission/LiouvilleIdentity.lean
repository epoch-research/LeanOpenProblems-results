import FormalConjectures.Util.ProblemImports

open BigOperators Finset Nat Real
open scoped ArithmeticFunction.Omega

def omega_mult (k : ℕ) : ℕ :=
  k.factorization.sum (fun _ e => e)

noncomputable
def b (n : ℕ) : ℝ :=
  Finset.sum (Icc 1 n) fun k =>
    let sign : ℤ := (fun k : ℕ =>
      let exponent : ℤ := (k : ℤ) - (omega_mult k : ℤ)
      if exponent % 2 = 0 then 1 else -1) k
    (sign : ℝ) / (k : ℝ)

lemma omega_mult_eq_cardFactors (n : ℕ) : omega_mult n = ArithmeticFunction.cardFactors n := by
  unfold omega_mult
  rw [ArithmeticFunction.cardFactors_eq_sum_factorization]

-- integer sign depending only on Omega parity
def liouvilleZ (n : ℕ) : ℤ := if omega_mult n % 2 = 0 then 1 else -1

def cZ (n : ℕ) : ℤ := if n % 2 = 0 then -liouvilleZ n else liouvilleZ n

lemma sign_eq_neg_cZ (k : ℕ) :
    (let exponent : ℤ := (k : ℤ) - (omega_mult k : ℤ)
      if exponent % 2 = 0 then (1 : ℤ) else -1) = - cZ k := by
  unfold cZ liouvilleZ
  by_cases hk : k % 2 = 0
  · simp [hk]
    -- need parity relation for Int subtraction when k even
    have hkz : (k : ℤ) % 2 = 0 := by exact_mod_cast hk
    by_cases ho : omega_mult k % 2 = 0
    · simp [ho]
      have hoz : ((omega_mult k : ℤ) % 2 = 0) := by exact_mod_cast ho
      have hsub : (((k : ℤ) - (omega_mult k : ℤ)) % 2 = 0) := by
        rw [Int.sub_emod]
        rw [hkz, hoz]
        norm_num
      simp [hsub]
    · simp [ho]
      have hoz : ¬ ((omega_mult k : ℤ) % 2 = 0) := by
        intro h
        apply ho
        exact_mod_cast h
      have hsub : ¬ (((k : ℤ) - (omega_mult k : ℤ)) % 2 = 0) := by
        intro h
        apply hoz
        -- from k even and k-o even => o even
        have := congrArg (fun x : ℤ => x % 2) (show (omega_mult k : ℤ) = (k : ℤ) - ((k : ℤ) - (omega_mult k : ℤ)) by ring)
        rw [this]
        rw [Int.sub_emod, hkz, h]
        norm_num
      simp [hsub]
  · simp [hk]
    have hkz_ne : ¬ ((k : ℤ) % 2 = 0) := by
      intro h; apply hk; exact_mod_cast h
    -- Since residues mod 2 are 0 or 1, use omega? maybe
    sorry
