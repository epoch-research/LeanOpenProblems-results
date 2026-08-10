import FormalConjectures.Util.ProblemImports

open Nat Finset

-- Key: centralBinom n ≤ (2n)^(count Prime (2n+1))
theorem cb_le (n : ℕ) (hn : 0 < n) :
    Nat.centralBinom n ≤ (2 * n) ^ (Nat.count Nat.Prime (2 * n + 1)) := by
  have hpos : 0 < 2 * n := by omega
  rw [← Nat.prod_pow_factorization_centralBinom n]
  rw [Nat.count_eq_card_filter_range]
  set S := (Finset.range (2*n+1)).filter (fun p => Nat.Prime p) with hS
  have hsub : S ⊆ Finset.range (2*n+1) := Finset.filter_subset _ _
  calc (∏ p ∈ Finset.range (2*n+1), p ^ (Nat.centralBinom n).factorization p)
      = ∏ p ∈ S, p ^ (Nat.centralBinom n).factorization p := by
        symm
        apply Finset.prod_subset hsub
        intro p hp hpnot
        have : ¬ Nat.Prime p := by
          simp only [hS, Finset.mem_filter] at hpnot
          tauto
        rw [Nat.factorization_eq_zero_of_non_prime _ this, pow_zero]
    _ ≤ ∏ _p ∈ S, (2 * n) := by
        apply Finset.prod_le_prod'
        intro p hp
        exact Nat.pow_factorization_choose_le hpos
    _ = (2 * n) ^ S.card := by rw [Finset.prod_const]

-- π lower bound, pure Nat
theorem pi_lower (n a K : ℕ) (hn : 0 < n) (ha : 2 * n < 2 ^ a) (hK : a * K ≤ 2 * n) :
    K ≤ Nat.count Nat.Prime (2 * n + 1) := by
  set c := Nat.count Nat.Prime (2 * n + 1) with hc
  have h4 : 4 ^ n ≤ 2 * n * Nat.centralBinom n :=
    Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
  have hcb : 2 * n * Nat.centralBinom n ≤ 2 * n * (2 * n) ^ c :=
    Nat.mul_le_mul_left _ (cb_le n hn)
  have hH : (2:ℕ) ^ (2 * n) ≤ (2 * n) ^ (c + 1) := by
    have e4 : (4:ℕ) ^ n = 2 ^ (2 * n) := by
      rw [show (4:ℕ) = 2^2 by norm_num, ← pow_mul]
    have epow : 2 * n * (2 * n) ^ c = (2 * n) ^ (c + 1) := by ring
    calc (2:ℕ)^(2*n) = 4^n := e4.symm
      _ ≤ 2 * n * Nat.centralBinom n := h4
      _ ≤ 2 * n * (2 * n) ^ c := hcb
      _ = (2 * n) ^ (c + 1) := epow
  by_contra hlt
  push_neg at hlt  -- c < K
  have hK1 : K ≠ 0 := by omega
  have h1 : (2 * n) ^ (c + 1) ≤ (2 * n) ^ K :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (2 * n) ^ K < (2 ^ a) ^ K := Nat.pow_lt_pow_left ha hK1
  have h3 : (2 ^ a) ^ K = 2 ^ (a * K) := by rw [← pow_mul]
  have h4' : (2:ℕ) ^ (a * K) ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) hK
  have : (2:ℕ) ^ (2 * n) < 2 ^ (2 * n) := by
    calc (2:ℕ)^(2*n) ≤ (2*n)^(c+1) := hH
      _ ≤ (2*n)^K := h1
      _ < (2^a)^K := h2
      _ = 2^(a*K) := h3
      _ ≤ 2^(2*n) := h4'
  exact absurd this (lt_irrefl _)

open Real in
theorem increase_step (n qi qi1 : ℕ) (hn : 2 ≤ n)
    (hqin : n ≤ qi)
    (hA : qi * (n + 1) ≤ qi1 * n)
    (hB : (n + 1) * (n + 1) ≤ qi1 * n) :
    Int.toNat ⌊(n : ℝ) ^ ((qi : ℝ) / n)⌋ <
      Int.toNat ⌊((n + 1 : ℕ) : ℝ) ^ ((qi1 : ℝ) / (n + 1))⌋ := by
  have hx0 : (0:ℝ) < n := by positivity
  have hx1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hx1' : (0:ℝ) < (n:ℝ) + 1 := by positivity
  set x : ℝ := (n : ℝ) with hxdef
  -- a and b
  set a : ℝ := x ^ ((qi:ℝ)/x) with hadef
  set b : ℝ := (x + 1) ^ ((qi1:ℝ)/(x+1)) with hbdef
  have hcast : ((n + 1 : ℕ) : ℝ) = x + 1 := by push_cast [hxdef]; ring
  rw [hcast]
  -- logs
  have hla : Real.log a = ((qi:ℝ)/x) * Real.log x := Real.log_rpow hx0 _
  have hlb : Real.log b = ((qi1:ℝ)/(x+1)) * Real.log (x+1) := Real.log_rpow hx1' _
  have hlogx : (0:ℝ) ≤ Real.log x := Real.log_nonneg hx1
  -- a ≥ x
  have hqix : (1:ℝ) ≤ (qi:ℝ)/x := by
    rw [le_div_iff₀ hx0, one_mul, hxdef]; exact_mod_cast hqin
  have hax : x ≤ a := by
    have := Real.rpow_le_rpow_of_exponent_le hx1 hqix
    rwa [Real.rpow_one] at this
  have ha0 : (0:ℝ) < a := lt_of_lt_of_le hx0 hax
  have hb0 : (0:ℝ) < b := Real.rpow_pos_of_pos hx1' _
  -- d := log((x+1)/x) ≥ 1/(x+1)
  have hdivpos : (0:ℝ) < (x+1)/x := by positivity
  have hd_eq : Real.log ((x+1)/x) = Real.log (x+1) - Real.log x :=
    Real.log_div (by positivity) (by positivity)
  have hxx1 : (0:ℝ) < x/(x+1) := by positivity
  have hlog_small : Real.log (x/(x+1)) ≤ x/(x+1) - 1 := Real.log_le_sub_one_of_pos hxx1
  have hd_lb : (1:ℝ)/(x+1) ≤ Real.log (x+1) - Real.log x := by
    have hneg : Real.log (x/(x+1)) = -(Real.log (x+1) - Real.log x) := by
      rw [Real.log_div (by positivity) (by positivity)]; ring
    have hrw : x/(x+1) - 1 = -(1/(x+1)) := by field_simp; ring
    rw [hneg, hrw] at hlog_small
    linarith
  -- numerator ≥ x+1
  have hnum : (x + 1) ≤ qi1 * x * Real.log (x+1) - qi * (x+1) * Real.log x := by
    have hlogsub : Real.log (x+1) = Real.log x + (Real.log (x+1) - Real.log x) := by ring
    -- term1 coeff ≥ 0
    have hcoef : (0:ℝ) ≤ (qi1 * x - qi * (x+1)) := by
      have : (qi:ℝ) * (x+1) ≤ qi1 * x := by
        have := (by exact_mod_cast hA : ((qi * (n+1):ℕ):ℝ) ≤ ((qi1 * n:ℕ):ℝ))
        push_cast [hxdef] at this ⊢; linarith
      linarith
    have hterm1 : (0:ℝ) ≤ (qi1 * x - qi * (x+1)) * Real.log x := mul_nonneg hcoef hlogx
    -- term2 ≥ x+1
    have hqi1x : (x+1)*(x+1) ≤ qi1 * x := by
      have := (by exact_mod_cast hB : (((n+1)*(n+1):ℕ):ℝ) ≤ ((qi1 * n:ℕ):ℝ))
      push_cast [hxdef] at this ⊢; linarith
    have hterm2 : (x + 1) ≤ qi1 * x * (Real.log (x+1) - Real.log x) := by
      have h1 : qi1 * x * (1/(x+1)) ≤ qi1 * x * (Real.log (x+1) - Real.log x) := by
        apply mul_le_mul_of_nonneg_left hd_lb
        positivity
      have h2 : (x+1) ≤ qi1 * x * (1/(x+1)) := by
        rw [mul_one_div, le_div_iff₀ hx1']
        linarith [hqi1x]
      linarith
    -- combine
    have expand : qi1 * x * Real.log (x+1) - qi * (x+1) * Real.log x
        = (qi1 * x - qi * (x+1)) * Real.log x + qi1 * x * (Real.log (x+1) - Real.log x) := by
      rw [hlogsub]; ring
    rw [expand]; linarith
  -- log b - log a ≥ 1/x
  have hlogdiff : (1:ℝ)/x ≤ Real.log b - Real.log a := by
    rw [hla, hlb]
    have heq : ((qi1:ℝ)/(x+1))*Real.log (x+1) - ((qi:ℝ)/x)*Real.log x
             = (qi1*x*Real.log (x+1) - qi*(x+1)*Real.log x)/(x*(x+1)) := by
      field_simp
    rw [heq, le_div_iff₀ (by positivity)]
    have hone : (1:ℝ)/x * (x*(x+1)) = x+1 := by field_simp
    rw [hone]
    exact hnum
  -- a + 1 ≤ b
  have hab : a + 1 ≤ b := by
    have h1a : (0:ℝ) < a + 1 := by linarith
    have hloga1 : Real.log (a+1) ≤ Real.log a + 1/a := by
      have : Real.log (a+1) - Real.log a = Real.log ((a+1)/a) := (Real.log_div (by linarith) ha0.ne').symm
      have hle : Real.log ((a+1)/a) ≤ (a+1)/a - 1 := Real.log_le_sub_one_of_pos (by positivity)
      have : (a+1)/a - 1 = 1/a := by field_simp; ring
      linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < (a+1)/a by positivity),
                (Real.log_div (show (a:ℝ)+1 ≠ 0 by linarith) ha0.ne')]
    have hinva : (1:ℝ)/a ≤ 1/x := by
      apply one_div_le_one_div_of_le hx0 hax
    have : Real.log (a+1) ≤ Real.log b := by
      have := hlogdiff
      linarith
    exact (Real.log_le_log_iff h1a hb0).mp this
  -- floors
  have hfa : (0:ℤ) ≤ ⌊a⌋ := by
    apply Int.le_floor.mpr; simpa using le_of_lt ha0
  have hfloor : ⌊a⌋ < ⌊b⌋ := by
    have hb1 : ((⌊a⌋ + 1 : ℤ) : ℝ) ≤ b := by
      push_cast; linarith [Int.floor_le a]
    have := Int.le_floor.mpr hb1
    omega
  show Int.toNat ⌊a⌋ < Int.toNat ⌊b⌋
  -- toNat mono
  omega
