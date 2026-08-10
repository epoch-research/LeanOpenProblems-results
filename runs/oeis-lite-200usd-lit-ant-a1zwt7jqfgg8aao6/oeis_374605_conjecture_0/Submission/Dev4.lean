import FormalConjectures.Util.ProblemImports
open Finset

-- ascFactorial first-factor split: n.ascFactorial (k+1) = n * (n+1).ascFactorial k
theorem asc_split (n k : ℕ) : n.ascFactorial (k+1) = n * (n+1).ascFactorial k := by
  induction k with
  | zero => simp [Nat.ascFactorial_succ, Nat.ascFactorial_zero]
  | succ k ih =>
    rw [Nat.ascFactorial_succ, ih, Nat.ascFactorial_succ]
    ring

theorem choose_mul_fact (p k : ℕ) (hk : 1 ≤ k) (hkp : k ≤ p) :
    (Nat.choose (p - 1 + k) k) * (Nat.factorial k) = p.ascFactorial k := by
  have hpk : k ≤ p - 1 + k := by omega
  have h1 := Nat.choose_mul_factorial_mul_factorial hpk
  have hsub : (p - 1 + k) - k = p - 1 := by omega
  rw [hsub] at h1
  have h2 : (Nat.factorial (p-1)) * p.ascFactorial k = (Nat.factorial (p-1+k)) := by
    have := Nat.factorial_mul_ascFactorial (p-1) k
    have hp1 : p - 1 + 1 = p := by omega
    rw [hp1] at this; exact this
  rw [← h2] at h1
  have hpos : 0 < (Nat.factorial (p-1)) := Nat.factorial_pos _
  have key : (Nat.factorial (p-1)) * ((p - 1 + k).choose k * k.factorial) = (Nat.factorial (p-1)) * p.ascFactorial k := by
    rw [← Nat.mul_assoc, Nat.mul_comm (Nat.factorial (p-1))] at *
    linarith [h1]
  exact Nat.eq_of_mul_eq_mul_left hpos key

-- p divides C(p-1+k,k) for 1 ≤ k ≤ p-1
theorem p_dvd_choose1 (p k : ℕ) [hp : Fact p.Prime] (hk : 1 ≤ k) (hkp : k ≤ p - 1) :
    p ∣ Nat.choose (p - 1 + k) k := by
  apply hp.1.dvd_choose (a := k) (b := p - 1 + k) <;> omega

-- (A_k : ZMod p) where A_k = C(p-1+k,k)/p satisfies A_k * k = 1
-- (p+1).ascFactorial m ≡ m! mod p
theorem asc_mod (p m : ℕ) : (((p+1).ascFactorial m : ℕ) : ZMod p) = (m.factorial : ZMod p) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.ascFactorial_succ, Nat.factorial_succ]
    push_cast [ih]
    have hpz : (p : ZMod p) = 0 := ZMod.natCast_self p
    have hh : ((p : ZMod p) + 1 + (m:ZMod p)) = (m:ZMod p) + 1 := by rw [hpz]; ring
    rw [hh]

theorem Ak_mod (p k : ℕ) [hp : Fact p.Prime] (hk : 1 ≤ k) (hkp : k ≤ p - 1) :
    ((Nat.choose (p-1+k) k / p : ℕ) : ZMod p) * (k : ZMod p) = 1 := by
  have hcf := choose_mul_fact p k hk (by omega)
  have hsplit := asc_split p (k-1)
  have hk1 : k - 1 + 1 = k := by omega
  rw [hk1] at hsplit
  -- hcf: C*k! = p.asc k ; hsplit: p.asc k = p * (p+1).asc (k-1)
  rw [hsplit] at hcf
  -- hcf : C * k! = p * (p+1).asc (k-1)
  have hdvd := p_dvd_choose1 p k hk hkp
  obtain ⟨A, hA⟩ := hdvd   -- C = p * A
  rw [hA] at hcf
  -- p*A*k! = p*(p+1).asc(k-1)
  have hp0 : 0 < p := hp.1.pos
  have hAk : A * k.factorial = (p+1).ascFactorial (k-1) := by
    have : p * (A * k.factorial) = p * (p+1).ascFactorial (k-1) := by ring_nf; ring_nf at hcf; linarith [hcf]
    exact Nat.eq_of_mul_eq_mul_left hp0 this
  -- divide: A_k = C/p = A
  have hquot : Nat.choose (p-1+k) k / p = A := by rw [hA]; exact Nat.mul_div_cancel_left A hp0
  rw [hquot]
  -- (A:ZMod p) * k = 1
  -- from hAk cast: A * k! = (k-1)! mod p, and k! = k*(k-1)!
  have hcast : (A : ZMod p) * (k.factorial : ZMod p) = ((k-1).factorial : ZMod p) := by
    have hc : ((A * k.factorial : ℕ) : ZMod p) = (((p+1).ascFactorial (k-1) : ℕ) : ZMod p) := by
      rw [hAk]
    push_cast at hc
    rw [hc, asc_mod]
  have hfact : (k.factorial : ZMod p) = (k : ZMod p) * ((k-1).factorial : ZMod p) := by
    have : k.factorial = k * (k-1).factorial := by
      conv_lhs => rw [← hk1, Nat.factorial_succ, hk1]
    rw [this]; push_cast; ring
  have hunit : ((k-1).factorial : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.Prime.dvd_factorial hp.1 |>.mp hd
    omega
  rw [hfact] at hcast
  -- (A) * (k * (k-1)!) = (k-1)!  => (A*k)*(k-1)! = 1*(k-1)!
  have : ((A : ZMod p) * (k:ZMod p)) * ((k-1).factorial : ZMod p) = 1 * ((k-1).factorial : ZMod p) := by
    rw [one_mul]; linear_combination hcast
  exact mul_right_cancel₀ hunit this
