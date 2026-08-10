import FormalConjectures.Util.ProblemImports

open Finset Nat Int

/-- Key divisibility step of the reduction: if `s ∣ E` and `1 ≤ s ≤ n`, then
`n ∣ C(n,s) * E`, because `s * C(n,s) = n * C(n-1,s-1)`. -/
theorem reduction_step (n s : ℕ) (E : ℤ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hdvd : (s : ℤ) ∣ E) : (n : ℤ) ∣ (n.choose s : ℤ) * E := by
  obtain ⟨E', rfl⟩ := hdvd
  -- s * C(n,s) = n * C(n-1,s-1)
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have key : (n' + 1) * n'.choose s' = (n' + 1).choose (s' + 1) * (s' + 1) :=
    Nat.succ_mul_choose_eq n' s'
  -- goal: (n'+1) ∣ C(n'+1,s'+1) * ((s'+1) * E')
  refine ⟨(n'.choose s' : ℤ) * E', ?_⟩
  have keyZ : ((n' + 1 : ℕ) : ℤ) * (n'.choose s' : ℤ)
      = ((n' + 1).choose (s' + 1) : ℤ) * ((s' + 1 : ℕ) : ℤ) := by
    exact_mod_cast key
  push_cast
  push_cast at keyZ
  linear_combination (-E') * keyZ

/-- Alternating partial sum of binomials: `A i n = ∑_{k<n} (-1)^k C(k,i)`. -/
def Aa (i n : ℕ) : ℤ := ∑ k ∈ Finset.range n, (-1 : ℤ) ^ k * (k.choose i : ℤ)

lemma Aa_succ (i n : ℕ) : Aa i (n + 1) = Aa i n + (-1 : ℤ) ^ n * (n.choose i : ℤ) := by
  unfold Aa; rw [Finset.sum_range_succ]

/-- The key recurrence: for `i ≥ 1`, `2·A i n + A (i-1) n = (-1)^(n-1) C(n,i)`.
    Stated as `2·A (i+1) n + A i n = (-1)^(n-1) C(n,i+1)`. -/
lemma Aa_recur (i n : ℕ) :
    2 * Aa (i + 1) n + Aa i n = (-1 : ℤ) ^ (n + 1) * (n.choose (i + 1) : ℤ) := by
  induction n with
  | zero => simp [Aa]
  | succ m ih =>
    rw [Aa_succ, Aa_succ]
    have hchoose : ((m + 1).choose (i + 1) : ℤ) = (m.choose i : ℤ) + (m.choose (i + 1) : ℤ) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    -- pow: (-1)^(m+1+1) = (-1)^(m+1) * (-1)
    have hpow : (-1 : ℤ) ^ (m + 1 + 1) = (-1 : ℤ) ^ (m + 1) * (-1) := by ring
    have hpowm : (-1 : ℤ) ^ (m + 1) = (-1 : ℤ) ^ m * (-1) := by ring
    rw [hpow, hchoose]
    rw [show 2 * (Aa (i+1) m + (-1:ℤ)^m * (m.choose (i+1):ℤ)) + (Aa i m + (-1:ℤ)^m * (m.choose i:ℤ))
        = (2 * Aa (i+1) m + Aa i m) + (-1:ℤ)^m * (2 * (m.choose (i+1):ℤ) + (m.choose i:ℤ)) from by ring]
    rw [ih, hpowm]
    ring

/-! ## General reduction identity (works for any `f : ℕ → ℤ`) -/

/-- `i`-th forward difference of `f` at `0`. -/
def fdiff (f : ℕ → ℤ) (i : ℕ) : ℤ := (fwdDiff (1 : ℕ))^[i] f 0

/-- `E_s(f) = ∑_{i<s} (Δ^i f)(0) (-2)^{s-1-i}`. -/
def EE (f : ℕ → ℤ) (s : ℕ) : ℤ := ∑ i ∈ Finset.range s, fdiff f i * (-2 : ℤ) ^ (s - 1 - i)

/-- `S(n)(f) = ∑_{k<n} (-1)^k f(k)`. -/
def SS (f : ℕ → ℤ) (n : ℕ) : ℤ := ∑ k ∈ Finset.range n, (-1 : ℤ) ^ k * f k

/-- `T(n)(f) = ∑_{s≤n} C(n,s) E_s(f)`. -/
def TT (f : ℕ → ℤ) (n : ℕ) : ℤ := ∑ s ∈ Finset.range (n + 1), (n.choose s : ℤ) * EE f s

lemma EE_zero (f : ℕ → ℤ) : EE f 0 = 0 := by simp [EE]

lemma EE_succ (f : ℕ → ℤ) (s : ℕ) : EE f (s + 1) = fdiff f s - 2 * EE f s := by
  unfold EE
  rw [Finset.sum_range_succ]
  have h1 : s + 1 - 1 - s = 0 := by omega
  rw [h1, pow_zero, mul_one]
  have h2 : ∀ i ∈ Finset.range s,
      fdiff f i * (-2 : ℤ) ^ (s + 1 - 1 - i) = -2 * (fdiff f i * (-2 : ℤ) ^ (s - 1 - i)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [show s + 1 - 1 - i = (s - 1 - i) + 1 from by omega, pow_succ]
    ring
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
  ring

/-- Gregory–Newton reconstruction (from Mathlib's `shift_eq_sum_fwdDiff_iter`). -/
lemma newton (f : ℕ → ℤ) (n : ℕ) :
    f n = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * fdiff f k := by
  have H := shift_eq_sum_fwdDiff_iter (h := (1 : ℕ)) f n 0
  simp only [smul_eq_mul, mul_one, zero_add, nsmul_eq_mul] at H
  rw [H]
  rfl

lemma TT_recur (f : ℕ → ℤ) (m : ℕ) : TT f (m + 1) = f m - TT f m := by
  have hL : TT f (m + 1) = ∑ s ∈ Finset.range (m + 2), ((m + 1).choose s : ℤ) * EE f s := rfl
  rw [hL, Finset.sum_range_succ']
  -- peel s = 0 term
  simp only [Nat.choose_zero_right, EE_zero, mul_zero, add_zero, Nat.cast_one]
  -- now: ∑ t ∈ range(m+1), C(m+1, t+1) * EE f (t+1) = f m - ∑ s ∈ range(m+1), C(m,s) EE f s
  have hpascal : ∀ t, ((m + 1).choose (t + 1) : ℤ) = (m.choose t : ℤ) + (m.choose (t + 1) : ℤ) := by
    intro t; rw [Nat.choose_succ_succ]; push_cast; ring
  have hstep : ∀ t ∈ Finset.range (m + 1),
      ((m + 1).choose (t + 1) : ℤ) * EE f (t + 1)
        = (m.choose t : ℤ) * (fdiff f t - 2 * EE f t) + (m.choose (t + 1) : ℤ) * EE f (t + 1) := by
    intro t _; rw [hpascal, EE_succ]; ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
  -- A-part: ∑ C(m,t)(fdiff - 2 EE) ; B-part: ∑ C(m,t+1) EE f(t+1)
  have hA : ∑ t ∈ Finset.range (m + 1), (m.choose t : ℤ) * (fdiff f t - 2 * EE f t)
      = f m - 2 * TT f m := by
    have : ∀ t ∈ Finset.range (m + 1),
        (m.choose t : ℤ) * (fdiff f t - 2 * EE f t)
          = (m.choose t : ℤ) * fdiff f t - 2 * ((m.choose t : ℤ) * EE f t) := by
      intro t _; ring
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← newton, ← Finset.mul_sum]
    rfl
  have hB : ∑ t ∈ Finset.range (m + 1), (m.choose (t + 1) : ℤ) * EE f (t + 1) = TT f m := by
    rw [Finset.sum_range_succ]
    have : ((m.choose (m + 1)) : ℤ) = 0 := by
      rw [Nat.choose_eq_zero_of_lt (by omega)]; rfl
    rw [this, zero_mul, add_zero]
    -- ∑ t ∈ range m, C(m,t+1) EE f(t+1) = TT f m = ∑ s ∈ range(m+1), C(m,s) EE f s
    unfold TT
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, EE_zero, mul_zero, add_zero, Nat.cast_one]
  rw [hA, hB]; ring

/-- **Reduction identity:** `S(n) = (-1)^{n+1} · ∑_{s≤n} C(n,s) E_s`. -/
theorem reduction (f : ℕ → ℤ) (n : ℕ) : SS f n = (-1 : ℤ) ^ (n + 1) * TT f n := by
  induction n with
  | zero => simp [SS, TT, EE]
  | succ m ih =>
    have hSS : SS f (m + 1) = SS f m + (-1 : ℤ) ^ m * f m := by
      simp only [SS, Finset.sum_range_succ]
    rw [hSS, ih, TT_recur]
    rw [pow_succ, pow_succ]
    ring

/-- **Conditional divisibility:** if `s ∣ E_s(f)` for all `1 ≤ s ≤ n`, then `n ∣ S(n)(f)`. -/
theorem divis (f : ℕ → ℤ) (n : ℕ)
    (hE : ∀ s, 1 ≤ s → s ≤ n → (s : ℤ) ∣ EE f s) : (n : ℤ) ∣ SS f n := by
  rw [reduction]
  apply _root_.dvd_mul_of_dvd_right
  unfold TT
  apply Finset.dvd_sum
  intro s hs
  rw [Finset.mem_range] at hs
  rcases Nat.eq_zero_or_pos s with h0 | hpos
  · subst h0; rw [EE_zero, mul_zero]; exact dvd_zero _
  · exact reduction_step n s (EE f s) hpos (by omega) (hE s hpos (by omega))

/-- **2-adic reduction:** if `2^i ∣ (Δ^i f)(0)` for all `i`, then `2^(s-1) ∣ E_s(f)`.
    (Each term of `E_s` has `v₂ ≥ i + (s-1-i) = s-1`.) Hence the 2-part of `s ∣ E_s`
    holds, since `v₂(s) ≤ s-1`. -/
lemma two_adic_EE (f : ℕ → ℤ) (hf : ∀ i, (2 : ℤ) ^ i ∣ fdiff f i) (s : ℕ) :
    (2 : ℤ) ^ (s - 1) ∣ EE f s := by
  unfold EE
  apply Finset.dvd_sum
  intro i hi
  rw [Finset.mem_range] at hi
  have h1 : (2 : ℤ) ^ (s - 1) = (2 : ℤ) ^ i * (2 : ℤ) ^ (s - 1 - i) := by
    rw [← pow_add]; congr 1; omega
  rw [h1]
  refine mul_dvd_mul (hf i) ?_
  rw [show (-2 : ℤ) = (-1) * 2 from by ring, mul_pow]
  exact (dvd_refl _).mul_left _

/-- The 2-part of `s ∣ E_s(f)` follows from `2^i ∣ (Δ^i f)(0)`, since `v₂(s) ≤ s-1`. -/
lemma two_part_EE (f : ℕ → ℤ) (hf : ∀ i, (2 : ℤ) ^ i ∣ fdiff f i) (s : ℕ) (hs : 1 ≤ s) :
    (2 : ℤ) ^ (padicValNat 2 s) ∣ EE f s := by
  refine dvd_trans (pow_dvd_pow 2 ?_) (two_adic_EE f hf s)
  have h1 : (2 : ℕ) ^ (padicValNat 2 s) ∣ s := pow_padicValNat_dvd
  have h2 : (2 : ℕ) ^ (padicValNat 2 s) ≤ s := Nat.le_of_dvd hs h1
  have h3 : padicValNat 2 s < 2 ^ (padicValNat 2 s) := Nat.lt_two_pow _
  omega
