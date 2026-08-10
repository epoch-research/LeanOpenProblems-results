import FormalConjectures.Util.ProblemImports

/--
A181546: $a(n) = \sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n-k}{k}^4$.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n / 2 + 1)) fun k => ((n-k).choose k) ^ 4

-- The general function F(n, L) mentioned in the conjecture.
def F (n L : ℕ) : ℕ :=
  Finset.sum (Finset.range (n / 2 + 1)) fun k => ((n-k).choose k) ^ L

open Filter Asymptotics Real
open scoped Nat
open Topology

/--
The conjectured limit value, specialized for a given L.
$T(L) = \frac{\mathrm{Fib}(L)\sqrt{5} + \mathrm{Lucas}(L)}{2}$.
We use `lucasNumber` from $\mathbb{Z}$ and cast to $\mathbb{R}$.
-/
noncomputable def limit_value (L : ℕ) : ℝ :=
  let fib_L : ℝ := Nat.fib L
  let lucas_L : ℝ := (lucasNumber L : ℤ)
  (fib_L * sqrt 5 + lucas_L) / 2

noncomputable section

local notation "Φ" => goldenRatio
local notation "Ψ" => goldenConj

theorem phi_pow_succ_succ (m : ℕ) : Φ ^ (m+2) = Φ^(m+1) + Φ^m := by
  have := goldenRatio_sq
  calc Φ ^ (m+2) = Φ^2 * Φ^m := by ring
    _ = (Φ + 1) * Φ^m := by rw [goldenRatio_sq]
    _ = Φ^(m+1) + Φ^m := by ring

theorem psi_pow_succ_succ (m : ℕ) : Ψ ^ (m+2) = Ψ^(m+1) + Ψ^m := by
  calc Ψ ^ (m+2) = Ψ^2 * Ψ^m := by ring
    _ = (Ψ + 1) * Ψ^m := by rw [goldenConj_sq]
    _ = Ψ^(m+1) + Ψ^m := by ring

theorem lucas_real (n : ℕ) : (lucasNumber n : ℝ) = Φ ^ n + Ψ ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [lucasNumber, LucasSequence.V]; norm_num
    | 1 =>
      simp only [lucasNumber, LucasSequence.V, pow_one]
      push_cast
      linarith [goldenRatio_add_goldenConj]
    | (m+2) =>
      have hrec : lucasNumber (m+2) = lucasNumber (m+1) + lucasNumber m := by
        simp [lucasNumber, LucasSequence.V]
      rw [hrec]
      push_cast
      rw [ih (m+1) (by omega), ih m (by omega), phi_pow_succ_succ, psi_pow_succ_succ]
      ring

theorem limit_value_eq (L : ℕ) : limit_value L = Φ ^ L := by
  unfold limit_value
  simp only
  rw [lucas_real, Real.coe_fib_eq]
  have h5 : Real.sqrt 5 ≠ 0 := by positivity
  field_simp
  ring

def b (n k : ℕ) : ℕ := (n-k).choose k

theorem succ_choose_mul (a k : ℕ) :
    (a+1).choose k * (a+1-k) = (a+1) * a.choose k := by
  have h1 := Nat.choose_succ_right_eq (a+1) k
  have h2 := Nat.succ_mul_choose_eq a k
  simp only [Nat.succ_eq_add_one] at h2
  omega

theorem b_ratio_k_abstract (c j : ℕ) :
    c.choose (j+1) * (c+1) * (j+1) = (c+1).choose j * (c+1-j) * (c-j) := by
  have h1 := Nat.choose_succ_right_eq c j
  have h2 := succ_choose_mul c j
  nlinarith [h1, h2, Nat.zero_le (c.choose j), Nat.zero_le (c.choose (j+1))]

theorem b_ratio_k (n j : ℕ) (h : 2*j+1 ≤ n) :
    b n (j+1) * (n-j) * (j+1) = b n j * (n-2*j) * (n-2*j-1) := by
  have key := b_ratio_k_abstract (n-j-1) j
  have c1 : (n-j-1)+1 = n-j := by omega
  rw [c1] at key
  have c2 : n-j-j = n-2*j := by omega
  have c3 : n-j-1-j = n-2*j-1 := by omega
  rw [c2, c3] at key
  unfold b
  have e1 : n - (j+1) = n-j-1 := by omega
  rw [e1]
  exact key

-- real cast of b_ratio_k
theorem b_ratio_k_real (n j : ℕ) (h : 2*j+1 ≤ n) :
    (b n (j+1) : ℝ) * ((n:ℝ)-j) * ((j:ℝ)+1) = (b n j : ℝ) * ((n:ℝ)-2*j) * ((n:ℝ)-2*j-1) := by
  have key := b_ratio_k n j h
  have hc1 : ((n - j : ℕ) : ℝ) = (n:ℝ) - j := by rw [Nat.cast_sub (by omega : j ≤ n)]
  have hc2 : ((n - 2*j : ℕ) : ℝ) = (n:ℝ) - 2*j := by
    rw [Nat.cast_sub (by omega : 2*j ≤ n)]; push_cast; ring
  have hc3 : ((n - 2*j - 1 : ℕ) : ℝ) = (n:ℝ) - 2*j - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n - 2*j), hc2]; push_cast; ring
  have : ((b n (j+1) * (n-j) * (j+1) : ℕ) : ℝ) = ((b n j * (n-2*j) * (n-2*j-1) : ℕ) : ℝ) := by
    exact_mod_cast key
  push_cast at this
  rw [hc1, hc2, hc3] at this
  linarith [this]

-- generic division helpers
theorem ratio_le_helper (A B P Q c : ℝ) (heq : A*P = B*Q) (hP : 0 < P) (hB : 0 ≤ B)
    (hQ : Q ≤ c*P) : A ≤ c*B := by
  have h1 : B*Q ≤ B*(c*P) := mul_le_mul_of_nonneg_left hQ hB
  have h2 : A*P ≤ (c*B)*P := by rw [heq]; nlinarith [h1]
  exact le_of_mul_le_mul_right (by linarith [h2]) hP

theorem ratio_ge_helper (A B P Q c : ℝ) (heq : A*P = B*Q) (hP : 0 < P) (hB : 0 ≤ B)
    (hQ : c*P ≤ Q) : c*B ≤ A := by
  have h1 : B*(c*P) ≤ B*Q := mul_le_mul_of_nonneg_left hQ hB
  have h2 : (c*B)*P ≤ A*P := by rw [heq]; nlinarith [h1]
  exact le_of_mul_le_mul_right (by linarith [h2]) hP

-- Real inequalities (proven earlier)
theorem ineq_monodec (N J s : ℝ) (hs : s^2 = 5) (hs0 : 0 < s) (hN : 2 ≤ N)
    (hJ0 : 0 ≤ J) (hJn : 2*J ≤ N) (hlo : (5-s)*N ≤ 10*J) :
    (N-2*J)*(N-2*J-1) ≤ (N-J)*(J+1) := by
  have hsN : 0 ≤ s*N := by positivity
  have key : 0 ≤ s*N - (5*N-10*J) := by linarith
  have hsN2 : s^2 * N^2 = 5 * N^2 := by rw [hs]
  nlinarith [mul_nonneg key (by linarith : (0:ℝ) ≤ s*N + (5*N-10*J)), hsN2, hN, hJ0, hJn]

theorem ineq_monoinc (N J s : ℝ) (hs : s^2 = 5) (hs0 : 0 < s) (hN : 2 ≤ N)
    (hJ0 : 0 ≤ J) (hJn : 2*J ≤ N) (hhi : 10*J ≤ (5-s)*N - 10) :
    (N-J)*(J+1) ≤ (N-2*J)*(N-2*J-1) := by
  have hsN : 0 ≤ s*N := by positivity
  have key : 0 ≤ (5*N-10*J) - s*N := by nlinarith [hs0, hN]
  have hsN2 : s^2 * N^2 = 5 * N^2 := by rw [hs]
  nlinarith [mul_nonneg key (by linarith : (0:ℝ) ≤ (5*N-10*J) + s*N), hsN2, hN, hJ0, hJn]

theorem ineq_strongdec (N J s β : ℝ) (hs : s^2 = 5) (hs0 : 0 < s) (hN : 2 ≤ N)
    (hJ0 : 0 ≤ J) (hJn : 2*J ≤ N) (hb : 0 < β)
    (hstr : (5-s)*N + 10*β*N ≤ 10*J) :
    β*s/2 * N^2 ≤ (N-J)*(J+1) - (N-2*J)*(N-2*J-1) := by
  have key : 10*β*N ≤ s*N - (5*N-10*J) := by linarith
  have h2 : 0 ≤ s*N + (5*N-10*J) := by nlinarith [hs0, hN]
  have hbN : 0 ≤ 10*β*N := by positivity
  have hprod := mul_le_mul_of_nonneg_right key h2
  have hsN2 : s^2 * N^2 = 5 * N^2 := by rw [hs]
  have hextra : 0 ≤ 10*β*N*(5*N-10*J) := mul_nonneg hbN (by linarith)
  nlinarith [hprod, hsN2, hN, hJ0, hJn, hextra]

theorem ineq_stronginc (N J s β : ℝ) (hs : s^2 = 5) (hs0 : 0 < s) (hN : 2 ≤ N)
    (hJ0 : 0 ≤ J) (hJn : 2*J ≤ N) (hb : 0 < β)
    (hstr : 10*J ≤ (5-s)*N - 10*β*N) :
    β*s/2 * N^2 - 2*N ≤ (N-2*J)*(N-2*J-1) - (N-J)*(J+1) := by
  have key : 10*β*N ≤ (5*N-10*J) - s*N := by linarith
  have h2 : 0 ≤ s*N := by positivity
  have hbN : 0 ≤ 10*β*N := by positivity
  have hprod := mul_le_mul_of_nonneg_right key h2
  have hsN2 : s^2 * N^2 = 5 * N^2 := by rw [hs]
  have hextra : 0 ≤ ((5*N-10*J)-s*N)*(5*N-10*J) := by
    apply mul_nonneg; nlinarith [hs0,hN]; linarith
  nlinarith [hprod, hsN2, hN, hJ0, hJn, hextra]

theorem sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
theorem sqrt5_pos : (0:ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
theorem sqrt5_gt2 : (2:ℝ) < Real.sqrt 5 := by
  have := sqrt5_sq; nlinarith [sqrt5_pos]
theorem sqrt5_lt3 : Real.sqrt 5 < 3 := by
  have := sqrt5_sq; nlinarith [sqrt5_pos]

-- helper: b n (j+1) = 0 when 2*j = n
theorem b_succ_zero (n j : ℕ) (h : 2*j = n) : b n (j+1) = 0 := by
  unfold b
  apply Nat.choose_eq_zero_of_lt
  omega

theorem mono_dec_step (n j : ℕ) (hn2 : 2 ≤ n) (hjn : 2*j ≤ n)
    (hge : (5 - Real.sqrt 5) * n ≤ 10 * j) : (b n (j+1) : ℝ) ≤ (b n j : ℝ) := by
  rcases Nat.lt_or_ge (2*j+1) (n+1) with hlt | hge2
  · have h2j1 : 2*j+1 ≤ n := by omega
    have heq := b_ratio_k_real n j h2j1
    have hjle : (j:ℝ) ≤ n := by exact_mod_cast (by omega : j ≤ n)
    have hQP : ((n:ℝ)-2*j)*((n:ℝ)-2*j-1) ≤ ((n:ℝ)-j)*((j:ℝ)+1) :=
      ineq_monodec n j (Real.sqrt 5) sqrt5_sq sqrt5_pos
        (by exact_mod_cast hn2) (by positivity)
        (by exact_mod_cast hjn) (by exact_mod_cast hge)
    have hP : (0:ℝ) < ((n:ℝ)-j)*((j:ℝ)+1) := by
      apply mul_pos
      · have : (j:ℝ) + 1 ≤ n := by exact_mod_cast (by omega : j+1 ≤ n); 
        linarith
      · positivity
    have heq2 : (b n (j+1):ℝ) * (((n:ℝ)-j)*((j:ℝ)+1)) = (b n j:ℝ) * (((n:ℝ)-2*j)*((n:ℝ)-2*j-1)) := by
      linear_combination heq
    have := ratio_le_helper (b n (j+1)) (b n j) (((n:ℝ)-j)*((j:ℝ)+1))
      (((n:ℝ)-2*j)*((n:ℝ)-2*j-1)) 1 heq2 hP (by positivity)
      (by rw [one_mul]; exact hQP)
    rwa [one_mul] at this
  · have : 2*j = n := by omega
    rw [b_succ_zero n j this, Nat.cast_zero]
    positivity

-- helper: P = (n-j)(j+1) ≤ n^2  and  P > 0  (for 2j+1 ≤ n)
theorem P_pos (n j : ℕ) (h : 2*j+1 ≤ n) : (0:ℝ) < ((n:ℝ)-j)*((j:ℝ)+1) := by
  have hjle : (j:ℝ)+1 ≤ n := by exact_mod_cast (by omega : j+1 ≤ n)
  apply mul_pos <;> [linarith; positivity]
theorem P_le_n2 (n j : ℕ) (h : 2*j+1 ≤ n) : ((n:ℝ)-j)*((j:ℝ)+1) ≤ (n:ℝ)^2 := by
  have h1 : (j:ℝ) ≤ n := by exact_mod_cast (by omega : j ≤ n)
  have h2 : (j:ℝ)+1 ≤ n := by exact_mod_cast (by omega : j+1 ≤ n)
  have h3 : (0:ℝ) ≤ (n:ℝ)-j := by linarith
  nlinarith [Nat.cast_nonneg (α:=ℝ) j, Nat.cast_nonneg (α:=ℝ) n]

theorem mono_inc_step (n j : ℕ) (hn2 : 2 ≤ n) (hjn : 2*j ≤ n)
    (hhi : 10 * j ≤ (5 - Real.sqrt 5) * n - 10) : (b n j : ℝ) ≤ (b n (j+1) : ℝ) := by
  have hreal : (10*j : ℝ) ≤ 3*n := by
    have := sqrt5_gt2; nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have hnat : 10*j ≤ 3*n := by exact_mod_cast hreal
  have h2j1 : 2*j+1 ≤ n := by omega
  have heq := b_ratio_k_real n j h2j1
  have hQP : ((n:ℝ)-j)*((j:ℝ)+1) ≤ ((n:ℝ)-2*j)*((n:ℝ)-2*j-1) :=
    ineq_monoinc n j (Real.sqrt 5) sqrt5_sq sqrt5_pos (by exact_mod_cast hn2)
      (by positivity) (by exact_mod_cast hjn) (by exact_mod_cast hhi)
  have heq2 : (b n (j+1):ℝ) * (((n:ℝ)-j)*((j:ℝ)+1)) = (b n j:ℝ) * (((n:ℝ)-2*j)*((n:ℝ)-2*j-1)) := by
    linear_combination heq
  have := ratio_ge_helper (b n (j+1)) (b n j) (((n:ℝ)-j)*((j:ℝ)+1))
    (((n:ℝ)-2*j)*((n:ℝ)-2*j-1)) 1 heq2 (P_pos n j h2j1) (by positivity)
    (by rw [one_mul]; exact hQP)
  rwa [one_mul] at this

theorem strong_dec_step (n j : ℕ) (hn2 : 2 ≤ n) (hjn : 2*j ≤ n) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hstr : (5 - Real.sqrt 5) * n + 10*β*n ≤ 10 * j) :
    (b n (j+1) : ℝ) ≤ (1 - β*Real.sqrt 5/4) * (b n j : ℝ) := by
  have hcpos : (0:ℝ) ≤ 1 - β*Real.sqrt 5/4 := by
    have := sqrt5_lt3; nlinarith
  rcases Nat.lt_or_ge (2*j+1) (n+1) with hlt | hge2
  · have h2j1 : 2*j+1 ≤ n := by omega
    have heq := b_ratio_k_real n j h2j1
    have hAdd : β*Real.sqrt 5/2 * (n:ℝ)^2 ≤ ((n:ℝ)-j)*((j:ℝ)+1) - ((n:ℝ)-2*j)*((n:ℝ)-2*j-1) :=
      ineq_strongdec n j (Real.sqrt 5) β sqrt5_sq sqrt5_pos (by exact_mod_cast hn2)
        (by positivity) (by exact_mod_cast hjn) hβ (by exact_mod_cast hstr)
    have hPn2 := P_le_n2 n j h2j1
    have hc : (0:ℝ) ≤ β*Real.sqrt 5/4 := by positivity
    have hP0 : (0:ℝ) ≤ ((n:ℝ)-j)*((j:ℝ)+1) := (P_pos n j h2j1).le
    have hprod1 : (0:ℝ) ≤ β*Real.sqrt 5/4 * ((n:ℝ)^2 - ((n:ℝ)-j)*((j:ℝ)+1)) :=
      mul_nonneg hc (by linarith [hPn2])
    have hprod2 : (0:ℝ) ≤ β*Real.sqrt 5/4 * (((n:ℝ)-j)*((j:ℝ)+1)) := mul_nonneg hc hP0
    have hQc : ((n:ℝ)-2*j)*((n:ℝ)-2*j-1) ≤ (1 - β*Real.sqrt 5/4) * (((n:ℝ)-j)*((j:ℝ)+1)) := by
      nlinarith [hAdd, hprod1, hprod2]
    have heq2 : (b n (j+1):ℝ) * (((n:ℝ)-j)*((j:ℝ)+1)) = (b n j:ℝ) * (((n:ℝ)-2*j)*((n:ℝ)-2*j-1)) := by
      linear_combination heq
    exact ratio_le_helper (b n (j+1)) (b n j) (((n:ℝ)-j)*((j:ℝ)+1))
      (((n:ℝ)-2*j)*((n:ℝ)-2*j-1)) (1 - β*Real.sqrt 5/4) heq2 (P_pos n j h2j1) (by positivity) hQc
  · have : 2*j = n := by omega
    rw [b_succ_zero n j this]
    have : (0:ℝ) ≤ (1 - β*Real.sqrt 5/4) * (b n j : ℝ) := mul_nonneg hcpos (by positivity)
    rw [Nat.cast_zero]; linarith

theorem strong_inc_step (n j : ℕ) (hn2 : 2 ≤ n) (hjn : 2*j ≤ n) (hβ : 0 < β)
    (hnlarge : 8 ≤ β * Real.sqrt 5 * n)
    (hstr : 10 * j ≤ (5 - Real.sqrt 5) * n - 10*β*n) :
    (1 + β*Real.sqrt 5/4) * (b n j : ℝ) ≤ (b n (j+1) : ℝ) := by
  have hreal : (10*j : ℝ) ≤ 3*n := by
    have := sqrt5_gt2; nlinarith [Nat.cast_nonneg (α:=ℝ) n, mul_nonneg (mul_nonneg hβ.le sqrt5_pos.le) (Nat.cast_nonneg (α:=ℝ) n)]
  have hnat : 10*j ≤ 3*n := by exact_mod_cast hreal
  have h2j1 : 2*j+1 ≤ n := by omega
  have heq := b_ratio_k_real n j h2j1
  have hAdd : β*Real.sqrt 5/2 * (n:ℝ)^2 - 2*n ≤ ((n:ℝ)-2*j)*((n:ℝ)-2*j-1) - ((n:ℝ)-j)*((j:ℝ)+1) :=
    ineq_stronginc n j (Real.sqrt 5) β sqrt5_sq sqrt5_pos (by exact_mod_cast hn2)
      (by positivity) (by exact_mod_cast hjn) hβ (by exact_mod_cast hstr)
  have hPn2 := P_le_n2 n j h2j1
  have hnn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hc : (0:ℝ) ≤ β*Real.sqrt 5/4 := by positivity
  have hP0 : (0:ℝ) ≤ ((n:ℝ)-j)*((j:ℝ)+1) := (P_pos n j h2j1).le
  have hkey : 2*(n:ℝ) ≤ β*Real.sqrt 5/4 * (n:ℝ)^2 := by nlinarith [hnlarge, hnn]
  have hprod1 : (0:ℝ) ≤ β*Real.sqrt 5/4 * ((n:ℝ)^2 - ((n:ℝ)-j)*((j:ℝ)+1)) :=
    mul_nonneg hc (by linarith [hPn2])
  have hQc : (1 + β*Real.sqrt 5/4) * (((n:ℝ)-j)*((j:ℝ)+1)) ≤ ((n:ℝ)-2*j)*((n:ℝ)-2*j-1) := by
    nlinarith [hAdd, hprod1, hkey]
  have heq2 : (b n (j+1):ℝ) * (((n:ℝ)-j)*((j:ℝ)+1)) = (b n j:ℝ) * (((n:ℝ)-2*j)*((n:ℝ)-2*j-1)) := by
    linear_combination heq
  exact ratio_ge_helper (b n (j+1)) (b n j) (((n:ℝ)-j)*((j:ℝ)+1))
    (((n:ℝ)-2*j)*((n:ℝ)-2*j-1)) (1 + β*Real.sqrt 5/4) heq2 (P_pos n j h2j1) (by positivity) hQc

-- monotone decreasing for k ≥ m₀ (m₀ ≥ alpha* n)
theorem b_mono_from (n m₀ : ℕ) (hn2 : 2 ≤ n)
    (hm : (5 - Real.sqrt 5) * n ≤ 10 * m₀) :
    ∀ k, m₀ ≤ k → k ≤ n/2 → (b n k : ℝ) ≤ (b n m₀ : ℝ) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ k hmk ih =>
    intro hk2
    have hkn2 : k ≤ n/2 := by omega
    have hkstep : (5 - Real.sqrt 5) * n ≤ 10 * k := by
      have : (10:ℝ) * m₀ ≤ 10 * k := by
        have : (m₀:ℝ) ≤ k := by exact_mod_cast hmk
        linarith
      linarith [hm]
    have h2k : 2*k ≤ n := by omega
    have := mono_dec_step n k hn2 h2k hkstep
    exact le_trans this (ih hkn2)

-- monotone increasing for k ≤ m₀ (m₀ ≤ alpha* n region)
theorem b_mono_to (n m₀ : ℕ) (hn2 : 2 ≤ n)
    (hm : 10 * (m₀:ℝ) ≤ (5 - Real.sqrt 5) * n) :
    ∀ d, d ≤ m₀ → (b n (m₀ - d) : ℝ) ≤ (b n m₀ : ℝ) := by
  have hm0n : 2 * m₀ ≤ n := by
    have h3 : (10:ℝ)*m₀ ≤ 3*n := by have := sqrt5_gt2; nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    have : 10*m₀ ≤ 3*n := by exact_mod_cast h3
    omega
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have hdm : d ≤ m₀ := by omega
    have hstep : (b n (m₀-(d+1)) : ℝ) ≤ (b n (m₀-d) : ℝ) := by
      have hj : m₀-(d+1)+1 = m₀ - d := by omega
      have hineq : 10 * ((m₀-(d+1)):ℕ) ≤ (5 - Real.sqrt 5) * n - 10 := by
        have hle : (((m₀-(d+1)):ℕ):ℝ) ≤ (m₀:ℝ) - 1 := by
          have : ((m₀-(d+1):ℕ):ℝ) = (m₀:ℝ) - (d+1) := by
            rw [Nat.cast_sub (by omega)]; push_cast; ring
          rw [this]; have : (0:ℝ) ≤ (d:ℝ) := by positivity
          linarith
        nlinarith [hle, hm]
      have h2j : 2*(m₀-(d+1)) ≤ n := by omega
      have := mono_inc_step n (m₀-(d+1)) hn2 h2j hineq
      rwa [hj] at this
    exact le_trans hstep (ih hdm)

theorem geom_high (n a : ℕ) (hn2 : 2 ≤ n) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (ha : (5 - Real.sqrt 5) * n + 10*β*n ≤ 10 * a) :
    ∀ t, a + t ≤ n/2 → (b n (a+t) : ℝ) ≤ (1 - β*Real.sqrt 5/4)^t * (b n a : ℝ) := by
  have hcpos : (0:ℝ) ≤ 1 - β*Real.sqrt 5/4 := by have := sqrt5_lt3; nlinarith
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have ht' : a + t ≤ n/2 := by omega
    have hstep : (b n (a+t+1) : ℝ) ≤ (1 - β*Real.sqrt 5/4) * (b n (a+t) : ℝ) := by
      have h2j : 2*(a+t) ≤ n := by omega
      have hthr : (5 - Real.sqrt 5) * n + 10*β*n ≤ 10 * ((a+t:ℕ):ℝ) := by
        push_cast
        have htnn : (0:ℝ) ≤ (t:ℝ) := by positivity
        linarith [ha]
      exact strong_dec_step n (a+t) hn2 h2j hβ hβ1 hthr
    have hih := ih ht'
    calc (b n (a+(t+1)) : ℝ) = (b n (a+t+1):ℝ) := by ring_nf
      _ ≤ (1 - β*Real.sqrt 5/4) * (b n (a+t):ℝ) := hstep
      _ ≤ (1 - β*Real.sqrt 5/4) * ((1 - β*Real.sqrt 5/4)^t * (b n a:ℝ)) :=
          mul_le_mul_of_nonneg_left hih hcpos
      _ = (1 - β*Real.sqrt 5/4)^(t+1) * (b n a:ℝ) := by ring

theorem geom_low (n a : ℕ) (hn2 : 2 ≤ n) (hβ : 0 < β)
    (hnlarge : 8 ≤ β * Real.sqrt 5 * n)
    (ha : 10 * (a:ℝ) ≤ (5 - Real.sqrt 5) * n - 10*β*n) :
    ∀ t, t ≤ a → (1 + β*Real.sqrt 5/4)^t * (b n (a-t) : ℝ) ≤ (b n a : ℝ) := by
  have h2a : 2*a ≤ n := by
    have h3 : (10:ℝ)*a ≤ 3*n := by
      have := sqrt5_gt2
      nlinarith [Nat.cast_nonneg (α:=ℝ) n, mul_nonneg (mul_nonneg hβ.le sqrt5_pos.le) (Nat.cast_nonneg (α:=ℝ) n)]
    have : 10*a ≤ 3*n := by exact_mod_cast h3
    omega
  have hcpos : (0:ℝ) ≤ 1 + β*Real.sqrt 5/4 := by positivity
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have ht' : t ≤ a := by omega
    have hj : a - (t+1) + 1 = a - t := by omega
    have hstep : (1 + β*Real.sqrt 5/4) * (b n (a-(t+1)):ℝ) ≤ (b n (a-t):ℝ) := by
      have h2j : 2*(a-(t+1)) ≤ n := by omega
      have hthr : 10 * ((a-(t+1)):ℕ) ≤ (5 - Real.sqrt 5) * n - 10*β*n := by
        have hcast : (((a-(t+1)):ℕ):ℝ) = (a:ℝ) - (t+1) := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        have hle : (((a-(t+1)):ℕ):ℝ) ≤ (a:ℝ) - 1 := by
          rw [hcast]
          have htnn : (0:ℝ) ≤ (t:ℝ) := by positivity
          linarith
        nlinarith [hle, ha]
      have := strong_inc_step n (a-(t+1)) hn2 h2j hβ hnlarge hthr
      rwa [hj] at this
    have hih := ih ht'
    calc (1 + β*Real.sqrt 5/4)^(t+1) * (b n (a-(t+1)):ℝ)
        = (1 + β*Real.sqrt 5/4)^t * ((1 + β*Real.sqrt 5/4) * (b n (a-(t+1)):ℝ)) := by ring
      _ ≤ (1 + β*Real.sqrt 5/4)^t * (b n (a-t):ℝ) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ ≤ (b n a:ℝ) := hih

-- R_k - φ identity
theorem R_sub_phi (n k : ℕ) (hk2 : 2*k+1 ≤ n) :
    ((n:ℝ)+1-k)/((n:ℝ)+1-2*k) - goldenRatio
      = Real.sqrt 5 * ((k:ℝ) - ((n:ℝ)+1)*((5-Real.sqrt 5)/10)) / ((n:ℝ)+1-2*k) := by
  have hkn : (2*(k:ℝ)+1) ≤ n := by exact_mod_cast hk2
  have hden : (0:ℝ) < (n:ℝ)+1-2*k := by linarith
  have hgr : goldenRatio = (1+Real.sqrt 5)/2 := rfl
  have hid : ((n:ℝ)+1-k) - (1+Real.sqrt 5)/2*((n:ℝ)+1-2*k)
      = Real.sqrt 5*((k:ℝ)-((n:ℝ)+1)*((5-Real.sqrt 5)/10)) := by
    linear_combination (-((n:ℝ)+1)/10) * sqrt5_sq
  rw [hgr, div_sub' (ne_of_gt hden)]
  congr 1
  linear_combination (-((n:ℝ)+1)/10) * sqrt5_sq

theorem R_close (n k : ℕ) (hk2 : 2*k+1 ≤ n) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : |(k:ℝ) - ((n:ℝ)+1)*((5-Real.sqrt 5)/10)| ≤ ρ)
    (D : ℝ) (hD0 : 0 < D) (hD : D ≤ (n:ℝ)+1-2*k) :
    |((n:ℝ)+1-k)/((n:ℝ)+1-2*k) - goldenRatio| ≤ Real.sqrt 5 * ρ / D := by
  rw [R_sub_phi n k hk2]
  have hden : (0:ℝ) < (n:ℝ)+1-2*k := by linarith
  rw [abs_div, abs_of_pos hden, abs_mul, abs_of_pos sqrt5_pos]
  have hnum : Real.sqrt 5 * |(k:ℝ) - ((n:ℝ)+1)*((5-Real.sqrt 5)/10)| ≤ Real.sqrt 5 * ρ :=
    mul_le_mul_of_nonneg_left hρ sqrt5_pos.le
  gcongr

theorem poly_geom (c : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun m : ℕ => ((m:ℝ)+1)^c * r^m) atTop (𝓝 0) := by
  have habs : |r| < 1 := by rw [abs_of_nonneg hr0]; exact hr1
  have hbase := tendsto_pow_const_mul_const_pow_of_abs_lt_one c habs
  -- 2^c * (m^c r^m) → 0
  have hbase2 : Tendsto (fun m : ℕ => (2:ℝ)^c * ((m:ℝ)^c * r^m)) atTop (𝓝 0) := by
    simpa using hbase.const_mul ((2:ℝ)^c)
  apply squeeze_zero' (f := fun m : ℕ => ((m:ℝ)+1)^c * r^m)
    (g := fun m : ℕ => (2:ℝ)^c * ((m:ℝ)^c * r^m))
  · filter_upwards with m
    positivity
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
    have h1 : ((m:ℝ)+1)^c ≤ (2*m)^c := by
      apply pow_le_pow_left₀ (by positivity); linarith
    have h2 : (2*(m:ℝ))^c = (2:ℝ)^c * (m:ℝ)^c := by rw [mul_pow]
    calc ((m:ℝ)+1)^c * r^m ≤ (2*(m:ℝ))^c * r^m := by
            apply mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (2:ℝ)^c * ((m:ℝ)^c * r^m) := by rw [h2]; ring
  · exact hbase2

theorem tendsto_div_const (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℕ => n / d) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨d*b, fun n hn => ?_⟩
  rw [Nat.le_div_iff_mul_le hd]
  calc b * d = d * b := by ring
    _ ≤ n := hn

theorem key_tendsto (c d : ℕ) (hd : 0 < d) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^c * r^(n/d)) atTop (𝓝 0) := by
  have hg := poly_geom c r hr0 hr1
  have hcomp : Tendsto (fun n : ℕ => ((d:ℝ)^c) * (((n/d : ℕ):ℝ)+1)^c * r^(n/d)) atTop (𝓝 0) := by
    have := (hg.comp (tendsto_div_const d hd)).const_mul ((d:ℝ)^c)
    simpa [Function.comp, mul_assoc] using this
  apply squeeze_zero' (f := fun n : ℕ => ((n:ℝ)+1)^c * r^(n/d))
    (g := fun n : ℕ => ((d:ℝ)^c) * (((n/d : ℕ):ℝ)+1)^c * r^(n/d))
  · filter_upwards with n; positivity
  · filter_upwards with n
    have hn1 : (n:ℝ)+1 ≤ (d:ℝ)*(((n/d:ℕ):ℝ)+1) := by
      have hdm := Nat.div_add_mod n d
      have hmod := Nat.mod_lt n hd
      have : n+1 ≤ d*(n/d) + d := by omega
      have hcast : ((d*(n/d)+d : ℕ):ℝ) = (d:ℝ)*((n/d:ℕ):ℝ)+d := by push_cast; ring
      have : ((n:ℝ)+1) ≤ ((d*(n/d)+d:ℕ):ℝ) := by exact_mod_cast this
      rw [hcast] at this; linarith
    have h1 : ((n:ℝ)+1)^c ≤ ((d:ℝ)*(((n/d:ℕ):ℝ)+1))^c := by
      apply pow_le_pow_left₀ (by positivity) hn1
    have h2 : ((d:ℝ)*(((n/d:ℕ):ℝ)+1))^c = (d:ℝ)^c * (((n/d:ℕ):ℝ)+1)^c := by rw [mul_pow]
    calc ((n:ℝ)+1)^c * r^(n/d) ≤ ((d:ℝ)*(((n/d:ℕ):ℝ)+1))^c * r^(n/d) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (d:ℝ)^c * (((n/d:ℕ):ℝ)+1)^c * r^(n/d) := by rw [h2]
  · exact hcomp

theorem tail_high_bound (n m P : ℕ) (hn2 : 2 ≤ n) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hm : (5 - Real.sqrt 5) * n ≤ 10 * m)
    (hmP : (5 - Real.sqrt 5) * n + 10*β*n ≤ 10 * (m+P))
    (k : ℕ) (hk1 : m+2*P ≤ k) (hk2 : k ≤ n/2) :
    (b n k : ℝ) ≤ (1 - β*Real.sqrt 5/4)^P * (b n m : ℝ) := by
  have hc0 : (0:ℝ) ≤ 1 - β*Real.sqrt 5/4 := by have := sqrt5_lt3; nlinarith
  have hc1 : (1 - β*Real.sqrt 5/4) ≤ 1 := by nlinarith [mul_nonneg hβ.le sqrt5_pos.le]
  have hmPn : m+P ≤ n/2 := by omega
  have hmono : (b n (m+P) : ℝ) ≤ (b n m : ℝ) :=
    b_mono_from n m hn2 hm (m+P) (by omega) hmPn
  have hmP' : (5 - Real.sqrt 5) * n + 10*β*n ≤ 10 * ((m+P:ℕ):ℝ) := by push_cast; linarith [hmP]
  have hgeom := geom_high n (m+P) hn2 hβ hβ1 hmP' (k - (m+P))
  have hke : (m+P) + (k - (m+P)) = k := by omega
  rw [hke] at hgeom
  have hgeom2 := hgeom hk2
  have hpow : (1 - β*Real.sqrt 5/4)^(k-(m+P)) ≤ (1 - β*Real.sqrt 5/4)^P :=
    pow_le_pow_of_le_one hc0 hc1 (by omega)
  calc (b n k : ℝ) ≤ (1 - β*Real.sqrt 5/4)^(k-(m+P)) * (b n (m+P) : ℝ) := hgeom2
    _ ≤ (1 - β*Real.sqrt 5/4)^P * (b n (m+P) : ℝ) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
    _ ≤ (1 - β*Real.sqrt 5/4)^P * (b n m : ℝ) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)

theorem tail_low_bound (n m₀ P : ℕ) (hn2 : 2 ≤ n) (hβ : 0 < β)
    (hnlarge : 8 ≤ β * Real.sqrt 5 * n)
    (hm0 : 10 * (m₀:ℝ) ≤ (5 - Real.sqrt 5) * n)
    (hm0P : 10 * ((m₀-P:ℕ):ℝ) ≤ (5 - Real.sqrt 5) * n - 10*β*n)
    (hPm0 : P ≤ m₀)
    (k : ℕ) (hk1 : k + 2*P ≤ m₀) :
    (1 + β*Real.sqrt 5/4)^P * (b n k : ℝ) ≤ (b n m₀ : ℝ) := by
  have hc1 : (1:ℝ) ≤ 1 + β*Real.sqrt 5/4 := by nlinarith [mul_nonneg hβ.le sqrt5_pos.le]
  have hmono : (b n (m₀-P) : ℝ) ≤ (b n m₀ : ℝ) :=
    b_mono_to n m₀ hn2 hm0 P hPm0
  have hgeom := geom_low n (m₀-P) hn2 hβ hnlarge hm0P (m₀-P-k)
  have hke : (m₀-P) - (m₀-P-k) = k := by omega
  rw [hke] at hgeom
  have hgeom2 := hgeom (by omega)
  have hpow : (1 + β*Real.sqrt 5/4)^P ≤ (1 + β*Real.sqrt 5/4)^(m₀-P-k) :=
    pow_le_pow_right₀ hc1 (by omega)
  calc (1 + β*Real.sqrt 5/4)^P * (b n k : ℝ)
      ≤ (1 + β*Real.sqrt 5/4)^(m₀-P-k) * (b n k : ℝ) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
    _ ≤ (b n (m₀-P) : ℝ) := hgeom2
    _ ≤ (b n m₀ : ℝ) := hmono

theorem b_ratio_n (n k : ℕ) (h : 2*k ≤ n) :
    b (n+1) k * (n+1-2*k) = (n+1-k) * b n k := by
  have key := succ_choose_mul (n-k) k
  have c1 : (n-k)+1 = n+1-k := by omega
  rw [c1] at key
  have c2 : (n+1-k)-k = n+1-2*k := by omega
  rw [c2] at key
  unfold b
  have e1 : (n+1) - k = n+1-k := by omega
  rw [e1]
  linarith [key]

theorem b_ratio_n_real (n k : ℕ) (h : 2*k ≤ n) :
    (b (n+1) k : ℝ) = ((n:ℝ)+1-k)/((n:ℝ)+1-2*k) * (b n k : ℝ) := by
  have key := b_ratio_n n k h
  have hden : (0:ℝ) < (n:ℝ)+1-2*k := by
    have : (2*(k:ℝ)) ≤ n := by exact_mod_cast h
    linarith
  have hcast : (b (n+1) k : ℝ) * ((n:ℝ)+1-2*k) = ((n:ℝ)+1-k) * (b n k : ℝ) := by
    have h1 : ((b (n+1) k * (n+1-2*k) : ℕ) : ℝ) = (((n+1-k) * b n k : ℕ)) := by exact_mod_cast key
    have hc1 : ((n+1-2*k : ℕ):ℝ) = (n:ℝ)+1-2*k := by
      rw [Nat.cast_sub (by omega : 2*k ≤ n+1)]; push_cast; ring
    have hc2 : ((n+1-k : ℕ):ℝ) = (n:ℝ)+1-k := by
      rw [Nat.cast_sub (by omega : k ≤ n+1)]; push_cast; ring
    push_cast at h1
    rw [hc1, hc2] at h1
    linarith [h1]
  rw [eq_comm, div_mul_eq_mul_div, div_eq_iff (ne_of_gt hden)]
  linarith [hcast]

theorem b_pos (n k : ℕ) (h : 2*k ≤ n) : 1 ≤ b n k := by
  unfold b
  exact Nat.choose_pos (by omega)

theorem b_boundary (n : ℕ) : b (n+1) (n/2+1) ≤ 1 := by
  unfold b
  rcases Nat.lt_or_ge ((n+1)-(n/2+1)) (n/2+1) with hlt | hge
  · rw [Nat.choose_eq_zero_of_lt hlt]; omega
  · have heq : (n+1)-(n/2+1) = n/2+1 := by omega
    rw [heq, Nat.choose_self]

theorem term_eq (n k L : ℕ) (h : 2*k ≤ n) :
    (b (n+1) k : ℝ)^L = (((n:ℝ)+1-k)/((n:ℝ)+1-2*k))^L * (b n k : ℝ)^L := by
  rw [b_ratio_n_real n k h, mul_pow]

theorem central_R (n k d P : ℕ) (hd : 40 ≤ d) (hn : 80 ≤ n)
    (hk2 : 2*k+1 ≤ n)
    (hPub : (P:ℝ) ≤ (n:ℝ)/d + 1)
    (hku : (k:ℝ) < (5-Real.sqrt 5)/10*n + 1 + 2*P)
    (hkl : (5-Real.sqrt 5)/10*n - 1 - 2*P < (k:ℝ)) :
    |((n:ℝ)+1-k)/((n:ℝ)+1-2*k) - goldenRatio| ≤ 40/n + 20/d := by
  have hs := sqrt5_sq
  have hs0 := sqrt5_pos
  have hs3 := sqrt5_lt3
  have hs2 := sqrt5_gt2
  have hnR : (80:ℝ) ≤ n := by exact_mod_cast hn
  have hdR : (40:ℝ) ≤ d := by exact_mod_cast hd
  have hn0 : (0:ℝ) < n := by linarith
  have hd0 : (0:ℝ) < d := by linarith
  -- ρ bound
  have hρ : |(k:ℝ) - ((n:ℝ)+1)*((5-Real.sqrt 5)/10)| ≤ 2 + 2*P := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have : ((n:ℝ)+1)*((5-Real.sqrt 5)/10) ≤ (5-Real.sqrt 5)/10*n + 1 := by nlinarith [hs0, hs3]
      linarith [hkl, this]
    · have : (5-Real.sqrt 5)/10*n ≤ ((n:ℝ)+1)*((5-Real.sqrt 5)/10) := by nlinarith [hs0, hs3, hnR]
      linarith [hku, this]
  have hD0 : (0:ℝ) < (n:ℝ)/(2*Real.sqrt 5) := by positivity
  have hD : (n:ℝ)/(2*Real.sqrt 5) ≤ (n:ℝ)+1-2*k := by
    have h2A : 2*((5-Real.sqrt 5)/10*n) = (n:ℝ) - n/Real.sqrt 5 := by
      rw [eq_sub_iff_add_eq]; field_simp; nlinarith [hs, hs0]
    have hub : 2*(k:ℝ) < (n:ℝ) - n/Real.sqrt 5 + 2 + 4*P := by rw [← h2A]; linarith [hku]
    have e1 : (n:ℝ)/Real.sqrt 5 - 1 - 4*P ≤ ((n:ℝ)+1-2*k) := by linarith
    have hnd : (n:ℝ)/d ≤ n/40 := div_le_div_of_nonneg_left (by positivity) (by positivity) hdR
    have hroot : (n:ℝ)/Real.sqrt 5 - n/(2*Real.sqrt 5) = n/(2*Real.sqrt 5) := by
      field_simp; ring
    have hbound : (n:ℝ)/(2*Real.sqrt 5) ≤ (n:ℝ)/Real.sqrt 5 - 1 - 4*P := by
      nlinarith [hroot, hPub, hnd, hnR, hs0, hs2, hs3]
    linarith [e1, hbound]
  have hmain := R_close n k hk2 (2+2*P) (by positivity) hρ ((n:ℝ)/(2*Real.sqrt 5)) hD0 hD
  have hval : Real.sqrt 5 * (2+2*P) / ((n:ℝ)/(2*Real.sqrt 5)) = (20+20*P)/n := by
    rw [div_div_eq_mul_div]
    field_simp
    nlinarith [hs, hs0]
  rw [hval] at hmain
  have hfin : (20+20*(P:ℝ))/n ≤ 40/n + 20/d := by
    have hPd : (P:ℝ)*d ≤ n + d := by
      have h := mul_le_mul_of_nonneg_right hPub hd0.le
      rwa [add_mul, div_mul_cancel₀ _ (ne_of_gt hd0), one_mul] at h
    have key : (20+20*(P:ℝ)) * d ≤ 40*d+20*n := by nlinarith [hPd]
    calc (20+20*(P:ℝ))/n = (20+20*(P:ℝ))*d/(n*d) := by field_simp
      _ ≤ (40*d+20*n)/(n*d) := (div_le_div_iff_of_pos_right (by positivity)).mpr key
      _ = 40/n+20/d := by field_simp
  linarith [hmain, hfin]

theorem central_pow (n k d P L : ℕ) (hd : 40 ≤ d) (hn : 80 ≤ n)
    (hk2 : 2*k+1 ≤ n)
    (hPub : (P:ℝ) ≤ (n:ℝ)/d + 1)
    (hku : (k:ℝ) < (5-Real.sqrt 5)/10*n + 1 + 2*P)
    (hkl : (5-Real.sqrt 5)/10*n - 1 - 2*P < (k:ℝ)) :
    |(((n:ℝ)+1-k)/((n:ℝ)+1-2*k))^L - goldenRatio^L| ≤ (40/n + 20/d) * ((L:ℝ) * 3^(L-1)) := by
  set R := ((n:ℝ)+1-k)/((n:ℝ)+1-2*k) with hR
  have hcl := central_R n k d P hd hn hk2 hPub hku hkl
  have hnR : (80:ℝ) ≤ n := by exact_mod_cast hn
  have hdR : (40:ℝ) ≤ d := by exact_mod_cast hd
  have hkn : (2*(k:ℝ)+1) ≤ n := by exact_mod_cast hk2
  have hden : (0:ℝ) < (n:ℝ)+1-2*k := by linarith
  have hnum : (0:ℝ) ≤ (n:ℝ)+1-k := by linarith
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hphi0 : (0:ℝ) ≤ goldenRatio := goldenRatio_pos.le
  have hgr : goldenRatio = (1+Real.sqrt 5)/2 := rfl
  have hphilt : goldenRatio < 2 := by rw [hgr]; have := sqrt5_lt3; linarith
  have hbnd : (40:ℝ)/n + 20/d ≤ 1 := by
    have h1 : (40:ℝ)/n ≤ 1/2 := by rw [div_le_iff₀ (by linarith)]; linarith
    have h2 : (20:ℝ)/d ≤ 1/2 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  have hR3 : R ≤ 3 := by
    have habs := abs_le.mp hcl
    linarith [habs.2, hbnd]
  have hmax : max |R| |goldenRatio| ≤ 3 := by
    rw [abs_of_nonneg hR0, abs_of_nonneg hphi0]
    exact max_le hR3 (by linarith [hphilt])
  have hmax0 : (0:ℝ) ≤ max |R| |goldenRatio| := le_trans (abs_nonneg R) (le_max_left _ _)
  have h1 : (max |R| |goldenRatio|) ^ (L-1) ≤ 3^(L-1) := pow_le_pow_left₀ hmax0 hmax (L-1)
  calc |R^L - goldenRatio^L| ≤ |R - goldenRatio| * L * (max |R| |goldenRatio|)^(L-1) :=
        abs_pow_sub_pow_le R goldenRatio L
    _ ≤ (40/n+20/d) * L * 3^(L-1) := by
        apply mul_le_mul _ h1 (by positivity) (by positivity)
        apply mul_le_mul hcl le_rfl (by positivity) (by positivity)
    _ = (40/n+20/d) * ((L:ℝ) * 3^(L-1)) := by ring

def FW (n L : ℕ) : ℕ := Finset.sum (Finset.range (n / 2 + 1)) fun k => (b n k) ^ L

theorem F_cast (n L : ℕ) : (FW n L : ℝ) = ∑ k ∈ Finset.range (n/2+1), (b n k : ℝ)^L := by
  unfold FW; push_cast; rfl

-- lower bound FW n L ≥ n  (for L ≥ 1, n ≥ 2)
theorem F_lower (n L : ℕ) (hL : 1 ≤ L) (hn : 2 ≤ n) : n ≤ FW n L := by
  unfold FW
  have h0m : (0:ℕ) ∈ Finset.range (n/2+1) := Finset.mem_range.mpr (by omega)
  have h1m : (1:ℕ) ∈ Finset.range (n/2+1) := Finset.mem_range.mpr (by omega)
  have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (n/2+1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h0m
    · exact h1m
  have hle : (∑ k ∈ ({0,1}:Finset ℕ), (b n k)^L) ≤ ∑ k ∈ Finset.range (n/2+1), (b n k)^L :=
    Finset.sum_le_sum_of_subset hsub
  have hsum2 : (∑ k ∈ ({0,1}:Finset ℕ), (b n k)^L) = (b n 0)^L + (b n 1)^L := by
    rw [Finset.sum_insert (by simp), Finset.sum_singleton]
  have hb0 : b n 0 = 1 := by unfold b; simp
  have hb1 : b n 1 = n - 1 := by unfold b; simp [Nat.choose_one_right]
  have hpow1 : n - 1 ≤ (b n 1)^L := by
    rw [hb1]; exact Nat.le_self_pow (by omega) _
  rw [hsum2, hb0] at hle
  have : 1^L = 1 := one_pow L
  omega

theorem b_boundary_pow (n L : ℕ) : (b (n+1) (n/2+1) : ℝ)^L ≤ 1 := by
  have h := b_boundary n
  have : (b (n+1) (n/2+1) : ℝ) ≤ 1 := by exact_mod_cast h
  exact pow_le_one₀ (by positivity) this

theorem T_le_F (n L : ℕ) :
    (∑ k ∈ Finset.range (n/2+1), (b (n+1) k : ℝ)^L) ≤ (FW (n+1) L : ℝ) := by
  rw [F_cast]
  have hsub : Finset.range (n/2+1) ⊆ Finset.range ((n+1)/2+1) :=
    Finset.range_mono (by omega)
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)

theorem F_le_T (n L : ℕ) :
    (FW (n+1) L : ℝ) ≤ (∑ k ∈ Finset.range (n/2+1), (b (n+1) k : ℝ)^L) + 1 := by
  rw [F_cast]
  have hsub : (Finset.range ((n+1)/2+1)) ⊆ Finset.range (n/2+2) :=
    Finset.range_mono (by omega)
  calc ∑ k ∈ Finset.range ((n+1)/2+1), (b (n+1) k : ℝ)^L
      ≤ ∑ k ∈ Finset.range (n/2+2), (b (n+1) k : ℝ)^L := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro k _ _; positivity
    _ = (∑ k ∈ Finset.range (n/2+1), (b (n+1) k : ℝ)^L) + (b (n+1) (n/2+1) : ℝ)^L := by
        rw [show n/2+2 = (n/2+1)+1 from rfl, Finset.sum_range_succ]
    _ ≤ (∑ k ∈ Finset.range (n/2+1), (b (n+1) k : ℝ)^L) + 1 := by
        have := b_boundary_pow n L; linarith

theorem sum_filter_high (n m P L : ℕ) (hn2 : 2 ≤ n) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hm : (5 - Real.sqrt 5) * n ≤ 10 * m)
    (hmP : (5 - Real.sqrt 5) * n + 10*β*n ≤ 10 * (m+P)) :
    (∑ k ∈ (Finset.range (n/2+1)).filter (fun k => m+2*P ≤ k), (b n k : ℝ)^L)
      ≤ ((n:ℝ)+1) * (((1-β*Real.sqrt 5/4)^P)^L * (b n m : ℝ)^L) := by
  set C : ℝ := ((1-β*Real.sqrt 5/4)^P)^L * (b n m : ℝ)^L with hC
  have hC0 : 0 ≤ C := by
    have hc0 : (0:ℝ) ≤ 1 - β*Real.sqrt 5/4 := by have := sqrt5_lt3; nlinarith
    rw [hC]; positivity
  have hterm : ∀ k ∈ (Finset.range (n/2+1)).filter (fun k => m+2*P ≤ k), (b n k : ℝ)^L ≤ C := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    have hk2 : k ≤ n/2 := by omega
    have hb := tail_high_bound n m P hn2 hβ hβ1 hm hmP k hk.2 hk2
    have hc0 : (0:ℝ) ≤ 1 - β*Real.sqrt 5/4 := by have := sqrt5_lt3; nlinarith
    calc (b n k : ℝ)^L ≤ ((1-β*Real.sqrt 5/4)^P * (b n m : ℝ))^L :=
          pow_le_pow_left₀ (by positivity) hb L
      _ = C := by rw [hC, mul_pow]
  calc (∑ k ∈ (Finset.range (n/2+1)).filter (fun k => m+2*P ≤ k), (b n k : ℝ)^L)
      ≤ ∑ _k ∈ (Finset.range (n/2+1)).filter (fun k => m+2*P ≤ k), C :=
        Finset.sum_le_sum hterm
    _ = (((Finset.range (n/2+1)).filter (fun k => m+2*P ≤ k)).card : ℝ) * C := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((n:ℝ)+1) * C := by
        apply mul_le_mul_of_nonneg_right _ hC0
        have : ((Finset.range (n/2+1)).filter (fun k => m+2*P ≤ k)).card ≤ n/2+1 := by
          calc _ ≤ (Finset.range (n/2+1)).card := Finset.card_filter_le _ _
            _ = n/2+1 := Finset.card_range _
        have hcard2 : (((Finset.range (n/2+1)).filter (fun k => m+2*P ≤ k)).card : ℝ) ≤ ((n/2+1:ℕ):ℝ) := by
          exact_mod_cast this
        have hn21 : ((n/2+1 : ℕ):ℝ) ≤ (n:ℝ)+1 := by
          have h : n/2+1 ≤ n+1 := by omega
          exact_mod_cast h
        linarith

theorem sum_filter_low (n m₀ P L : ℕ) (hn2 : 2 ≤ n) (hβ : 0 < β)
    (hnlarge : 8 ≤ β * Real.sqrt 5 * n)
    (hm0 : 10 * (m₀:ℝ) ≤ (5 - Real.sqrt 5) * n)
    (hm0P : 10 * ((m₀-P:ℕ):ℝ) ≤ (5 - Real.sqrt 5) * n - 10*β*n)
    (hPm0 : P ≤ m₀) :
    (∑ k ∈ (Finset.range (n/2+1)).filter (fun k => k+2*P ≤ m₀), (b n k : ℝ)^L)
      ≤ ((n:ℝ)+1) * ((b n m₀ : ℝ)^L / ((1+β*Real.sqrt 5/4)^P)^L) := by
  have hg0 : (0:ℝ) < (1+β*Real.sqrt 5/4)^P := by positivity
  set C : ℝ := (b n m₀ : ℝ)^L / ((1+β*Real.sqrt 5/4)^P)^L with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hterm : ∀ k ∈ (Finset.range (n/2+1)).filter (fun k => k+2*P ≤ m₀), (b n k : ℝ)^L ≤ C := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    have hb := tail_low_bound n m₀ P hn2 hβ hnlarge hm0 hm0P hPm0 k hk.2
    have hbk : (b n k : ℝ) ≤ (b n m₀ : ℝ) / (1+β*Real.sqrt 5/4)^P := by
      rw [le_div_iff₀ hg0]; linarith [hb]
    calc (b n k : ℝ)^L ≤ ((b n m₀ : ℝ) / (1+β*Real.sqrt 5/4)^P)^L :=
          pow_le_pow_left₀ (by positivity) hbk L
      _ = C := by rw [hC, div_pow]
  calc (∑ k ∈ (Finset.range (n/2+1)).filter (fun k => k+2*P ≤ m₀), (b n k : ℝ)^L)
      ≤ ∑ _k ∈ (Finset.range (n/2+1)).filter (fun k => k+2*P ≤ m₀), C :=
        Finset.sum_le_sum hterm
    _ = (((Finset.range (n/2+1)).filter (fun k => k+2*P ≤ m₀)).card : ℝ) * C := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((n:ℝ)+1) * C := by
        apply mul_le_mul_of_nonneg_right _ hC0
        have hcard : ((Finset.range (n/2+1)).filter (fun k => k+2*P ≤ m₀)).card ≤ n/2+1 := by
          calc _ ≤ (Finset.range (n/2+1)).card := Finset.card_filter_le _ _
            _ = n/2+1 := Finset.card_range _
        have hcard2 : (((Finset.range (n/2+1)).filter (fun k => k+2*P ≤ m₀)).card : ℝ) ≤ ((n/2+1:ℕ):ℝ) := by
          exact_mod_cast hcard
        have hn21 : ((n/2+1 : ℕ):ℝ) ≤ (n:ℝ)+1 := by
          have h : n/2+1 ≤ n+1 := by omega
          exact_mod_cast h
        linarith

set_option maxHeartbeats 2000000 in
theorem per_n_bound (d L : ℕ) (hd : 40 ≤ d) (hL : 1 ≤ L) (n : ℕ) (hn4 : 4*d ≤ n) :
    |(FW (n+1) L : ℝ)/(FW n L : ℝ) - goldenRatio^L|
      ≤ (40/(n:ℝ) + 20/(d:ℝ)) * ((L:ℝ) * 3^(L-1))
        + 2*((n:ℝ)+1)^(L+1) * ((1 - (1/(d:ℝ))*Real.sqrt 5/4)^L)^(n/d+1)
        + 2*((n:ℝ)+1)^(L+1) * (((1 + (1/(d:ℝ))*Real.sqrt 5/4)^L)⁻¹)^(n/d+1)
        + 1/(FW n L : ℝ) := by
  -- numeric facts
  have hd0 : (0:ℝ) < d := by
    have hdpos : (0:ℕ) < d := by omega
    exact_mod_cast hdpos
  have hdR : (40:ℝ) ≤ d := by exact_mod_cast hd
  have hn160 : 160 ≤ n := by omega
  have hnR : (160:ℝ) ≤ n := by exact_mod_cast hn160
  have hn80 : 80 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hnpos : (0:ℝ) < n := by linarith
  have hs2 := sqrt5_gt2
  have hs3 := sqrt5_lt3
  have hs0 := sqrt5_pos
  have hssq := sqrt5_sq
  set β : ℝ := 1/(d:ℝ) with hβdef
  have hβ0 : 0 < β := by rw [hβdef]; positivity
  have hβ1 : β ≤ 1 := by rw [hβdef, div_le_one hd0]; linarith
  set P : ℕ := n/d + 1 with hPdef
  set S : ℝ := (FW n L : ℝ) with hSdef
  have hS_eq : S = ∑ k ∈ Finset.range (n/2+1), (b n k : ℝ)^L := by rw [hSdef]; exact F_cast n L
  have hFlow : (n:ℝ) ≤ S := by rw [hSdef]; exact_mod_cast F_lower n L hL hn2
  have hSpos : 0 < S := by linarith
  -- α facts
  have hαpos : (0:ℝ) < (5 - Real.sqrt 5)/10 := by linarith
  have hα0 : 0 ≤ (5 - Real.sqrt 5)/10 * (n:ℝ) := by positivity
  set m : ℕ := ⌈(5 - Real.sqrt 5)/10 * (n:ℝ)⌉₊ with hmdef
  set m₀ : ℕ := ⌊(5 - Real.sqrt 5)/10 * (n:ℝ)⌋₊ with hm0def
  have hmU : (m:ℝ) < (5 - Real.sqrt 5)/10 * n + 1 := by rw [hmdef]; exact Nat.ceil_lt_add_one hα0
  have hmL : (5 - Real.sqrt 5)/10 * n ≤ (m:ℝ) := by rw [hmdef]; exact Nat.le_ceil _
  have hm0U : (m₀:ℝ) ≤ (5 - Real.sqrt 5)/10 * n := by rw [hm0def]; exact Nat.floor_le hα0
  have hm0L : (5 - Real.sqrt 5)/10 * n - 1 < (m₀:ℝ) := by
    rw [hm0def]; have := Nat.lt_floor_add_one ((5 - Real.sqrt 5)/10 * (n:ℝ)); linarith
  -- P facts
  have hPub : (P:ℝ) ≤ (n:ℝ)/d + 1 := by
    rw [hPdef]; push_cast
    have : ((n/d : ℕ):ℝ) ≤ (n:ℝ)/d := Nat.cast_div_le
    linarith
  have hPlbnat : (n:ℝ)/d ≤ (P:ℝ) := by
    rw [hPdef]; push_cast
    have h1 : n < (n/d+1)*d := by
      have hexp : (n/d+1)*d = d*(n/d)+d := by ring
      have hdm := Nat.div_add_mod n d
      have hmod := Nat.mod_lt n (show 0<d by omega)
      linarith [hexp, hdm, hmod]
    rw [div_le_iff₀ hd0]
    have hcast : (n:ℝ) ≤ (((n/d+1)*d : ℕ):ℝ) := by exact_mod_cast (le_of_lt h1)
    calc (n:ℝ) ≤ (((n/d+1)*d:ℕ):ℝ) := hcast
      _ = (((n/d:ℕ):ℝ)+1)*d := by push_cast; ring
  have hnd : (n:ℝ)/d ≤ n/40 := div_le_div_of_nonneg_left (by positivity) (by positivity) hdR
  have hPub40 : (P:ℝ) ≤ (n:ℝ)/40 + 1 := by linarith [hPub, hnd]
  have hbetaPlb : 10*β*(n:ℝ) ≤ 10*(P:ℝ) := by
    rw [hβdef]
    have : (n:ℝ)/d ≤ P := hPlbnat
    have h10 : 10*(1/(d:ℝ))*n = 10*((n:ℝ)/d) := by field_simp
    rw [h10]; linarith
  -- m ≤ n/2
  have h2m : 2*(m:ℝ) < n := by
    have hsn : 2*(n:ℝ) < Real.sqrt 5 * n := by
      have := mul_lt_mul_of_pos_right hs2 hnpos; linarith
    nlinarith [hmU, hsn, hnR]
  have hmle : m ≤ n/2 := by
    have h2mn : 2*m < n := by exact_mod_cast (by exact_mod_cast h2m : (2*m:ℝ) < (n:ℝ))
    omega
  have hm0le : m₀ ≤ n/2 := le_trans (Nat.floor_le_ceil _) hmle
  -- P ≤ m₀
  have hPm0R : (P:ℝ) ≤ (m₀:ℝ) := by
    have hsn : 2*(n:ℝ) < Real.sqrt 5 * n := by
      have := mul_lt_mul_of_pos_right hs2 hnpos; linarith
    nlinarith [hPub40, hm0L, hsn, hnR]
  have hPm0 : P ≤ m₀ := by exact_mod_cast hPm0R
  -- conditions for tail bounds
  have hm_cond : (5 - Real.sqrt 5) * n ≤ 10 * (m:ℝ) := by linarith [hmL]
  have hmP_cond : (5 - Real.sqrt 5) * n + 10*β*n ≤ 10 * ((m:ℝ) + (P:ℝ)) := by
    linarith [hm_cond, hbetaPlb]
  have hm0_cond : 10 * (m₀:ℝ) ≤ (5 - Real.sqrt 5) * n := by linarith [hm0U]
  have hnlarge : 8 ≤ β * Real.sqrt 5 * n := by
    rw [hβdef]
    have hge4 : (4:ℝ) ≤ (n:ℝ)/d := by
      rw [le_div_iff₀ hd0]
      have h4d : (4*d:ℝ) ≤ n := by exact_mod_cast hn4
      linarith
    have heq : 1/(d:ℝ)*Real.sqrt 5*n = Real.sqrt 5 * ((n:ℝ)/d) := by field_simp
    rw [heq]; nlinarith [hge4, hs2]
  have hm0P_cond : 10 * ((m₀-P:ℕ):ℝ) ≤ (5 - Real.sqrt 5) * n - 10*β*n := by
    rw [Nat.cast_sub hPm0]
    linarith [hm0_cond, hbetaPlb]
  -- small bounds on the decay base
  have hβ40 : β ≤ 1/40 := by
    rw [hβdef]; exact one_div_le_one_div_of_le (by norm_num) hdR
  have hbprod : β*Real.sqrt 5 ≤ (1/40)*3 := mul_le_mul hβ40 hs3.le hs0.le (by norm_num)
  have h1mc : 0 ≤ 1 - β*Real.sqrt 5/4 := by nlinarith [hbprod]
  have hβsq_nn : 0 ≤ β*Real.sqrt 5/4 := by positivity
  -- TT and error bounds
  set TT : ℝ := ∑ k ∈ Finset.range (n/2+1), (b (n+1) k : ℝ)^L with hTTdef
  have hTT_lo : TT ≤ (FW (n+1) L : ℝ) := T_le_F n L
  have hTT_hi : (FW (n+1) L : ℝ) ≤ TT + 1 := F_le_T n L
  have hTT_eq : TT = ∑ k ∈ Finset.range (n/2+1),
      (((n:ℝ)+1-k)/((n:ℝ)+1-2*k))^L * (b n k : ℝ)^L := by
    rw [hTTdef]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    exact term_eq n k L (by omega)
  have hTTphi : TT - goldenRatio^L * S
      = ∑ k ∈ Finset.range (n/2+1),
          ((((n:ℝ)+1-k)/((n:ℝ)+1-2*k))^L - goldenRatio^L)*(b n k:ℝ)^L := by
    rw [hTT_eq, hS_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  have habsTT : |TT - goldenRatio^L*S|
      ≤ ∑ k ∈ Finset.range (n/2+1),
          |(((n:ℝ)+1-k)/((n:ℝ)+1-2*k))^L - goldenRatio^L| * (b n k:ℝ)^L := by
    rw [hTTphi]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro k _
    exact le_of_eq (by rw [abs_mul, abs_of_nonneg (show (0:ℝ)≤(b n k:ℝ)^L by positivity)])
  -- index helpers for central region
  have hk2n : ∀ k:ℕ, k < m+2*P → 2*k+1 ≤ n := by
    intro k hk
    have hkR : (k:ℝ) < (m:ℝ)+2*P := by
      have hc : (k:ℝ) < ((m+2*P:ℕ):ℝ) := by exact_mod_cast hk
      push_cast at hc; linarith
    have hsn : 2*(n:ℝ) < Real.sqrt 5 * n := by
      have := mul_lt_mul_of_pos_right hs2 hnpos; linarith
    have h2k : 2*(k:ℝ) < n := by nlinarith [hkR, hmU, hPub40, hsn, hnR]
    have h2kn : 2*k < n := by exact_mod_cast h2k
    omega
  have hkuf : ∀ k:ℕ, k < m+2*P → (k:ℝ) < (5-Real.sqrt 5)/10*n + 1 + 2*P := by
    intro k hk
    have hkR : (k:ℝ) < (m:ℝ)+2*P := by
      have hc : (k:ℝ) < ((m+2*P:ℕ):ℝ) := by exact_mod_cast hk
      push_cast at hc; linarith
    linarith [hmU, hkR]
  have hklf : ∀ k:ℕ, m₀ < k+2*P → (5-Real.sqrt 5)/10*n - 1 - 2*P < (k:ℝ) := by
    intro k hk
    have hkR : (m₀:ℝ) < (k:ℝ)+2*P := by
      have hc : ((m₀:ℕ):ℝ) < ((k+2*P:ℕ):ℝ) := by exact_mod_cast hk
      push_cast at hc; linarith
    linarith [hm0L, hkR]
  -- φ bounds
  have hphi_le : goldenRatio ≤ (n:ℝ)+1 := by
    have hlt : goldenRatio < 2 := by rw [show goldenRatio=(1+Real.sqrt 5)/2 from rfl]; linarith
    linarith
  have hphi_nn : (0:ℝ) ≤ goldenRatio := goldenRatio_pos.le
  -- tail per-term bound
  have htail_term : ∀ k:ℕ, 2*k ≤ n →
      |(((n:ℝ)+1-k)/((n:ℝ)+1-2*k))^L - goldenRatio^L| ≤ 2*((n:ℝ)+1)^L := by
    intro k hk2
    have hkn : 2*(k:ℝ) ≤ n := by exact_mod_cast hk2
    have hden : (0:ℝ) < (n:ℝ)+1-2*k := by linarith
    have hnum : (0:ℝ) ≤ (n:ℝ)+1-k := by linarith
    have hRk0 : 0 ≤ ((n:ℝ)+1-k)/((n:ℝ)+1-2*k) := by positivity
    have hRkle : ((n:ℝ)+1-k)/((n:ℝ)+1-2*k) ≤ (n:ℝ)+1 := by
      rw [div_le_iff₀ hden]
      nlinarith [hkn, hnum, mul_nonneg (show (0:ℝ)≤(n:ℝ)+1 by linarith) (show (0:ℝ)≤(n:ℝ)-2*k by linarith)]
    have h1 : (((n:ℝ)+1-k)/((n:ℝ)+1-2*k))^L ≤ ((n:ℝ)+1)^L := pow_le_pow_left₀ hRk0 hRkle L
    have h2 : goldenRatio^L ≤ ((n:ℝ)+1)^L := pow_le_pow_left₀ hphi_nn hphi_le L
    have h3 : (0:ℝ) ≤ (((n:ℝ)+1-k)/((n:ℝ)+1-2*k))^L := pow_nonneg hRk0 L
    have h4 : (0:ℝ) ≤ goldenRatio^L := pow_nonneg hphi_nn L
    have habs : |(((n:ℝ)+1-k)/((n:ℝ)+1-2*k))^L - goldenRatio^L|
        ≤ (((n:ℝ)+1-k)/((n:ℝ)+1-2*k))^L + goldenRatio^L := by
      rw [abs_le]; constructor <;> linarith [h3, h4]
    linarith [habs, h1, h2]
  -- bm and bm0 bounds
  have hbmS : (b n m:ℝ)^L ≤ S := by
    rw [hS_eq]
    apply Finset.single_le_sum (f := fun k => (b n k:ℝ)^L) (fun i _ => by positivity)
    exact Finset.mem_range.mpr (by omega)
  have hbm0S : (b n m₀:ℝ)^L ≤ S := by
    rw [hS_eq]
    apply Finset.single_le_sum (f := fun k => (b n k:ℝ)^L) (fun i _ => by positivity)
    exact Finset.mem_range.mpr (by omega)
  -- conversions between power forms
  have hconvH : ((1-β*Real.sqrt 5/4)^P)^L = ((1-β*Real.sqrt 5/4)^L)^P := pow_right_comm _ _ _
  have hconvL : (((1+β*Real.sqrt 5/4)^P)^L)⁻¹ = (((1+β*Real.sqrt 5/4)^L)⁻¹)^P := by
    rw [pow_right_comm, inv_pow]
  -- central sum bound
  have hcentral_sum : (∑ k ∈ (Finset.range (n/2+1)).filter (fun k => ¬(m+2*P ≤ k ∨ k+2*P ≤ m₀)),
        |(((n:ℝ)+1-k)/((n:ℝ)+1-2*k))^L - goldenRatio^L| * (b n k:ℝ)^L)
      ≤ (40/(n:ℝ)+20/(d:ℝ))*((L:ℝ)*3^(L-1)) * S := by
    have hb : ∀ k ∈ (Finset.range (n/2+1)).filter (fun k => ¬(m+2*P ≤ k ∨ k+2*P ≤ m₀)),
        |(((n:ℝ)+1-k)/((n:ℝ)+1-2*k))^L - goldenRatio^L| * (b n k:ℝ)^L
          ≤ (40/(n:ℝ)+20/(d:ℝ))*((L:ℝ)*3^(L-1)) * (b n k:ℝ)^L := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨hkr, hkn⟩ := hk
      push_neg at hkn
      obtain ⟨hkA, hkB⟩ := hkn
      have hcp := central_pow n k d P L hd hn80 (hk2n k hkA) hPub (hkuf k hkA) (hklf k hkB)
      exact mul_le_mul_of_nonneg_right hcp (by positivity)
    calc (∑ k ∈ (Finset.range (n/2+1)).filter (fun k => ¬(m+2*P ≤ k ∨ k+2*P ≤ m₀)),
            |(((n:ℝ)+1-k)/((n:ℝ)+1-2*k))^L - goldenRatio^L| * (b n k:ℝ)^L)
        ≤ ∑ k ∈ (Finset.range (n/2+1)).filter (fun k => ¬(m+2*P ≤ k ∨ k+2*P ≤ m₀)),
            (40/(n:ℝ)+20/(d:ℝ))*((L:ℝ)*3^(L-1)) * (b n k:ℝ)^L := Finset.sum_le_sum hb
      _ = (40/(n:ℝ)+20/(d:ℝ))*((L:ℝ)*3^(L-1))
            * ∑ k ∈ (Finset.range (n/2+1)).filter (fun k => ¬(m+2*P ≤ k ∨ k+2*P ≤ m₀)), (b n k:ℝ)^L := by
          rw [Finset.mul_sum]
      _ ≤ (40/(n:ℝ)+20/(d:ℝ))*((L:ℝ)*3^(L-1)) * S := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [hS_eq]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun k _ _ => by positivity)
  -- tail sum bounds
  have hsumA := sum_filter_high n m P L hn2 hβ0 hβ1 hm_cond hmP_cond
  have hsumB := sum_filter_low n m₀ P L hn2 hβ0 hnlarge hm0_cond hm0P_cond hPm0
  have hHInn : (0:ℝ) ≤ ((1-β*Real.sqrt 5/4)^P)^L := pow_nonneg (pow_nonneg h1mc P) L
  have hsumA' : (∑ k ∈ (Finset.range (n/2+1)).filter (fun k => m+2*P ≤ k), (b n k:ℝ)^L)
      ≤ ((n:ℝ)+1)*((1-β*Real.sqrt 5/4)^P)^L * S := by
    refine hsumA.trans ?_
    calc ((n:ℝ)+1)*(((1-β*Real.sqrt 5/4)^P)^L*(b n m:ℝ)^L)
        = (((n:ℝ)+1)*((1-β*Real.sqrt 5/4)^P)^L)*(b n m:ℝ)^L := by ring
      _ ≤ (((n:ℝ)+1)*((1-β*Real.sqrt 5/4)^P)^L)*S :=
          mul_le_mul_of_nonneg_left hbmS (mul_nonneg (by linarith) hHInn)
      _ = ((n:ℝ)+1)*((1-β*Real.sqrt 5/4)^P)^L * S := by ring
  have hsumB' : (∑ k ∈ (Finset.range (n/2+1)).filter (fun k => k+2*P ≤ m₀), (b n k:ℝ)^L)
      ≤ ((n:ℝ)+1)*S*(((1+β*Real.sqrt 5/4)^P)^L)⁻¹ := by
    refine hsumB.trans ?_
    rw [div_eq_mul_inv, ← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hbm0S (by linarith)
  have hunion : (∑ k ∈ (Finset.range (n/2+1)).filter (fun k => m+2*P ≤ k ∨ k+2*P ≤ m₀), (b n k:ℝ)^L)
      ≤ (∑ k ∈ (Finset.range (n/2+1)).filter (fun k => m+2*P ≤ k), (b n k:ℝ)^L)
        + (∑ k ∈ (Finset.range (n/2+1)).filter (fun k => k+2*P ≤ m₀), (b n k:ℝ)^L) := by
    rw [Finset.filter_or]
    have hinter := Finset.sum_union_inter
      (s₁ := (Finset.range (n/2+1)).filter (fun k => m+2*P ≤ k))
      (s₂ := (Finset.range (n/2+1)).filter (fun k => k+2*P ≤ m₀))
      (f := fun k => (b n k:ℝ)^L)
    have hpos : 0 ≤ ∑ k ∈ ((Finset.range (n/2+1)).filter (fun k => m+2*P ≤ k))
        ∩ ((Finset.range (n/2+1)).filter (fun k => k+2*P ≤ m₀)), (b n k:ℝ)^L :=
      Finset.sum_nonneg (fun k _ => by positivity)
    linarith [hinter, hpos]
  have htail_sum : (∑ k ∈ (Finset.range (n/2+1)).filter (fun k => m+2*P ≤ k ∨ k+2*P ≤ m₀),
        |(((n:ℝ)+1-k)/((n:ℝ)+1-2*k))^L - goldenRatio^L| * (b n k:ℝ)^L)
      ≤ 2*((n:ℝ)+1)^(L+1)*((1-β*Real.sqrt 5/4)^L)^P * S
        + 2*((n:ℝ)+1)^(L+1)*(((1+β*Real.sqrt 5/4)^L)⁻¹)^P * S := by
    have hb : ∀ k ∈ (Finset.range (n/2+1)).filter (fun k => m+2*P ≤ k ∨ k+2*P ≤ m₀),
        |(((n:ℝ)+1-k)/((n:ℝ)+1-2*k))^L - goldenRatio^L| * (b n k:ℝ)^L
          ≤ 2*((n:ℝ)+1)^L * (b n k:ℝ)^L := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      exact mul_le_mul_of_nonneg_right (htail_term k (by omega)) (by positivity)
    calc (∑ k ∈ (Finset.range (n/2+1)).filter (fun k => m+2*P ≤ k ∨ k+2*P ≤ m₀),
            |(((n:ℝ)+1-k)/((n:ℝ)+1-2*k))^L - goldenRatio^L| * (b n k:ℝ)^L)
        ≤ ∑ k ∈ (Finset.range (n/2+1)).filter (fun k => m+2*P ≤ k ∨ k+2*P ≤ m₀),
            2*((n:ℝ)+1)^L * (b n k:ℝ)^L := Finset.sum_le_sum hb
      _ = 2*((n:ℝ)+1)^L
            * ∑ k ∈ (Finset.range (n/2+1)).filter (fun k => m+2*P ≤ k ∨ k+2*P ≤ m₀), (b n k:ℝ)^L := by
          rw [Finset.mul_sum]
      _ ≤ 2*((n:ℝ)+1)^L * (((n:ℝ)+1)*((1-β*Real.sqrt 5/4)^P)^L*S
            + ((n:ℝ)+1)*S*(((1+β*Real.sqrt 5/4)^P)^L)⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact le_trans hunion (add_le_add hsumA' hsumB')
      _ = 2*((n:ℝ)+1)^(L+1)*((1-β*Real.sqrt 5/4)^L)^P * S
            + 2*((n:ℝ)+1)^(L+1)*(((1+β*Real.sqrt 5/4)^L)⁻¹)^P * S := by
          rw [← hconvH, ← hconvL, pow_succ]; ring
  -- combine into Σg ≤ B*S
  have hSg : (∑ k ∈ Finset.range (n/2+1),
        |(((n:ℝ)+1-k)/((n:ℝ)+1-2*k))^L - goldenRatio^L| * (b n k:ℝ)^L)
      ≤ ((40/(n:ℝ)+20/(d:ℝ))*((L:ℝ)*3^(L-1))
          + 2*((n:ℝ)+1)^(L+1)*((1-β*Real.sqrt 5/4)^L)^P
          + 2*((n:ℝ)+1)^(L+1)*(((1+β*Real.sqrt 5/4)^L)⁻¹)^P) * S := by
    have hsplit := (Finset.sum_filter_add_sum_filter_not (Finset.range (n/2+1))
      (fun k => m+2*P ≤ k ∨ k+2*P ≤ m₀)
      (fun k => |(((n:ℝ)+1-k)/((n:ℝ)+1-2*k))^L - goldenRatio^L| * (b n k:ℝ)^L)).symm
    rw [hsplit]
    have hexp : ((40/(n:ℝ)+20/(d:ℝ))*((L:ℝ)*3^(L-1))
          + 2*((n:ℝ)+1)^(L+1)*((1-β*Real.sqrt 5/4)^L)^P
          + 2*((n:ℝ)+1)^(L+1)*(((1+β*Real.sqrt 5/4)^L)⁻¹)^P) * S
        = (2*((n:ℝ)+1)^(L+1)*((1-β*Real.sqrt 5/4)^L)^P * S
            + 2*((n:ℝ)+1)^(L+1)*(((1+β*Real.sqrt 5/4)^L)⁻¹)^P * S)
          + (40/(n:ℝ)+20/(d:ℝ))*((L:ℝ)*3^(L-1)) * S := by ring
    rw [hexp]
    exact add_le_add htail_sum hcentral_sum
  -- final assembly
  have hnum : |(FW (n+1) L:ℝ) - goldenRatio^L*S|
      ≤ 1 + ((40/(n:ℝ)+20/(d:ℝ))*((L:ℝ)*3^(L-1))
          + 2*((n:ℝ)+1)^(L+1)*((1-β*Real.sqrt 5/4)^L)^P
          + 2*((n:ℝ)+1)^(L+1)*(((1+β*Real.sqrt 5/4)^L)⁻¹)^P) * S := by
    have h1 : |(FW (n+1) L:ℝ) - TT| ≤ 1 := by
      rw [abs_of_nonneg (by linarith [hTT_lo] : (0:ℝ) ≤ (FW (n+1) L:ℝ) - TT)]
      linarith [hTT_hi]
    have h2 := le_trans habsTT hSg
    calc |(FW (n+1) L:ℝ) - goldenRatio^L*S|
        = |((FW (n+1) L:ℝ) - TT) + (TT - goldenRatio^L*S)| := by
            rw [show (FW (n+1) L:ℝ) - goldenRatio^L*S
              = ((FW (n+1) L:ℝ) - TT) + (TT - goldenRatio^L*S) from by ring]
      _ ≤ |(FW (n+1) L:ℝ) - TT| + |TT - goldenRatio^L*S| := abs_add_le _ _
      _ ≤ 1 + ((40/(n:ℝ)+20/(d:ℝ))*((L:ℝ)*3^(L-1))
            + 2*((n:ℝ)+1)^(L+1)*((1-β*Real.sqrt 5/4)^L)^P
            + 2*((n:ℝ)+1)^(L+1)*(((1+β*Real.sqrt 5/4)^L)⁻¹)^P) * S := by linarith [h1, h2]
  have heqd : (FW (n+1) L:ℝ)/S - goldenRatio^L = ((FW (n+1) L:ℝ) - goldenRatio^L*S)/S := by
    field_simp
  rw [heqd, abs_div, abs_of_pos hSpos, div_le_iff₀ hSpos]
  calc |(FW (n+1) L:ℝ) - goldenRatio^L*S|
      ≤ 1 + ((40/(n:ℝ)+20/(d:ℝ))*((L:ℝ)*3^(L-1))
          + 2*((n:ℝ)+1)^(L+1)*((1-β*Real.sqrt 5/4)^L)^P
          + 2*((n:ℝ)+1)^(L+1)*(((1+β*Real.sqrt 5/4)^L)⁻¹)^P) * S := hnum
    _ = ((40/(n:ℝ)+20/(d:ℝ))*((L:ℝ)*3^(L-1))
          + 2*((n:ℝ)+1)^(L+1)*((1-β*Real.sqrt 5/4)^L)^P
          + 2*((n:ℝ)+1)^(L+1)*(((1+β*Real.sqrt 5/4)^L)⁻¹)^P
          + 1/S) * S := by field_simp; ring

set_option maxHeartbeats 1000000 in
theorem main_pos (L : ℕ) (hL : 1 ≤ L) :
    Tendsto (fun n => (FW (n+1) L:ℝ)/(FW n L:ℝ)) atTop (𝓝 (goldenRatio^L)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set KLe : ℝ := (L:ℝ)*3^(L-1) with hKLe
  have hKL0 : 0 ≤ KLe := by rw [hKLe]; positivity
  obtain ⟨d, hd40, hdε⟩ : ∃ d:ℕ, 40 ≤ d ∧ (20/(d:ℝ))*KLe < ε := by
    set X : ℕ := ⌈20*KLe/ε⌉₊ + 1 with hX
    refine ⟨max 40 X, le_max_left _ _, ?_⟩
    have hdpos : (0:ℝ) < ((max 40 X : ℕ):ℝ) := by
      have : 0 < max 40 X := by omega
      exact_mod_cast this
    have hge : 20*KLe/ε < ((max 40 X : ℕ):ℝ) := by
      have h1 : (X:ℝ) ≤ ((max 40 X:ℕ):ℝ) := by exact_mod_cast le_max_right 40 X
      have h2 : 20*KLe/ε < (X:ℝ) := by
        rw [hX]; push_cast
        have := Nat.le_ceil (20*KLe/ε)
        linarith
      linarith
    rw [div_mul_eq_mul_div, div_lt_iff₀ hdpos]
    rw [div_lt_iff₀ hε] at hge
    nlinarith [hge]
  have hdpos : 0 < d := by omega
  have hdRpos : (0:ℝ) < d := by exact_mod_cast hdpos
  -- the bound function
  set G : ℕ → ℝ := fun n => (40/(n:ℝ) + 20/(d:ℝ)) * KLe
        + 2*((n:ℝ)+1)^(L+1) * ((1 - (1/(d:ℝ))*Real.sqrt 5/4)^L)^(n/d+1)
        + 2*((n:ℝ)+1)^(L+1) * (((1 + (1/(d:ℝ))*Real.sqrt 5/4)^L)⁻¹)^(n/d+1)
        + 1/(FW n L : ℝ) with hGdef
  -- per-n bound, eventually
  have hbound_ev : ∀ᶠ n in atTop,
      |(FW (n+1) L:ℝ)/(FW n L:ℝ) - goldenRatio^L| ≤ G n := by
    filter_upwards [eventually_ge_atTop (4*d)] with n hn
    exact per_n_bound d L hd40 hL n hn
  -- decay helper
  have hdecay : ∀ (r:ℝ), 0 ≤ r → r < 1 →
      Tendsto (fun n:ℕ => 2*((n:ℝ)+1)^(L+1)*r^(n/d+1)) atTop (𝓝 0) := by
    intro r hr0 hr1
    have hk := key_tendsto (L+1) d hdpos r hr0 hr1
    have heq : (fun n:ℕ => 2*((n:ℝ)+1)^(L+1)*r^(n/d+1))
        = fun n:ℕ => (2*r)*(((n:ℝ)+1)^(L+1)*r^(n/d)) := by
      funext n; rw [pow_succ]; ring
    rw [heq]; simpa using hk.const_mul (2*r)
  -- base bounds
  have hcpos : (0:ℝ) < (1/(d:ℝ))*Real.sqrt 5/4 := by positivity
  have hbase_pos : (0:ℝ) < 1 - (1/(d:ℝ))*Real.sqrt 5/4 := by
    have hbsmall : (1/(d:ℝ))*Real.sqrt 5/4 ≤ (1/40)*3/4 := by
      have h1 : (1/(d:ℝ)) ≤ 1/40 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hd40)
      have h2 : Real.sqrt 5 ≤ 3 := sqrt5_lt3.le
      nlinarith [sqrt5_pos, h1, h2]
    linarith
  have hbase_lt : 1 - (1/(d:ℝ))*Real.sqrt 5/4 < 1 := by linarith [hcpos]
  have hB : Tendsto (fun n:ℕ => 2*((n:ℝ)+1)^(L+1)
        * ((1 - (1/(d:ℝ))*Real.sqrt 5/4)^L)^(n/d+1)) atTop (𝓝 0) :=
    hdecay _ (pow_nonneg hbase_pos.le L) (pow_lt_one₀ hbase_pos.le hbase_lt (by omega))
  have hLOpos : (1:ℝ) < 1 + (1/(d:ℝ))*Real.sqrt 5/4 := by linarith [hcpos]
  have hLOpowgt : (1:ℝ) < (1 + (1/(d:ℝ))*Real.sqrt 5/4)^L := one_lt_pow₀ hLOpos (by omega)
  have hC : Tendsto (fun n:ℕ => 2*((n:ℝ)+1)^(L+1)
        * (((1 + (1/(d:ℝ))*Real.sqrt 5/4)^L)⁻¹)^(n/d+1)) atTop (𝓝 0) :=
    hdecay _ (by positivity) (inv_lt_one_of_one_lt₀ hLOpowgt)
  have hD : Tendsto (fun n:ℕ => 1/(FW n L:ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun n:ℕ => 1/(n:ℝ))
    · filter_upwards with n; positivity
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hle : (n:ℝ) ≤ (FW n L:ℝ) := by exact_mod_cast F_lower n L hL hn
      exact one_div_le_one_div_of_le (by exact_mod_cast (show 0 < n by omega)) hle
    · exact tendsto_one_div_atTop_nhds_zero_nat
  have h40 : Tendsto (fun n:ℕ => 40/(n:ℝ)) atTop (𝓝 0) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat).const_mul (40:ℝ)
    simpa [mul_one_div] using this
  have hA : Tendsto (fun n:ℕ => (40/(n:ℝ)+20/(d:ℝ))*KLe) atTop (𝓝 ((20/(d:ℝ))*KLe)) := by
    have hs : Tendsto (fun n:ℕ => 40/(n:ℝ)+20/(d:ℝ)) atTop (𝓝 (20/(d:ℝ))) := by
      have := h40.add (tendsto_const_nhds (x := (20/(d:ℝ))))
      simpa using this
    have := hs.mul_const KLe
    simpa using this
  have hG : Tendsto G atTop (𝓝 ((20/(d:ℝ))*KLe)) := by
    rw [hGdef]
    have hcomb := ((hA.add hB).add hC).add hD
    simpa using hcomb
  have hGlt : ∀ᶠ n in atTop, G n < ε := hG.eventually_lt_const hdε
  have hfinal : ∀ᶠ n in atTop,
      |(FW (n+1) L:ℝ)/(FW n L:ℝ) - goldenRatio^L| < ε := by
    filter_upwards [hbound_ev, hGlt] with n h1 h2
    linarith
  rw [eventually_atTop] at hfinal
  obtain ⟨N, hN⟩ := hfinal
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  exact hN n hn

theorem F_zero (n : ℕ) : FW n 0 = n/2+1 := by
  unfold FW
  simp [pow_zero, Finset.sum_const, Finset.card_range]

theorem main_zero :
    Tendsto (fun n => (FW (n+1) 0:ℝ)/(FW n 0:ℝ)) atTop (𝓝 (goldenRatio^0)) := by
  have hFatTop : Tendsto (fun n:ℕ => FW n 0) atTop atTop := by
    apply tendsto_atTop_mono (f := fun n:ℕ => n/2) (fun n => by show n/2 ≤ FW n 0; rw [F_zero]; omega)
    exact tendsto_div_const 2 (by norm_num)
  have hone : Tendsto (fun n:ℕ => 1/(FW n 0:ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hFatTop
  have hh : Tendsto (fun n:ℕ => 1 + 1/(FW n 0:ℝ)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1:ℝ))).add hone
    simpa using this
  rw [pow_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
  · intro n
    have hFpos : (0:ℝ) < (FW n 0:ℝ) := by rw [F_zero]; positivity
    rw [le_div_iff₀ hFpos, one_mul]
    have hle : FW n 0 ≤ FW (n+1) 0 := by rw [F_zero, F_zero]; omega
    exact_mod_cast hle
  · intro n
    have hFpos : (0:ℝ) < (FW n 0:ℝ) := by rw [F_zero]; positivity
    rw [div_le_iff₀ hFpos]
    have hle : FW (n+1) 0 ≤ FW n 0 + 1 := by rw [F_zero, F_zero]; omega
    have hcast : (FW (n+1) 0:ℝ) ≤ (FW n 0:ℝ)+1 := by exact_mod_cast hle
    have hexp : (1+1/(FW n 0:ℝ))*(FW n 0:ℝ) = (FW n 0:ℝ)+1 := by field_simp
    rw [hexp]; exact hcast

theorem main_all (L : ℕ) :
    Tendsto (fun n => (FW (n+1) L:ℝ)/(FW n L:ℝ)) atTop (𝓝 (goldenRatio^L)) := by
  rcases Nat.eq_zero_or_pos L with h0 | hpos
  · subst h0; exact main_zero
  · exact main_pos L hpos

theorem oeis_181546_conjecture_0 (L : ℕ) :
    Tendsto (fun n => (F (n+1) L : ℝ) / (F n L : ℝ)) atTop (nhds (limit_value L)) := by
  rw [limit_value_eq]
  exact main_all L
