import FormalConjectures.Util.ProblemImports

open scoped BigOperators

open Finset

/-- The sum which A175386 $a(n)$ is the denominator of. -/
def S (n : ℕ) : ℚ :=
  Finset.sum (Finset.Icc 1 n) fun i : ℕ =>
    let num : ℕ := Nat.choose (2 * n - (i + 1)) (i - 1)
    (num : ℚ) / (i : ℚ)

/-- Fibonacci sum-of-choose in `range` form: `fib (N+1) = ∑_{j<N+1} C(N-j, j)`. -/
lemma fib_eq_sum_choose_range (N : ℕ) :
    Nat.fib (N + 1) = ∑ j ∈ Finset.range (N + 1), Nat.choose (N - j) j := by
  rw [Nat.fib_succ_eq_sum_choose, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => Nat.choose a b) N]
  rw [← Finset.sum_range_reflect (fun k => Nat.choose k (N - k)) (N + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  -- reflect index: term is choose (N+1-1-j) (N - (N+1-1-j)) = choose (N-j) (N-(N-j))
  have h1 : N + 1 - 1 - j = N - j := by omega
  rw [h1]
  congr 1
  omega

/-- Reindex a sum over `Icc 1 n` as a sum over `range n`. -/
lemma sum_Icc_one_shift {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ i ∈ Finset.Icc 1 n, f i = ∑ k ∈ Finset.range n, f (k + 1) := by
  have hIcc : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext x; simp [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff]
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have : n + 1 - 1 = n := by omega
  rw [this]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.add_comm]

/-- `∑_{i=1}^n C(2n-i, i) = fib(2n+1) - 1`, phrased as `... + 1 = fib(2n+1)`. -/
lemma sumA_eq (n : ℕ) :
    (∑ i ∈ Finset.Icc 1 n, Nat.choose (2 * n - i) i) + 1 = Nat.fib (2 * n + 1) := by
  have hrange : Nat.fib (2 * n + 1) = ∑ j ∈ Finset.range (n + 1), Nat.choose (2 * n - j) j := by
    rw [fib_eq_sum_choose_range (2 * n)]
    symm
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_range] at *
      omega
    · intro x _ hx2
      simp only [Finset.mem_range] at *
      apply Nat.choose_eq_zero_of_lt
      omega
  rw [hrange, Finset.sum_range_succ' (fun j => Nat.choose (2 * n - j) j) n]
  simp only [Nat.sub_zero, Nat.choose_zero_right]
  congr 1
  rw [sum_Icc_one_shift]

/-- `∑_{i=1}^n C(2n-i-1, i-1) = fib(2n-1)`. -/
lemma sumB_eq (n : ℕ) (hn : 1 ≤ n) :
    (∑ i ∈ Finset.Icc 1 n, Nat.choose (2 * n - (i + 1)) (i - 1)) = Nat.fib (2 * n - 1) := by
  have h2 : 2 * n - 1 = (2 * n - 2) + 1 := by omega
  rw [h2, fib_eq_sum_choose_range (2 * n - 2)]
  have hsub : (∑ j ∈ Finset.range (2 * n - 2 + 1), Nat.choose (2 * n - 2 - j) j)
      = ∑ j ∈ Finset.range n, Nat.choose (2 * n - 2 - j) j := by
    symm
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_range] at *
      omega
    · intro x _ hx2
      simp only [Finset.mem_range] at *
      apply Nat.choose_eq_zero_of_lt
      omega
  rw [hsub, sum_Icc_one_shift]
  apply Finset.sum_congr rfl
  intro i _
  congr 1 <;> omega

/-- Pointwise identity: `2n · C(2n-i-1, i-1) = i · (C(2n-i,i) + C(2n-i-1,i-1))`. -/
lemma nat_ident (n i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ n) :
    2 * n * Nat.choose (2 * n - (i + 1)) (i - 1)
      = i * (Nat.choose (2 * n - i) i + Nat.choose (2 * n - (i + 1)) (i - 1)) := by
  have hab := Nat.add_one_mul_choose_eq (2 * n - (i + 1)) (i - 1)
  have e1 : 2 * n - (i + 1) + 1 = 2 * n - i := by omega
  have e2 : i - 1 + 1 = i := by omega
  rw [e1, e2] at hab
  -- hab : (2n - i) * C(2n-(i+1))(i-1) = C(2n-i) i * i
  set C := Nat.choose (2 * n - (i + 1)) (i - 1) with hC
  set A := Nat.choose (2 * n - i) i with hA
  calc 2 * n * C = ((2 * n - i) + i) * C := by rw [show (2 * n - i) + i = 2 * n from by omega]
    _ = (2 * n - i) * C + i * C := by ring
    _ = A * i + i * C := by rw [hab]
    _ = i * (A + C) := by ring

/-- The core identity: `2n · S(n) = fib(2n+1) + fib(2n-1) - 1` in `ℚ`. -/
lemma two_n_S (n : ℕ) (hn : 1 ≤ n) :
    (2 * n : ℚ) * S n
      = (Nat.fib (2 * n + 1) : ℚ) + (Nat.fib (2 * n - 1) : ℚ) - 1 := by
  rw [S, Finset.mul_sum]
  have hpt : ∀ i ∈ Finset.Icc 1 n,
      (2 * n : ℚ) * ((Nat.choose (2 * n - (i + 1)) (i - 1) : ℚ) / (i : ℚ))
        = (Nat.choose (2 * n - i) i : ℚ) + (Nat.choose (2 * n - (i + 1)) (i - 1) : ℚ) := by
    intro i hi
    simp only [Finset.mem_Icc] at hi
    have hi0 : (i : ℚ) ≠ 0 := by
      have : 1 ≤ i := hi.1
      positivity
    have hnat := nat_ident n i hi.1 hi.2
    have hcast : (2 * n : ℚ) * (Nat.choose (2 * n - (i + 1)) (i - 1) : ℚ)
        = (i : ℚ) * ((Nat.choose (2 * n - i) i : ℚ)
            + (Nat.choose (2 * n - (i + 1)) (i - 1) : ℚ)) := by
      have := congrArg (fun m : ℕ => (m : ℚ)) hnat
      push_cast at this ⊢
      linarith [this]
    field_simp
    linarith [hcast]
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
  have hA := sumA_eq n
  have hB := sumB_eq n hn
  have hAcast : (∑ i ∈ Finset.Icc 1 n, (Nat.choose (2 * n - i) i : ℚ))
      = ((∑ i ∈ Finset.Icc 1 n, Nat.choose (2 * n - i) i : ℕ) : ℚ) := by push_cast; ring
  have hBcast : (∑ i ∈ Finset.Icc 1 n, (Nat.choose (2 * n - (i + 1)) (i - 1) : ℚ))
      = ((∑ i ∈ Finset.Icc 1 n, Nat.choose (2 * n - (i + 1)) (i - 1) : ℕ) : ℚ) := by
    push_cast; ring
  rw [hAcast, hBcast, hB]
  have hA' : ((∑ i ∈ Finset.Icc 1 n, Nat.choose (2 * n - i) i : ℕ) : ℚ)
      = (Nat.fib (2 * n + 1) : ℚ) - 1 := by
    have : ((∑ i ∈ Finset.Icc 1 n, Nat.choose (2 * n - i) i : ℕ) : ℚ) + 1
        = (Nat.fib (2 * n + 1) : ℚ) := by
      rw [← hA]; push_cast; ring
    linarith
  rw [hA']
  push_cast
  ring

/--
A175386: $a(n)$ is the denominator of the sum
$$\sum_{i=1}^n \frac{1}{i} \binom{2n-i-1}{i-1}$$
-/
def a (n : ℕ) : ℕ :=
  (Finset.sum (Finset.Icc 1 n) fun i : ℕ =>
    let num : ℕ := Nat.choose (2 * n - (i + 1)) (i - 1)
    (num : ℚ) / (i : ℚ)
  ).den

lemma a_eq_den (n : ℕ) : a n = (S n).den := rfl

/-! ### Number theory: `2n ∤ L_{2n} - 1` -/

/-- Lucas number `L_{2n}` as a natural number. -/
def Mnat (n : ℕ) : ℕ := Nat.fib (2 * n + 1) + Nat.fib (2 * n - 1)

lemma fib_mod4_period (k : ℕ) : Nat.fib (k + 6) % 4 = Nat.fib k % 4 := by
  have h : k + 6 = k + 5 + 1 := rfl
  rw [h, Nat.fib_add k 5]
  have h5 : Nat.fib 5 = 5 := rfl
  have h6 : Nat.fib 6 = 8 := rfl
  rw [h5, h6]
  omega

lemma fib_mod2_period (k : ℕ) : Nat.fib (k + 3) % 2 = Nat.fib k % 2 := by
  have h : k + 3 = k + 2 + 1 := rfl
  rw [h, Nat.fib_add k 2]
  have h2 : Nat.fib 2 = 1 := rfl
  have h3 : Nat.fib 3 = 2 := rfl
  rw [h2, h3]
  omega

/-- Step of period 3 for `Mnat` modulo 4. -/
lemma Mstep4 (m : ℕ) (hm : 1 ≤ m) : Mnat (m + 3) % 4 = Mnat m % 4 := by
  unfold Mnat
  have e1 : 2 * (m + 3) + 1 = (2 * m + 1) + 6 := by omega
  have e2 : 2 * (m + 3) - 1 = (2 * m - 1) + 6 := by omega
  rw [e1, e2]
  have p1 := fib_mod4_period (2 * m + 1)
  have p2 := fib_mod4_period (2 * m - 1)
  omega

/-- The mod-4 dichotomy for `Mnat`: it is `≡ 2 (mod 4)` iff `3 ∣ n`, else `≡ 3`. -/
lemma Mnat_mod4_cases (n : ℕ) (hn : 1 ≤ n) :
    (3 ∣ n ∧ Mnat n % 4 = 2) ∨ (¬ (3 ∣ n) ∧ Mnat n % 4 = 3) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 4 with h3 | h3
    · interval_cases n
      · right; exact ⟨by decide, by decide⟩
      · right; exact ⟨by decide, by decide⟩
      · left; exact ⟨by decide, by decide⟩
    · have hm : 1 ≤ n - 3 := by omega
      have hlt : n - 3 < n := by omega
      have := ih (n - 3) hlt hm
      have hstep : Mnat n % 4 = Mnat (n - 3) % 4 := by
        have : n = (n - 3) + 3 := by omega
        rw [this]; exact Mstep4 (n - 3) hm
      have hdvd : (3 ∣ n) ↔ (3 ∣ (n - 3)) := by
        constructor
        · rintro ⟨c, hc⟩; exact ⟨c - 1, by omega⟩
        · rintro ⟨c, hc⟩; exact ⟨c + 1, by omega⟩
      rcases this with ⟨hd, hM⟩ | ⟨hd, hM⟩
      · left; exact ⟨hdvd.mpr hd, by rw [hstep, hM]⟩
      · right; exact ⟨fun h => hd (hdvd.mp h), by rw [hstep, hM]⟩

lemma Mnat_ge_one (n : ℕ) (hn : 1 ≤ n) : 1 ≤ Mnat n := by
  unfold Mnat
  have : 1 ≤ Nat.fib (2 * n + 1) := Nat.fib_pos.mpr (by omega)
  omega

/-- Step of period 2 for `Mnat` modulo 5 (Lucas has period 4). -/
lemma Mstep5 (m : ℕ) (hm : 1 ≤ m) : Mnat (m + 2) % 5 = Mnat m % 5 := by
  unfold Mnat
  have e1 : 2 * (m + 2) + 1 = (2 * m - 1) + 6 := by omega
  have e2 : 2 * (m + 2) - 1 = (2 * m - 1) + 4 := by omega
  have e3 : 2 * m + 1 = (2 * m - 1) + 2 := by omega
  rw [e1, e2, e3]
  set j := 2 * m - 1 with hj
  have b1 : Nat.fib (j + 6) = Nat.fib j * 5 + Nat.fib (j + 1) * 8 := by
    have := Nat.fib_add j 5
    simpa [show Nat.fib 5 = 5 from rfl, show Nat.fib 6 = 8 from rfl] using this
  have b2 : Nat.fib (j + 4) = Nat.fib j * 2 + Nat.fib (j + 1) * 3 := by
    have := Nat.fib_add j 3
    simpa [show Nat.fib 3 = 2 from rfl, show Nat.fib 4 = 3 from rfl] using this
  have b3 : Nat.fib (j + 2) = Nat.fib j + Nat.fib (j + 1) := Nat.fib_add_two
  rw [b1, b2, b3]
  omega

/-- For `n` odd, `Mnat n ≡ 3 (mod 5)`. -/
lemma Mnat_mod5_odd (n : ℕ) (hn : 1 ≤ n) (hodd : n % 2 = 1) : Mnat n % 5 = 3 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · interval_cases n
      · decide
      · omega  -- n = 2 excluded by hodd
    · have hm : 1 ≤ n - 2 := by omega
      have hlt : n - 2 < n := by omega
      have hodd2 : (n - 2) % 2 = 1 := by omega
      have := ih (n - 2) hlt hm hodd2
      have hstep : Mnat n % 5 = Mnat (n - 2) % 5 := by
        have hn2 : n = (n - 2) + 2 := by omega
        rw [hn2]; exact Mstep5 (n - 2) hm
      rw [hstep, this]

/-- The Lucas-power identity in a field: `2 F_{k+1} - F_k = α^k + β^k`
when `α, β` are roots of `X² - X - 1` with `α + β = 1`. -/
lemma lucas_pow {K : Type*} [Field K] (α β : K)
    (hα : α ^ 2 = α + 1) (hβ : β ^ 2 = β + 1) (hsum : α + β = 1) (k : ℕ) :
    2 * (Nat.fib (k + 1) : K) - (Nat.fib k : K) = α ^ k + β ^ k := by
  induction k using Nat.twoStepInduction with
  | zero => norm_num
  | one =>
    show 2 * (Nat.fib (1 + 1) : K) - (Nat.fib 1 : K) = α ^ 1 + β ^ 1
    rw [show Nat.fib (1 + 1) = 1 from rfl, show Nat.fib 1 = 1 from rfl, pow_one, pow_one]
    push_cast
    linear_combination -hsum
  | more k ih1 ih2 =>
    have hαsucc : α ^ (k + 2) = α ^ (k + 1) + α ^ k := by
      have h : α ^ (k + 2) = α ^ k * α ^ 2 := by ring
      rw [h, hα]; ring
    have hβsucc : β ^ (k + 2) = β ^ (k + 1) + β ^ k := by
      have h : β ^ (k + 2) = β ^ k * β ^ 2 := by ring
      rw [h, hβ]; ring
    have hf3 : Nat.fib (k + 2 + 1) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
    have hf2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
    rw [hαsucc, hβsucc,
      show α ^ (k + 1) + α ^ k + (β ^ (k + 1) + β ^ k)
        = (α ^ (k + 1) + β ^ (k + 1)) + (α ^ k + β ^ k) from by ring,
      ← ih1, ← ih2, hf3, hf2]
    push_cast
    ring

/-- The finite-field order argument: if `α` is a root of `X²-X-1` in a field of characteristic
`p ≥ 7`, and `n` is odd with smallest prime factor `p`, then `α^{2n} + (1-α)^{2n} ≠ 1`. -/
lemma field_core {K : Type*} [Field K] (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) [CharP K p]
    (α : K) (hα : α ^ 2 = α + 1)
    (n : ℕ) (hn1 : 1 ≤ n) (hodd : ¬ (2 ∣ n))
    (hpn : p ∣ n) (hpmin : ∀ q, q.Prime → q ∣ n → p ≤ q)
    (hfield : α ^ (2 * n) + (1 - α) ^ (2 * n) = 1) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  set β : K := 1 - α with hβdef
  have hβ : β ^ 2 = β + 1 := by rw [hβdef]; linear_combination hα
  have hsum : α + β = 1 := by rw [hβdef]; ring
  have hab : α * β = -1 := by rw [hβdef]; linear_combination -hα
  have hα0 : α ≠ 0 := by intro h; rw [h] at hα; simp at hα
  -- characteristic facts
  have hchar2 : (2 : K) ≠ 0 := by
    rw [show (2 : K) = ((2 : ℕ) : K) by norm_num, Ne, CharP.cast_eq_zero_iff K p 2]
    intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  have hchar3 : (3 : K) ≠ 0 := by
    rw [show (3 : K) = ((3 : ℕ) : K) by norm_num, Ne, CharP.cast_eq_zero_iff K p 3]
    intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  -- Frobenius: α^p is a root of X²-X-1
  have hroot : (α ^ p) ^ 2 = α ^ p + 1 := by
    have h1 : (α ^ p) ^ 2 = (α ^ 2) ^ p := by rw [← pow_mul, ← pow_mul, Nat.mul_comm p 2]
    rw [h1, hα, add_pow_char, one_pow]
  have hdich : α ^ p = α ∨ α ^ p = β := by
    have hz : (α ^ p - α) * (α ^ p - β) = 0 := by
      have hexp : (α ^ p - α) * (α ^ p - β)
          = (α ^ p) ^ 2 - (α + β) * α ^ p + α * β := by ring
      rw [hexp, hsum, hab, hroot]; ring
    rcases mul_eq_zero.mp hz with h | h
    · left; exact sub_eq_zero.mp h
    · right; exact sub_eq_zero.mp h
  -- order of α divides p-1 or 2(p+1)
  have hD : orderOf α ∣ (p - 1) ∨ orderOf α ∣ 2 * (p + 1) := by
    rcases hdich with h | h
    · left
      apply orderOf_dvd_of_pow_eq_one
      have hcancel : α ^ (p - 1) * α = 1 * α := by
        rw [one_mul, ← pow_succ, Nat.sub_add_cancel (show 1 ≤ p by omega)]; exact h
      exact mul_right_cancel₀ hα0 hcancel
    · right
      apply orderOf_dvd_of_pow_eq_one
      have h1 : α ^ (p + 1) = -1 := by rw [pow_succ', h]; exact hab
      calc α ^ (2 * (p + 1)) = (α ^ (p + 1)) ^ 2 := by rw [← pow_mul]; congr 1; ring
        _ = (-1) ^ 2 := by rw [h1]
        _ = 1 := by ring
  -- prime factors of orderOf α are < p
  have hprimebound : ∀ q, q.Prime → q ∣ orderOf α → q < p := by
    intro q hq hqD
    rcases hD with hDp | hDp
    · have hqd : q ∣ p - 1 := hqD.trans hDp
      have := Nat.le_of_dvd (by omega) hqd
      omega
    · have hq2 : q ∣ 2 * (p + 1) := hqD.trans hDp
      rcases (Nat.Prime.dvd_mul hq).mp hq2 with h2 | hpp
      · have := Nat.le_of_dvd (by norm_num) h2; omega
      · rcases eq_or_ne q 2 with hq2e | hq2e
        · omega
        · obtain ⟨c, hc⟩ := hpp
          have hqodd : ¬ (2 ∣ q) := by
            intro h2q
            rcases hq.eq_one_or_self_of_dvd 2 h2q with h | h
            · omega
            · exact hq2e h.symm
          have h2pp : 2 ∣ (p + 1) := by
            have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
            omega
          have h2c : 2 ∣ c := by
            have : 2 ∣ q * c := hc ▸ h2pp
            rcases (Nat.Prime.dvd_mul Nat.prime_two).mp this with hh | hh
            · exact absurd hh hqodd
            · exact hh
          have hcpos : 1 ≤ c := by
            rcases Nat.eq_zero_or_pos c with h0 | h0
            · rw [h0, Nat.mul_zero] at hc; omega
            · exact h0
          have hc2 : 2 ≤ c := by
            rcases h2c with ⟨d, hd⟩; omega
          have hle : 2 * q ≤ p + 1 := by
            calc 2 * q = q * 2 := by ring
              _ ≤ q * c := Nat.mul_le_mul_left q hc2
              _ = p + 1 := hc.symm
          omega
  -- coprimality
  have hcopDn : Nat.Coprime (orderOf α) n := by
    by_contra hne
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
    have hqD : q ∣ orderOf α := hqd.trans (Nat.gcd_dvd_left _ _)
    have hqn : q ∣ n := hqd.trans (Nat.gcd_dvd_right _ _)
    have h1 := hprimebound q hq hqD
    have h2 := hpmin q hq hqn
    omega
  -- w := α^{2n} is a primitive 6th root of unity
  set w := α ^ (2 * n) with hw
  have hw0 : w ≠ 0 := pow_ne_zero _ hα0
  have hwb : w * β ^ (2 * n) = 1 := by
    rw [hw, ← mul_pow, hab, pow_mul]; norm_num
  -- hfield : w + β^{2n} = 1
  have hquad : w ^ 2 - w + 1 = 0 := by linear_combination w * hfield - hwb
  have hw3 : w ^ 3 = -1 := by linear_combination (w + 1) * hquad
  have hw6 : w ^ 6 = 1 := by
    have : w ^ 6 = (w ^ 3) ^ 2 := by ring
    rw [this, hw3]; ring
  have hwne1 : w ≠ 1 := by intro h; rw [h] at hquad; simp at hquad
  -- orderOf w = 6
  have hdvd6 : orderOf w ∣ 6 := orderOf_dvd_of_pow_eq_one hw6
  have hne0 : orderOf w ≠ 0 := by
    intro h; rw [h] at hdvd6; exact absurd (Nat.eq_zero_of_zero_dvd hdvd6) (by norm_num)
  have hpow_ord : w ^ (orderOf w) = 1 := pow_orderOf_eq_one w
  have hord : orderOf w = 6 := by
    obtain ⟨d, hdeq⟩ : ∃ d, orderOf w = d := ⟨_, rfl⟩
    rw [hdeq] at hdvd6 hpow_ord hne0 ⊢
    have hdle : d ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
    have hdpos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hne0
    interval_cases d
    · exact absurd (by simpa using hpow_ord) hwne1
    · exfalso
      -- w^2 = 1, with hquad → w = 2, then 3 = 0
      have hw2 : w ^ 2 = 1 := hpow_ord
      have hw22 : w = 2 := by linear_combination hw2 - hquad
      rw [hw22] at hquad
      apply hchar3; linear_combination hquad
    · exfalso
      -- w^3 = 1 but w^3 = -1
      rw [hw3] at hpow_ord
      apply hchar2; linear_combination -hpow_ord
    · exact absurd hdvd6 (by norm_num)
    · exact absurd hdvd6 (by norm_num)
    · rfl
  -- orderOf α = 12
  have hpow_eq : orderOf w = orderOf α / Nat.gcd (orderOf α) (2 * n) := by
    rw [hw]; exact orderOf_pow' α (by omega)
  have hgdvd : Nat.gcd (orderOf α) (2 * n) ∣ orderOf α := Nat.gcd_dvd_left _ _
  have hDeq : orderOf α = Nat.gcd (orderOf α) (2 * n) * 6 := by
    have h6eq : orderOf α / Nat.gcd (orderOf α) (2 * n) = 6 := by rw [← hpow_eq]; exact hord
    rw [← h6eq]; exact (Nat.mul_div_cancel' hgdvd).symm
  have h2D : 2 ∣ orderOf α := by rw [hDeq]; exact Dvd.dvd.mul_left (by norm_num) _
  have hg2 : Nat.gcd (orderOf α) (2 * n) = 2 := by
    have hcop2 := Nat.Coprime.coprime_dvd_left hgdvd hcopDn
    have hgdvd2 : Nat.gcd (orderOf α) (2 * n) ∣ 2 :=
      hcop2.dvd_of_dvd_mul_right (Nat.gcd_dvd_right _ _)
    have h2g : 2 ∣ Nat.gcd (orderOf α) (2 * n) := Nat.dvd_gcd h2D ⟨n, rfl⟩
    exact Nat.dvd_antisymm hgdvd2 h2g
  have hD12 : orderOf α = 12 := by rw [hg2] at hDeq; omega
  have hα12 : α ^ 12 = 1 := by rw [← hD12]; exact pow_orderOf_eq_one α
  have hβ12 : β ^ 12 = 1 := by
    have hαβ12 : α ^ 12 * β ^ 12 = 1 := by rw [← mul_pow, hab]; norm_num
    rw [hα12, one_mul] at hαβ12; exact hαβ12
  -- L_12 = 2 forces p ∣ 320
  have hL := lucas_pow α β hα hβ hsum 12
  rw [hα12, hβ12] at hL
  rw [show Nat.fib (12 + 1) = 233 from rfl, show Nat.fib 12 = 144 from rfl] at hL
  have h320 : (320 : K) = 0 := by push_cast at hL; linear_combination hL
  have hp320 : p ∣ 320 := by
    have := (CharP.cast_eq_zero_iff K p 320).mp h320; exact this
  have : p ∣ 2 ^ 6 * 5 := by norm_num at hp320 ⊢; exact hp320
  rcases (Nat.Prime.dvd_mul hp).mp this with h | h
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
  · have := Nat.le_of_dvd (by norm_num) h; omega

/-- Case (c): the finite-field argument packaged for `p = minFac n ≥ 7`. -/
lemma case_c (n : ℕ) (hn1 : 1 ≤ n) (hodd : ¬ (2 ∣ n))
    (hp7 : 7 ≤ Nat.minFac n) (hn' : n ≠ 1)
    (hpMnat : Nat.minFac n ∣ (Mnat n - 1)) : False := by
  set p := Nat.minFac n with hpdef
  have hp : p.Prime := Nat.minFac_prime hn'
  haveI : Fact p.Prime := ⟨hp⟩
  have hpn : p ∣ n := Nat.minFac_dvd n
  have hpmin : ∀ q, q.Prime → q ∣ n → p ≤ q := fun q hq hqn =>
    Nat.minFac_le_of_dvd hq.two_le hqn
  have hMge : 1 ≤ Mnat n := Mnat_ge_one n hn1
  -- build the splitting field
  set f : Polynomial (ZMod p) := Polynomial.X ^ 2 - Polynomial.X - 1 with hf
  set K := f.SplittingField with hK
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have hinj : Function.Injective (algebraMap (ZMod p) K) := (algebraMap (ZMod p) K).injective
  have hsplits : Polynomial.Splits (f.map (algebraMap (ZMod p) K)) :=
    Polynomial.SplittingField.splits f
  have hdeg2 : (f.map (algebraMap (ZMod p) K)).degree = 2 := by
    rw [Polynomial.degree_map_eq_of_injective hinj, hf]; compute_degree!
  have hdeg : (f.map (algebraMap (ZMod p) K)).degree ≠ 0 := by rw [hdeg2]; decide
  obtain ⟨α, hαroot⟩ := hsplits.exists_eval_eq_zero hdeg
  have heval : Polynomial.eval α (f.map (algebraMap (ZMod p) K)) = α ^ 2 - α - 1 := by
    rw [Polynomial.eval_map]
    show Polynomial.eval₂ (algebraMap (ZMod p) K) α
      (Polynomial.X ^ 2 - Polynomial.X - 1) = α ^ 2 - α - 1
    simp
  rw [heval] at hαroot
  have hα2 : α ^ 2 = α + 1 := by linear_combination hαroot
  -- (Mnat n : ZMod p) = 1
  have hpZ : (p : ℤ) ∣ ((Mnat n : ℤ) - 1) := by
    have h1 : ((Mnat n - 1 : ℕ) : ℤ) = (Mnat n : ℤ) - 1 := by
      rw [Nat.cast_sub hMge]; norm_num
    rw [← h1]
    exact_mod_cast hpMnat
  have hzmod : (Mnat n : ZMod p) = 1 := by
    have h0 : (((Mnat n : ℤ) - 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpZ
    push_cast at h0
    linear_combination h0
  have hMK : (Mnat n : K) = 1 := by
    have := congrArg (algebraMap (ZMod p) K) hzmod
    rwa [map_natCast, map_one] at this
  -- hfield : α^{2n} + (1-α)^{2n} = 1
  have hfibrec : Nat.fib (2 * n + 1) = Nat.fib (2 * n - 1) + Nat.fib (2 * n) := by
    have e : 2 * n + 1 = (2 * n - 1) + 2 := by omega
    have e2 : (2 * n - 1) + 1 = 2 * n := by omega
    rw [e, Nat.fib_add_two, e2]
  have hβ2 : (1 - α) ^ 2 = (1 - α) + 1 := by linear_combination hα2
  have hfield : α ^ (2 * n) + (1 - α) ^ (2 * n) = 1 := by
    have hLK := lucas_pow α (1 - α) hα2 hβ2 (by ring) (2 * n)
    rw [← hLK]
    have hKfib : (Nat.fib (2 * n + 1) : K) = (Nat.fib (2 * n - 1) : K) + (Nat.fib (2 * n) : K) := by
      rw [hfibrec]; push_cast; ring
    have hMval : (Mnat n : K) = 2 * (Nat.fib (2 * n + 1) : K) - (Nat.fib (2 * n) : K) := by
      unfold Mnat; push_cast; linear_combination -hKfib
    rw [← hMval]; exact hMK
  exact field_core p hp hp7 α hα2 n hn1 hodd hpn hpmin hfield

/-- Number theory core: `2n ∤ L_{2n} - 1` for `n > 1`. -/
lemma not_dvd_lucas (n : ℕ) (hn : 1 < n) :
    ¬ ((2 * n : ℤ) ∣ ((Nat.fib (2 * n + 1) : ℤ) + (Nat.fib (2 * n - 1) : ℤ) - 1)) := by
  intro h
  have hn1 : 1 ≤ n := by omega
  have hMge : 1 ≤ Mnat n := Mnat_ge_one n hn1
  -- rephrase h with Mnat
  have hdvdZ : (2 * (n : ℤ)) ∣ ((Mnat n : ℤ) - 1) := by
    have hMint : (Mnat n : ℤ) = (Nat.fib (2 * n + 1) : ℤ) + (Nat.fib (2 * n - 1) : ℤ) := by
      unfold Mnat; push_cast; ring
    rw [hMint]; convert h using 1
  -- turn ℤ-divisibility by k into ℕ-divisibility of Mnat n - 1
  have toNat : ∀ k : ℕ, (k : ℤ) ∣ (2 * (n : ℤ)) → k ∣ (Mnat n - 1) := by
    intro k hk
    have hkM : (k : ℤ) ∣ ((Mnat n : ℤ) - 1) := dvd_trans hk hdvdZ
    have hcast : ((Mnat n - 1 : ℕ) : ℤ) = (Mnat n : ℤ) - 1 := by
      rw [Nat.cast_sub hMge]; norm_num
    rw [← hcast] at hkM
    exact_mod_cast hkM
  by_cases he : 2 ∣ n
  · -- n even : 4 ∣ 2n but Mnat n % 4 ≠ 1
    have h4 : (4 : ℕ) ∣ (Mnat n - 1) := by
      apply toNat 4
      obtain ⟨m, hm⟩ := he
      refine ⟨(m : ℤ), ?_⟩
      rw [hm]; push_cast; ring
    rcases Mnat_mod4_cases n hn1 with ⟨_, hM⟩ | ⟨_, hM⟩ <;> omega
  · -- n odd
    by_cases h3 : 3 ∣ n
    · -- Mnat n even, but 2 ∣ 2n and 2 ∣ Mnat-1 needs Mnat even; Mnat%4 = 2 so Mnat even → Mnat-1 odd
      have h2 : (2 : ℕ) ∣ (Mnat n - 1) := by
        apply toNat 2; exact ⟨(n : ℤ), by ring⟩
      rcases Mnat_mod4_cases n hn1 with ⟨_, hM⟩ | ⟨hcontra, _⟩
      · omega
      · exact hcontra h3
    · by_cases h5 : 5 ∣ n
      · -- Mnat n % 5 = 3, but 5 ∣ 2n and 5 ∣ Mnat-1 → Mnat%5=1
        have h5d : (5 : ℕ) ∣ (Mnat n - 1) := by
          apply toNat 5
          obtain ⟨m, hm⟩ := h5
          refine ⟨2 * (m : ℤ), ?_⟩
          rw [hm]; push_cast; ring
        have hodd : n % 2 = 1 := by omega
        have := Mnat_mod5_odd n hn1 hodd
        omega
      · -- minFac n ≥ 7
        have hodd : ¬ (2 ∣ n) := he
        have hp7 : 7 ≤ Nat.minFac n := by
          have hp := Nat.minFac_prime (show n ≠ 1 by omega)
          have hpdvd := Nat.minFac_dvd n
          by_contra hlt
          have h2le := hp.two_le
          interval_cases h : (Nat.minFac n)
          · exact he hpdvd
          · exact h3 hpdvd
          · exact absurd hp (by decide)
          · exact h5 hpdvd
          · exact absurd hp (by decide)
        have hpMnat : Nat.minFac n ∣ (Mnat n - 1) := by
          apply toNat (Nat.minFac n)
          have : (Nat.minFac n : ℤ) ∣ (n : ℤ) := by exact_mod_cast Nat.minFac_dvd n
          exact Dvd.dvd.mul_left this 2
        exact case_c n hn1 hodd hp7 (by omega) hpMnat

/-- The main result. -/
theorem main (n : ℕ) (hn : 1 < n) : a n ≠ 1 := by
  rw [a_eq_den]
  intro hden
  apply not_dvd_lucas n hn
  -- from den = 1, S n is an integer
  have hSint : (S n) = ((S n).num : ℚ) := by
    rw [← Rat.num_div_den (S n), hden]
    simp
  have hkey := two_n_S n (by omega)
  rw [hSint] at hkey
  -- hkey : 2 * n * (S n).num = fib(2n+1) + fib(2n-1) - 1  (in ℚ)
  have : ((Nat.fib (2 * n + 1) : ℤ) + (Nat.fib (2 * n - 1) : ℤ) - 1 : ℤ)
      = 2 * n * (S n).num := by
    have hq : ((((Nat.fib (2 * n + 1) : ℤ) + (Nat.fib (2 * n - 1) : ℤ) - 1) : ℤ) : ℚ)
        = (((2 * n * (S n).num : ℤ)) : ℚ) := by
      push_cast
      push_cast at hkey
      linarith [hkey]
    exact_mod_cast hq
  exact ⟨(S n).num, this⟩


/--
A175386 We conjecture that sum((1/i)*C(2n-i-1,i-1),i=1..n) is not an integer for $n>1$.
-/
theorem oeis_175386_conjecture_0 (n : ℕ) (hn : 1 < n) : a n ≠ 1 := main n hn

