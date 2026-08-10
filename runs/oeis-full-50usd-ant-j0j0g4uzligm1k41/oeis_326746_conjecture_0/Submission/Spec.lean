import FormalConjectures.Util.ProblemImports

open Nat List

/--
A326746: $a(n) = (\text{sum of digits of } n) \bmod (\text{sum of digits of } n+1)$.
-/
def a (n : ℕ) : ℕ :=
  (Nat.digits 10 n).sum % (Nat.digits 10 (n + 1)).sum

/-- The count of non-negative integers $n < N$ such that $a(n) = m$. -/
def count_a_eq (N m : ℕ) : ℕ :=
  (List.range N).countP fun n => a n = m

open Filter Real Finset Topology

namespace OEIS326746

/-- digit sum base 10 -/
def S (n : ℕ) : ℕ := (Nat.digits 10 n).sum


/-- Key digit-sum recursion: S n = S (n/10) + n % 10. -/
theorem DS (n : ℕ) : S n = S (n / 10) + n % 10 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [S]
  · unfold S
    rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) h]
    simp [List.sum_cons, Nat.add_comm]

/-- When the last digit is ≤ 8, incrementing does not carry. -/
theorem succ_no_carry {n : ℕ} (h : n % 10 ≤ 8) :
    (n + 1) % 10 = n % 10 + 1 ∧ (n + 1) / 10 = n / 10 := by
  have key : n + 1 = (n % 10 + 1) + 10 * (n / 10) := by
    have := Nat.div_add_mod n 10
    omega
  have h10 : n % 10 + 1 < 10 := by omega
  refine ⟨?_, ?_⟩
  · rw [key, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h10]
  · rw [key, Nat.add_mul_div_left _ _ (by norm_num : 0 < 10),
      Nat.div_eq_of_lt h10, Nat.zero_add]

/-- `S` in terms of digit sum: alias so we can rewrite `a`. -/
theorem a_eq (n : ℕ) : a n = S n % S (n + 1) := rfl

/-- digit sum increments by 1 when no carry. -/
theorem S_succ_no_carry {t : ℕ} (h : t % 10 ≠ 9) : S (t + 1) = S t + 1 := by
  have h8 : t % 10 ≤ 8 := by omega
  obtain ⟨hm, hd⟩ := succ_no_carry h8
  rw [DS (t + 1), hd, hm, DS t]
  ring

/-- Value of `a` when the last digit is ≤ 8. -/
theorem a_low {n : ℕ} (h : n % 10 ≤ 8) : a n = S (n / 10) + n % 10 := by
  obtain ⟨hm, hd⟩ := succ_no_carry h
  rw [a_eq, DS n, DS (n + 1), hd, hm]
  rw [Nat.mod_eq_of_lt (by omega : S (n / 10) + n % 10 < S (n / 10) + (n % 10 + 1))]

/-- Value of `a = 8` when last digit is 9, no double carry, and digit sum ≥ 8. -/
theorem a_eq_eight {n : ℕ} (h9 : n % 10 = 9) (hnc : (n / 10) % 10 ≠ 9)
    (hS : 8 ≤ S (n / 10)) : a n = 8 := by
  set t := n / 10 with ht
  -- n = 10 t + 9
  have hn : n = 10 * t + 9 := by
    have := Nat.div_add_mod n 10; omega
  -- n + 1 = 10 (t+1)
  have hsucc : n + 1 = 10 * (t + 1) := by omega
  have hSn : S n = S t + 9 := by rw [DS n, ht, h9]
  have hSn1 : S (n + 1) = S t + 1 := by
    rw [hsucc, DS (10 * (t + 1))]
    have hmod : (10 * (t + 1)) % 10 = 0 := by omega
    have hdiv : (10 * (t + 1)) / 10 = t + 1 := by
      rw [Nat.mul_div_cancel_left]; norm_num
    rw [hmod, hdiv, S_succ_no_carry hnc]
  rw [a_eq, hSn, hSn1]
  -- (S t + 9) % (S t + 1) = 8
  have : S t + 9 = 8 + (S t + 1) := by ring
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-! ### Level-set counting bounds -/

/-- count of `t < N` with digit sum exactly `s`. -/
def c (N s : ℕ) : ℕ := ((Finset.range N).filter (fun t => S t = s)).card

/-- count of `t < N` with digit sum `≤ B`. -/
def cle (N B : ℕ) : ℕ := ((Finset.range N).filter (fun t => S t ≤ B)).card

/-- Hockey stick identity. -/
theorem hockey (D : ℕ) : ∀ s, ∑ i ∈ Finset.range (s + 1), (D + i).choose i = (D + s + 1).choose s := by
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, ih]
    exact (Nat.choose_succ_succ (D + s + 1) s).symm

/-- `cle` as a sum of level sets. -/
theorem cle_eq_sum (N B : ℕ) : cle N B = ∑ b ∈ Finset.range (B + 1), c N b := by
  unfold cle c
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun t => S t) (t := Finset.range (B + 1)) ?_]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mem_range] at hb
    rw [Finset.filter_filter]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨ht, _, h3⟩; exact ⟨ht, h3⟩
    · rintro ⟨ht, h3⟩; exact ⟨ht, by omega, h3⟩
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ht ⊢
    omega

/-- The key injection bound: shifting off the last digit. -/
theorem c_pow_succ_le (D s : ℕ) : c (10 ^ (D + 1)) s ≤ cle (10 ^ D) s := by
  unfold c cle
  apply Finset.card_le_card_of_injOn (fun n => n / 10)
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn ⊢
    obtain ⟨hlt, hSn⟩ := hn
    refine ⟨?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 10), ← pow_succ]; exact hlt
    · have := DS n; omega
  · intro n hn n' hn' heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn hn'
    obtain ⟨_, hSn⟩ := hn
    obtain ⟨_, hSn'⟩ := hn'
    have e1 := DS n
    have e2 := DS n'
    simp only at heq
    rw [heq] at e1
    omega

/-- Level-set bound: `c (10^D) s ≤ (D+s).choose s`. -/
theorem c_pow_le (D s : ℕ) : c (10 ^ D) s ≤ (D + s).choose s := by
  induction D generalizing s with
  | zero =>
    unfold c
    rw [pow_zero, Finset.range_one, Finset.filter_singleton]
    have hS0 : S 0 = 0 := by simp [S]
    by_cases hs : s = 0
    · subst hs; simp [hS0]
    · rw [if_neg (by rw [hS0]; omega)]
      simp
  | succ D ih =>
    calc c (10 ^ (D + 1)) s ≤ cle (10 ^ D) s := c_pow_succ_le D s
      _ = ∑ b ∈ Finset.range (s + 1), c (10 ^ D) b := cle_eq_sum _ _
      _ ≤ ∑ b ∈ Finset.range (s + 1), (D + b).choose b :=
            Finset.sum_le_sum (fun b _ => ih b)
      _ = (D + s + 1).choose s := hockey D s
      _ = (D + 1 + s).choose s := by ring_nf

theorem c_mono {N M s : ℕ} (h : N ≤ M) : c N s ≤ c M s := by
  unfold c
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨lt_of_lt_of_le hx.1 h, hx.2⟩

theorem c_le_choose (N s : ℕ) : c N s ≤ (Nat.log 10 N + 1 + s).choose s := by
  have hlt : N < 10 ^ (Nat.log 10 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  calc c N s ≤ c (10 ^ (Nat.log 10 N + 1)) s := c_mono (le_of_lt hlt)
    _ ≤ (Nat.log 10 N + 1 + s).choose s := c_pow_le _ _

theorem cle_bound (N B : ℕ) :
    cle N B ≤ (B + 1) * (Nat.log 10 N + 1 + B) ^ B := by
  rw [cle_eq_sum]
  calc ∑ b ∈ Finset.range (B + 1), c N b
      ≤ ∑ _b ∈ Finset.range (B + 1), (Nat.log 10 N + 1 + B) ^ B := by
        apply Finset.sum_le_sum
        intro b hb
        rw [Finset.mem_range] at hb
        calc c N b ≤ (Nat.log 10 N + 1 + b).choose b := c_le_choose N b
          _ ≤ (Nat.log 10 N + 1 + b) ^ b := Nat.choose_le_pow _ _
          _ ≤ (Nat.log 10 N + 1 + B) ^ b := Nat.pow_le_pow_left (by omega) b
          _ ≤ (Nat.log 10 N + 1 + B) ^ B := Nat.pow_le_pow_right (by omega) (by omega)
    _ = (B + 1) * (Nat.log 10 N + 1 + B) ^ B := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- `Nat.log 10` tends to infinity. -/
theorem log_tendsto : Tendsto (fun N => Nat.log 10 N) atTop atTop := by
  apply Filter.tendsto_atTop_atTop.2
  intro M
  refine ⟨10 ^ M, fun N hN => ?_⟩
  calc M = Nat.log 10 (10 ^ M) := (Nat.log_pow (by norm_num) M).symm
    _ ≤ Nat.log 10 N := Nat.log_mono_right hN

/-- The auxiliary polynomial-over-exponential bound tends to zero. -/
theorem phi_tendsto (B : ℕ) :
    Tendsto (fun L : ℕ => (B + 1 : ℝ) * ((L : ℝ) + 1 + B) ^ B / (10 : ℝ) ^ L)
      atTop (𝓝 0) := by
  have hbase : Tendsto (fun L : ℕ => ((B + 1 : ℝ) * 2 ^ B) * ((L : ℝ) ^ B / (10 : ℝ) ^ L))
      atTop (𝓝 0) := by
    have := (tendsto_pow_const_div_const_pow_of_one_lt B (by norm_num : (1 : ℝ) < 10))
    simpa using this.const_mul ((B + 1 : ℝ) * 2 ^ B)
  apply squeeze_zero' (g := fun L : ℕ => ((B + 1 : ℝ) * 2 ^ B) * ((L : ℝ) ^ B / (10 : ℝ) ^ L))
  · filter_upwards with L
    positivity
  · filter_upwards [Filter.eventually_ge_atTop (B + 1)] with L hL
    have hBL : ((B : ℝ) + 1) ≤ L := by exact_mod_cast hL
    have h2L : ((L : ℝ) + 1 + B) ≤ 2 * L := by linarith
    have hpow : ((L : ℝ) + 1 + B) ^ B ≤ 2 ^ B * (L : ℝ) ^ B := by
      calc ((L : ℝ) + 1 + B) ^ B ≤ (2 * (L : ℝ)) ^ B :=
            pow_le_pow_left₀ (by positivity) h2L B
        _ = 2 ^ B * (L : ℝ) ^ B := by rw [mul_pow]
    have key : (B + 1 : ℝ) * ((L : ℝ) + 1 + B) ^ B ≤ (B + 1) * 2 ^ B * (L : ℝ) ^ B := by
      nlinarith [hpow, (by positivity : (0:ℝ) ≤ (B + 1 : ℝ))]
    calc (B + 1 : ℝ) * ((L : ℝ) + 1 + B) ^ B / (10:ℝ) ^ L
        ≤ ((B + 1) * 2 ^ B * (L : ℝ) ^ B) / (10:ℝ) ^ L := by
          rw [div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < (10:ℝ) ^ L)]
          exact key
      _ = (B + 1 : ℝ) * 2 ^ B * ((L : ℝ) ^ B / (10:ℝ) ^ L) := by ring
  · exact hbase


theorem count_eq_card (N m : ℕ) :
    count_a_eq N m = ((Finset.range N).filter (fun n => a n = m)).card := by
  unfold count_a_eq
  rw [List.countP_eq_length_filter]
  simp [Finset.filter, Finset.range, Finset.card, Multiset.filter, Multiset.range]

/-- count of `n < N` with `n % 100 = 99`. -/
def cnt99 (N : ℕ) : ℕ := ((Finset.range N).filter (fun n => n % 100 = 99)).card

/-- count of `t < M` with `t % 10 = 9`. -/
def cnt9 (M : ℕ) : ℕ := ((Finset.range M).filter (fun t => t % 10 = 9)).card

theorem cnt9_le (M : ℕ) : cnt9 M ≤ M / 10 + 1 := by
  unfold cnt9
  apply le_trans (Finset.card_le_card_of_injOn (fun t => t / 10) ?_ ?_)
    (le_of_eq (Finset.card_range _))
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ht
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  · intro t ht t' ht' heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ht ht'
    simp only at heq
    have h1 := Nat.div_add_mod t 10
    have h2 := Nat.div_add_mod t' 10
    omega

theorem cnt99_le (N : ℕ) : cnt99 N ≤ N / 100 + 1 := by
  unfold cnt99
  apply le_trans (Finset.card_le_card_of_injOn (fun n => n / 100) ?_ ?_)
    (le_of_eq (Finset.card_range _))
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  · intro n hn n' hn' heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn hn'
    simp only at heq
    have h1 := Nat.div_add_mod n 100
    have h2 := Nat.div_add_mod n' 100
    omega

/-- The key decomposition bound for `m ≠ 8`. -/
theorem count_le (N m : ℕ) (hm : m ≠ 8) :
    count_a_eq N m ≤ cle N m + cle N 7 + cnt99 N := by
  rw [count_eq_card]
  set A := (Finset.range N).filter (fun n => a n = m) with hA
  set P1 := (Finset.range N).filter (fun n => n % 10 ≤ 8 ∧ a n = m) with hP1
  set P2 := (Finset.range N).filter (fun n => n % 10 = 9 ∧ (n / 10) % 10 ≠ 9 ∧ a n = m) with hP2
  set P3 := (Finset.range N).filter (fun n => n % 100 = 99) with hP3
  have hsub : A ⊆ P1 ∪ P2 ∪ P3 := by
    intro n hn
    simp only [hA, Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hlt, ham⟩ := hn
    simp only [Finset.mem_union, hP1, hP2, hP3, Finset.mem_filter, Finset.mem_range]
    by_cases h9 : n % 10 = 9
    · by_cases h99 : (n / 10) % 10 = 9
      · right
        refine ⟨hlt, ?_⟩
        omega
      · left; right; exact ⟨hlt, h9, h99, ham⟩
    · left; left; exact ⟨hlt, by omega, ham⟩
  have hP1card : P1.card ≤ cle N m := by
    unfold cle
    apply Finset.card_le_card_of_injOn (fun n => n / 10)
    · intro n hn
      simp only [hP1, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      obtain ⟨hlt, hle, ham⟩ := hn
      have hav := a_low hle
      refine ⟨by omega, ?_⟩
      rw [hav] at ham; omega
    · intro n hn n' hn' heq
      simp only [hP1, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn hn'
      obtain ⟨_, hle, ham⟩ := hn
      obtain ⟨_, hle', ham'⟩ := hn'
      have h1 := a_low hle
      have h2 := a_low hle'
      simp only at heq
      rw [heq] at h1
      have hdm1 := Nat.div_add_mod n 10
      have hdm2 := Nat.div_add_mod n' 10
      omega
  have hP2card : P2.card ≤ cle N 7 := by
    unfold cle
    apply Finset.card_le_card_of_injOn (fun n => n / 10)
    · intro n hn
      simp only [hP2, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      obtain ⟨hlt, h9, h99, ham⟩ := hn
      refine ⟨by omega, ?_⟩
      by_contra hcon
      have : a n = 8 := a_eq_eight h9 h99 (by omega)
      omega
    · intro n hn n' hn' heq
      simp only [hP2, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn hn'
      obtain ⟨_, h9, _, _⟩ := hn
      obtain ⟨_, h9', _, _⟩ := hn'
      simp only at heq
      have hdm1 := Nat.div_add_mod n 10
      have hdm2 := Nat.div_add_mod n' 10
      omega
  have hP3card : P3.card ≤ cnt99 N := by rw [hP3]; exact le_of_eq rfl
  calc A.card ≤ (P1 ∪ P2 ∪ P3).card := Finset.card_le_card hsub
    _ ≤ (P1 ∪ P2).card + P3.card := Finset.card_union_le _ _
    _ ≤ (P1.card + P2.card) + P3.card := by
        exact Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ cle N m + cle N 7 + cnt99 N := by
        have := hP1card; have := hP2card; have := hP3card; omega

/-- Covering lower bound for the "good" set producing value 8. -/
theorem count8_cover (K : ℕ) :
    10 * K ≤ ((Finset.range (10 * K)).filter (fun t => t % 10 ≠ 9 ∧ 8 ≤ S t)).card
              + cnt9 (10 * K) + cle (10 * K) 7 := by
  set Cset := (Finset.range (10 * K)).filter (fun t => t % 10 ≠ 9 ∧ 8 ≤ S t) with hC
  have hsub : (Finset.range (10 * K)) ⊆
      (Cset ∪ (Finset.range (10 * K)).filter (fun t => t % 10 = 9))
      ∪ (Finset.range (10 * K)).filter (fun t => S t ≤ 7) := by
    intro t ht
    simp only [Finset.mem_range] at ht
    simp only [hC, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    by_cases h9 : t % 10 = 9
    · left; right; exact ⟨ht, h9⟩
    · by_cases hS : 8 ≤ S t
      · left; left; exact ⟨ht, h9, hS⟩
      · right; exact ⟨ht, by omega⟩
  calc 10 * K = (Finset.range (10 * K)).card := (Finset.card_range _).symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Cset ∪ (Finset.range (10 * K)).filter (fun t => t % 10 = 9)).card
          + ((Finset.range (10 * K)).filter (fun t => S t ≤ 7)).card :=
        Finset.card_union_le _ _
    _ ≤ (Cset.card + ((Finset.range (10 * K)).filter (fun t => t % 10 = 9)).card)
          + ((Finset.range (10 * K)).filter (fun t => S t ≤ 7)).card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ = Cset.card + cnt9 (10 * K) + cle (10 * K) 7 := rfl

/-- Injection lower bound: the good set injects into `{a = 8}`. -/
theorem count8_inj (K : ℕ) :
    ((Finset.range (10 * K)).filter (fun t => t % 10 ≠ 9 ∧ 8 ≤ S t)).card
      ≤ count_a_eq (100 * K) 8 := by
  rw [count_eq_card]
  apply Finset.card_le_card_of_injOn (fun t => 10 * t + 9)
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ht
    obtain ⟨hlt, h9, hS⟩ := ht
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    have hdiv : (10 * t + 9) / 10 = t := by omega
    refine ⟨by omega, ?_⟩
    apply a_eq_eight
    · omega
    · rw [hdiv]; exact h9
    · rw [hdiv]; exact hS
  · intro t ht t' ht' heq
    simp only at heq
    omega

/-- Core density-zero fact for cumulative digit-sum level sets. -/
theorem cle_tendsto (B : ℕ) : Tendsto (fun N => (cle N B : ℝ) / N) atTop (𝓝 0) := by
  have hg : Tendsto (fun N : ℕ =>
      (B + 1 : ℝ) * ((Nat.log 10 N : ℝ) + 1 + B) ^ B / (10:ℝ) ^ (Nat.log 10 N))
      atTop (𝓝 0) := (phi_tendsto B).comp log_tendsto
  apply squeeze_zero' (g := fun N : ℕ =>
      (B + 1 : ℝ) * ((Nat.log 10 N : ℝ) + 1 + B) ^ B / (10:ℝ) ^ (Nat.log 10 N))
  · filter_upwards with N
    positivity
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    set L := Nat.log 10 N with hLdef
    have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hpowpos : (0:ℝ) < (10:ℝ) ^ L := by positivity
    have hpowle : (10:ℝ) ^ L ≤ (N:ℝ) := by
      have h := Nat.pow_log_le_self 10 (by omega : N ≠ 0)
      calc (10:ℝ) ^ L = ((10 ^ L : ℕ):ℝ) := by push_cast; ring
        _ ≤ (N:ℝ) := by exact_mod_cast h
    have hcle : (cle N B : ℝ) ≤ (B + 1 : ℝ) * ((L:ℝ) + 1 + B) ^ B := by
      have h := cle_bound N B
      calc (cle N B:ℝ) ≤ (((B + 1) * (L + 1 + B) ^ B : ℕ):ℝ) := by exact_mod_cast h
        _ = (B + 1 : ℝ) * ((L:ℝ) + 1 + B) ^ B := by push_cast; ring
    have hnum_nonneg : (0:ℝ) ≤ (B + 1 : ℝ) * ((L:ℝ) + 1 + B) ^ B := by positivity
    calc (cle N B:ℝ) / N
        ≤ ((B + 1 : ℝ) * ((L:ℝ) + 1 + B) ^ B) / N := by gcongr
      _ ≤ ((B + 1 : ℝ) * ((L:ℝ) + 1 + B) ^ B) / (10:ℝ) ^ L := by gcongr
  · exact hg

/-! ### Final assembly -/

theorem count_le_self (N m : ℕ) : count_a_eq N m ≤ N := by
  unfold count_a_eq
  exact le_trans List.countP_le_length List.length_range.le

theorem F_nonneg (N m : ℕ) : (0:ℝ) ≤ (count_a_eq N m : ℝ) / N := by positivity

theorem F_le_one (N m : ℕ) : (count_a_eq N m : ℝ) / N ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast count_le_self N m

/-- Upper bound for `m ≠ 8`: limsup ≤ 1/100. -/
theorem limsup_Fm_le {m : ℕ} (hm : m ≠ 8) :
    Filter.limsup (fun N : ℕ => (count_a_eq N m : ℝ) / N) atTop ≤ 1 / 100 := by
  have hle : ∀ N : ℕ, (count_a_eq N m : ℝ) / N ≤
      (cle N m : ℝ) / N + (cle N 7 : ℝ) / N + ((N : ℝ) / 100 + 1) / N := by
    intro N
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · have hNR : (0:ℝ) < N := by exact_mod_cast h
      rw [← add_div, ← add_div, div_le_div_iff_of_pos_right hNR]
      have hc := count_le N m hm
      have h99 := cnt99_le N
      have hcast99 : (cnt99 N : ℝ) ≤ (N : ℝ) / 100 + 1 := by
        calc (cnt99 N : ℝ) ≤ ((N / 100 + 1 : ℕ) : ℝ) := by exact_mod_cast h99
          _ = ((N / 100 : ℕ) : ℝ) + 1 := by push_cast; ring
          _ ≤ (N : ℝ) / 100 + 1 := by
              have := Nat.cast_div_le (m := N) (n := 100) (α := ℝ); linarith
      have hccast : (count_a_eq N m : ℝ) ≤ (cle N m : ℝ) + (cle N 7 : ℝ) + (cnt99 N : ℝ) := by
        calc (count_a_eq N m : ℝ) ≤ ((cle N m + cle N 7 + cnt99 N : ℕ) : ℝ) := by exact_mod_cast hc
          _ = (cle N m : ℝ) + (cle N 7 : ℝ) + (cnt99 N : ℝ) := by push_cast; ring
      linarith
  have h3 : Tendsto (fun N : ℕ => ((N : ℝ) / 100 + 1) / N) atTop (𝓝 (1 / 100)) := by
    have base : Tendsto (fun N : ℕ => (1:ℝ) / 100 + 1 / (N : ℝ)) atTop (𝓝 (1 / 100 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at base
    refine base.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with N hN
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp
  have htend : Tendsto (fun N : ℕ => (cle N m : ℝ) / N + (cle N 7 : ℝ) / N + ((N : ℝ) / 100 + 1) / N)
      atTop (𝓝 (1 / 100)) := by
    have hsum := ((cle_tendsto m).add (cle_tendsto 7)).add h3
    have heq : ((0:ℝ) + 0) + 1 / 100 = 1 / 100 := by norm_num
    rwa [heq] at hsum
  have hb : IsBoundedUnder (· ≥ ·) atTop (fun N : ℕ => (count_a_eq N m : ℝ) / N) :=
    ⟨0, Filter.eventually_map.2 (Filter.Eventually.of_forall (fun N => F_nonneg N m))⟩
  have hcob : IsCoboundedUnder (· ≤ ·) atTop (fun N : ℕ => (count_a_eq N m : ℝ) / N) :=
    hb.isCoboundedUnder_le
  calc Filter.limsup (fun N : ℕ => (count_a_eq N m : ℝ) / N) atTop
      ≤ Filter.limsup
          (fun N : ℕ => (cle N m : ℝ) / N + (cle N 7 : ℝ) / N + ((N : ℝ) / 100 + 1) / N) atTop :=
        limsup_le_limsup (Filter.Eventually.of_forall hle) hcob htend.isBoundedUnder_le
    _ = 1 / 100 := htend.limsup_eq

/-- Lower bound: limsup for value 8 is ≥ 1/100. -/
theorem limsup_F8_ge :
    (1 : ℝ) / 100 ≤ Filter.limsup (fun N : ℕ => (count_a_eq N 8 : ℝ) / N) atTop := by
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (fun N : ℕ => (count_a_eq N 8 : ℝ) / N) :=
    ⟨1, Filter.eventually_map.2 (Filter.Eventually.of_forall (fun N => F_le_one N 8))⟩
  apply le_limsup_of_frequently_le _ hbdd
  -- eventually cle (10K) 7 ≤ K
  have hevN : ∀ᶠ N in atTop, (cle N 7 : ℝ) ≤ (N : ℝ) / 10 := by
    have h1 : ∀ᶠ N in atTop, (cle N 7 : ℝ) / N < 1 / 10 :=
      (cle_tendsto 7).eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1 / 10))
    filter_upwards [h1, Filter.eventually_gt_atTop 0] with N hN hNpos
    have hNR : (0:ℝ) < N := by exact_mod_cast hNpos
    rw [div_lt_iff₀ hNR] at hN
    linarith
  have hcomp : Tendsto (fun K : ℕ => 10 * K) atTop atTop := by
    apply Filter.tendsto_atTop_atTop.2
    intro M; exact ⟨M, fun K hK => by omega⟩
  have hevK : ∀ᶠ K in atTop, cle (10 * K) 7 ≤ K := by
    filter_upwards [hcomp.eventually hevN] with K hK
    have hR : (cle (10 * K) 7 : ℝ) ≤ (K : ℝ) := by
      have e : ((10 * K : ℕ) : ℝ) / 10 = (K : ℝ) := by push_cast; ring
      rw [e] at hK; exact hK
    exact_mod_cast hR
  obtain ⟨K1, hK1⟩ := Filter.eventually_atTop.1 hevK
  rw [Filter.frequently_atTop]
  intro a
  refine ⟨100 * (max a K1 + 1), by omega, ?_⟩
  set K := max a K1 + 1 with hKdef
  have hKpos : 0 < K := by omega
  have hcle7 : cle (10 * K) 7 ≤ K := hK1 K (by omega)
  have hcnt9 : cnt9 (10 * K) ≤ K + 1 := by have := cnt9_le (10 * K); omega
  have hcover := count8_cover K
  have hinj := count8_inj K
  have hcountK : K ≤ count_a_eq (100 * K) 8 := by omega
  have hcast : (K : ℝ) ≤ (count_a_eq (100 * K) 8 : ℝ) := by exact_mod_cast hcountK
  have h100K : (0:ℝ) < ((100 * K : ℕ) : ℝ) := by
    have : 0 < 100 * K := by omega
    exact_mod_cast this
  calc (1 : ℝ) / 100 = (K : ℝ) / ((100 * K : ℕ) : ℝ) := by
        rw [eq_div_iff (ne_of_gt h100K)]; push_cast; ring
    _ ≤ (count_a_eq (100 * K) 8 : ℝ) / ((100 * K : ℕ) : ℝ) :=
        (div_le_div_iff_of_pos_right h100K).2 hcast


end OEIS326746

/--
oeis_326746_conjecture_0:
The frequency of occurrence for the values of a(n) for large values of n has an interesting distribution - it is a bell-shaped curve but with large increases for a(n) = 8, and a smaller increase for a(n) = 17. The value a(n) = 8 is likely the most common value as every time n increases by 100 the value of a(n) goes through ten smaller cycles, and 8 appears to be the only value that is present in all ten cycles. The reason a(n) = 17 also appears more often is not clear, although the distribution for n up to 10^10 also shows a slight increase in the number of occurrences for a(n) = 26, suggesting that a(n) values of the form a(n) = 8 + 9 * k, where k >= 0, occur more frequently than one would predicted from the surrounding bell-curve distribution.

We formalize the core claim that 8 is the most common value by asserting that its asymptotic frequency is at least that of any other value $m$.
The asymptotic frequency is captured by the $\limsup$ of the proportion of occurrences up to $N$.
-/
theorem oeis_326746_conjecture_0 :
  ∀ m : ℕ,
    Filter.limsup (fun N : ℕ => (count_a_eq N 8 : ℝ) / N) atTop
    ≥
    Filter.limsup (fun N : ℕ => (count_a_eq N m : ℝ) / N) atTop
    := by
  intro m
  by_cases hm : m = 8
  · subst hm; exact le_refl _
  · exact le_trans (OEIS326746.limsup_Fm_le hm) OEIS326746.limsup_F8_ge
