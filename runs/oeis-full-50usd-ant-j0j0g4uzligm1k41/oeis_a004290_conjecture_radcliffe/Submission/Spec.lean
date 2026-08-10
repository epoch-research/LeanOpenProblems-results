import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A004290: Least positive multiple of $n$ that when written in base 10 uses only 0's and 1's.
-/
noncomputable def A004290 (n : ℕ) : ℕ :=
  -- The set of positive multiples of $n$ that are composed only of 0's and 1's in base 10.
  let S := { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }

  -- The sequence value is the smallest element of this set, which is the infimum.
  -- For n=0, the set is empty, and sInf on the empty set of ℕ is 0. The OEIS definition
  -- explicitly states "Least positive multiple of n", which implies n > 0.
  -- However, if S is empty, sInf S = 0. A004290(0) is an edge case, but the conjecture
  -- only concerns n < 10^k - 1, where we assume k ≥ 1, so n ≥ 1.
  sInf S

/-! ### Auxiliary developments

The following lemmas develop the machinery needed for the conjecture.

* `digits_pow_ten` : the base-10 digits of `10 ^ k` are `k` zeros followed by a one.
* `repunit L = (10 ^ L - 1) / 9` is the base-10 repunit with `L` ones.
* `digits_repunit` : the base-10 digits of `repunit L` are `L` ones.
* `key_dvd` : `10 ^ k - 1` divides `repunit (9 * k)`.

These suffice to prove the first conjunct completely, and to prove the "≤" half of the
second conjunct (namely that `repunit (9*k)` is *a* valid `0/1`-multiple of `10^k - 1`).
-/

/-- The base-10 digits of `10 ^ k` are `k` zeros followed by a single one. -/
theorem digits_pow_ten (k : ℕ) : Nat.digits 10 (10 ^ k) = List.replicate k 0 ++ [1] := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h : (10 : ℕ) ^ (n + 1) = 10 * 10 ^ n := by ring
    rw [h, Nat.digits_def' (b := 10) (by norm_num) (by positivity)]
    have h1 : (10 * 10 ^ n) % 10 = 0 := by omega
    have h2 : (10 * 10 ^ n) / 10 = 10 ^ n := by rw [Nat.mul_div_cancel_left]; norm_num
    rw [h1, h2, ih]; simp [List.replicate_succ]

/-- The base-10 repunit with `L` ones. -/
def repunit (L : ℕ) : ℕ := (10 ^ L - 1) / 9

theorem nine_dvd_pow_ten_sub_one (L : ℕ) : 9 ∣ (10 ^ L - 1) := by
  have h : (10 : ℕ) ^ L % 9 = 1 := by
    have hmod : (10 : ℕ) ≡ 1 [MOD 9] := by decide
    have := hmod.pow L; unfold Nat.ModEq at this; simpa using this
  omega

theorem repunit_succ (L : ℕ) : repunit (L + 1) = 10 * repunit L + 1 := by
  unfold repunit
  have hdvd : 9 ∣ (10 ^ L - 1) := nine_dvd_pow_ten_sub_one L
  have h10 : (1 : ℕ) ≤ 10 ^ L := Nat.one_le_pow _ _ (by norm_num)
  have hexp : (10 : ℕ) ^ (L + 1) = 10 * 10 ^ L := by ring
  rw [hexp]; omega

/-- The base-10 digits of `repunit L` are `L` ones. -/
theorem digits_repunit (L : ℕ) : Nat.digits 10 (repunit L) = List.replicate L 1 := by
  induction L with
  | zero => simp [repunit]
  | succ n ih =>
    rw [repunit_succ, Nat.digits_def' (b := 10) (by norm_num) (by positivity)]
    have h1 : (10 * repunit n + 1) % 10 = 1 := by omega
    have h2 : (10 * repunit n + 1) / 10 = repunit n := by omega
    rw [h1, h2, ih, List.replicate_succ]

theorem sum_pow_ten_mul (L : ℕ) : (∑ i ∈ Finset.range L, (10 : ℕ) ^ i) * 9 = 10 ^ L - 1 := by
  induction L with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    have h1 : (1 : ℕ) ≤ 10 ^ n := Nat.one_le_pow _ _ (by norm_num)
    have h2 : (10 : ℕ) ^ (n + 1) = 10 * 10 ^ n := by ring
    omega

theorem repunit_eq_sum (L : ℕ) : repunit L = ∑ i ∈ Finset.range L, 10 ^ i := by
  have h := sum_pow_ten_mul L; unfold repunit; omega

/-- The cofactor identity `(∑_{t<9} (10^k)^t) * (10^k - 1) = 10^(9k) - 1`. -/
theorem C_mul (k : ℕ) :
    (∑ t ∈ Finset.range 9, ((10 : ℕ) ^ k) ^ t) * (10 ^ k - 1) = 10 ^ (9 * k) - 1 := by
  have h1 : (1 : ℕ) ≤ 10 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have h9 : (1 : ℕ) ≤ 10 ^ (9 * k) := Nat.one_le_pow _ _ (by norm_num)
  have hz := geom_sum_mul ((10 : ℤ) ^ k) 9
  have hpz : ((10 : ℤ) ^ k) ^ 9 = (10 : ℤ) ^ (9 * k) := by rw [← pow_mul]; ring_nf
  rw [hpz] at hz
  zify [h1, h9]; linarith [hz]

/-- `9` divides the cofactor `∑_{t<9} (10^k)^t` (nine terms, each `≡ 1 (mod 9)`). -/
theorem nine_dvd_C (k : ℕ) : 9 ∣ (∑ t ∈ Finset.range 9, ((10 : ℕ) ^ k) ^ t) := by
  have hmod : ∀ t ∈ Finset.range 9, ((10 : ℕ) ^ k) ^ t ≡ 1 [MOD 9] := by
    intro t _
    have h1 : (10 : ℕ) ^ k ≡ 1 [MOD 9] := by
      have : (10 : ℕ) ≡ 1 [MOD 9] := by decide
      simpa using this.pow k
    simpa using h1.pow t
  have hsum := Nat.ModEq.sum hmod
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hsum
  exact (Nat.modEq_zero_iff_dvd).mp hsum

/-- **Key divisibility.** `10^k - 1` divides the repunit `repunit (9*k) = (10^(9k)-1)/9`.
This is the crux of the second conjunct: it shows the repunit of `9k` ones is a positive
`0/1`-multiple of `10^k - 1`. -/
theorem key_dvd (k : ℕ) : (10 ^ k - 1) ∣ repunit (9 * k) := by
  set C := ∑ t ∈ Finset.range 9, ((10 : ℕ) ^ k) ^ t with hC
  have hCmul : C * (10 ^ k - 1) = 10 ^ (9 * k) - 1 := C_mul k
  obtain ⟨D, hD⟩ := nine_dvd_C k
  have hrep : repunit (9 * k) * 9 = 10 ^ (9 * k) - 1 := by
    rw [repunit_eq_sum]; exact sum_pow_ten_mul (9 * k)
  have hkey : (9 * D) * (10 ^ k - 1) = repunit (9 * k) * 9 := by rw [← hD, hCmul, hrep]
  have hDD : repunit (9 * k) = D * (10 ^ k - 1) := by nlinarith [hkey]
  exact ⟨D, by rw [hDD]; ring⟩

theorem repunit_pos {L : ℕ} (hL : 0 < L) : 0 < repunit L := by
  rw [repunit_eq_sum]
  apply Finset.sum_pos (fun i _ => by positivity)
  exact ⟨0, Finset.mem_range.mpr hL⟩

/-- Membership: `repunit (9*k)` is a positive `0/1`-multiple of `10^k - 1`. -/
theorem repunit_mem (k : ℕ) (hk : k > 0) :
    repunit (9 * k) ∈
      { m : ℕ | 0 < m ∧ (10 ^ k - 1) ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
  refine ⟨repunit_pos (by positivity), key_dvd k, ?_⟩
  rw [digits_repunit]
  intro d hd
  rw [List.mem_replicate] at hd
  exact Or.inr hd.2

/- ### Machinery for the minimality half of the second conjunct

The following lemmas establish that every positive `0/1`-multiple of `10^k - 1` has base-10
digit sum at least `9k`, and that any `0/1` number `M` satisfies `repunit (digitSum M) ≤ M`.
Together they force `repunit (9k) ≤ M` for every candidate `M`, giving the "≥" half. -/

/-- `repunit` is monotone. -/
theorem repunit_mono {a b : ℕ} (h : a ≤ b) : repunit a ≤ repunit b := by
  rw [repunit_eq_sum, repunit_eq_sum]
  apply Finset.sum_le_sum_of_subset
  intro x hx; simp only [Finset.mem_range] at *; omega

/-- For a `0/1` number `M`, the repunit with as many ones as `M`'s digit sum is `≤ M`;
i.e. the smallest `0/1` number with a given number of ones is the corresponding repunit. -/
theorem repunit_le_of_zero_one (M : ℕ)
    (h01 : ∀ d ∈ Nat.digits 10 M, d = 0 ∨ d = 1) :
    repunit ((Nat.digits 10 M).sum) ≤ M := by
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp [repunit]
    · have hdig := Nat.digits_def' (b := 10) (by norm_num) hM
      have hd : M % 10 = 0 ∨ M % 10 = 1 := by
        apply h01; rw [hdig]; exact List.mem_cons_self
      have htail01 : ∀ d ∈ Nat.digits 10 (M / 10), d = 0 ∨ d = 1 := by
        intro d hdmem; apply h01; rw [hdig]; exact List.mem_cons_of_mem _ hdmem
      have hlt : M / 10 < M := Nat.div_lt_self hM (by norm_num)
      have hih := ih (M / 10) hlt htail01
      have hsum : (Nat.digits 10 M).sum = M % 10 + (Nat.digits 10 (M / 10)).sum := by
        rw [hdig]; simp [List.sum_cons]
      have hMeq : M = 10 * (M / 10) + M % 10 := (Nat.div_add_mod M 10).symm
      rcases hd with hd0 | hd1
      · rw [hsum, hd0]; simp; omega
      · rw [hsum, hd1]
        have : repunit (1 + (Nat.digits 10 (M / 10)).sum)
            = 10 * repunit ((Nat.digits 10 (M / 10)).sum) + 1 := by
          rw [Nat.add_comm]; exact repunit_succ _
        rw [this]; omega

/-- Sub-additivity of the base-10 digit sum. -/
theorem digitsum_subadditive_aux :
    ∀ n a b, a + b = n →
      (Nat.digits 10 (a + b)).sum ≤ (Nat.digits 10 a).sum + (Nat.digits 10 b).sum := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hab
    subst hab
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    have habpos : 0 < a + b := by omega
    have ea := Nat.div_add_mod a 10
    have eb := Nat.div_add_mod b 10
    have eab := Nat.div_add_mod (a + b) 10
    have ma : a % 10 < 10 := Nat.mod_lt _ (by norm_num)
    have mb : b % 10 < 10 := Nat.mod_lt _ (by norm_num)
    rw [Nat.digits_def' (b := 10) (by norm_num) habpos,
        Nat.digits_def' (b := 10) (by norm_num) ha,
        Nat.digits_def' (b := 10) (by norm_num) hb]
    simp only [List.sum_cons]
    set carry := (a % 10 + b % 10) / 10 with hc
    have hcarry : carry ≤ 1 := by omega
    have hdiv : (a + b) / 10 = a / 10 + b / 10 + carry := by omega
    rw [hdiv]
    have hsum1 : (a / 10 + b / 10) + carry < a + b := by omega
    have step1 := ih ((a/10 + b/10) + carry) hsum1 (a/10 + b/10) carry rfl
    have hsum2 : a / 10 + b / 10 < a + b := by omega
    have step2 := ih (a/10 + b/10) hsum2 (a/10) (b/10) rfl
    have hcds : (Nat.digits 10 carry).sum = carry := by interval_cases carry <;> simp
    calc (a + b) % 10 + (Nat.digits 10 (a / 10 + b / 10 + carry)).sum
        ≤ (a + b) % 10 + ((Nat.digits 10 (a/10 + b/10)).sum + (Nat.digits 10 carry).sum) :=
              Nat.add_le_add_left step1 _
      _ ≤ (a + b) % 10 + (((Nat.digits 10 (a/10)).sum + (Nat.digits 10 (b/10)).sum) + carry) := by
              rw [hcds]; exact Nat.add_le_add_left (Nat.add_le_add_right step2 _) _
      _ ≤ (a % 10 + (Nat.digits 10 (a / 10)).sum) + (b % 10 + (Nat.digits 10 (b / 10)).sum) := by
              omega

theorem digitsum_subadditive (a b : ℕ) :
    (Nat.digits 10 (a + b)).sum ≤ (Nat.digits 10 a).sum + (Nat.digits 10 b).sum :=
  digitsum_subadditive_aux (a + b) a b rfl

/-- Splitting the digit sum at a power-of-ten block boundary. -/
theorem digitsum_split (k B Q : ℕ) (hB : B < 10^k) (hQ : 0 < Q) :
    (Nat.digits 10 (B + 10^k * Q)).sum = (Nat.digits 10 B).sum + (Nat.digits 10 Q).sum := by
  have hlen : (Nat.digits 10 B).length ≤ k := (Nat.digits_length_le_iff (by norm_num) B).mpr hB
  have key := Nat.digits_append_zeroes_append_digits (b := 10)
      (k := k - (Nat.digits 10 B).length) (m := Q) (n := B) (by norm_num) hQ
  have hlenadd : (Nat.digits 10 B).length + (k - (Nat.digits 10 B).length) = k := by omega
  rw [hlenadd] at key
  rw [← key]; simp [List.sum_append]

/-- The digit sum of `10^k - 1` (the number `99…9` with `k` nines) is `9k`. -/
theorem digitsum_pow_sub_one (k : ℕ) : (Nat.digits 10 (10^k - 1)).sum = 9 * k := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h1 : (1:ℕ) ≤ 10^n := Nat.one_le_pow _ _ (by norm_num)
    have hpos : 0 < 10^(n+1) - 1 := by
      have : (1:ℕ) ≤ 10^(n+1) := Nat.one_le_pow _ _ (by norm_num)
      have h2 : (10:ℕ)^(n+1) = 10 * 10^n := by ring
      omega
    rw [Nat.digits_def' (b := 10) (by norm_num) hpos]
    have hmod : (10^(n+1) - 1) % 10 = 9 := by
      have h2 : (10:ℕ)^(n+1) = 10 * 10^n := by ring
      omega
    have hdiv : (10^(n+1) - 1) / 10 = 10^n - 1 := by
      have h2 : (10:ℕ)^(n+1) = 10 * 10^n := by ring
      omega
    rw [hmod, hdiv, List.sum_cons, ih]; ring

/-- **Digit-sum lower bound.** Every positive multiple `M` of `10^k - 1` has base-10 digit
sum at least `9k`. The proof folds `M` modulo the block size `10^k`: writing
`M = B + 10^k · Q` with `B < 10^k`, the number `B + Q` is again a positive multiple of
`10^k - 1` (since `10^k ≡ 1`), strictly smaller than `M`, and digit sums are sub-additive. -/
theorem digitsum_multiple_ge (k : ℕ) (hk : 0 < k) :
    ∀ M, 0 < M → (10^k - 1) ∣ M → 9 * k ≤ (Nat.digits 10 M).sum := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro hM hdvd
    have hkpow : (1:ℕ) ≤ 10^k := Nat.one_le_pow _ _ (by norm_num)
    have h2 : (2:ℕ) ≤ 10^k := by
      calc (2:ℕ) ≤ 10^1 := by norm_num
        _ ≤ 10^k := Nat.pow_le_pow_right (by norm_num) hk
    have h1lt : (1:ℕ) < 10^k := by omega
    set B := M % 10^k with hBdef
    set Q := M / 10^k with hQdef
    have hBlt : B < 10^k := Nat.mod_lt _ (by positivity)
    have hMeq : M = B + 10^k * Q := (Nat.mod_add_div M (10^k)).symm
    rcases Nat.eq_zero_or_pos Q with hQ0 | hQpos
    · have hMlt : M < 10^k := by rw [hMeq, hQ0]; simpa using hBlt
      obtain ⟨c, hc⟩ := hdvd
      have hc1 : c = 1 := by
        rcases Nat.lt_or_ge c 2 with h | h
        · interval_cases c
          · simp at hc; omega
          · rfl
        · exfalso
          obtain ⟨q, hq⟩ : ∃ q, 10^k = q + 1 := ⟨10^k - 1, by omega⟩
          have hqpos : 1 ≤ q := by omega
          have hc' : M = q * c := by rw [hc, hq, Nat.add_sub_cancel]
          have hmul : q * 2 ≤ q * c := Nat.mul_le_mul_left _ h
          omega
      have hMval : M = 10^k - 1 := by rw [hc, hc1, mul_one]
      have : (Nat.digits 10 M).sum = 9 * k := by rw [hMval]; exact digitsum_pow_sub_one k
      omega
    · have hBQpos : 0 < B + Q := by omega
      have hTeq : (10:ℕ)^k * Q = (10^k - 1) * Q + Q := by
        have hkk : (10:ℕ)^k = (10^k - 1) + 1 := by omega
        calc (10:ℕ)^k * Q = ((10^k - 1) + 1) * Q := by rw [← hkk]
          _ = (10^k - 1) * Q + Q := by ring
      have hdecomp : M = (B + Q) + (10^k - 1) * Q := by rw [hMeq, hTeq]; ring
      have h1 : (10^k - 1) ∣ (10^k - 1) * Q := dvd_mul_right _ _
      have heq : B + Q = M - (10^k - 1) * Q := by omega
      have hdvdBQ : (10^k - 1) ∣ (B + Q) := by rw [heq]; exact Nat.dvd_sub hdvd h1
      have hQlt : Q < 10^k * Q := lt_mul_of_one_lt_left hQpos h1lt
      have hBQlt : B + Q < M := by rw [hMeq]; omega
      have hih := ih (B + Q) hBQlt hBQpos hdvdBQ
      have hsplit : (Nat.digits 10 M).sum = (Nat.digits 10 B).sum + (Nat.digits 10 Q).sum := by
        rw [hMeq]; exact digitsum_split k B Q hBlt hQpos
      have hsub := digitsum_subadditive B Q
      omega

/--
Conjecture from A004290 by David Radcliffe:
a(10^k) = 10^k and a(10^k - 1) = (10^(9k) - 1) / 9 for all k.
Is a(n) < a(10^k - 1) for all n < 10^k - 1?
We formalize the second, unproven part. The first two parts are stated as assumptions
to establish the right-hand side of the inequality.
-/
theorem oeis_a004290_conjecture_radcliffe (k : ℕ) (hk : k > 0) :
  (A004290 (10 ^ k) = 10 ^ k) ∧
  (A004290 (10 ^ k - 1) = (10 ^ (9 * k) - 1) / 9) ∧
  (∀ n : ℕ, n < 10 ^ k - 1 → A004290 n < A004290 (10 ^ k - 1)) :=
by
  refine ⟨?_, ?_, ?_⟩
  · -- First conjunct: A004290 (10^k) = 10^k.  (Fully proved.)
    unfold A004290
    set S := { m : ℕ | 0 < m ∧ 10 ^ k ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } with hS
    have hdig : ∀ d ∈ Nat.digits 10 (10 ^ k), d = 0 ∨ d = 1 := by
      rw [digits_pow_ten]; intro d hd
      simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hd
      rcases hd with ⟨_, h⟩ | h <;> simp [h]
    have hmem : (10 ^ k) ∈ S := ⟨by positivity, dvd_refl _, hdig⟩
    have hne : S.Nonempty := ⟨_, hmem⟩
    apply le_antisymm
    · exact Nat.sInf_le hmem
    · obtain ⟨hpos, hdvd, _⟩ := Nat.sInf_mem hne
      exact Nat.le_of_dvd hpos hdvd
  · -- Second conjunct: A004290 (10^k - 1) = (10^(9k) - 1)/9 = repunit (9k).
    -- The "≤" direction is fully proved: `repunit (9*k)` is a valid 0/1-multiple.
    -- The "≥" direction (minimality) is the digit-class folding argument.
    unfold A004290
    show sInf { m : ℕ | 0 < m ∧ (10 ^ k - 1) ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }
        = (10 ^ (9 * k) - 1) / 9
    have hRHS : (10 ^ (9 * k) - 1) / 9 = repunit (9 * k) := rfl
    rw [hRHS]
    apply le_antisymm
    · exact Nat.sInf_le (repunit_mem k hk)
    · -- Minimality: any 0/1-multiple of 10^k-1 has ≥ 9k ones, hence is ≥ repunit (9k).
      -- (digit-class folding mod 10^k - 1 : the coefficient sum is ≥ 9k.)
      set S := { m : ℕ | 0 < m ∧ (10 ^ k - 1) ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }
        with hSdef
      have hne : S.Nonempty := ⟨_, repunit_mem k hk⟩
      obtain ⟨hMpos, hMdvd, hM01⟩ := Nat.sInf_mem hne
      have hge : 9 * k ≤ (Nat.digits 10 (sInf S)).sum :=
        digitsum_multiple_ge k hk (sInf S) hMpos hMdvd
      have h1 : repunit (9 * k) ≤ repunit ((Nat.digits 10 (sInf S)).sum) := repunit_mono hge
      have h2 : repunit ((Nat.digits 10 (sInf S)).sum) ≤ sInf S :=
        repunit_le_of_zero_one (sInf S) hM01
      omega
  · -- Third conjunct: the record property (the genuinely open part of the conjecture).
    -- Equivalent to: every n < 10^k - 1 has a 0/1-multiple with < 9k digits.
    -- This is an O(log n) bound with tight constant 9 whose core obstruction is the gap
    -- between abundant signed {-1,0,1} digit relations (pigeonhole) and the required
    -- unsigned {0,1} multiples; posed as an open question in OEIS A004290.
    sorry
