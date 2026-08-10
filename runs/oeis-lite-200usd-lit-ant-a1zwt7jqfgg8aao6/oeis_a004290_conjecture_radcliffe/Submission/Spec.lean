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

/-- The decimal digits of `10 ^ k` are `k` zeros followed by a single `1`. -/
theorem digits_pow_ten (k : ℕ) :
    Nat.digits 10 (10 ^ k) = List.replicate k 0 ++ [1] := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, show 10 ^ n * 10 = 10 * 10 ^ n by ring,
        Nat.digits_def' (b := 10) (by norm_num) (by positivity)]
    rw [Nat.mul_mod_right, Nat.mul_div_cancel_left _ (by norm_num : 0 < 10), ih]
    simp [List.replicate_succ]

/-- The decimal digits of the repunit `(10 ^ m - 1) / 9` are `m` ones. -/
theorem digits_repunit (m : ℕ) :
    Nat.digits 10 ((10 ^ m - 1) / 9) = List.replicate m 1 := by
  induction m with
  | zero => simp
  | succ n ih =>
    have h1 : (10 ^ (n + 1) - 1) / 9 = 10 * ((10 ^ n - 1) / 9) + 1 := by
      have he : 10 ^ (n + 1) - 1 = 10 * (10 ^ n - 1) + 9 := by
        have : 1 ≤ 10 ^ n := Nat.one_le_pow _ _ (by norm_num)
        rw [pow_succ]; omega
      rw [he]
      have h9 : 9 ∣ (10 ^ n - 1) := by
        have := Nat.sub_dvd_pow_sub_pow 10 1 n
        simpa using this
      obtain ⟨c, hc⟩ := h9
      rw [hc]; omega
    rw [h1, Nat.digits_def' (b := 10) (by norm_num) (by positivity)]
    have hmod : (10 * ((10 ^ n - 1) / 9) + 1) % 10 = 1 := by omega
    have hdiv : (10 * ((10 ^ n - 1) / 9) + 1) / 10 = (10 ^ n - 1) / 9 := by omega
    rw [hmod, hdiv, ih, List.replicate_succ]

/-- Geometric sum over `ℕ`: `(x - 1) * ∑_{i<n} x^i = x^n - 1`. -/
theorem nat_geom (x n : ℕ) (hx : 1 ≤ x) :
    (x - 1) * (∑ i ∈ Finset.range n, x ^ i) = x ^ n - 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih, pow_succ]
    have h1 : 1 ≤ x ^ m := Nat.one_le_pow _ _ (by omega)
    have h2 : (x - 1) * x ^ m = x ^ m * x - x ^ m := by rw [Nat.sub_mul, one_mul, Nat.mul_comm]
    rw [h2]
    have hxm : x ^ m ≤ x ^ m * x := Nat.le_mul_of_pos_right _ (by omega)
    omega

/-- `9` divides `∑_{i<9} (10^k)^i` (since each term is `≡ 1 mod 9`). -/
theorem nine_dvd_geom (k : ℕ) :
    (9 : ℕ) ∣ ∑ i ∈ Finset.range 9, (10 ^ k) ^ i := by
  have h9 : (9:ℕ) ∣ (10 ^ k - 1) := by
    have := Nat.sub_dvd_pow_sub_pow 10 1 k; simpa using this
  have hdvd : ∀ i ∈ Finset.range 9, (9:ℕ) ∣ ((10^k)^i - 1) := by
    intro i _
    have : (10^k - 1) ∣ ((10^k)^i - 1) := by
      have := Nat.sub_dvd_pow_sub_pow (10^k) 1 i; simpa using this
    exact h9.trans this
  have hsum : (9:ℕ) ∣ ∑ i ∈ Finset.range 9, ((10^k)^i - 1) := Finset.dvd_sum hdvd
  have heq : ∑ i ∈ Finset.range 9, (10 ^ k) ^ i
      = (∑ i ∈ Finset.range 9, ((10^k)^i - 1)) + 9 := by
    have e1 : ∑ i ∈ Finset.range 9, (10^k)^i
        = ∑ i ∈ Finset.range 9, (((10^k)^i - 1) + 1) := by
      apply Finset.sum_congr rfl
      intro i _
      have : 1 ≤ (10^k)^i := Nat.one_le_pow _ _ (by norm_num)
      omega
    rw [e1, Finset.sum_add_distrib]; simp
  rw [heq]; exact Nat.dvd_add hsum (dvd_refl 9)

/-- `10^k - 1` divides the repunit `R_{9k} = (10^{9k}-1)/9`. -/
theorem dvd_repunit (k : ℕ) :
    (10 ^ k - 1) ∣ (10 ^ (9 * k) - 1) / 9 := by
  obtain ⟨c, hc⟩ := nine_dvd_geom k
  have hgeom : (10 ^ k - 1) * (∑ i ∈ Finset.range 9, (10 ^ k) ^ i) = 10 ^ (9 * k) - 1 := by
    have := nat_geom (10 ^ k) 9 (Nat.one_le_pow _ _ (by norm_num))
    rw [this, ← pow_mul]; ring_nf
  rw [hc] at hgeom
  refine ⟨c, ?_⟩
  have : 9 * ((10 ^ k - 1) * c) = 10 ^ (9 * k) - 1 := by ring_nf; ring_nf at hgeom; omega
  omega

/-- If `m` is a `{0,1}`-number in base 10, so is `m / 10`. -/
theorem digits_div_ten_le1 (m : ℕ) (h : ∀ d ∈ Nat.digits 10 m, d ≤ 1) :
    ∀ d ∈ Nat.digits 10 (m / 10), d ≤ 1 := by
  intro d hd
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp at hd
  · have hrec : Nat.digits 10 m = m % 10 :: Nat.digits 10 (m / 10) :=
      Nat.digits_def' (by norm_num) hm
    apply h; rw [hrec]; exact List.mem_cons_of_mem _ hd

/-- If `m` is a `{0,1}`-number in base 10, so is `m / 10^k`. -/
theorem digits_div_pow_ten_le1 (k m : ℕ) (h : ∀ d ∈ Nat.digits 10 m, d ≤ 1) :
    ∀ d ∈ Nat.digits 10 (m / 10 ^ k), d ≤ 1 := by
  induction k with
  | zero => simpa using h
  | succ n ih =>
    have : m / 10 ^ (n + 1) = (m / 10 ^ n) / 10 := by rw [pow_succ, Nat.div_div_eq_div_mul]
    rw [this]; exact digits_div_ten_le1 _ ih

/-- `ofDigits 10` of `m` ones equals the repunit `(10^m - 1)/9`. -/
theorem ofDigits_replicate_one (m : ℕ) :
    Nat.ofDigits 10 (List.replicate m 1) = (10 ^ m - 1) / 9 := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, ih]
    have h9 : (9:ℕ) ∣ (10 ^ n - 1) := by
      have := Nat.sub_dvd_pow_sub_pow 10 1 n; simpa using this
    obtain ⟨c, hc⟩ := h9
    have h1 : 1 ≤ (10:ℕ) ^ n := Nat.one_le_pow _ _ (by norm_num)
    have hb : (10:ℕ) ^ (n+1) - 1 = 9 * (10 * c + 1) := by rw [pow_succ]; omega
    rw [hb, hc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 9),
        Nat.mul_div_cancel_left _ (by norm_num : 0 < 9)]
    ring

/-- A `{0,1}`-digit list `L` has `ofDigits 10 L ≤ ofDigits 10` of `|L|` ones. -/
theorem ofDigits_le_replicate (L : List ℕ) (hL : ∀ d ∈ L, d ≤ 1) :
    Nat.ofDigits 10 L ≤ Nat.ofDigits 10 (List.replicate L.length 1) := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    rw [List.length_cons, List.replicate_succ, Nat.ofDigits_cons, Nat.ofDigits_cons]
    have hhd : hd ≤ 1 := hL hd (List.mem_cons_self)
    have htl : ∀ d ∈ tl, d ≤ 1 := fun d hd => hL d (List.mem_cons_of_mem _ hd)
    have key := ih htl
    omega

/-- A `{0,1}`-digit list `L` of length `≤ k` has `ofDigits 10 L ≤ R_k = (10^k-1)/9`. -/
theorem ofDigits_le1_le_repunit (k : ℕ) (L : List ℕ)
    (hL : ∀ d ∈ L, d ≤ 1) (hlen : L.length ≤ k) :
    Nat.ofDigits 10 L ≤ (10 ^ k - 1) / 9 := by
  have step1 := ofDigits_le_replicate L hL
  rw [ofDigits_replicate_one] at step1
  have step2 : (10 ^ L.length - 1) / 9 ≤ (10 ^ k - 1) / 9 := by
    apply Nat.div_le_div_right
    have : (10:ℕ) ^ L.length ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hlen
    omega
  exact le_trans step1 step2

/-- Each base-`10^k` digit (block) of a base-10 `{0,1}`-number is `≤ R_k = (10^k-1)/9`. -/
theorem block_le_repunit (k : ℕ) (hk : 0 < k) :
    ∀ M, (∀ d ∈ Nat.digits 10 M, d ≤ 1) →
      ∀ c ∈ Nat.digits (10 ^ k) M, c ≤ (10 ^ k - 1) / 9 := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro hM c hc
    rcases Nat.eq_zero_or_pos M with hM0 | hM0
    · subst hM0; simp at hc
    · have hbase : 1 < 10 ^ k := by
        calc 1 < 10 := by norm_num
          _ ≤ 10 ^ k := Nat.le_self_pow (by omega) 10
      have hrec : Nat.digits (10 ^ k) M = M % 10 ^ k :: Nat.digits (10 ^ k) (M / 10 ^ k) :=
        Nat.digits_def' hbase hM0
      rw [hrec] at hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · rw [Nat.self_mod_pow_eq_ofDigits_take k M (by norm_num : 2 ≤ 10)]
        apply ofDigits_le1_le_repunit k
        · intro d hd; exact hM d (List.mem_of_mem_take hd)
        · exact le_trans (List.length_take_le _ _) (le_refl _)
      · have hlt : M / 10 ^ k < M := Nat.div_lt_self hM0 hbase
        exact ih (M / 10 ^ k) hlt (digits_div_pow_ten_le1 k M hM) c hc'

/-- Total "deficit" of a digit list with cap `r`: `∑(r - x) + ∑ x = |L| * r`. -/
theorem deficit_sum (r : ℕ) : ∀ A : List ℕ, (∀ x ∈ A, x ≤ r) →
    (A.map (fun y => r - y)).sum + A.sum = A.length * r := by
  intro A
  induction A with
  | nil => intro _; simp
  | cons x tl ih =>
    intro hbd
    have hx : x ≤ r := hbd x List.mem_cons_self
    have htl : ∀ y ∈ tl, y ≤ r := fun y hy => hbd y (List.mem_cons_of_mem _ hy)
    have IH := ih htl
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [Nat.succ_mul]; omega

/-- Weighted lower bound: for a list `L` with all entries `≤ r` (`B ≥ 1`),
`r * ∑_{i<|L|} B^i ≤ ofDigits B L + (∑(r - x)) * B^{|L|}`. -/
theorem ofDigits_weighted_lb (B r : ℕ) (hB : 1 ≤ B) :
    ∀ L : List ℕ, (∀ x ∈ L, x ≤ r) →
      r * (∑ i ∈ Finset.range L.length, B ^ i) ≤
        Nat.ofDigits B L + ((L.map (fun y => r - y)).sum) * B ^ L.length := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons x tl ih =>
    intro hbd
    have hx : x ≤ r := hbd x List.mem_cons_self
    have htl : ∀ y ∈ tl, y ≤ r := fun y hy => hbd y (List.mem_cons_of_mem _ hy)
    have IH := ih htl
    set n := tl.length with hn
    set P := B ^ n with hP
    set Otl := Nat.ofDigits B tl with hOtl
    set Dtl := (tl.map (fun y => r - y)).sum with hD
    have hPpos : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
    have hBP : 1 ≤ B * P := Nat.mul_pos (by omega) (by omega)
    rw [List.length_cons, List.map_cons, List.sum_cons, Nat.ofDigits_cons]
    rw [show B ^ (n+1) = B * P by rw [pow_succ]; ring]
    rw [Finset.sum_range_succ' (fun i => B ^ i) n]
    simp only [pow_zero, pow_succ]
    have hSrw : (∑ i ∈ Finset.range n, B ^ i * B) = B * (∑ i ∈ Finset.range n, B ^ i) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [hSrw]
    have key : r * B * (∑ i ∈ Finset.range n, B ^ i) ≤ B * Otl + Dtl * (B * P) := by
      calc r * B * (∑ i ∈ Finset.range n, B ^ i)
          = B * (r * (∑ i ∈ Finset.range n, B ^ i)) := by ring
        _ ≤ B * (Otl + Dtl * P) := Nat.mul_le_mul_left B IH
        _ = B * Otl + Dtl * (B * P) := by ring
    have hfin : r ≤ x + (r - x) * (B * P) := by
      have h1 : (r - x) * 1 ≤ (r - x) * (B * P) := Nat.mul_le_mul_left _ hBP
      omega
    nlinarith [key, hfin, Nat.mul_le_mul_left (B*P) hx]

/-- **Lower bound for Part 2.**  Any positive `{0,1}`-number divisible by `10^k - 1`
is at least the repunit `R_{9k} = (10^{9k}-1)/9`.

Proof (the "block" argument): write `M` in base `B = 10^k`.  Each base-`B` block is a
base-10 `{0,1}`-number `< 10^k`, hence `≤ R_k = (10^k-1)/9`.  Since `B ≡ 1 (mod 10^k-1)`,
divisibility of `M` forces the block sum `Σ` to be divisible by `10^k-1 = 9 R_k`; being
positive, `Σ ≥ 9 R_k`.  With every block `≤ R_k`, a weighted minimisation shows that the
value is at least `R_k (1 + B + ⋯ + B^8) = R_{9k}`. -/
theorem a004290_lower (k : ℕ) (hk : 0 < k) (M : ℕ)
    (hMpos : 0 < M) (hdvd : (10 ^ k - 1) ∣ M)
    (h01 : ∀ d ∈ Nat.digits 10 M, d = 0 ∨ d = 1) :
    (10 ^ (9 * k) - 1) / 9 ≤ M := by
  have h10 : (10:ℕ) ≤ 10 ^ k := by
    calc (10:ℕ) = 10 ^ 1 := (pow_one 10).symm
      _ ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hBge2 : 2 ≤ (10:ℕ) ^ k := by omega
  have h9dvd : (9:ℕ) ∣ (10 ^ k - 1) := by
    have := Nat.sub_dvd_pow_sub_pow 10 1 k; simpa using this
  have h9r : 9 * ((10 ^ k - 1) / 9) = 10 ^ k - 1 := by
    obtain ⟨c, hc⟩ := h9dvd; rw [hc, Nat.mul_div_cancel_left _ (by norm_num)]
  have hr1 : 1 ≤ (10 ^ k - 1) / 9 := by omega
  have hle1 : ∀ d ∈ Nat.digits 10 M, d ≤ 1 := by
    intro d hd; rcases h01 d hd with h | h <;> omega
  set L := Nat.digits (10 ^ k) M with hLdef
  have hMeq : Nat.ofDigits (10 ^ k) L = M := Nat.ofDigits_digits (10 ^ k) M
  have hblock : ∀ x ∈ L, x ≤ (10 ^ k - 1) / 9 := fun x hx => block_le_repunit k hk M hle1 x hx
  have hz : ∀ (L0 : List ℕ), (∀ x ∈ L0, x = 0) → Nat.ofDigits (10 ^ k) L0 = 0 := by
    intro L0; induction L0 with
    | nil => intro _; simp [Nat.ofDigits]
    | cons a t ih =>
      intro hh
      rw [Nat.ofDigits_cons, hh a List.mem_cons_self,
          ih (fun x hx => hh x (List.mem_cons_of_mem _ hx))]; ring
  have hsumpos : 0 < L.sum := by
    rcases Nat.eq_zero_or_pos L.sum with h0 | h0
    · exfalso
      have hall : ∀ x ∈ L, x = 0 := by
        intro x hx
        have := List.single_le_sum (fun y _ => Nat.zero_le y) x hx; omega
      have := hz L hall; rw [hMeq] at this; omega
    · exact h0
  have hmod : (10:ℕ) ^ k % (10 ^ k - 1) = 1 := by
    have e : (10:ℕ) ^ k % (10 ^ k - 1) = ((10 ^ k - 1) + 1) % (10 ^ k - 1) := by congr 1; omega
    rw [e, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hcong : M ≡ L.sum [MOD (10 ^ k - 1)] := Nat.modEq_digits_sum (10 ^ k - 1) (10 ^ k) hmod M
  have hMmod : M ≡ 0 [MOD (10 ^ k - 1)] := (Nat.modEq_zero_iff_dvd).mpr hdvd
  have hsumdvd : (10 ^ k - 1) ∣ L.sum :=
    (Nat.modEq_zero_iff_dvd).mp (hcong.symm.trans hMmod)
  have hsumge : 10 ^ k - 1 ≤ L.sum := Nat.le_of_dvd hsumpos hsumdvd
  have h9rle : 9 * ((10 ^ k - 1) / 9) ≤ L.sum := by rw [h9r]; exact hsumge
  have hlen : 9 ≤ L.length := by
    have hsle : L.sum ≤ L.length * ((10 ^ k - 1) / 9) := by
      have := List.sum_le_card_nsmul L ((10 ^ k - 1) / 9) hblock
      simpa [smul_eq_mul] using this
    have h9le : 9 * ((10 ^ k - 1) / 9) ≤ L.length * ((10 ^ k - 1) / 9) := le_trans h9rle hsle
    exact Nat.le_of_mul_le_mul_right h9le (by omega)
  set A := L.take 9 with hAdef
  set C := L.drop 9 with hCdef
  have hsplit : L = A ++ C := (List.take_append_drop 9 L).symm
  have hAlen : A.length = 9 := by rw [hAdef, List.length_take]; omega
  have hval : Nat.ofDigits (10 ^ k) L
      = Nat.ofDigits (10 ^ k) A + (10 ^ k) ^ 9 * Nat.ofDigits (10 ^ k) C := by
    conv_lhs => rw [hsplit]
    rw [Nat.ofDigits_append, hAlen]
  have hAbd : ∀ x ∈ A, x ≤ (10 ^ k - 1) / 9 :=
    fun x hx => hblock x (by rw [hsplit]; exact List.mem_append_left _ hx)
  have hwlb := ofDigits_weighted_lb (10 ^ k) ((10 ^ k - 1) / 9) (by omega) A hAbd
  rw [hAlen] at hwlb
  have hdef := deficit_sum ((10 ^ k - 1) / 9) A hAbd
  rw [hAlen] at hdef
  have hCsum : C.sum = L.sum - A.sum := by
    have : L.sum = A.sum + C.sum := by rw [hsplit]; simp [List.sum_append]
    omega
  have hdefle : (A.map (fun y => (10 ^ k - 1) / 9 - y)).sum ≤ C.sum := by omega
  have hCge2 : C.sum ≤ Nat.ofDigits (10 ^ k) C := Nat.sum_le_ofDigits C (by omega)
  have hStep : ((10 ^ k - 1) / 9) * (∑ i ∈ Finset.range 9, (10 ^ k) ^ i)
      ≤ Nat.ofDigits (10 ^ k) L := by
    rw [hval]
    calc ((10 ^ k - 1) / 9) * (∑ i ∈ Finset.range 9, (10 ^ k) ^ i)
        ≤ Nat.ofDigits (10 ^ k) A + (A.map (fun y => (10 ^ k - 1) / 9 - y)).sum * (10 ^ k) ^ 9 :=
          hwlb
      _ ≤ Nat.ofDigits (10 ^ k) A + C.sum * (10 ^ k) ^ 9 := by
          apply Nat.add_le_add_left; exact Nat.mul_le_mul_right _ hdefle
      _ = Nat.ofDigits (10 ^ k) A + (10 ^ k) ^ 9 * C.sum := by rw [Nat.mul_comm]
      _ ≤ Nat.ofDigits (10 ^ k) A + (10 ^ k) ^ 9 * Nat.ofDigits (10 ^ k) C := by
          apply Nat.add_le_add_left; exact Nat.mul_le_mul_left _ hCge2
  have hReq : ((10 ^ k - 1) / 9) * (∑ i ∈ Finset.range 9, (10 ^ k) ^ i)
      = (10 ^ (9 * k) - 1) / 9 := by
    obtain ⟨c, hc⟩ := h9dvd
    have hgeom : (10 ^ k - 1) * (∑ i ∈ Finset.range 9, (10 ^ k) ^ i) = 10 ^ (9 * k) - 1 := by
      have := nat_geom (10 ^ k) 9 (Nat.one_le_pow _ _ (by norm_num))
      rw [this, ← pow_mul]; ring_nf
    rw [hc] at hgeom ⊢
    rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 9)]
    have : 9 * (c * (∑ i ∈ Finset.range 9, (10 ^ k) ^ i)) = 10 ^ (9 * k) - 1 := by
      rw [← hgeom]; ring
    omega
  rw [hReq, hMeq] at hStep
  exact hStep

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
  · -- Part 1: `A004290 (10 ^ k) = 10 ^ k`.
    -- The smallest positive multiple of `10 ^ k` whose decimal digits are all `0` or `1`
    -- is `10 ^ k` itself: every positive multiple of `10 ^ k` is `≥ 10 ^ k`, and `10 ^ k`
    -- has digits `0…0 1`, all of which lie in `{0, 1}`.
    unfold A004290
    set S := { m : ℕ | 0 < m ∧ (10 ^ k) ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }
      with hS
    have hmem : (10 ^ k) ∈ S := by
      refine ⟨by positivity, dvd_refl _, ?_⟩
      intro d hd
      rw [digits_pow_ten] at hd
      simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hd
      rcases hd with ⟨_, h⟩ | h
      · exact Or.inl h
      · exact Or.inr h
    have hlb : ∀ m ∈ S, 10 ^ k ≤ m := fun m hm => Nat.le_of_dvd hm.1 hm.2.1
    exact le_antisymm (Nat.sInf_le hmem) (hlb _ (Nat.sInf_mem ⟨_, hmem⟩))
  · -- Part 2: `A004290 (10 ^ k - 1) = (10 ^ (9 * k) - 1) / 9` (the repunit with `9 * k` ones).
    --
    -- Membership: `R_{9k} = (10^{9k}-1)/9` is positive, its decimal digits are `9*k` ones
    -- (`digits_repunit`), and `10^k - 1` divides it (`dvd_repunit`).
    -- Minimality: `a004290_lower` shows any positive `{0,1}`-multiple of `10^k-1` is `≥ R_{9k}`.
    unfold A004290
    set S := { m : ℕ | 0 < m ∧ (10 ^ k - 1) ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }
      with hS
    have h9k : (10:ℕ) ≤ 10 ^ (9 * k) := by
      calc (10:ℕ) = 10 ^ 1 := (pow_one 10).symm
        _ ≤ 10 ^ (9 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hmem : (10 ^ (9 * k) - 1) / 9 ∈ S := by
      refine ⟨by omega, dvd_repunit k, ?_⟩
      intro d hd
      rw [digits_repunit] at hd
      rw [List.mem_replicate] at hd
      exact Or.inr hd.2
    refine le_antisymm (Nat.sInf_le hmem) ?_
    have hmem' := Nat.sInf_mem (⟨_, hmem⟩ : S.Nonempty)
    exact a004290_lower k hk (sInf S) hmem'.1 hmem'.2.1 hmem'.2.2
  · -- Part 3 (the open Radcliffe conjecture):  for every `n < 10 ^ k - 1`,
    -- `A004290 n < A004290 (10 ^ k - 1) = R_{9k}`.
    --
    -- Equivalently: every `n ≤ 10 ^ k - 2` has a `{0,1}`-multiple with fewer than `9 * k`
    -- decimal digits.  Numerically (verified for all `n ≤ 3·10^5`, and for divisors of
    -- `10^m - 1` below `10^7`), the only `n` achieving the extremal count `9 * digits(n)`
    -- are the repdigits `10^j - 1`, which are exactly the excluded values; every other `n`
    -- has gap `≥ 2`.  A proof of this O(log n)-digit bound with the optimal constant `9` is,
    -- to current knowledge, an open problem: it reduces (in the case of moduli of large
    -- multiplicative order) to producing a *nonempty* `{0,1}`-zero-sum subset of
    -- `{10^0, …, 10^{9k-1}} (mod n)`, for which standard pigeonhole yields only signed
    -- `{-1,0,1}` relations.  This is the genuinely unresolved content of the conjecture.
    sorry
