import FormalConjectures.Util.ProblemImports
open Nat
open Classical

lemma modEq_nine_digits_sum_symm (n : ℕ) : n % 9 = (digits 10 n).sum % 9 := modEq_nine_digits_sum n

def makeBlock (P j c_1 x : ℕ) : List ℕ :=
  [if j < c_1 then 1 else 0, if j < x then 1 else 0] ++ List.replicate (2 * P - 2) 0

lemma length_makeBlock (P j c_1 x : ℕ) (hP : P > 0) : (makeBlock P j c_1 x).length = 2 * P := by
  simp [makeBlock]
  omega

lemma ofDigits_makeBlock (P j c_1 x b : ℕ) :
    ofDigits b (makeBlock P j c_1 x) = (if j < c_1 then 1 else 0) + (if j < x then 1 else 0) * b := by
  simp [makeBlock, ofDigits]

def makeBlocks (P c_1 x : ℕ) : ℕ → List ℕ
  | 0 => []
  | j + 1 => makeBlocks P c_1 x j ++ makeBlock P j c_1 x

lemma length_makeBlocks (P c_1 x len : ℕ) (hP : P > 0) : (makeBlocks P c_1 x len).length = len * 2 * P := by
  induction' len with len ih
  · simp [makeBlocks]
  · simp [makeBlocks, ih, length_makeBlock _ _ _ _ hP]
    ring

lemma ofDigits_makeBlocks (P c_1 x len b : ℕ) (hP : P > 0) :
    ofDigits b (makeBlocks P c_1 x len) = ∑ j ∈ Finset.range len, ((if j < c_1 then 1 else 0) + (if j < x then 1 else 0) * b) * b ^ (j * 2 * P) := by
  induction' len with len ih
  · simp [makeBlocks]
  · rw [makeBlocks, ofDigits_append, ih, length_makeBlocks _ _ _ _ hP, ofDigits_makeBlock, Finset.sum_range_succ]
    ring

lemma ofDigits_replicate_zero (b L : ℕ) : ofDigits b (List.replicate L 0) = 0 := by simp

def K_list (L P c_1 x len : ℕ) : List ℕ := List.replicate L 0 ++ makeBlocks P c_1 x len

lemma ofDigits_K_list (L P c_1 x len b : ℕ) (hP : P > 0) :
    ofDigits b (K_list L P c_1 x len) = b ^ L * ∑ j ∈ Finset.range len, ((if j < c_1 then 1 else 0) + (if j < x then 1 else 0) * b) * b ^ (j * 2 * P) := by
  simp [K_list, ofDigits_append, ofDigits_makeBlocks P c_1 x len b hP, mul_comm]

lemma sum_makeBlock (P j c_1 x : ℕ) : (makeBlock P j c_1 x).sum = (if j < c_1 then 1 else 0) + (if j < x then 1 else 0) := by simp [makeBlock]

lemma sum_makeBlocks (P c_1 x len : ℕ) :
    (makeBlocks P c_1 x len).sum = (∑ j ∈ Finset.range len, if j < c_1 then 1 else 0) + (∑ j ∈ Finset.range len, if j < x then 1 else 0) := by
  induction' len with len ih
  · simp [makeBlocks]
  · rw [makeBlocks, List.sum_append, ih, sum_makeBlock, Finset.sum_range_succ, Finset.sum_range_succ]
    omega

lemma sum_ite_lt (c len : ℕ) (h : c ≤ len) : ∑ j ∈ Finset.range len, (if j < c then 1 else 0 : ℕ) = c := by
  have : ∑ j ∈ Finset.range len, (if j < c then 1 else 0 : ℕ) = ∑ j ∈ Finset.range c, 1 := by
    rw [← Finset.sum_range_add_sum_Ico _ h]
    have h1 : ∑ j ∈ Finset.range c, (if j < c then 1 else 0 : ℕ) = ∑ j ∈ Finset.range c, 1 := by
      apply Finset.sum_congr rfl
      intro y hy
      simp at hy
      rw [if_pos hy]
    have h2 : ∑ j ∈ Finset.Ico c len, (if j < c then 1 else 0 : ℕ) = ∑ j ∈ Finset.Ico c len, 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      simp at hy
      have h3 : ¬ (y < c) := by omega
      rw [if_neg h3]
    rw [h1, h2, Finset.sum_const_zero, add_zero]
  rw [this]; simp

lemma bound_makeBlock (P j c_1 x y : ℕ) (h : y ∈ makeBlock P j c_1 x) : y < 10 := by
  simp [makeBlock] at h; rcases h with h | h | h
  · subst h; split <;> omega
  · subst h; split <;> omega
  · have : y = 0 := h.2; omega

lemma bound_makeBlocks (P c_1 x len y : ℕ) (h : y ∈ makeBlocks P c_1 x len) : y < 10 := by
  induction' len with len ih
  · simp [makeBlocks] at h
  · rw [makeBlocks, List.mem_append] at h; cases h with
    | inl h => exact ih h
    | inr h => exact bound_makeBlock _ _ _ _ _ h

lemma bound_K_list (L P c_1 x len y : ℕ) (h : y ∈ K_list L P c_1 x len) : y < 10 := by
  rw [K_list, List.mem_append] at h; cases h with
  | inl h => have : y = 0 := List.eq_of_mem_replicate h; omega
  | inr h => exact bound_makeBlocks _ _ _ _ _ h

lemma sum_K_list (L P c_1 x len : ℕ) (hc : c_1 ≤ len) (hx : x ≤ len) : (K_list L P c_1 x len).sum = c_1 + x := by
  simp [K_list, sum_makeBlocks, sum_ite_lt _ _ hc, sum_ite_lt _ _ hx]

lemma sum_K_list_digits (L P c_1 x len : ℕ) (hc : c_1 ≤ len) (hx : x ≤ len) : (digits 10 (ofDigits 10 (K_list L P c_1 x len))).sum = c_1 + x := by
  have h1 : (K_list L P c_1 x len) ∈ {l : List ℕ | l.length = (K_list L P c_1 x len).length ∧ ∀ y ∈ l, y < 10} := by
    simp
    intro y hy
    exact bound_K_list _ _ _ _ _ _ hy
  have h2 : 1 < 10 := by omega
  rw [sum_digits_ofDigits_eq_sum h2 h1]
  exact sum_K_list L P c_1 x len hc hx

lemma exists_period (m : ℕ) (hm : m > 0) : ∃ L P : ℕ, L ≥ m ∧ P > 0 ∧ (10 ^ L) % m = (10 ^ (L + P)) % m := by
  let f : Fin (m + 1) → Fin m := fun i => ⟨(10 ^ (m + (i : ℕ))) % m, mod_lt _ hm⟩
  have h_card : Fintype.card (Fin m) < Fintype.card (Fin (m + 1)) := by rw [Fintype.card_fin, Fintype.card_fin]; exact lt_add_one m
  obtain ⟨i, j, hij, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f h_card
  wlog h_lt : i < j generalizing i j
  · have h_lt' : j < i := by omega
    exact this j i hij.symm hf.symm h_lt'
  · use m + i, j - i
    refine ⟨le_add_right m ↑i, tsub_pos_of_lt h_lt, ?_⟩
    have h1 : f i = f j := hf; injection h1 with h2
    have h3 : m + (j : ℕ) = m + (i : ℕ) + ((j : ℕ) - (i : ℕ)) := by omega
    rw [← h3]; exact h2

lemma period_mul (m L P k : ℕ) (h : (10 ^ L) % m = (10 ^ (L + P)) % m) : (10 ^ L) % m = (10 ^ (L + k * P)) % m := by
  induction' k with k ih
  · simp
  · have h2 : L + (k + 1) * P = L + k * P + P := by ring
    rw [h2, pow_add, Nat.mul_mod, ← ih, ← Nat.mul_mod, ← pow_add]; exact h

lemma exists_period_large (n m : ℕ) (hm : m > 0) : ∃ L P : ℕ, L ≥ n ∧ P > 0 ∧ (10 ^ L) % m = (10 ^ (L + P)) % m := by
  obtain ⟨L0, P, _, hP, h_eq⟩ := exists_period m hm
  use L0 + n * P, P
  constructor
  · have : P ≥ 1 := by omega
    have : n * P ≥ n := Nat.le_mul_of_pos_right _ this
    omega
  · constructor
    · exact hP
    · have h1 : 10 ^ (L0 + n * P) % m = 10 ^ L0 % m := (period_mul m L0 P n h_eq).symm
      have h_tmp : L0 + n * P + P = L0 + (n + 1) * P := by ring
      have h2 : 10 ^ (L0 + n * P + P) % m = 10 ^ (L0 + (n + 1) * P) % m := by rw [h_tmp]
      have h3 : 10 ^ (L0 + (n + 1) * P) % m = 10 ^ L0 % m := (period_mul m L0 P (n + 1) h_eq).symm
      rw [h1, h2, h3]

lemma mod_sum (len m : ℕ) (f : ℕ → ℕ) : (∑ j ∈ Finset.range len, f j) % m = (∑ j ∈ Finset.range len, f j % m) % m := by
  induction' len with len ih
  · simp
  · rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 : ((∑ j ∈ Finset.range len, f j) + f len) % m = ((∑ j ∈ Finset.range len, f j) % m + f len % m) % m := Nat.add_mod _ _ _
    have h2 : ((∑ j ∈ Finset.range len, f j % m) + f len % m) % m = ((∑ j ∈ Finset.range len, f j % m) % m + f len % m) % m := by rw [Nat.add_mod (∑ j ∈ Finset.range len, f j % m) (f len % m) m, Nat.mod_mod]
    rw [h1, ih, ← h2]

lemma K_val_term_mod (c_1 x j L P m : ℕ) (h : (10 ^ L) % m = (10 ^ (L + P)) % m) :
    ((if j < c_1 then 1 else 0) * 10 ^ (L + j * 2 * P) + (if j < x then 1 else 0) * 10 ^ (L + j * 2 * P + 1)) % m =
    ((if j < c_1 then 1 else 0) * 10 ^ L + (if j < x then 1 else 0) * 10 ^ (L + 1)) % m := by
  have h1 : (10 ^ (L + j * 2 * P)) % m = (10 ^ L) % m := (period_mul m L P (j * 2) h).symm
  have h2 : (10 ^ (L + j * 2 * P + 1)) % m = (10 ^ (L + 1)) % m := by
    have eq1 : 10 ^ (L + j * 2 * P + 1) = 10 ^ (L + j * 2 * P) * 10 := by ring
    have eq2 : 10 ^ (L + 1) = 10 ^ L * 10 := by ring
    rw [eq1, eq2, Nat.mul_mod, h1, ← Nat.mul_mod]
  have h3 : ((if j < c_1 then 1 else 0) * 10 ^ (L + j * 2 * P)) % m = ((if j < c_1 then 1 else 0) * 10 ^ L) % m := by rw [Nat.mul_mod, h1, ← Nat.mul_mod]
  have h4 : ((if j < x then 1 else 0) * 10 ^ (L + j * 2 * P + 1)) % m = ((if j < x then 1 else 0) * 10 ^ (L + 1)) % m := by rw [Nat.mul_mod, h2, ← Nat.mul_mod]
  rw [Nat.add_mod, h3, h4, ← Nat.add_mod]

lemma K_val_mod (c_1 x L P len m : ℕ) (h : (10 ^ L) % m = (10 ^ (L + P)) % m) :
    (∑ j ∈ Finset.range len, ((if j < c_1 then 1 else 0) * 10 ^ (L + j * 2 * P) + (if j < x then 1 else 0) * 10 ^ (L + j * 2 * P + 1))) % m =
    (∑ j ∈ Finset.range len, ((if j < c_1 then 1 else 0) * 10 ^ L + (if j < x then 1 else 0) * 10 ^ (L + 1))) % m := by
  rw [mod_sum]
  have h_eq : ∑ j ∈ Finset.range len, ((if j < c_1 then 1 else 0) * 10 ^ (L + j * 2 * P) + (if j < x then 1 else 0) * 10 ^ (L + j * 2 * P + 1)) % m =
              ∑ j ∈ Finset.range len, ((if j < c_1 then 1 else 0) * 10 ^ L + (if j < x then 1 else 0) * 10 ^ (L + 1)) % m := by
    apply Finset.sum_congr rfl; intro j _ ; exact K_val_term_mod c_1 x j L P m h
  rw [h_eq, ← mod_sum]

lemma K_val_eq (c_1 x L P len : ℕ) :
    10 ^ L * ∑ j ∈ Finset.range len, ((if j < c_1 then 1 else 0) + (if j < x then 1 else 0) * 10) * 10 ^ (j * 2 * P) =
    ∑ j ∈ Finset.range len, ((if j < c_1 then 1 else 0) * 10 ^ (L + j * 2 * P) + (if j < x then 1 else 0) * 10 ^ (L + j * 2 * P + 1)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have eq1 : 10 ^ (L + j * 2 * P) = 10 ^ L * 10 ^ (j * 2 * P) := by ring
  have eq2 : 10 ^ (L + j * 2 * P + 1) = 10 ^ L * 10 ^ (j * 2 * P) * 10 := by ring
  rw [eq1, eq2]; ring

lemma K_val_sum_eval (c_1 x L len : ℕ) (hc : c_1 ≤ len) (hx : x ≤ len) :
    ∑ j ∈ Finset.range len, ((if j < c_1 then 1 else 0) * 10 ^ L + (if j < x then 1 else 0) * 10 ^ (L + 1)) =
    c_1 * 10 ^ L + x * 10 ^ (L + 1) := by
  have h1 : ∑ j ∈ Finset.range len, (if j < c_1 then 1 else 0) * 10 ^ L = (∑ j ∈ Finset.range len, (if j < c_1 then 1 else 0 : ℕ)) * 10 ^ L := by rw [Finset.sum_mul]
  have h2 : ∑ j ∈ Finset.range len, (if j < x then 1 else 0) * 10 ^ (L + 1) = (∑ j ∈ Finset.range len, (if j < x then 1 else 0 : ℕ)) * 10 ^ (L + 1) := by rw [Finset.sum_mul]
  rw [Finset.sum_add_distrib, h1, h2, sum_ite_lt c_1 len hc, sum_ite_lt x len hx]

lemma K_val_sum_final (n x L : ℕ) (hx : x ≤ n) : (n - x) * 10 ^ L + x * 10 ^ (L + 1) = 10 ^ L * (n + 9 * x) := by
  have h1 : x * 10 ^ (L + 1) = 10 * x * 10 ^ L := by ring
  rw [h1]
  have h2 : (n - x) * 10 ^ L + 10 * x * 10 ^ L = (n - x + 10 * x) * 10 ^ L := by rw [add_mul]
  rw [h2]
  have h3 : n - x + 10 * x = n + 9 * x := by omega
  rw [h3]; ring

lemma dsum_le_n (n : ℕ) : (digits 10 n).sum ≤ n := digit_sum_le 10 n

lemma n_eq_m_plus_9y (n m : ℕ) (hm : m = (digits 10 n).sum) (hlen : m ≤ n) :
    ∃ y : ℕ, n = m + 9 * y := by
  have h_mod : n % 9 = m % 9 := by rw [hm]; exact modEq_nine_digits_sum_symm n
  have h_sub : (n - m) % 9 = 0 := by omega
  use (n - m) / 9; omega

lemma construct_x (n m y : ℕ) (hm : m > 0) (hnm : m ≤ n) : ∃ x : ℕ, x ≤ n ∧ (x + y) % m = 0 := by
  use (m - (y % m)) % m
  constructor
  · have h1 : (m - (y % m)) % m < m := Nat.mod_lt _ hm; omega
  · have h1 : ((m - (y % m)) % m + y) % m = ((m - (y % m)) % m % m + y % m) % m := Nat.add_mod _ _ _
    have h2 : ((m - (y % m)) % m % m + y % m) % m = ((m - (y % m)) % m + y % m) % m := by rw [Nat.mod_mod]
    rw [h1, h2]
    have h3 : ((m - (y % m)) % m + y % m) % m = (m - (y % m) + y) % m := (Nat.add_mod _ _ _).symm
    rw [h3]
    have h4 : y % m ≤ m := le_of_lt (Nat.mod_lt _ hm)
    have h_tmp : y = m * (y / m) + y % m := (Nat.div_add_mod y m).symm
    have h6 : m - (y % m) + y = m + m * (y / m) := by omega
    rw [h6]
    have h7 : (m + m * (y / m)) % m = ((m % m) + (m * (y / m)) % m) % m := Nat.add_mod _ _ _
    rw [h7]; simp

lemma ten_pow_gt (n : ℕ) : 10 ^ n > n := by
  induction' n with n ih
  · simp
  · have h_tmp : 10 ^ (n + 1) = 10 ^ n * 10 := by ring
    rw [h_tmp]
    nlinarith

lemma K_val_gt_n (c_1 x len P L n : ℕ) (h : c_1 + x > 0) (hc : c_1 ≤ len) (hx : x ≤ len) (hL : L ≥ n) :
    10 ^ L * ∑ j ∈ Finset.range len, ((if j < c_1 then 1 else 0) + (if j < x then 1 else 0) * 10) * 10 ^ (j * 2 * P) > n := by
  have h_sum : ∑ j ∈ Finset.range len, ((if j < c_1 then 1 else 0) + (if j < x then 1 else 0) * 10) * 10 ^ (j * 2 * P) ≥ 1 := by
    have hlen : len > 0 := by omega
    cases len with
    | zero => omega
    | succ len' =>
      rw [Finset.sum_range_succ']
      have h_base : ((if 0 < c_1 then 1 else 0) + (if 0 < x then 1 else 0) * 10) * 10 ^ (0 * 2 * P) ≥ 1 := by
        cases Nat.eq_zero_or_pos c_1 with
        | inl hc1 =>
          subst hc1
          have hx1 : x > 0 := by omega
          have h_if_c1 : (if 0 < 0 then 1 else 0) = 0 := if_neg (by omega)
          have h_if_x : (if 0 < x then 1 else 0) = 1 := if_pos (by omega)
          rw [h_if_c1, h_if_x]
          simp
        | inr hc1 =>
          have hc1_pos : c_1 > 0 := hc1
          have h_if_c1 : (if 0 < c_1 then 1 else 0) = 1 := if_pos (by omega)
          rw [h_if_c1]
          by_cases hx2 : 0 < x
          · have h_if_x : (if 0 < x then 1 else 0) = 1 := if_pos hx2
            rw [h_if_x]
            simp
          · have h_if_x : (if 0 < x then 1 else 0) = 0 := if_neg hx2
            rw [h_if_x]
            simp
      omega
  have h1 : 10 ^ L * ∑ j ∈ Finset.range len, ((if j < c_1 then 1 else 0) + (if j < x then 1 else 0) * 10) * 10 ^ (j * 2 * P) ≥ 10 ^ L := by
    have h_mul : 10 ^ L * 1 ≤ 10 ^ L * ∑ j ∈ Finset.range len, ((if j < c_1 then 1 else 0) + (if j < x then 1 else 0) * 10) * 10 ^ (j * 2 * P) := Nat.mul_le_mul_left _ h_sum
    omega
  have h2 : 10 ^ L ≥ 10 ^ n := Nat.pow_le_pow_right (by decide) hL
  have h3 : 10 ^ n > n := ten_pow_gt n
  omega

lemma list_sum_eq_zero (L : List ℕ) (h : L.sum = 0) (x : ℕ) (hx : x ∈ L) : x = 0 := by
  induction' L with hd tl ih
  · simp at hx
  · simp at h
    simp at hx
    cases hx with
    | inl hx => omega
    | inr hx => exact ih (by omega) hx

lemma ofDigits_all_zero (b : ℕ) (L : List ℕ) (h : ∀ x ∈ L, x = 0) : ofDigits b L = 0 := by
  induction' L with hd tl ih
  · simp
  · have h1 : hd = 0 := h hd (List.Mem.head _)
    have h2 : ∀ x ∈ tl, x = 0 := fun x hx => h x (List.Mem.tail _ hx)
    simp [ofDigits, h1, ih h2]

lemma dsum_pos_of_pos {n : ℕ} (hn : n > 0) : (digits 10 n).sum > 0 := by
  by_contra h
  have h1 : (digits 10 n).sum = 0 := by omega
  have h2 : ∀ x ∈ digits 10 n, x = 0 := fun x hx => list_sum_eq_zero _ h1 x hx
  have h3 : ofDigits 10 (digits 10 n) = 0 := ofDigits_all_zero 10 (digits 10 n) h2
  have h4 : ofDigits 10 (digits 10 n) = n := ofDigits_digits 10 n
  omega

/--
A272479: $a(n)$ is the smallest $k$ different from $n$ such that $(n, k)$ is a Harshad amicable pair.
Let $D(n)$ be the sum of digits of $n$.
$m$ and $k$ are Harshad amicable if they are distinct integers such that $D(m) \mid k$ and $D(k) \mid m$.
For any $n$ with no Harshad amicable partner, $a(n)=0$ (Conjecture: the sequence contains no zeros.)
-/
noncomputable def a (n : ℕ) : ℕ :=
  let dsum (m : ℕ) : ℕ := (digits 10 m).sum

  let partners : Set ℕ := {k | k > 0 ∧ k ≠ n ∧ dsum n ∣ k ∧ dsum k ∣ n}

  -- The set of partners is bounded below by 1. If it is non-empty, `sInf`
  -- correctly returns the smallest element. If empty, we return 0 as per the OEIS comment.
  if h : partners.Nonempty then
    sInf partners
  else
    0

/-- A272479 Conjecture: the sequence contains no zeros. -/
theorem oeis_272479_conjecture_0 : ∀ n : ℕ, n > 0 → a n ≠ 0 := by
  intro n hn
  have h_nonempty : {k | k > 0 ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧ (digits 10 k).sum ∣ n}.Nonempty := by
    let m := (digits 10 n).sum
    have hm : m > 0 := dsum_pos_of_pos hn
    have hnm : m ≤ n := dsum_le_n n
    obtain ⟨y, hy⟩ := n_eq_m_plus_9y n m rfl hnm
    obtain ⟨x, hx_le, hx_mod⟩ := construct_x n m y hm hnm
    let c_1 := n - x
    have hc1 : c_1 + x = n := by omega
    have hc1_le : c_1 ≤ n := by omega
    obtain ⟨L, P, hL, hP, h_period⟩ := exists_period_large n m hm
    let K := ofDigits 10 (K_list L P c_1 x n)
    use K
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : K = 10 ^ L * ∑ j ∈ Finset.range n, ((if j < c_1 then 1 else 0) + (if j < x then 1 else 0) * 10) * 10 ^ (j * 2 * P) := by
        exact ofDigits_K_list L P c_1 x n 10 hP
      rw [this]
      have hc : c_1 + x > 0 := by omega
      have h_gt : 10 ^ L * ∑ j ∈ Finset.range n, ((if j < c_1 then 1 else 0) + (if j < x then 1 else 0) * 10) * 10 ^ (j * 2 * P) > n := K_val_gt_n c_1 x n P L n hc hc1_le hx_le hL
      omega
    · have : K = 10 ^ L * ∑ j ∈ Finset.range n, ((if j < c_1 then 1 else 0) + (if j < x then 1 else 0) * 10) * 10 ^ (j * 2 * P) := by
        exact ofDigits_K_list L P c_1 x n 10 hP
      rw [this]
      have hc : c_1 + x > 0 := by omega
      have h_gt : 10 ^ L * ∑ j ∈ Finset.range n, ((if j < c_1 then 1 else 0) + (if j < x then 1 else 0) * 10) * 10 ^ (j * 2 * P) > n := K_val_gt_n c_1 x n P L n hc hc1_le hx_le hL
      omega
    · have h_K_val : K = 10 ^ L * ∑ j ∈ Finset.range n, ((if j < c_1 then 1 else 0) + (if j < x then 1 else 0) * 10) * 10 ^ (j * 2 * P) := ofDigits_K_list L P c_1 x n 10 hP
      have h_K_eq : K = ∑ j ∈ Finset.range n, ((if j < c_1 then 1 else 0) * 10 ^ (L + j * 2 * P) + (if j < x then 1 else 0) * 10 ^ (L + j * 2 * P + 1)) := by
        rw [h_K_val, K_val_eq c_1 x L P n]
      have h_K_mod : K % m = (∑ j ∈ Finset.range n, ((if j < c_1 then 1 else 0) * 10 ^ L + (if j < x then 1 else 0) * 10 ^ (L + 1))) % m := by
        rw [h_K_eq, K_val_mod c_1 x L P n m h_period]
      have h_sum_eval : ∑ j ∈ Finset.range n, ((if j < c_1 then 1 else 0) * 10 ^ L + (if j < x then 1 else 0) * 10 ^ (L + 1)) = c_1 * 10 ^ L + x * 10 ^ (L + 1) := K_val_sum_eval c_1 x L n hc1_le hx_le
      have h_sum_final : c_1 * 10 ^ L + x * 10 ^ (L + 1) = 10 ^ L * (n + 9 * x) := by
        have ht1 : x * 10 ^ (L + 1) = 10 * x * 10 ^ L := by ring
        rw [ht1]
        have ht2 : c_1 * 10 ^ L + 10 * x * 10 ^ L = (c_1 + 10 * x) * 10 ^ L := by rw [add_mul]
        rw [ht2]
        have ht3 : c_1 + 10 * x = n + 9 * x := by omega
        rw [ht3]
        ring
      have h_n_9x : n + 9 * x = m + 9 * (x + y) := by
        have h_n_sub : n = m + 9 * y := hy
        rw [h_n_sub]
        ring
      have h_K_mod2 : K % m = (10 ^ L * (m + 9 * (x + y))) % m := by
        rw [h_K_mod, h_sum_eval, h_sum_final, h_n_9x]
      have h_mod_0 : (m + 9 * (x + y)) % m = 0 := by
        have h_xy : x + y = ((x + y) / m) * m := by
          have h_mod_zero : (x + y) % m = 0 := hx_mod
          have h_div : x + y = m * ((x + y) / m) + (x + y) % m := (Nat.div_add_mod (x + y) m).symm
          rw [h_mod_zero, add_zero, mul_comm] at h_div
          exact h_div
        rw [h_xy]
        have h_m_mul : m + 9 * (((x + y) / m) * m) = m * 1 + m * (9 * ((x + y) / m)) := by ring
        rw [h_m_mul, ← Nat.mul_add]
        exact Nat.mul_mod_right m (1 + 9 * ((x + y) / m))
      have h_K_mod3 : (10 ^ L * (m + 9 * (x + y))) % m = 0 := by
        rw [Nat.mul_mod, h_mod_0, Nat.mul_zero, Nat.zero_mod]
      rw [h_K_mod3] at h_K_mod2
      exact Nat.dvd_of_mod_eq_zero h_K_mod2
    · have h_dsum : (digits 10 K).sum = c_1 + x := sum_K_list_digits L P c_1 x n hc1_le hx_le
      rw [h_dsum]
      have h_c1_x : c_1 + x = n := by omega
      rw [h_c1_x]
  
  have h_a : a n = sInf {k | k > 0 ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧ (digits 10 k).sum ∣ n} := by
    unfold a
    dsimp
    have h_eq : (let dsum (m : ℕ) := (digits 10 m).sum; {k | k > 0 ∧ k ≠ n ∧ dsum n ∣ k ∧ dsum k ∣ n}) = {k | k > 0 ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧ (digits 10 k).sum ∣ n} := rfl
    rw [h_eq]
    exact dif_pos h_nonempty
  rw [h_a]
  have h_min_mem := Nat.sInf_mem h_nonempty
  have h_min_gt : sInf {k | k > 0 ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧ (digits 10 k).sum ∣ n} > 0 := h_min_mem.1
  omega

theorem oeis_272479_conjecture_0.disproof : ¬ (type_of% @oeis_272479_conjecture_0) := sorry
