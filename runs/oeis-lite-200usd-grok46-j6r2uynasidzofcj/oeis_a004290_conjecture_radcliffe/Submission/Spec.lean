import FormalConjectures.Util.ProblemImports

open Nat Set Finset

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

/-- A natural number uses only digits `0` and `1` in base 10. -/
def Is01 (m : ℕ) : Prop := ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1

/-- The set used to define `A004290`. -/
def A004290Set (n : ℕ) : Set ℕ :=
  { m : ℕ | 0 < m ∧ n ∣ m ∧ Is01 m }

lemma A004290_eq (n : ℕ) : A004290 n = sInf (A004290Set n) := rfl

lemma Is01.zero : Is01 0 := by
  intro d hd
  simp at hd

lemma Is01.one : Is01 1 := by
  intro d hd
  have hdig : Nat.digits 10 1 = [1] := Nat.digits_of_lt 10 1 (by decide) (by decide)
  rw [hdig] at hd
  simp only [List.mem_singleton] at hd
  exact Or.inr hd

lemma ofDigits_replicate_one (l : ℕ) :
    Nat.ofDigits 10 (List.replicate l 1) = ∑ i ∈ Finset.range l, 10 ^ i := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, ih, Finset.sum_range_succ', pow_zero,
      Finset.mul_sum]
    simp [pow_succ, mul_comm, add_comm]

lemma geom_sum_ten (l : ℕ) :
    ∑ i ∈ Finset.range l, 10 ^ i = (10 ^ l - 1) / 9 := by
  have hmul : (∑ i ∈ Finset.range l, 10 ^ i) * 9 = 10 ^ l - 1 := by
    simpa using (geom_sum_mul_of_one_le (x := 10) (by decide : 1 ≤ 10) l)
  rw [← hmul, Nat.mul_div_cancel _ (by decide : 0 < 9)]

lemma nine_dvd_ten_pow_sub_one (l : ℕ) : 9 ∣ 10 ^ l - 1 := by
  refine ⟨∑ i ∈ Finset.range l, 10 ^ i, ?_⟩
  rw [mul_comm]
  exact (geom_sum_mul_of_one_le (x := 10) (by decide : 1 ≤ 10) l).symm

lemma repunit_eq (l : ℕ) :
    Nat.ofDigits 10 (List.replicate l 1) = (10 ^ l - 1) / 9 := by
  rw [ofDigits_replicate_one, geom_sum_ten]

lemma digits_repunit (l : ℕ) (hl : 0 < l) :
    Nat.digits 10 ((10 ^ l - 1) / 9) = List.replicate l 1 := by
  rw [← repunit_eq]
  refine Nat.digits_ofDigits 10 (by decide) (List.replicate l 1) ?_ ?_
  · intro x hx
    have : x = 1 := List.eq_of_mem_replicate hx
    omega
  · intro h
    cases l with
    | zero => omega
    | succ l =>
      rw [List.getLast_replicate_succ]
      exact one_ne_zero

lemma Is01.repunit (l : ℕ) : Is01 ((10 ^ l - 1) / 9) := by
  intro d hd
  by_cases hl : l = 0
  · subst l
    simp at hd
  · rw [digits_repunit l (Nat.pos_of_ne_zero hl)] at hd
    exact Or.inr (List.eq_of_mem_replicate hd)

lemma A004290_le {n m : ℕ} (hm : 0 < m) (hdvd : n ∣ m) (h01 : Is01 m) :
    A004290 n ≤ m := by
  rw [A004290_eq]
  exact Nat.sInf_le (s := A004290Set n) ⟨hm, hdvd, h01⟩

lemma A004290_zero : A004290 0 = 0 := by
  rw [A004290_eq]
  have hempty : A004290Set 0 = ∅ := by
    ext m
    simp only [A004290Set, Is01, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    rcases h with ⟨hpos, hdvd, _⟩
    have hm0 : m = 0 := by
      simpa [zero_dvd_iff] using hdvd
    exact Nat.ne_of_gt hpos hm0
  simp [hempty]

lemma digits_ten_pow (k : ℕ) : Nat.digits 10 (10 ^ k) = List.replicate k 0 ++ [1] := by
  have h := Nat.digits_base_pow_mul (b := 10) (k := k) (m := 1) (by decide) (by decide)
  simpa [Nat.digits_of_lt 10 1 (by decide) (by decide)] using h

lemma is01_ten_pow (k : ℕ) : Is01 (10 ^ k) := by
  intro d hd
  rw [digits_ten_pow] at hd
  simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hd
  rcases hd with (⟨_, h0⟩ | h1)
  · exact Or.inl h0
  · exact Or.inr h1

lemma A004290Set_ten_pow_mem (k : ℕ) : 10 ^ k ∈ A004290Set (10 ^ k) :=
  ⟨pow_pos (by decide : 0 < 10) k, dvd_rfl, is01_ten_pow k⟩

lemma A004290_ten_pow (k : ℕ) : A004290 (10 ^ k) = 10 ^ k := by
  apply le_antisymm
  · exact A004290_le (pow_pos (by decide : 0 < 10) k) dvd_rfl (is01_ten_pow k)
  · have hne : (A004290Set (10 ^ k)).Nonempty := ⟨_, A004290Set_ten_pow_mem k⟩
    have hmem := Nat.sInf_mem hne
    rw [A004290_eq]
    exact Nat.le_of_dvd hmem.1 hmem.2.1

lemma repunit_pos (l : ℕ) (hl : 0 < l) : 0 < (10 ^ l - 1) / 9 := by
  have hle : 10 ≤ 10 ^ l := Nat.le_pow hl
  exact Nat.div_pos (by omega) (by decide)

lemma ten_pow_modEq_one {k : ℕ} (hk : 0 < k) : 10 ^ k ≡ 1 [MOD 10 ^ k - 1] := by
  set m := 10 ^ k - 1
  have hmpos : 1 < m := by
    have : 10 ≤ 10 ^ k := Nat.le_pow hk
    omega
  have hmk : 10 ^ k = m + 1 := by omega
  change 10 ^ k % m = 1 % m
  rw [hmk, Nat.add_mod_left]

lemma sum_ten_pow_k_mod_nine {k : ℕ} : ∑ i ∈ Finset.range 9, (10 ^ k) ^ i ≡ 0 [MOD 9] := by
  have h10 : 10 ≡ 1 [MOD 9] := by decide
  have hk1 : 10 ^ k ≡ 1 [MOD 9] := by
    simpa using (Nat.ModEq.pow k h10)
  have hterms : ∀ i ∈ Finset.range 9, (10 ^ k) ^ i ≡ 1 [MOD 9] := by
    intro i _
    simpa using (Nat.ModEq.pow i hk1)
  have hsum : ∑ i ∈ Finset.range 9, (10 ^ k) ^ i ≡ ∑ i ∈ Finset.range 9, (1 : ℕ) [MOD 9] :=
    Nat.ModEq.sum hterms
  have : ∑ i ∈ Finset.range 9, (1 : ℕ) = 9 := by simp
  rw [this] at hsum
  exact hsum

lemma dvd_repunit_nine {k : ℕ} (hk : 0 < k) :
    (10 ^ k - 1) ∣ (10 ^ (9 * k) - 1) / 9 := by
  have hfactor :
      10 ^ (9 * k) - 1 = (10 ^ k - 1) * ∑ i ∈ Finset.range 9, (10 ^ k) ^ i := by
    have hle : 1 ≤ 10 ^ k := Nat.one_le_pow k 10 (by decide)
    have := geom_sum_mul_of_one_le (x := 10 ^ k) hle 9
    have hpow : (10 ^ k) ^ 9 = 10 ^ (9 * k) := by rw [← pow_mul, mul_comm]
    rw [hpow] at this
    linarith
  have hsum9 : 9 ∣ ∑ i ∈ Finset.range 9, (10 ^ k) ^ i :=
    (Nat.modEq_zero_iff_dvd).1 sum_ten_pow_k_mod_nine
  obtain ⟨q, hq⟩ := hsum9
  refine ⟨q, ?_⟩
  have : (10 ^ (9 * k) - 1) / 9 = (10 ^ k - 1) * q := by
    rw [hfactor, hq, mul_left_comm, Nat.mul_div_cancel_left _ (by decide : 0 < 9)]
  exact this

lemma A004290_repunit_le {k : ℕ} (hk : 0 < k) :
    A004290 (10 ^ k - 1) ≤ (10 ^ (9 * k) - 1) / 9 :=
  A004290_le (repunit_pos (9 * k) (by omega)) (dvd_repunit_nine hk) (Is01.repunit (9 * k))

/-- The `i`-th base-10 digit of `x` (0 if past the end). -/
def digit10 (x i : ℕ) : ℕ := (Nat.digits 10 x).getD i 0

lemma digit10_eq (x i : ℕ) : digit10 x i = x / 10 ^ i % 10 := by
  simpa [digit10] using (Nat.getD_digits x i (by decide : 2 ≤ 10))

lemma Is01.digit10_le_one {x : ℕ} (h : Is01 x) (i : ℕ) :
    digit10 x i = 0 ∨ digit10 x i = 1 := by
  unfold digit10
  by_cases hi : i < (Nat.digits 10 x).length
  · rw [List.getD_eq_getElem (l := Nat.digits 10 x) (n := i) (d := 0) hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default (l := Nat.digits 10 x) (n := i) (d := 0) (le_of_not_gt hi)]
    exact Or.inl rfl

lemma ofDigits_eq_finset_sum (L : List ℕ) :
    Nat.ofDigits 10 L = ∑ i ∈ Finset.range L.length, L.getD i 0 * 10 ^ i := by
  induction L with
  | nil => simp [Nat.ofDigits_nil]
  | cons a L ih =>
    rw [Nat.ofDigits_cons, ih]
    simp only [List.length_cons]
    rw [Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, pow_zero, mul_one, pow_succ]
    rw [Finset.mul_sum]
    simp [mul_comm, mul_left_comm, mul_assoc, add_comm]

lemma ofDigits_digits_sum (x : ℕ) :
    x = ∑ i ∈ Finset.range (Nat.digits 10 x).length, digit10 x i * 10 ^ i := by
  conv_lhs => rw [← Nat.ofDigits_digits 10 x]
  simpa [digit10] using ofDigits_eq_finset_sum (Nat.digits 10 x)

lemma ten_pow_modEq_of_mod {k : ℕ} (hk : 0 < k) (i : ℕ) :
    10 ^ i ≡ 10 ^ (i % k) [MOD 10 ^ k - 1] := by
  have h1 := ten_pow_modEq_one hk
  have hdiv : k * (i / k) + i % k = i := Nat.div_add_mod i k
  have : 10 ^ i = (10 ^ k) ^ (i / k) * 10 ^ (i % k) := by
    rw [← pow_mul, ← pow_add, hdiv]
  rw [this]
  have hpow : (10 ^ k) ^ (i / k) ≡ 1 [MOD 10 ^ k - 1] := by
    simpa using (Nat.ModEq.pow (i / k) h1)
  have := hpow.mul_right (10 ^ (i % k))
  simpa [one_mul] using this

lemma is01_modEq_weighted {k x : ℕ} (hk : 0 < k) :
    x ≡ ∑ i ∈ Finset.range (Nat.digits 10 x).length, digit10 x i * 10 ^ (i % k)
      [MOD 10 ^ k - 1] := by
  have hx := ofDigits_digits_sum x
  conv_lhs => rw [hx]
  refine Nat.ModEq.sum ?_
  intro i hi
  exact (ten_pow_modEq_of_mod hk i).mul_left _

/-- Number of ones of `x` in positions congruent to `r` modulo `k`. -/
def countMod (k x r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (Nat.digits 10 x).length,
    if i % k = r then digit10 x i else 0

lemma weighted_eq_countMod {k x : ℕ} (hk : 0 < k) :
    ∑ i ∈ Finset.range (Nat.digits 10 x).length, digit10 x i * 10 ^ (i % k) =
      ∑ r ∈ Finset.range k, countMod k x r * 10 ^ r := by
  simp only [countMod]
  have hmul :
      ∑ r ∈ Finset.range k,
          (∑ i ∈ Finset.range (Nat.digits 10 x).length,
            if i % k = r then digit10 x i else 0) * 10 ^ r =
        ∑ r ∈ Finset.range k,
          ∑ i ∈ Finset.range (Nat.digits 10 x).length,
            (if i % k = r then digit10 x i else 0) * 10 ^ r := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    rw [Finset.sum_mul]
  rw [hmul, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hir : i % k < k := Nat.mod_lt i hk
  rw [Finset.sum_eq_single (i % k)]
  · simp
  · intro r hr hne
    simp [hne.symm]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hir)).elim

lemma countMod_le_of_is01 {k x r : ℕ} (h01 : Is01 x) :
    countMod k x r ≤
      ((Finset.range (Nat.digits 10 x).length).filter (fun i => i % k = r)).card := by
  unfold countMod
  set s := Finset.range (Nat.digits 10 x).length
  set t := s.filter (fun i => i % k = r)
  have hsum : ∑ i ∈ s, (if i % k = r then digit10 x i else 0) = ∑ i ∈ t, digit10 x i := by
    simp [t, Finset.sum_filter]
  rw [hsum]
  have hle : ∀ i ∈ t, digit10 x i ≤ 1 := by
    intro i hi
    rcases h01.digit10_le_one i with h0 | h1
    · simp [h0]
    · simp [h1]
  refine (Finset.sum_le_card_nsmul t (fun i => digit10 x i) 1 hle).trans ?_
  simp [t]

lemma filter_mod_eq_image (k L r : ℕ) (hk : 0 < k) (hr : r < k) :
    (Finset.range L).filter (fun i => i % k = r) =
      (Finset.range (if r < L then (L - 1 - r) / k + 1 else 0)).image
        (fun q => q * k + r) := by
  ext i
  constructor
  · intro hi
    have hiL : i < L := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hir : i % k = r := (Finset.mem_filter.mp hi).2
    by_cases hrL : r < L
    · refine Finset.mem_image.mpr ⟨i / k, ?_, ?_⟩
      · simp only [if_pos hrL, Finset.mem_range]
        have hid : k * (i / k) + r = i := by
          have := Nat.div_add_mod i k
          rwa [hir] at this
        have hmul : i / k * k ≤ L - 1 - r := by
          have : r ≤ L - 1 := Nat.le_pred_of_lt hrL
          have : k * (i / k) + r < L := by
            rw [hid]; exact hiL
          simpa [mul_comm] using (Nat.le_sub_of_add_le (by omega) : k * (i / k) ≤ L - 1 - r)
        have : i / k ≤ (L - 1 - r) / k :=
          (Nat.le_div_iff_mul_le hk).2 hmul
        exact Nat.lt_succ_of_le this
      · have := Nat.div_add_mod i k
        rw [hir] at this
        linarith
    · have : i % k ≤ i := Nat.mod_le i k
      omega
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨q, hq, rfl⟩
    by_cases hrL : r < L
    · simp only [if_pos hrL, Finset.mem_range] at hq
      have hqL : q * k + r < L := by
        have : q ≤ (L - 1 - r) / k := Nat.lt_succ_iff.mp hq
        have : q * k ≤ L - 1 - r := by
          simpa [mul_comm] using (Nat.le_div_iff_mul_le hk).1 this
        have : r ≤ L - 1 := Nat.le_pred_of_lt hrL
        omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hqL, ?_⟩
      have : (q * k + r) % k = r % k := by
        simpa [add_comm] using (Nat.add_mul_mod_self_right r q k)
      rwa [Nat.mod_eq_of_lt hr] at this
    · simp [hrL] at hq

lemma card_filter_mod (k L r : ℕ) (hk : 0 < k) (hr : r < k) :
    ((Finset.range L).filter (fun i => i % k = r)).card =
      if r < L then (L - 1 - r) / k + 1 else 0 := by
  rw [filter_mod_eq_image k L r hk hr, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    have : a * k = b * k := Nat.add_right_cancel hab
    exact Nat.mul_right_cancel hk this

lemma card_filter_mod_le_nine {k L r : ℕ} (hk : 0 < k) (hL : L ≤ 9 * k - 1) (hr : r < k) :
    ((Finset.range L).filter (fun i => i % k = r)).card ≤ 9 := by
  rw [card_filter_mod k L r hk hr]
  split_ifs with hrL
  · have : (L - 1 - r) / k ≤ 8 := by
      have : L - 1 - r ≤ k * 8 + (k - 1) := by
        have : 1 ≤ k := Nat.succ_le_of_lt hk
        have : 1 ≤ 9 * k := by omega
        omega
      exact (Nat.div_le_iff_le_mul_add_pred hk).2 this
    omega
  · omega

lemma card_filter_mod_high_le_eight {k L : ℕ} (hk : 0 < k) (hL : L ≤ 9 * k - 1) :
    ((Finset.range L).filter (fun i => i % k = k - 1)).card ≤ 8 := by
  have hr : k - 1 < k := Nat.sub_one_lt_of_lt hk
  rw [card_filter_mod k L (k - 1) hk hr]
  split_ifs with hrL
  · have heq : L - 1 - (k - 1) = L - k := by
      have : k ≤ L := by omega
      omega
    rw [heq]
    have : (L - k) / k ≤ 7 := by
      have : L - k ≤ k * 7 + (k - 1) := by
        have : 1 ≤ k := Nat.succ_le_of_lt hk
        omega
      exact (Nat.div_le_iff_le_mul_add_pred hk).2 this
    omega
  · omega

lemma S_le_of_short {k x : ℕ} (hk : 0 < k) (h01 : Is01 x)
    (hL : (Nat.digits 10 x).length ≤ 9 * k - 1) :
    ∑ r ∈ Finset.range k, countMod k x r * 10 ^ r ≤ 9 * 10 ^ (k - 1) - 1 := by
  have hterm : ∀ r ∈ Finset.range k,
      countMod k x r * 10 ^ r ≤ (if r = k - 1 then 8 else 9) * 10 ^ r := by
    intro r hr
    have hrk : r < k := Finset.mem_range.mp hr
    have hcnt := countMod_le_of_is01 (k := k) (x := x) (r := r) h01
    by_cases hlast : r = k - 1
    · subst r
      have := card_filter_mod_high_le_eight (L := (Nat.digits 10 x).length) hk hL
      have : countMod k x (k - 1) ≤ 8 := hcnt.trans this
      simp only [↓reduceIte]
      exact Nat.mul_le_mul_right _ this
    · have := card_filter_mod_le_nine (L := (Nat.digits 10 x).length) hk hL hrk
      have : countMod k x r ≤ 9 := hcnt.trans this
      simp only [hlast, ↓reduceIte]
      exact Nat.mul_le_mul_right _ this
  refine (Finset.sum_le_sum hterm).trans ?_
  have hval : ∑ r ∈ Finset.range k, (if r = k - 1 then 8 else 9) * 10 ^ r =
      9 * ∑ r ∈ Finset.range (k - 1), 10 ^ r + 8 * 10 ^ (k - 1) := by
    cases k with
    | zero => omega
    | succ k' =>
      simp only [Nat.add_one_sub_one]
      rw [Finset.sum_range_succ]
      simp only [↓reduceIte]
      have hrest :
          ∑ r ∈ Finset.range k', (if r = k' then 8 else 9) * 10 ^ r =
            ∑ r ∈ Finset.range k', 9 * 10 ^ r := by
        refine Finset.sum_congr rfl ?_
        intro r hr
        have : r ≠ k' := Nat.ne_of_lt (Finset.mem_range.mp hr)
        simp [this]
      rw [hrest, Finset.mul_sum]
  rw [hval, geom_sum_ten (k - 1),
    Nat.mul_div_cancel' (nine_dvd_ten_pow_sub_one (k - 1))]
  have : 1 ≤ 10 ^ (k - 1) := Nat.one_le_pow _ _ (by decide)
  omega

lemma S_lt_M_of_short {k x : ℕ} (hk : 0 < k) (h01 : Is01 x)
    (hL : (Nat.digits 10 x).length ≤ 9 * k - 1) :
    ∑ r ∈ Finset.range k, countMod k x r * 10 ^ r < 10 ^ k - 1 := by
  have hle := S_le_of_short hk h01 hL
  have hpow : 10 ^ k = 10 * 10 ^ (k - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hk]
    rw [pow_succ, mul_comm]
  have hlt0 : 9 * 10 ^ (k - 1) < 10 * 10 ^ (k - 1) :=
    Nat.mul_lt_mul_of_pos_right (by decide : 9 < 10) (pow_pos (by decide : 0 < 10) _)
  have hlt1 : 9 * 10 ^ (k - 1) < 10 ^ k := by
    rwa [hpow]
  have hpos : 1 ≤ 9 * 10 ^ (k - 1) := by
    have : 1 ≤ 10 ^ (k - 1) := Nat.one_le_pow _ _ (by decide)
    omega
  have hlt : 9 * 10 ^ (k - 1) - 1 < 10 ^ k - 1 :=
    Nat.sub_lt_sub_right hpos hlt1
  exact lt_of_le_of_lt hle hlt

lemma countMod_eq_zero_of_sum_eq_zero {k x : ℕ} (hk : 0 < k)
    (hS : ∑ r ∈ Finset.range k, countMod k x r * 10 ^ r = 0) {r : ℕ} (hr : r < k) :
    countMod k x r = 0 := by
  have hterm := (Finset.sum_eq_zero_iff.mp hS) r (Finset.mem_range.mpr hr)
  rcases Nat.mul_eq_zero.mp hterm with h | h
  · exact h
  · exact (pow_ne_zero r (by decide : (10 : ℕ) ≠ 0) h).elim

lemma digit10_le_countMod {k x i : ℕ} (hk : 0 < k)
    (hi : i < (Nat.digits 10 x).length) :
    digit10 x i ≤ countMod k x (i % k) := by
  unfold countMod
  have hmem : i ∈ Finset.range (Nat.digits 10 x).length := Finset.mem_range.mpr hi
  have := Finset.single_le_sum
    (f := fun j => if j % k = i % k then digit10 x j else 0)
    (fun _ _ => Nat.zero_le _) hmem
  simpa using this

lemma eq_zero_of_countMod_zero {k x : ℕ} (hk : 0 < k)
    (hS : ∑ r ∈ Finset.range k, countMod k x r * 10 ^ r = 0) : x = 0 := by
  rw [ofDigits_digits_sum x]
  refine Finset.sum_eq_zero ?_
  intro i hi
  have hcnt : countMod k x (i % k) = 0 :=
    countMod_eq_zero_of_sum_eq_zero hk hS (Nat.mod_lt i hk)
  have := digit10_le_countMod (k := k) hk (Finset.mem_range.mp hi)
  have : digit10 x i = 0 := by omega
  simp [this]

lemma no_short_01_multiple {k x : ℕ} (hk : 0 < k) (hpos : 0 < x) (h01 : Is01 x)
    (hdvd : (10 ^ k - 1) ∣ x) : 9 * k ≤ (Nat.digits 10 x).length := by
  by_contra h
  have hL : (Nat.digits 10 x).length ≤ 9 * k - 1 := by omega
  have hcong := is01_modEq_weighted (k := k) (x := x) hk
  rw [weighted_eq_countMod hk] at hcong
  have hSlt := S_lt_M_of_short hk h01 hL
  have hx0 : x % (10 ^ k - 1) = 0 := Nat.mod_eq_zero_of_dvd hdvd
  have hS0 : ∑ r ∈ Finset.range k, countMod k x r * 10 ^ r = 0 := by
    have : (∑ r ∈ Finset.range k, countMod k x r * 10 ^ r) % (10 ^ k - 1) =
        x % (10 ^ k - 1) := hcong.symm
    rw [hx0, Nat.mod_eq_of_lt hSlt] at this
    exact this
  exact Nat.ne_of_gt hpos (eq_zero_of_countMod_zero hk hS0)

lemma card_filter_mod_le_nine_exact {k L r : ℕ} (hk : 0 < k) (hL : L ≤ 9 * k) (hr : r < k) :
    ((Finset.range L).filter (fun i => i % k = r)).card ≤ 9 := by
  rw [card_filter_mod k L r hk hr]
  split_ifs with hrL
  · have : (L - 1 - r) / k ≤ 8 := by
      have : L - 1 - r ≤ k * 8 + (k - 1) := by
        have : 1 ≤ k := Nat.succ_le_of_lt hk
        omega
      exact (Nat.div_le_iff_le_mul_add_pred hk).2 this
    omega
  · omega

lemma S_le_M_of_len_le_ninek {k x : ℕ} (hk : 0 < k) (h01 : Is01 x)
    (hL : (Nat.digits 10 x).length ≤ 9 * k) :
    ∑ r ∈ Finset.range k, countMod k x r * 10 ^ r ≤ 10 ^ k - 1 := by
  have hterm : ∀ r ∈ Finset.range k, countMod k x r ≤ 9 := by
    intro r hr
    exact (countMod_le_of_is01 h01).trans
      (card_filter_mod_le_nine_exact hk hL (Finset.mem_range.mp hr))
  have : ∑ r ∈ Finset.range k, countMod k x r * 10 ^ r ≤
      ∑ r ∈ Finset.range k, 9 * 10 ^ r := by
    exact Finset.sum_le_sum fun r hr => Nat.mul_le_mul_right _ (hterm r hr)
  refine this.trans ?_
  rw [← Finset.mul_sum, geom_sum_ten, Nat.mul_div_cancel' (nine_dvd_ten_pow_sub_one k)]

lemma all_countMod_eq_nine {k x : ℕ} (hk : 0 < k)
    (hS : ∑ r ∈ Finset.range k, countMod k x r * 10 ^ r = 10 ^ k - 1)
    (hcnt : ∀ r ∈ Finset.range k, countMod k x r ≤ 9) :
    ∀ r ∈ Finset.range k, countMod k x r = 9 := by
  have hle : ∑ r ∈ Finset.range k, countMod k x r * 10 ^ r ≤
      ∑ r ∈ Finset.range k, 9 * 10 ^ r :=
    Finset.sum_le_sum fun r hr => Nat.mul_le_mul_right _ (hcnt r hr)
  have heqsum : ∑ r ∈ Finset.range k, 9 * 10 ^ r = 10 ^ k - 1 := by
    rw [← Finset.mul_sum, geom_sum_ten, Nat.mul_div_cancel' (nine_dvd_ten_pow_sub_one k)]
  have hEq : ∑ r ∈ Finset.range k, countMod k x r * 10 ^ r =
      ∑ r ∈ Finset.range k, 9 * 10 ^ r := by
    rw [hS, heqsum]
  have hterm : ∀ r ∈ Finset.range k, countMod k x r * 10 ^ r = 9 * 10 ^ r :=
    (Finset.sum_eq_sum_iff_of_le (fun r hr => Nat.mul_le_mul_right _ (hcnt r hr))).1 hEq
  intro r hr
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (by decide : 0 < 10) r) (hterm r hr)

lemma digits_length_ge_iff (x L : ℕ) (hL : 0 < L) :
    L ≤ (Nat.digits 10 x).length ↔ 10 ^ (L - 1) ≤ x := by
  by_cases hx : x = 0
  · subst x
    simp only [digits_zero, List.length_nil]
    constructor
    · intro h; omega
    · intro h
      have : 1 ≤ 10 ^ (L - 1) := Nat.one_le_pow _ _ (by decide)
      omega
  · have hb : 1 < 10 := by decide
    constructor
    · intro hlen
      have : ¬ (Nat.digits 10 x).length ≤ L - 1 := by omega
      have := (Nat.digits_length_le_iff hb x).not.mp this
      omega
    · intro hxge
      have : ¬ x < 10 ^ (L - 1) := by omega
      have := (Nat.digits_length_le_iff hb x).not.mpr this
      omega

lemma digits_eq_one_of_full {k x : ℕ} (hk : 0 < k) (h01 : Is01 x)
    (hlen : (Nat.digits 10 x).length = 9 * k)
    (hcnt : ∀ r ∈ Finset.range k, countMod k x r = 9) :
    ∀ i ∈ Finset.range (9 * k), digit10 x i = 1 := by
  intro i hi
  have hr : i % k < k := Nat.mod_lt i hk
  have hsum9 : countMod k x (i % k) = 9 := hcnt _ (Finset.mem_range.mpr hr)
  have hcard : ((Finset.range (9 * k)).filter (fun j => j % k = i % k)).card = 9 := by
    rw [card_filter_mod k (9 * k) (i % k) hk hr]
    have : i % k < 9 * k := lt_of_lt_of_le hr (by nlinarith)
    simp only [if_pos this]
    have heq : 9 * k - 1 - i % k = (k - 1 - i % k) + 8 * k := by
      have : 1 ≤ k := Nat.succ_le_of_lt hk
      omega
    rw [heq, Nat.add_mul_div_right _ _ hk]
    have : (k - 1 - i % k) / k = 0 :=
      Nat.div_eq_of_lt (by omega)
    omega
  have hsum' :
      ∑ j ∈ (Finset.range (9 * k)).filter (fun j => j % k = i % k), digit10 x j =
        countMod k x (i % k) := by
    unfold countMod
    rw [hlen, Finset.sum_filter]
  have hsumEq : ∑ j ∈ (Finset.range (9 * k)).filter (fun j => j % k = i % k),
      digit10 x j = 9 := by
    rw [hsum', hsum9]
  have himem : i ∈ (Finset.range (9 * k)).filter (fun j => j % k = i % k) := by
    exact Finset.mem_filter.mpr ⟨hi, rfl⟩
  by_contra hne
  have h0 : digit10 x i = 0 := by
    rcases h01.digit10_le_one i with h0 | h1
    · exact h0
    · exact (hne h1).elim
  have hle1 : ∀ j ∈ (Finset.range (9 * k)).filter (fun j => j % k = i % k),
      digit10 x j ≤ 1 := by
    intro j hj
    rcases h01.digit10_le_one j with h0' | h1'
    · simp [h0']
    · simp [h1']
  have : ∑ j ∈ ((Finset.range (9 * k)).filter (fun j => j % k = i % k)).erase i,
      digit10 x j ≤ 8 := by
    have hcard' :
        (((Finset.range (9 * k)).filter (fun j => j % k = i % k)).erase i).card = 8 := by
      rw [Finset.card_erase_of_mem himem, hcard]
    have hle' : ∀ j ∈ ((Finset.range (9 * k)).filter (fun j => j % k = i % k)).erase i,
        digit10 x j ≤ 1 := fun j hj => hle1 j (Finset.mem_of_mem_erase hj)
    have := Finset.sum_le_card_nsmul _ (fun j => digit10 x j) 1 hle'
    simpa [hcard'] using this
  have hsplit := Finset.sum_erase_add
    ((Finset.range (9 * k)).filter (fun j => j % k = i % k)) (fun j => digit10 x j) himem
  have : ∑ j ∈ ((Finset.range (9 * k)).filter (fun j => j % k = i % k)).erase i,
      digit10 x j + digit10 x i = 9 := by
    rw [hsplit, hsumEq]
  omega

lemma eq_repunit_of_full_digits {k x : ℕ} (hk : 0 < k) (h01 : Is01 x)
    (hlen : (Nat.digits 10 x).length = 9 * k)
    (hcnt : ∀ r ∈ Finset.range k, countMod k x r = 9) :
    x = (10 ^ (9 * k) - 1) / 9 := by
  have hall := digits_eq_one_of_full hk h01 hlen hcnt
  have hx := ofDigits_digits_sum x
  rw [hlen] at hx
  have : ∀ i ∈ Finset.range (9 * k), digit10 x i * 10 ^ i = 10 ^ i := by
    intro i hi
    simp [hall i hi]
  rw [Finset.sum_congr rfl this, geom_sum_ten] at hx
  exact hx

lemma A004290_nine_ones {k : ℕ} (hk : 0 < k) :
    A004290 (10 ^ k - 1) = (10 ^ (9 * k) - 1) / 9 := by
  apply le_antisymm
  · exact A004290_repunit_le hk
  · set M := 10 ^ k - 1
    set R := (10 ^ (9 * k) - 1) / 9
    have hRmem : R ∈ A004290Set M :=
      ⟨repunit_pos (9 * k) (by omega), dvd_repunit_nine hk, Is01.repunit (9 * k)⟩
    have hne : (A004290Set M).Nonempty := ⟨_, hRmem⟩
    have hmem := Nat.sInf_mem hne
    rw [A004290_eq]
    set x := sInf (A004290Set M)
    have hlen : 9 * k ≤ (Nat.digits 10 x).length :=
      no_short_01_multiple hk hmem.1 hmem.2.2 hmem.2.1
    have hxpos : x ≠ 0 := Nat.pos_iff_ne_zero.mp hmem.1
    by_cases hlong : 9 * k < (Nat.digits 10 x).length
    · have hxge : 10 ^ (9 * k) ≤ x := by
        have := (digits_length_ge_iff x (9 * k + 1) (by omega)).mp (by omega)
        simpa [Nat.add_sub_cancel] using this
      have hRlt : R < 10 ^ (9 * k) := by
        rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 9)]
        have : 10 ^ (9 * k) ≤ 9 * 10 ^ (9 * k) :=
          Nat.le_mul_of_pos_left _ (by decide : 0 < 9)
        have : 1 ≤ 10 ^ (9 * k) := Nat.one_le_pow _ _ (by decide)
        omega
      exact le_of_lt (lt_of_lt_of_le hRlt hxge)
    · have hlenEq : (Nat.digits 10 x).length = 9 * k := by omega
      have hcong := is01_modEq_weighted (k := k) (x := x) hk
      rw [weighted_eq_countMod hk] at hcong
      have hSle := S_le_M_of_len_le_ninek hk hmem.2.2 (by omega)
      have hx0 : x % M = 0 := Nat.mod_eq_zero_of_dvd hmem.2.1
      have hSmod : (∑ r ∈ Finset.range k, countMod k x r * 10 ^ r) % M = 0 := by
        have : (∑ r ∈ Finset.range k, countMod k x r * 10 ^ r) % M = x % M := hcong.symm
        rwa [this]
      have hcases : ∑ r ∈ Finset.range k, countMod k x r * 10 ^ r = 0 ∨
          ∑ r ∈ Finset.range k, countMod k x r * 10 ^ r = M := by
        rcases lt_or_eq_of_le hSle with hlt | heq
        · left
          rwa [Nat.mod_eq_of_lt hlt] at hSmod
        · right
          exact heq
      rcases hcases with hS0 | hSM
      · exact (hxpos (eq_zero_of_countMod_zero hk hS0)).elim
      · have hcntle : ∀ r ∈ Finset.range k, countMod k x r ≤ 9 := by
          intro r hr
          exact (countMod_le_of_is01 hmem.2.2).trans
            (card_filter_mod_le_nine_exact hk (by omega) (Finset.mem_range.mp hr))
        have hcnt := all_countMod_eq_nine hk (by
          change ∑ r ∈ Finset.range k, countMod k x r * 10 ^ r = 10 ^ k - 1
          exact hSM) hcntle
        exact (eq_repunit_of_full_digits hk hmem.2.2 hlenEq hcnt).symm.le

lemma Is01.mul_ten {x : ℕ} (hx : 0 < x) (h01 : Is01 x) : Is01 (10 * x) := by
  intro d hd
  have hdig := Nat.digits_base_mul (b := 10) (m := x) (by decide) hx
  rw [hdig] at hd
  simp only [List.mem_cons] at hd
  rcases hd with h0 | hmem
  · exact Or.inl h0
  · exact h01 d hmem

lemma Is01.mul_ten_pow {x t : ℕ} (hx : 0 < x) (h01 : Is01 x) : Is01 (x * 10 ^ t) := by
  induction t with
  | zero => simpa
  | succ t ih =>
    rw [pow_succ, ← mul_assoc]
    have hx' : 0 < x * 10 ^ t := mul_pos hx (pow_pos (by decide) _)
    simpa [mul_comm (10 ^ t), mul_left_comm, mul_assoc] using
      (Is01.mul_ten hx' ih)

lemma digits_mul_ten {x : ℕ} (hx : 0 < x) :
    Nat.digits 10 (10 * x) = 0 :: Nat.digits 10 x :=
  Nat.digits_base_mul (b := 10) (m := x) (by decide) hx

lemma last_digit_of_is01 {x : ℕ} (hx : 0 < x) (h01 : Is01 x) :
    x % 10 = 0 ∨ x % 10 = 1 := by
  have hhead : (Nat.digits 10 x).head! = x % 10 :=
    Nat.head!_digits (b := 10) (n := x) (by decide)
  have hne : Nat.digits 10 x ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (Nat.ne_of_gt hx)
  have hmem : (Nat.digits 10 x).head! ∈ Nat.digits 10 x := List.head!_mem_self hne
  have := h01 _ hmem
  rwa [hhead] at this

lemma ten_dvd_of_even_and_five {x : ℕ} (h2 : 2 ∣ x) (h5 : 5 ∣ x) : 10 ∣ x := by
  have : Nat.lcm 2 5 ∣ x := Nat.lcm_dvd h2 h5
  simpa [Nat.lcm_comm] using this

lemma not_two_dvd_of_is01_odd {x : ℕ} (hx : 0 < x) (h01 : Is01 x) (hlast : x % 10 = 1) :
    ¬ 2 ∣ x := by
  intro h
  have : x % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
  have : x % 2 = 1 := by
    have : x % 10 % 2 = 1 := by simp [hlast]
    rwa [Nat.mod_mod_of_dvd x (by decide : 2 ∣ 10)] at this
  omega

lemma not_five_dvd_of_is01_end_one {x : ℕ} (hx : 0 < x) (h01 : Is01 x) (hlast : x % 10 = 1) :
    ¬ 5 ∣ x := by
  intro h
  have : x % 5 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
  have : x % 5 = 1 := by
    have : x % 10 % 5 = 1 := by simp [hlast]
    rwa [Nat.mod_mod_of_dvd x (by decide : 5 ∣ 10)] at this
  omega

/-- Removing a factor of `10` from a 0-1 number preserves the 0-1 property. -/
lemma Is01.of_mul_ten {x : ℕ} (h01 : Is01 (10 * x)) : Is01 x := by
  by_cases hx : x = 0
  · subst x; exact Is01.zero
  · intro d hd
    have hxpos : 0 < x := Nat.pos_of_ne_zero hx
    have hdig := digits_mul_ten hxpos
    have : d ∈ Nat.digits 10 (10 * x) := by
      rw [hdig]; exact List.mem_cons_of_mem _ hd
    exact h01 d this

lemma padic_le_of_trailing {x t : ℕ} (hx : 0 < x) (h01 : Is01 x)
    (h10 : ¬ 10 ∣ x) : padicValNat 2 x = 0 ∧ padicValNat 5 x = 0 := by
  have hlast := last_digit_of_is01 hx h01
  rcases hlast with h0 | h1
  · exact (h10 (Nat.dvd_iff_mod_eq_zero.mpr h0)).elim
  · refine ⟨?_, ?_⟩
    · rw [padicValNat.eq_zero_iff]
      exact Or.inr (Or.inr (not_two_dvd_of_is01_odd hx h01 h1))
    · rw [padicValNat.eq_zero_iff]
      exact Or.inr (Or.inr (not_five_dvd_of_is01_end_one hx h01 h1))

lemma Is01.of_mul_ten_pow {x t : ℕ} (h01 : Is01 (x * 10 ^ t)) : Is01 x := by
  induction t with
  | zero => simpa using h01
  | succ t ih =>
    rw [pow_succ, ← mul_assoc] at h01
    have : Is01 (x * 10 ^ t) :=
      Is01.of_mul_ten (x := x * 10 ^ t)
        (by simpa [mul_comm, mul_left_comm, mul_assoc] using h01)
    exact ih this

/-- Every positive 0-1 number factors as a 0-1 number not divisible by 10,
times a power of 10. -/
lemma exists_strip_ten {x : ℕ} (hx : 0 < x) (h01 : Is01 x) :
    ∃ y s, x = y * 10 ^ s ∧ 0 < y ∧ Is01 y ∧ ¬ 10 ∣ y := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
    by_cases h10 : 10 ∣ x
    · obtain ⟨x', rfl⟩ := h10
      have hx'pos : 0 < x' := by
        have : 0 < 10 * x' := hx
        omega
      have h01' : Is01 x' := Is01.of_mul_ten (by simpa [mul_comm] using h01)
      have hlt : x' < 10 * x' := by nlinarith
      obtain ⟨y, s, hy, hypos, hy01, hydvd⟩ := ih x' hlt hx'pos h01'
      refine ⟨y, s + 1, ?_, hypos, hy01, hydvd⟩
      rw [hy, pow_succ]
      ring
    · exact ⟨x, 0, by simp, hx, h01, h10⟩

lemma last_digit_one_of_not_ten_dvd {y : ℕ} (hy : 0 < y) (h01 : Is01 y) (h10 : ¬ 10 ∣ y) :
    y % 10 = 1 := by
  rcases last_digit_of_is01 hy h01 with h0 | h1
  · exact (h10 (Nat.dvd_iff_mod_eq_zero.mpr h0)).elim
  · exact h1

lemma not_two_dvd_of_not_ten_dvd_is01 {y : ℕ} (hy : 0 < y) (h01 : Is01 y) (h10 : ¬ 10 ∣ y) :
    ¬ 2 ∣ y :=
  not_two_dvd_of_is01_odd hy h01 (last_digit_one_of_not_ten_dvd hy h01 h10)

lemma not_five_dvd_of_not_ten_dvd_is01 {y : ℕ} (hy : 0 < y) (h01 : Is01 y) (h10 : ¬ 10 ∣ y) :
    ¬ 5 ∣ y :=
  not_five_dvd_of_is01_end_one hy h01 (last_digit_one_of_not_ten_dvd hy h01 h10)

lemma A004290_one : A004290 1 = 1 := by
  apply le_antisymm
  · exact A004290_le (by decide : 0 < 1) dvd_rfl Is01.one
  · have hne : (A004290Set 1).Nonempty := ⟨1, ⟨by decide, dvd_rfl, Is01.one⟩⟩
    have hmem := Nat.sInf_mem hne
    rw [A004290_eq]
    exact Nat.le_of_dvd hmem.1 hmem.2.1

lemma repunit_sub {i j : ℕ} (hij : i ≤ j) :
    (10 ^ j - 1) / 9 - (10 ^ i - 1) / 9 = 10 ^ i * ((10 ^ (j - i) - 1) / 9) := by
  set Rj := (10 ^ j - 1) / 9
  set Ri := (10 ^ i - 1) / 9
  set Rd := (10 ^ (j - i) - 1) / 9
  have h9 : 0 < 9 := by decide
  have hj : Rj * 9 = 10 ^ j - 1 := Nat.div_mul_cancel (nine_dvd_ten_pow_sub_one j)
  have hi : Ri * 9 = 10 ^ i - 1 := Nat.div_mul_cancel (nine_dvd_ten_pow_sub_one i)
  have hd : Rd * 9 = 10 ^ (j - i) - 1 := Nat.div_mul_cancel (nine_dvd_ten_pow_sub_one (j - i))
  have hmul : (Rj - Ri) * 9 = 10 ^ i * Rd * 9 := by
    have h1i : 1 ≤ 10 ^ i := Nat.one_le_pow _ _ (by decide)
    have h1j : 1 ≤ 10 ^ j := Nat.one_le_pow _ _ (by decide)
    have h1d : 1 ≤ 10 ^ (j - i) := Nat.one_le_pow _ _ (by decide)
    have hji : i + (j - i) = j := Nat.add_sub_of_le hij
    have hleRi : Ri ≤ Rj := by
      apply Nat.div_le_div_right
      exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide : 0 < 10) hij) 1
    calc (Rj - Ri) * 9
        = Rj * 9 - Ri * 9 := Nat.mul_sub_right_distrib _ _ _
      _ = (10 ^ j - 1) - (10 ^ i - 1) := by rw [hj, hi]
      _ = 10 ^ j - 10 ^ i := by omega
      _ = 10 ^ i * 10 ^ (j - i) - 10 ^ i := by rw [← pow_add, hji]
      _ = 10 ^ i * 10 ^ (j - i) - 10 ^ i * 1 := by rw [mul_one]
      _ = 10 ^ i * (10 ^ (j - i) - 1) := (Nat.mul_sub_left_distrib _ _ _).symm
      _ = 10 ^ i * (Rd * 9) := by rw [hd]
      _ = 10 ^ i * Rd * 9 := by rw [mul_assoc]
  exact Nat.eq_of_mul_eq_mul_right h9 hmul

lemma exists_01_multiple_of_coprime {m : ℕ} (hm : Nat.Coprime m 10) (hmpos : 0 < m) :
    ∃ x, 0 < x ∧ m ∣ x ∧ Is01 x := by
  let R : ℕ → ℕ := fun l => (10 ^ l - 1) / 9
  let s : Finset ℕ := Finset.range (m + 1)
  let t : Finset ℕ := Finset.range m
  have hmaps : Set.MapsTo (fun i : ℕ => R i % m) s t := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.mod_lt _ hmpos)
  have hcard : t.card < s.card := by
    simp [s, t, Finset.card_range]
  obtain ⟨a, ha, b, hb, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  wlog hab : a < b generalizing a b
  · exact this b hb a ha hne.symm heq.symm (lt_of_le_of_ne (le_of_not_gt hab) hne.symm)
  have hsub : R b - R a = 10 ^ a * R (b - a) :=
    repunit_sub (Nat.le_of_lt hab)
  have hmod : R b ≡ R a [MOD m] := by
    rw [Nat.ModEq, heq]
  have hdvd : m ∣ R b - R a := (Nat.modEq_iff_dvd' (by
    have : a ≤ b := Nat.le_of_lt hab
    unfold R
    apply Nat.div_le_div_right
    exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide : 0 < 10) this) 1)).1
      (hmod.symm)
  rw [hsub] at hdvd
  have hcop : Nat.Coprime m (10 ^ a) := by
    simpa using (Nat.Coprime.pow_right a hm)
  have hR : m ∣ R (b - a) := (hcop.dvd_mul_left).1 hdvd
  have hpos : 0 < R (b - a) := by
    have hba : 0 < b - a := Nat.sub_pos_of_lt hab
    exact repunit_pos (b - a) hba
  exact ⟨R (b - a), hpos, hR, Is01.repunit (b - a)⟩

lemma A004290Set_nonempty_of_coprime {m : ℕ} (hm : Nat.Coprime m 10) (hmpos : 0 < m) :
    (A004290Set m).Nonempty := by
  obtain ⟨x, hxpos, hxdvd, hx01⟩ := exists_01_multiple_of_coprime hm hmpos
  exact ⟨x, hxpos, hxdvd, hx01⟩

lemma A004290_pos_of_coprime {m : ℕ} (hm : Nat.Coprime m 10) (hmpos : 0 < m) :
    0 < A004290 m := by
  have hne := A004290Set_nonempty_of_coprime hm hmpos
  have hmem := Nat.sInf_mem hne
  rw [A004290_eq]
  exact hmem.1

lemma A004290_mem_of_pos {n : ℕ} (h : 0 < A004290 n) :
    A004290 n ∈ A004290Set n := by
  have hne : (A004290Set n).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    rw [A004290_eq, hempty] at h
    simp at h
  rw [A004290_eq]
  exact Nat.sInf_mem hne

lemma A004290_le_of_dvd_of_pos {m n : ℕ} (h : m ∣ n) (hpos : 0 < A004290 n) :
    A004290 m ≤ A004290 n := by
  have hmem := A004290_mem_of_pos hpos
  exact A004290_le hmem.1 (h.trans hmem.2.1) hmem.2.2

lemma ten_pow_eq_two_five (t : ℕ) : 10 ^ t = 2 ^ t * 5 ^ t := by
  rw [← mul_pow]; rfl

lemma pow_max_eq (a b : ℕ) : 2 ^ max a b * 5 ^ max a b = 10 ^ max a b :=
  (ten_pow_eq_two_five (max a b)).symm

lemma two_pow_le_of_dvd_mul {a s y z : ℕ}
    (h2y : ¬ 2 ∣ y) (hdvd : 2 ^ a ∣ y * 2 ^ s * z) (h2z : ¬ 2 ∣ z) : a ≤ s := by
  have hz' : ¬ 2 ∣ (y * z) := by
    intro h
    rcases (Nat.prime_two.dvd_mul).1 h with hy | hz
    · exact h2y hy
    · exact h2z hz
  have : 2 ^ a ∣ (y * z) * 2 ^ s := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hdvd
  have hcop : Nat.Coprime (2 ^ a) (y * z) := by
    cases a with
    | zero => simp
    | succ a =>
      have : Nat.Coprime 2 (y * z) := (Nat.prime_two.coprime_iff_not_dvd).2 hz'
      simpa using this.pow_left (a + 1)
  have : 2 ^ a ∣ 2 ^ s := (hcop.dvd_mul_left).1 (by simpa [mul_comm] using this)
  exact (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).1 this

lemma five_pow_le_of_dvd_mul {b s y z : ℕ}
    (h5y : ¬ 5 ∣ y) (hdvd : 5 ^ b ∣ y * 5 ^ s * z) (h5z : ¬ 5 ∣ z) : b ≤ s := by
  have hz' : ¬ 5 ∣ (y * z) := by
    intro h
    rcases (Nat.prime_five.dvd_mul).1 h with hy | hz
    · exact h5y hy
    · exact h5z hz
  have : 5 ^ b ∣ (y * z) * 5 ^ s := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hdvd
  have hcop : Nat.Coprime (5 ^ b) (y * z) := by
    cases b with
    | zero => simp
    | succ b =>
      have : Nat.Coprime 5 (y * z) := (Nat.prime_five.coprime_iff_not_dvd).2 hz'
      simpa using this.pow_left (b + 1)
  have : 5 ^ b ∣ 5 ^ s := (hcop.dvd_mul_left).1 (by simpa [mul_comm] using this)
  exact (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 5)).1 this

lemma two_five_dvd_ten_pow {a b t : ℕ} (ha : a ≤ t) (hb : b ≤ t) :
    2 ^ a * 5 ^ b ∣ 10 ^ t := by
  have : 2 ^ a * 5 ^ b ∣ 2 ^ t * 5 ^ t :=
    Nat.mul_dvd_mul (pow_dvd_pow _ ha) (pow_dvd_pow _ hb)
  rwa [← ten_pow_eq_two_five] at this

lemma not_two_dvd_five_pow (s : ℕ) : ¬ 2 ∣ 5 ^ s := by
  intro h
  have hcop : Nat.Coprime 2 5 := by decide
  have hg : Nat.gcd 2 (5 ^ s) = 1 := hcop.pow_right s
  have : 2 ∣ Nat.gcd 2 (5 ^ s) := Nat.dvd_gcd dvd_rfl h
  rw [hg] at this
  omega

lemma not_five_dvd_two_pow (s : ℕ) : ¬ 5 ∣ 2 ^ s := by
  intro h
  have hcop : Nat.Coprime 5 2 := by decide
  have hg : Nat.gcd 5 (2 ^ s) = 1 := hcop.pow_right s
  have : 5 ∣ Nat.gcd 5 (2 ^ s) := Nat.dvd_gcd dvd_rfl h
  rw [hg] at this
  omega

lemma A004290_of_two_five_mul {a b m : ℕ} (hm : Nat.Coprime m 10) :
    A004290 (2 ^ a * 5 ^ b * m) = A004290 m * 10 ^ max a b := by
  set t := max a b with ht
  set n := 2 ^ a * 5 ^ b * m
  have hm0 : m ≠ 0 := by
    intro h; subst h; exact (by decide : ¬ Nat.Coprime 0 10) hm
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hypos : 0 < A004290 m := A004290_pos_of_coprime hm hmpos
  have hmem_m := A004290_mem_of_pos hypos
  have ha : a ≤ t := Nat.le_max_left a b
  have hb : b ≤ t := Nat.le_max_right a b
  have hpow_dvd : 2 ^ a * 5 ^ b ∣ 10 ^ t := two_five_dvd_ten_pow ha hb
  have hn_dvd_witness : n ∣ A004290 m * 10 ^ t := by
    have : 2 ^ a * 5 ^ b * m ∣ 10 ^ t * A004290 m :=
      Nat.mul_dvd_mul hpow_dvd hmem_m.2.1
    simpa [n, mul_comm, mul_left_comm, mul_assoc] using this
  apply le_antisymm
  · exact A004290_le (mul_pos hypos (pow_pos (by decide : 0 < 10) t))
      hn_dvd_witness (Is01.mul_ten_pow hypos hmem_m.2.2)
  · have hne : (A004290Set n).Nonempty :=
      ⟨A004290 m * 10 ^ t,
        mul_pos hypos (pow_pos (by decide) t), hn_dvd_witness,
        Is01.mul_ten_pow hypos hmem_m.2.2⟩
    have hxpos : 0 < A004290 n := by
      have hmem := Nat.sInf_mem hne
      rw [A004290_eq]; exact hmem.1
    have hxn := A004290_mem_of_pos hxpos
    obtain ⟨y, s, hyeq, hypos', hy01, hy10⟩ := exists_strip_ten hxn.1 hxn.2.2
    have h2y : ¬ 2 ∣ y := not_two_dvd_of_not_ten_dvd_is01 hypos' hy01 hy10
    have h5y : ¬ 5 ∣ y := not_five_dvd_of_not_ten_dvd_is01 hypos' hy01 hy10
    have hndvd : n ∣ y * 10 ^ s := by rw [← hyeq]; exact hxn.2.1
    have hm_y : m ∣ y := by
      have : m ∣ y * 10 ^ s :=
        (dvd_mul_left m (2 ^ a * 5 ^ b)).trans (by simpa [n, mul_assoc] using hndvd)
      have hcop : Nat.Coprime m (10 ^ s) := hm.pow_right s
      exact (hcop.dvd_mul_left).1 (by simpa [mul_comm] using this)
    have h10s : 10 ^ s = 2 ^ s * 5 ^ s := ten_pow_eq_two_five s
    have ha_le : a ≤ s := by
      have h2n : 2 ^ a ∣ n := ⟨5 ^ b * m, by simp [n, mul_assoc]⟩
      have : 2 ^ a ∣ y * 10 ^ s := h2n.trans hndvd
      have : 2 ^ a ∣ y * 2 ^ s * 5 ^ s := by
        simpa [h10s, mul_assoc] using this
      exact two_pow_le_of_dvd_mul h2y this (not_two_dvd_five_pow s)
    have hb_le : b ≤ s := by
      have h5n : 5 ^ b ∣ n := ⟨2 ^ a * m, by simp [n]; ring⟩
      have : 5 ^ b ∣ y * 10 ^ s := h5n.trans hndvd
      have : 5 ^ b ∣ y * 5 ^ s * 2 ^ s := by
        simpa [h10s, mul_assoc, mul_left_comm, mul_comm] using this
      exact five_pow_le_of_dvd_mul h5y this (not_five_dvd_two_pow s)
    have ht_le : t ≤ s := max_le ha_le hb_le
    have hmul : A004290 m ≤ y * 10 ^ (s - t) :=
      A004290_le (mul_pos hypos' (pow_pos (by decide) _))
        (dvd_mul_of_dvd_left hm_y _) (Is01.mul_ten_pow hypos' hy01)
    have : A004290 m * 10 ^ t ≤ y * 10 ^ s := by
      have := Nat.mul_le_mul_right (10 ^ t) hmul
      rwa [mul_assoc, ← pow_add, Nat.sub_add_cancel ht_le] at this
    simpa [hyeq] using this

lemma A004290_two_pow_five_pow {a b : ℕ} :
    A004290 (2 ^ a * 5 ^ b) = 10 ^ max a b := by
  have h := A004290_of_two_five_mul (a := a) (b := b) (m := 1) (by decide)
  simpa [A004290_one] using h

lemma A004290_mul_ten_pow {m t : ℕ} (hm : Nat.Coprime m 10) :
    A004290 (m * 2 ^ t * 5 ^ t) = A004290 m * 10 ^ t := by
  simpa [max_self, mul_left_comm, mul_assoc, mul_comm] using
    (A004290_of_two_five_mul (a := t) (b := t) (m := m) hm)

lemma exists_two_five_factor :
    ∀ n : ℕ, ∃ a b m, n = 2 ^ a * 5 ^ b * m ∧ (n = 0 ∨ Nat.Coprime m 10) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · exact ⟨0, 0, 0, by simp [hn0], Or.inl hn0⟩
    by_cases h2 : 2 ∣ n
    · obtain ⟨n', rfl⟩ := h2
      have hn' : n' < 2 * n' := by
        have : 0 < n' := by
          have : 0 < 2 * n' := Nat.pos_of_ne_zero hn0
          omega
        omega
      obtain ⟨a, b, m, heq, hm⟩ := ih n' hn'
      refine ⟨a + 1, b, m, ?_, ?_⟩
      · rw [heq, pow_succ, mul_assoc, mul_left_comm (2 ^ a)]
        ring
      · rcases hm with h0 | hcop
        · left; subst h0; simp
        · exact Or.inr hcop
    · by_cases h5 : 5 ∣ n
      · obtain ⟨n', rfl⟩ := h5
        have hn' : n' < 5 * n' := by
          have : 0 < n' := by
            have : 0 < 5 * n' := Nat.pos_of_ne_zero hn0
            omega
          nlinarith
        obtain ⟨a, b, m, heq, hm⟩ := ih n' hn'
        refine ⟨a, b + 1, m, ?_, ?_⟩
        · rw [heq, pow_succ]
          ring
        · rcases hm with h0 | hcop
          · left; subst h0; simp
          · exact Or.inr hcop
      · refine ⟨0, 0, n, by simp, Or.inr ?_⟩
        have h2c : Nat.Coprime n 2 := ((Nat.prime_two.coprime_iff_not_dvd).2 h2).symm
        have h5c : Nat.Coprime n 5 := ((Nat.prime_five.coprime_iff_not_dvd).2 h5).symm
        exact h2c.mul_right h5c

lemma exists_two_five_factor_pos {n : ℕ} (hn : n ≠ 0) :
    ∃ a b m, n = 2 ^ a * 5 ^ b * m ∧ Nat.Coprime m 10 := by
  obtain ⟨a, b, m, heq, hm⟩ := exists_two_five_factor n
  exact ⟨a, b, m, heq, hm.resolve_left hn⟩

lemma repunit_lt_pow (l : ℕ) : (10 ^ l - 1) / 9 < 10 ^ l := by
  have hpos : 0 < 9 := by decide
  rw [Nat.div_lt_iff_lt_mul hpos]
  have : 1 ≤ 10 ^ l := Nat.one_le_pow _ _ (by decide)
  omega

lemma pow_le_repunit {l : ℕ} (hl : 0 < l) : 10 ^ (l - 1) ≤ (10 ^ l - 1) / 9 := by
  have h9 : 0 < 9 := by decide
  rw [Nat.le_div_iff_mul_le h9]
  have hpow : 10 ^ l = 10 * 10 ^ (l - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hl]
    rw [pow_succ, mul_comm]
  rw [hpow]
  have : 1 ≤ 10 ^ (l - 1) := Nat.one_le_pow _ _ (by decide)
  omega

lemma pow_lt_repunit {l : ℕ} (hl : 1 < l) : 10 ^ (l - 1) < (10 ^ l - 1) / 9 := by
  have h9 : 0 < 9 := by decide
  have hpow : 10 ^ l = 10 * 10 ^ (l - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 0 < l)]
    rw [pow_succ, mul_comm]
  have hb : 1 < 10 ^ (l - 1) := (Nat.one_lt_pow_iff (by omega)).2 (by decide)
  have hmul : 9 * 10 ^ (l - 1) < 10 ^ l - 1 := by
    have : 9 * 10 ^ (l - 1) + 1 < 10 ^ l := by rw [hpow]; omega
    have h1 : 1 ≤ 10 ^ l := Nat.one_le_pow _ _ (by decide)
    omega
  have hy : 9 ∣ 10 ^ l - 1 := nine_dvd_ten_pow_sub_one l
  have hmul' : 10 ^ (l - 1) * 9 < (10 ^ l - 1) / 9 * 9 := by
    rw [Nat.div_mul_cancel hy, mul_comm]
    exact hmul
  exact Nat.lt_of_mul_lt_mul_right hmul'

lemma A004290_lt_of_witness {n x R : ℕ} (hpos : 0 < x) (hdvd : n ∣ x)
    (h01 : Is01 x) (hlt : x < R) : A004290 n < R :=
  lt_of_le_of_lt (A004290_le hpos hdvd h01) hlt

lemma two_pow_four_mul {k : ℕ} (hk : 0 < k) : 10 ^ k < 2 ^ (4 * k) := by
  have h : 10 ^ k < 16 ^ k := Nat.pow_lt_pow_left (by decide : 10 < 16) (Nat.pos_iff_ne_zero.mp hk)
  have heq : 16 ^ k = (2 ^ 4) ^ k := by simp
  rw [heq, ← pow_mul] at h
  simpa [mul_comm] using h

lemma t_lt_four_mul {t k : ℕ} (hk : 0 < k) (ht : 2 ^ t < 10 ^ k) : t < 4 * k := by
  by_contra h
  have : 4 * k ≤ t := by omega
  have : 2 ^ (4 * k) ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) this
  have : 10 ^ k < 2 ^ (4 * k) := two_pow_four_mul hk
  omega

lemma ten_pow_t_lt_repunit {t k : ℕ} (hk : 0 < k) (ht : t < 9 * k) :
    10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  have hle : t ≤ 9 * k - 1 := by omega
  rcases lt_or_eq_of_le hle with hlt | heq
  · have : 10 ^ t < 10 ^ (9 * k - 1) := Nat.pow_lt_pow_right (by decide : 1 < 10) hlt
    have h2 : 1 < 9 * k := by omega
    exact lt_trans this (pow_lt_repunit h2)
  · rw [heq]
    have h2 : 1 < 9 * k := by omega
    exact pow_lt_repunit h2

lemma A004290_two : A004290 2 = 10 := by
  simpa using A004290_two_pow_five_pow (a := 1) (b := 0)

lemma A004290_four : A004290 4 = 100 := by
  simpa using A004290_two_pow_five_pow (a := 2) (b := 0)

lemma A004290_five : A004290 5 = 10 := by
  simpa using A004290_two_pow_five_pow (a := 0) (b := 1)

lemma A004290_eight : A004290 8 = 1000 := by
  simpa using A004290_two_pow_five_pow (a := 3) (b := 0)

lemma is01_111 : Is01 111 := by
  have : 111 = (10 ^ 3 - 1) / 9 := by decide
  rw [this]; exact Is01.repunit 3

lemma is01_1110 : Is01 1110 := by
  have : 1110 = 10 * 111 := by decide
  rw [this]; exact Is01.mul_ten (by decide) is01_111

lemma is01_of_digit10 {x : ℕ} (h : ∀ i, digit10 x i = 0 ∨ digit10 x i = 1) :
    Is01 x := by
  intro d hd
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
  have : digit10 x i = (Nat.digits 10 x)[i] := by
    unfold digit10
    exact List.getD_eq_getElem (l := Nat.digits 10 x) (n := i) (d := 0) hi
  rw [← this]
  exact h i

lemma is01_1001 : Is01 1001 := by
  refine is01_of_digit10 ?_
  intro i
  rw [digit10_eq]
  match i with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | i + 4 =>
    have : 1001 / 10 ^ (i + 4) = 0 := by
      have : 10 ^ (i + 4) ≥ 10 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega)
      have : 10 ^ 4 = 10000 := by decide
      have : 1001 < 10 ^ (i + 4) := by omega
      exact Nat.div_eq_of_lt this
    simp [this]

lemma A004290_lt_repunit9 {n : ℕ} (hn : n < 9) :
    A004290 n < (10 ^ 9 - 1) / 9 := by
  have hR : (10 ^ 9 - 1) / 9 = 111111111 := by decide
  rw [hR]
  interval_cases n
  · rw [A004290_zero]; decide
  · rw [A004290_one]; decide
  · rw [A004290_two]; decide
  · exact A004290_lt_of_witness (by decide : 0 < 111) (by decide) is01_111 (by decide)
  · rw [A004290_four]; decide
  · rw [A004290_five]; decide
  · exact A004290_lt_of_witness (by decide : 0 < 1110) (by decide) is01_1110 (by decide)
  · exact A004290_lt_of_witness (by decide : 0 < 1001) (by decide) is01_1001 (by decide)
  · rw [A004290_eight]; decide

lemma two_pow_t_mul_lt {a b m k : ℕ} (hmpos : 0 < m)
    (h : 2 ^ a * 5 ^ b * m < 10 ^ k) : 2 ^ max a b * m < 10 ^ k := by
  cases Nat.le_total a b with
  | inl hab =>
    rw [max_eq_right hab]
    have h25 : 2 ^ b ≤ 5 ^ b := Nat.pow_le_pow_left (by decide : 2 ≤ 5) _
    have h1 : 2 ^ b * m ≤ 5 ^ b * m := Nat.mul_le_mul_right _ h25
    have h2a : 1 ≤ 2 ^ a := Nat.one_le_pow _ _ (by decide)
    have h2 : 5 ^ b * m ≤ 2 ^ a * 5 ^ b * m := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Nat.mul_le_mul_left (5 ^ b * m) h2a)
    omega
  | inr hba =>
    rw [max_eq_left hba]
    have h5 : 1 ≤ 5 ^ b := Nat.one_le_pow _ _ (by decide)
    have : 2 ^ a * m ≤ 2 ^ a * 5 ^ b * m := by
      have := Nat.mul_le_mul_left (2 ^ a) (Nat.mul_le_mul_right m h5)
      simpa [mul_assoc] using this
    omega

lemma repunit_mul_ten_lt {l t L : ℕ} (h : l + t < L) :
    ((10 ^ l - 1) / 9) * 10 ^ t < (10 ^ L - 1) / 9 := by
  have h9 : 0 < 9 := by decide
  have hmul : ((10 ^ l - 1) / 9 * 10 ^ t) * 9 = (10 ^ l - 1) * 10 ^ t := by
    rw [mul_right_comm, Nat.div_mul_cancel (nine_dvd_ten_pow_sub_one l)]
  have hlt : (10 ^ l - 1) * 10 ^ t < 10 ^ L - 1 := by
    have hle : l + t ≤ L - 1 := by omega
    have hpow : 10 ^ (l + t) ≤ 10 ^ (L - 1) := Nat.pow_le_pow_right (by decide) hle
    have ht : 1 ≤ 10 ^ t := Nat.one_le_pow _ _ (by decide)
    have hL : 1 ≤ 10 ^ L := Nat.one_le_pow _ _ (by decide)
    have hl : 1 ≤ 10 ^ l := Nat.one_le_pow _ _ (by decide)
    have hL1 : 1 ≤ L := by omega
    have heq : (10 ^ l - 1) * 10 ^ t = 10 ^ (l + t) - 10 ^ t := by
      rw [Nat.mul_sub_right_distrib, one_mul, pow_add]
    rw [heq]
    have hA : 10 ^ t ≤ 10 ^ (l + t) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hC : 1 ≤ 10 ^ (L - 1) := Nat.one_le_pow _ _ (by decide)
    have hstep : 10 ^ (l + t) - 10 ^ t ≤ 10 ^ (L - 1) - 1 := by
      have := Nat.sub_le_sub_right hpow (10 ^ t)
      have : 10 ^ (L - 1) - 10 ^ t ≤ 10 ^ (L - 1) - 1 :=
        Nat.sub_le_sub_left ht _
      omega
    have hstep2 : 10 ^ (L - 1) - 1 < 10 ^ L - 1 :=
      Nat.sub_lt_sub_right hC (Nat.pow_lt_pow_right (by decide : 1 < 10) (by omega))
    exact lt_of_le_of_lt hstep hstep2
  have : ((10 ^ l - 1) / 9 * 10 ^ t) * 9 < 10 ^ L - 1 := by
    rwa [hmul]
  have hy : 9 ∣ 10 ^ L - 1 := nine_dvd_ten_pow_sub_one L
  rw [← Nat.div_mul_cancel hy] at this
  exact Nat.lt_of_mul_lt_mul_right this

/-! ### Order of 10 modulo m -/

noncomputable def order10 (m : ℕ) : ℕ :=
  sInf {d : ℕ | 0 < d ∧ 10 ^ d ≡ 1 [MOD m]}

lemma order10_spec {m : ℕ} (hm : Nat.Coprime m 10) (hm1 : 1 < m) :
    0 < order10 m ∧ 10 ^ order10 m ≡ 1 [MOD m] := by
  have hne : {d : ℕ | 0 < d ∧ 10 ^ d ≡ 1 [MOD m]}.Nonempty := by
    refine ⟨Nat.totient m, Nat.totient_pos.2 (by omega), ?_⟩
    exact Nat.ModEq.pow_totient hm.symm
  exact Nat.sInf_mem hne

lemma order10_pos {m : ℕ} (hm : Nat.Coprime m 10) (hmpos : 0 < m) :
    0 < order10 m := by
  by_cases h1 : m = 1
  · subst m
    have hne : {d : ℕ | 0 < d ∧ 10 ^ d ≡ 1 [MOD 1]}.Nonempty :=
      ⟨1, by decide, by change 10 % 1 = 1 % 1; simp⟩
    exact (Nat.sInf_mem hne).1
  · exact (order10_spec hm (by omega)).1

lemma order10_modEq {m : ℕ} (hm : Nat.Coprime m 10) (hmpos : 0 < m) :
    10 ^ order10 m ≡ 1 [MOD m] := by
  by_cases h1 : m = 1
  · subst m; change (10 ^ order10 1) % 1 = 1 % 1; simp [Nat.mod_one]
  · exact (order10_spec hm (by omega)).2

lemma dvd_ten_pow_sub_one_of_order {m : ℕ} (hm : Nat.Coprime m 10) (hmpos : 0 < m) :
    m ∣ 10 ^ order10 m - 1 :=
  (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by decide))).1 (order10_modEq hm hmpos).symm

lemma order10_le_of_modEq {m d : ℕ} (hd : 0 < d) (h : 10 ^ d ≡ 1 [MOD m]) :
    order10 m ≤ d :=
  Nat.sInf_le ⟨hd, h⟩

/-! ### Threshold index of m -/

noncomputable def thresh (m : ℕ) : ℕ :=
  sInf {j : ℕ | 0 < j ∧ m < 10 ^ j - 1}

lemma thresh_spec {m k : ℕ} (hk : 0 < k) (hm : m < 10 ^ k - 1) :
    0 < thresh m ∧ m < 10 ^ thresh m - 1 ∧ thresh m ≤ k := by
  have hne : {j : ℕ | 0 < j ∧ m < 10 ^ j - 1}.Nonempty := ⟨k, hk, hm⟩
  refine ⟨(Nat.sInf_mem hne).1, (Nat.sInf_mem hne).2, Nat.sInf_le ⟨hk, hm⟩⟩

lemma le_of_lt_thresh {m j : ℕ} (hj : 0 < j) (h : j < thresh m) :
    10 ^ j - 1 ≤ m := by
  have : ¬ (0 < j ∧ m < 10 ^ j - 1) := fun hj' =>
    (notMem_of_lt_sInf h) hj'
  omega

/- ### Sums of distinct powers of 10 are 0-1 numbers -/

lemma sum_pow_split (S : Finset ℕ) (j : ℕ) :
    ∑ i ∈ S, 10 ^ i =
      ∑ i ∈ S.filter (fun i => i < j), 10 ^ i
      + 10 ^ j * ∑ i ∈ S.filter (fun i => j ≤ i), 10 ^ (i - j) := by
  have h := Finset.sum_filter_add_sum_filter_not S (fun i => i < j) (fun i => 10 ^ i)
  rw [← h]
  congr 1
  have : S.filter (fun i => ¬ i < j) = S.filter (fun i => j ≤ i) := by
    ext i; simp [not_lt]
  rw [this, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hij : j ≤ i := (Finset.mem_filter.mp hi).2
  have : 10 ^ i = 10 ^ j * 10 ^ (i - j) := by
    rw [← pow_add, Nat.add_sub_of_le hij]
  exact this

lemma sum_pow_low_lt (S : Finset ℕ) (j : ℕ) :
    ∑ i ∈ S.filter (fun i => i < j), 10 ^ i < 10 ^ j := by
  have hsub : S.filter (fun i => i < j) ⊆ Finset.range j := by
    intro i hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; exact Nat.zero_le _)).trans_lt ?_
  rw [geom_sum_ten]
  exact repunit_lt_pow j

lemma sum_pow_div (S : Finset ℕ) (j : ℕ) :
    (∑ i ∈ S, 10 ^ i) / 10 ^ j =
      ∑ i ∈ S.filter (fun i => j ≤ i), 10 ^ (i - j) := by
  rw [sum_pow_split S j]
  have hpos : 0 < 10 ^ j := pow_pos (by decide : 0 < 10) j
  rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt (sum_pow_low_lt S j), zero_add]

lemma digit10_sum_pow (S : Finset ℕ) (j : ℕ) :
    digit10 (∑ i ∈ S, 10 ^ i) j = if j ∈ S then 1 else 0 := by
  rw [digit10_eq, sum_pow_div]
  have hunion :
      S.filter (fun i => j ≤ i) =
        S.filter (fun i => i = j) ∪ S.filter (fun i => j < i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro h
      rcases eq_or_lt_of_le h.2 with hij | hij
      · exact Or.inl ⟨h.1, hij.symm⟩
      · exact Or.inr ⟨h.1, hij⟩
    · intro h
      rcases h with h | h
      · exact ⟨h.1, le_of_eq h.2.symm⟩
      · exact ⟨h.1, le_of_lt h.2⟩
  have hdisj :
      Disjoint (S.filter (fun i => i = j)) (S.filter (fun i => j < i)) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hx'
    have : x = j := (Finset.mem_filter.mp hx).2
    have : j < x := (Finset.mem_filter.mp hx').2
    omega
  rw [hunion, Finset.sum_union hdisj]
  have hleft :
      ∑ i ∈ S.filter (fun i => i = j), 10 ^ (i - j) = if j ∈ S then 1 else 0 := by
    by_cases hj : j ∈ S
    · have : S.filter (fun i => i = j) = {j} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · intro h; exact h.2
        · intro hi; subst i; exact ⟨hj, rfl⟩
      simp [this, hj]
    · have : S.filter (fun i => i = j) = ∅ := by
        ext i
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hi hij
        subst i
        exact hj hi
      simp [this, hj]
  have hright :
      ∑ i ∈ S.filter (fun i => j < i), 10 ^ (i - j) =
        10 * ∑ i ∈ S.filter (fun i => j < i), 10 ^ (i - j - 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hij : j < i := (Finset.mem_filter.mp hi).2
    have hpos : 1 ≤ i - j := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hij)
    calc 10 ^ (i - j)
        = 10 ^ (i - j - 1 + 1) := by
            apply congrArg (fun n => 10 ^ n)
            exact (Nat.sub_add_cancel hpos).symm
      _ = 10 ^ (i - j - 1) * 10 := Nat.pow_succ _ _
      _ = 10 * 10 ^ (i - j - 1) := mul_comm _ _
  rw [hleft, hright, Nat.add_mul_mod_self_left]
  split_ifs <;> simp

lemma is01_sum_pow (S : Finset ℕ) : Is01 (∑ i ∈ S, 10 ^ i) :=
  is01_of_digit10 fun j => by
    rw [digit10_sum_pow]
    split_ifs <;> simp

/- ### Expanding digit counts along the period of 10 -/

def expandPos (c : ℕ → ℕ) (d : ℕ) : Finset ℕ :=
  (Finset.range d).biUnion fun r =>
    (Finset.range (c r)).image fun j => r + j * d

lemma pairwise_expandPos (c : ℕ → ℕ) {d : ℕ} (hd : 0 < d) :
    (Finset.range d : Set ℕ).PairwiseDisjoint fun r =>
      (Finset.range (c r)).image fun j => r + j * d := by
  intro r hr r' hr' hne
  refine Finset.disjoint_left.mpr ?_
  intro x hx hx'
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j', hj', heq⟩ := Finset.mem_image.mp hx'
  have hrk : r < d := Finset.mem_range.mp hr
  have hrk' : r' < d := Finset.mem_range.mp hr'
  have hrj : (r + j * d) % d = r := by
    have : (r + d * j) % d = r % d := Nat.add_mul_mod_self_left r d j
    simpa [mul_comm, Nat.mod_eq_of_lt hrk] using this
  have hrj' : (r' + j' * d) % d = r' := by
    have : (r' + d * j') % d = r' % d := Nat.add_mul_mod_self_left r' d j'
    simpa [mul_comm, Nat.mod_eq_of_lt hrk'] using this
  have : r = r' := by
    rw [← heq] at hrj
    exact hrj.symm.trans hrj'
  exact hne this

def expandCounts (c : ℕ → ℕ) (d : ℕ) : ℕ :=
  ∑ r ∈ Finset.range d, ∑ j ∈ Finset.range (c r), 10 ^ (r + j * d)

lemma expandCounts_eq_sum_pos {c : ℕ → ℕ} {d : ℕ} (hd : 0 < d) :
    expandCounts c d = ∑ i ∈ expandPos c d, 10 ^ i := by
  unfold expandCounts expandPos
  rw [Finset.sum_biUnion (pairwise_expandPos c hd)]
  refine Finset.sum_congr rfl ?_
  intro r hr
  rw [Finset.sum_image]
  intro j hj j' hj' heq
  have : j * d = j' * d := Nat.add_left_cancel heq
  exact Nat.eq_of_mul_eq_mul_right hd this

lemma is01_expandCounts {c : ℕ → ℕ} {d : ℕ} (hd : 0 < d) :
    Is01 (expandCounts c d) := by
  rw [expandCounts_eq_sum_pos hd]
  exact is01_sum_pow _

lemma expandCounts_modEq {m d : ℕ} (c : ℕ → ℕ) (hd : 0 < d)
    (h : 10 ^ d ≡ 1 [MOD m]) :
    expandCounts c d ≡ ∑ r ∈ Finset.range d, c r * 10 ^ r [MOD m] := by
  unfold expandCounts
  refine Nat.ModEq.sum ?_
  intro r hr
  have hterm :
      ∑ j ∈ Finset.range (c r), 10 ^ (r + j * d) ≡
        ∑ j ∈ Finset.range (c r), 10 ^ r [MOD m] := by
    refine Nat.ModEq.sum ?_
    intro j hj
    have : 10 ^ (r + j * d) = 10 ^ r * (10 ^ d) ^ j := by
      rw [pow_add, mul_comm j, pow_mul]
    rw [this]
    have hj1 : (10 ^ d) ^ j ≡ 1 [MOD m] := by
      simpa using (Nat.ModEq.pow j h)
    simpa [mul_one] using hj1.mul_left (10 ^ r)
  refine hterm.trans ?_
  have hconst : ∑ j ∈ Finset.range (c r), 10 ^ r = c r * 10 ^ r := by
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [hconst]

lemma expandCounts_dvd {m d : ℕ} (c : ℕ → ℕ) (hd : 0 < d)
    (h : 10 ^ d ≡ 1 [MOD m])
    (hN : m ∣ ∑ r ∈ Finset.range d, c r * 10 ^ r) :
    m ∣ expandCounts c d := by
  have hmod : expandCounts c d ≡ ∑ r ∈ Finset.range d, c r * 10 ^ r [MOD m] :=
    expandCounts_modEq c hd h
  have : expandCounts c d % m = 0 := by
    rw [hmod, Nat.mod_eq_zero_of_dvd hN]
  exact Nat.dvd_of_mod_eq_zero this

lemma digits_length_le_of_lt_pow {N d : ℕ} (hN : N < 10 ^ d) :
    (Nat.digits 10 N).length ≤ d := by
  by_cases hd0 : d = 0
  · subst d
    have : N = 0 := Nat.lt_one_iff.mp (by simpa using hN)
    subst N
    simp
  · by_contra h
    have : d + 1 ≤ (Nat.digits 10 N).length := by omega
    have : 10 ^ d ≤ N := by
      simpa [Nat.add_sub_cancel] using
        (digits_length_ge_iff N (d + 1) (by omega)).mp this
    omega

lemma digits_sum_eq_of_lt {N d : ℕ} (hN : N < 10 ^ d) :
    N = ∑ r ∈ Finset.range d, digit10 N r * 10 ^ r := by
  have hx := ofDigits_digits_sum N
  have hlen := digits_length_le_of_lt_pow hN
  have hzero : ∑ r ∈ Finset.Ico (Nat.digits 10 N).length d, digit10 N r * 10 ^ r = 0 := by
    refine Finset.sum_eq_zero ?_
    intro r hr
    have : (Nat.digits 10 N).length ≤ r := (Finset.mem_Ico.mp hr).1
    have : digit10 N r = 0 := by
      unfold digit10
      exact List.getD_eq_default (l := Nat.digits 10 N) (n := r) (d := 0) this
    simp [this]
  calc N
      = ∑ r ∈ Finset.range (Nat.digits 10 N).length, digit10 N r * 10 ^ r := hx
    _ = ∑ r ∈ Finset.range d, digit10 N r * 10 ^ r := by
        rw [← Finset.sum_range_add_sum_Ico _ hlen, hzero, add_zero]

lemma expandCounts_of_digits_dvd {m N d : ℕ} (hd : 0 < d) (hN : N < 10 ^ d)
    (h : 10 ^ d ≡ 1 [MOD m]) (hdvd : m ∣ N) :
    m ∣ expandCounts (fun r => digit10 N r) d := by
  refine expandCounts_dvd (fun r => digit10 N r) hd h ?_
  rwa [← digits_sum_eq_of_lt hN]

lemma expandCounts_pos {c : ℕ → ℕ} {d : ℕ} (hd : 0 < d)
    (h : ∃ r < d, 0 < c r) : 0 < expandCounts c d := by
  obtain ⟨r, hr, hc⟩ := h
  have : 10 ^ r ≤ expandCounts c d := by
    unfold expandCounts
    have hmem : r ∈ Finset.range d := Finset.mem_range.mpr hr
    have : 10 ^ r ≤ ∑ j ∈ Finset.range (c r), 10 ^ (r + j * d) := by
      have : 0 ∈ Finset.range (c r) := Finset.mem_range.mpr hc
      have := Finset.single_le_sum (s := Finset.range (c r))
        (f := fun j => 10 ^ (r + j * d)) (fun _ _ => Nat.zero_le _) this
      simpa [mul_zero, add_zero] using this
    exact le_trans this (Finset.single_le_sum
      (s := Finset.range d)
      (f := fun r => ∑ j ∈ Finset.range (c r), 10 ^ (r + j * d))
      (fun _ _ => Nat.zero_le _) hmem)
  exact lt_of_lt_of_le (pow_pos (by decide : 0 < 10) r) this

lemma ten_pow_sub_one_coprime {l : ℕ} (hl : 0 < l) : Nat.Coprime (10 ^ l - 1) 10 := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hl)
  have h2 : Nat.Coprime (10 ^ (l + 1) - 1) 2 := by
    refine ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 ?_).symm
    intro h
    have hmod : (10 ^ (l + 1) - 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd h
    have heven : 10 ^ (l + 1) % 2 = 0 :=
      Nat.mod_eq_zero_of_dvd (dvd_pow (by decide : 2 ∣ 10) (Nat.succ_ne_zero l))
    have : 1 ≤ 10 ^ (l + 1) := Nat.one_le_pow _ _ (by decide)
    omega
  have h5 : Nat.Coprime (10 ^ (l + 1) - 1) 5 := by
    refine ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 ?_).symm
    intro h
    have hmod : (10 ^ (l + 1) - 1) % 5 = 0 := Nat.mod_eq_zero_of_dvd h
    have h0 : 10 ^ (l + 1) % 5 = 0 :=
      Nat.mod_eq_zero_of_dvd (dvd_pow (by decide : 5 ∣ 10) (Nat.succ_ne_zero l))
    have : 1 ≤ 10 ^ (l + 1) := Nat.one_le_pow _ _ (by decide)
    omega
  exact h2.mul_right h5

lemma expandCounts_le_pow {c : ℕ → ℕ} {d C : ℕ} (hd : 0 < d)
    (hC : ∀ r < d, 0 < c r → r + (c r - 1) * d + 1 ≤ C) :
    expandCounts c d < 10 ^ C ∨ expandCounts c d = 0 := by
  by_cases h0 : expandCounts c d = 0
  · exact Or.inr h0
  · left
    rw [expandCounts_eq_sum_pos hd]
    have hS : ∀ i ∈ expandPos c d, i < C := by
      intro i hi
      obtain ⟨r, hr, hi'⟩ := Finset.mem_biUnion.mp hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi'
      have hrk : r < d := Finset.mem_range.mp hr
      have hj' : j < c r := Finset.mem_range.mp hj
      have hc : 0 < c r := lt_of_le_of_lt (Nat.zero_le j) hj'
      have := hC r hrk hc
      have : j ≤ c r - 1 := by omega
      have : r + j * d ≤ r + (c r - 1) * d := Nat.add_le_add_left (Nat.mul_le_mul_right d this) _
      omega
    have hsub : expandPos c d ⊆ Finset.range C := by
      intro i hi; exact Finset.mem_range.mpr (hS i hi)
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; exact Nat.zero_le _)).trans_lt ?_
    rw [geom_sum_ten]
    exact repunit_lt_pow C

/- ### Arithmetic lemmas for the induction -/

lemma sixteen_pow_ge_two_mul_ten : ∀ δ, 2 ≤ δ → 2 * 10 ^ δ ≤ 16 ^ δ
  | 0, h => by omega
  | 1, h => by omega
  | 2, _ => by decide
  | δ + 3, h => by
      have ih : 2 * 10 ^ (δ + 2) ≤ 16 ^ (δ + 2) :=
        sixteen_pow_ge_two_mul_ten (δ + 2) (by omega)
      have hL : 2 * 10 ^ (δ + 3) = 20 * 10 ^ (δ + 2) := by
        rw [pow_succ]; ring
      have hR : 16 ^ (δ + 3) = 16 * 16 ^ (δ + 2) := by
        rw [show δ + 3 = δ + 2 + 1 from rfl, pow_succ, mul_comm]
      have : 20 * 10 ^ (δ + 2) ≤ 16 * (2 * 10 ^ (δ + 2)) := by
        have h20 : 20 ≤ 32 := by decide
        have : 20 * 10 ^ (δ + 2) ≤ 32 * 10 ^ (δ + 2) := Nat.mul_le_mul_right _ h20
        have : 32 * 10 ^ (δ + 2) = 16 * (2 * 10 ^ (δ + 2)) := by ring
        omega
      have : 16 * (2 * 10 ^ (δ + 2)) ≤ 16 * 16 ^ (δ + 2) :=
        Nat.mul_le_mul_left 16 ih
      omega

lemma two_mul_ten_pow_div {j k : ℕ} (hj : 2 ≤ j) (hjk : j ≤ k) :
    10 ^ k ≤ 2 * 10 ^ (k - j + 1) * (10 ^ (j - 1) - 1) := by
  have hj1 : 1 ≤ j := by omega
  have hpos : 2 ≤ 10 ^ (j - 1) := by
    have : 10 ≤ 10 ^ (j - 1) := Nat.le_pow (by omega)
    omega
  have hexp : k - j + 1 + (j - 1) = k := by omega
  have : 10 ^ k = 10 ^ (k - j + 1) * 10 ^ (j - 1) := by
    rw [← pow_add, hexp]
  have h2 : 10 ^ (j - 1) ≤ 2 * (10 ^ (j - 1) - 1) := by omega
  calc 10 ^ k
      = 10 ^ (k - j + 1) * 10 ^ (j - 1) := this
    _ ≤ 10 ^ (k - j + 1) * (2 * (10 ^ (j - 1) - 1)) :=
        Nat.mul_le_mul_left _ h2
    _ = 2 * 10 ^ (k - j + 1) * (10 ^ (j - 1) - 1) := by ring

lemma t_lt_four_mul_gap {t j k : ℕ} (hj : 2 ≤ j) (hjk : j < k)
    (h : 2 ^ t * (10 ^ (j - 1) - 1) < 10 ^ k) :
    t < 4 * (k - j + 1) := by
  set δ := k - j + 1
  have hδ : 2 ≤ δ := by omega
  by_contra ht
  have ht' : 4 * δ ≤ t := by omega
  have hpow : 2 ^ (4 * δ) ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) ht'
  have h16 : 16 ^ δ = 2 ^ (4 * δ) := by
    have : (16 : ℕ) = 2 ^ 4 := by decide
    rw [this, ← pow_mul]
  have hge := sixteen_pow_ge_two_mul_ten δ hδ
  have hdiv := two_mul_ten_pow_div hj (le_of_lt hjk)
  have : 2 ^ t * (10 ^ (j - 1) - 1) ≥ 10 ^ k := by
    have hpos : 0 < 10 ^ (j - 1) - 1 := by
      have : 10 ≤ 10 ^ (j - 1) := Nat.le_pow (by omega)
      omega
    have : 16 ^ δ * (10 ^ (j - 1) - 1) ≥ 2 * 10 ^ δ * (10 ^ (j - 1) - 1) :=
      Nat.mul_le_mul_right _ hge
    have : 2 ^ (4 * δ) * (10 ^ (j - 1) - 1) ≥ 2 * 10 ^ δ * (10 ^ (j - 1) - 1) := by
      rwa [h16] at this
    have : 2 ^ t * (10 ^ (j - 1) - 1) ≥ 2 * 10 ^ δ * (10 ^ (j - 1) - 1) :=
      le_trans this (Nat.mul_le_mul_right _ hpow)
    have : 2 * 10 ^ δ * (10 ^ (j - 1) - 1) ≥ 10 ^ k := by
      simpa [δ] using hdiv
    omega
  omega

lemma t_le_nine_mul_gap {t j k : ℕ} (hj : 1 ≤ j) (hjk : j < k)
    (hmlo : j = 1 ∨ 10 ^ (j - 1) - 1 ≤ 2 ^ t * (10 ^ (j - 1) - 1))
    (ht4 : t < 4 * k)
    (h : j = 1 ∨ 2 ^ t * (10 ^ (j - 1) - 1) < 10 ^ k) :
    t ≤ 9 * (k - j) := by
  by_cases hj1 : j = 1
  · subst j
    have : 4 * k ≤ 9 * (k - 1) + 3 := by
      have hk : 2 ≤ k := by omega
      omega
    omega
  · have hj2 : 2 ≤ j := by omega
    have hmul : 2 ^ t * (10 ^ (j - 1) - 1) < 10 ^ k := h.resolve_left hj1
    have := t_lt_four_mul_gap (j := j) (k := k) hj2 (by omega) hmul
    have : t ≤ 4 * (k - j + 1) - 1 := by omega
    have : 4 * (k - j + 1) - 1 ≤ 9 * (k - j) := by
      have : 1 ≤ k - j := by omega
      omega
    omega

lemma repunit_mul_ten_lt_of_add_le {l t L : ℕ}
    (h : l + t ≤ L) (ht : l + t < L ∨ 0 < t) :
    ((10 ^ l - 1) / 9) * 10 ^ t < (10 ^ L - 1) / 9 := by
  rcases lt_or_eq_of_le h with hlt | heq
  · exact repunit_mul_ten_lt hlt
  · have htpos : 0 < t := by
      rcases ht with hlt | ht
      · omega
      · exact ht
    have h9 : 0 < 9 := by decide
    have hmul : ((10 ^ l - 1) / 9 * 10 ^ t) * 9 = (10 ^ l - 1) * 10 ^ t := by
      rw [mul_right_comm, Nat.div_mul_cancel (nine_dvd_ten_pow_sub_one l)]
    have hpow : 10 ^ l * 10 ^ t = 10 ^ L := by
      rw [← pow_add, heq]
    have ht1 : 1 ≤ 10 ^ t := Nat.one_le_pow _ _ (by decide)
    have hl1 : 1 ≤ 10 ^ l := Nat.one_le_pow _ _ (by decide)
    have hL1 : 1 ≤ 10 ^ L := Nat.one_le_pow _ _ (by decide)
    have hdiff : (10 ^ l - 1) * 10 ^ t = 10 ^ L - 10 ^ t := by
      rw [Nat.mul_sub_right_distrib, one_mul, hpow]
    have hlt' : 10 ^ L - 10 ^ t < 10 ^ L - 1 := by
      have : 1 < 10 ^ t := Nat.one_lt_pow (Nat.ne_of_gt htpos) (by decide)
      have htle : t ≤ L := by omega
      have hpowle : 10 ^ t ≤ 10 ^ L := Nat.pow_le_pow_right (by decide) htle
      have hL1' : 1 ≤ 10 ^ L := Nat.one_le_pow _ _ (by decide)
      have hcancel1 : 10 ^ L - 10 ^ t + 10 ^ t = 10 ^ L := Nat.sub_add_cancel hpowle
      have hcancel2 : 10 ^ L - 1 + 1 = 10 ^ L := Nat.sub_add_cancel hL1'
      omega
    have : ((10 ^ l - 1) / 9 * 10 ^ t) * 9 < 10 ^ L - 1 := by
      rwa [hmul, hdiff]
    have hy : 9 ∣ 10 ^ L - 1 := nine_dvd_ten_pow_sub_one L
    rw [← Nat.div_mul_cancel hy] at this
    exact Nat.lt_of_mul_lt_mul_right this

lemma ten_pow_mul_lt_repunit {a t L : ℕ} (hL : 1 < L) (h : a + t < L) :
    10 ^ a * 10 ^ t < (10 ^ L - 1) / 9 := by
  have : 10 ^ a * 10 ^ t = 10 ^ (a + t) := (pow_add _ _ _).symm
  rw [this]
  have hle : a + t ≤ L - 1 := by omega
  have : 10 ^ (a + t) ≤ 10 ^ (L - 1) := Nat.pow_le_pow_right (by decide) hle
  exact lt_of_le_of_lt this (pow_lt_repunit hL)

lemma four_mul_succ_sub_one_le {j k : ℕ} (h : j < k) :
    4 * (k - j + 1) - 1 ≤ 9 * (k - j) := by
  have : 1 ≤ k - j := Nat.sub_pos_of_lt h
  omega

lemma four_mul_le_nine_pred {k : ℕ} (hk : 2 ≤ k) : 4 * k - 1 ≤ 9 * (k - 1) := by
  omega

lemma t_le_three_of_hard {t k : ℕ} (hk : 2 ≤ k)
    (h : 2 ^ t * (10 ^ (k - 1) - 1) < 10 ^ k) : t ≤ 3 := by
  by_contra ht
  have ht4 : 4 ≤ t := by omega
  have h16 : 16 ≤ 2 ^ t := by
    have : 2 ^ 4 ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) ht4
    exact this
  have hpos : 0 < 10 ^ (k - 1) - 1 := by
    have : 10 ≤ 10 ^ (k - 1) := Nat.le_pow (by omega)
    omega
  have hmul : 16 * (10 ^ (k - 1) - 1) ≤ 2 ^ t * (10 ^ (k - 1) - 1) :=
    Nat.mul_le_mul_right _ h16
  have hlt : 16 * (10 ^ (k - 1) - 1) < 10 ^ k := lt_of_le_of_lt hmul h
  have hexp : 10 ^ k = 10 * 10 ^ (k - 1) := by
    have hpos : 1 ≤ k := by omega
    have hsucc : k - 1 + 1 = k := Nat.sub_add_cancel hpos
    calc 10 ^ k
        = 10 ^ (k - 1 + 1) := (congrArg (fun n => 10 ^ n) hsucc).symm
      _ = 10 ^ (k - 1) * 10 := Nat.pow_succ 10 (k - 1)
      _ = 10 * 10 ^ (k - 1) := mul_comm _ _
  have hb : 1 ≤ 10 ^ (k - 1) := Nat.one_le_pow _ _ (by decide)
  have : 10 * 10 ^ (k - 1) ≤ 16 * (10 ^ (k - 1) - 1) := by
    have : 10 * 10 ^ (k - 1) + 16 ≤ 16 * 10 ^ (k - 1) := by
      have : 16 ≤ 6 * 10 ^ (k - 1) := by
        have : 10 ≤ 10 ^ (k - 1) := Nat.le_pow (by omega)
        nlinarith
      omega
    omega
  rw [hexp] at hlt
  omega

lemma dvd_repunit_of_coprime9 {m d : ℕ} (hd : 0 < d)
    (h9 : Nat.Coprime m 9) (hdvd : m ∣ 10 ^ d - 1) :
    m ∣ (10 ^ d - 1) / 9 := by
  have h9d := nine_dvd_ten_pow_sub_one d
  have : m ∣ 9 * ((10 ^ d - 1) / 9) := by
    rw [Nat.mul_div_cancel' h9d]
    exact hdvd
  exact (h9.dvd_mul_left).1 (by simpa [mul_comm] using this)

lemma A004290_le_repunit_order {m : ℕ} (hm : Nat.Coprime m 10) (hmpos : 0 < m)
    (h9 : Nat.Coprime m 9) :
    A004290 m ≤ (10 ^ order10 m - 1) / 9 := by
  have hdpos := order10_pos hm hmpos
  have hdvd := dvd_ten_pow_sub_one_of_order hm hmpos
  have hR := dvd_repunit_of_coprime9 hdpos h9 hdvd
  exact A004290_le (repunit_pos _ hdpos) hR (Is01.repunit _)

lemma A004290_le_expandCounts {m d : ℕ} (c : ℕ → ℕ) (hd : 0 < d)
    (h : 10 ^ d ≡ 1 [MOD m])
    (hN : m ∣ ∑ r ∈ Finset.range d, c r * 10 ^ r)
    (hpos : 0 < expandCounts c d) :
    A004290 m ≤ expandCounts c d :=
  A004290_le hpos (expandCounts_dvd c hd h hN) (is01_expandCounts hd)

lemma three_mul_ten_pow_add {k : ℕ} :
    10 ^ (2 * k) + 10 ^ k + 1 = 3 * ((10 ^ (2 * k) + 10 ^ k + 1) / 3) := by
  have : 3 ∣ 10 ^ (2 * k) + 10 ^ k + 1 := by
    have h10 : 10 ≡ 1 [MOD 3] := by decide
    have h1 : 10 ^ (2 * k) ≡ 1 [MOD 3] := by simpa using (Nat.ModEq.pow (2 * k) h10)
    have h2 : 10 ^ k ≡ 1 [MOD 3] := by simpa using (Nat.ModEq.pow k h10)
    have hsum : 10 ^ (2 * k) + 10 ^ k + 1 ≡ 1 + 1 + 1 [MOD 3] :=
      (h1.add h2).add (Nat.ModEq.refl 1)
    have : 10 ^ (2 * k) + 10 ^ k + 1 ≡ 0 [MOD 3] := by
      have : (1 + 1 + 1 : ℕ) = 3 := rfl
      rw [this] at hsum
      exact hsum.trans (by decide : 3 ≡ 0 [MOD 3])
    exact Nat.modEq_zero_iff_dvd.1 this
  rw [Nat.mul_div_cancel' this]

lemma dvd_repunit_three_mul {k m : ℕ} (hk : 0 < k)
    (hm : m = (10 ^ k - 1) / 3) (h3 : 3 ∣ 10 ^ k - 1) :
    m ∣ (10 ^ (3 * k) - 1) / 9 := by
  have h9 : 0 < 9 := by decide
  have hfactor : 10 ^ (3 * k) - 1 =
      (10 ^ k - 1) * (10 ^ (2 * k) + 10 ^ k + 1) := by
    have hle : 1 ≤ 10 ^ k := Nat.one_le_pow k 10 (by decide)
    have := geom_sum_mul_of_one_le (x := 10 ^ k) hle 3
    have hpow : (10 ^ k) ^ 3 = 10 ^ (3 * k) := by rw [← pow_mul, mul_comm]
    rw [hpow] at this
    have hsum : ∑ i ∈ Finset.range 3, (10 ^ k) ^ i = 1 + 10 ^ k + 10 ^ (2 * k) := by
      simp [Finset.sum_range_succ, pow_zero, pow_one, pow_two, pow_add]
      ring
    rw [hsum] at this
    linarith
  have : (10 ^ (3 * k) - 1) / 9 =
      ((10 ^ k - 1) / 3) * ((10 ^ (2 * k) + 10 ^ k + 1) / 3) := by
    have h3' : 3 ∣ 10 ^ (2 * k) + 10 ^ k + 1 := by
      have h10 : 10 ≡ 1 [MOD 3] := by decide
      have h1 : 10 ^ (2 * k) ≡ 1 [MOD 3] := by simpa using (Nat.ModEq.pow (2 * k) h10)
      have h2 : 10 ^ k ≡ 1 [MOD 3] := by simpa using (Nat.ModEq.pow k h10)
      have hsum : 10 ^ (2 * k) + 10 ^ k + 1 ≡ 1 + 1 + 1 [MOD 3] :=
        (h1.add h2).add (Nat.ModEq.refl 1)
      have : 10 ^ (2 * k) + 10 ^ k + 1 ≡ 0 [MOD 3] := by
        have : (1 + 1 + 1 : ℕ) = 3 := rfl
        rw [this] at hsum
        exact hsum.trans (by decide : 3 ≡ 0 [MOD 3])
      exact Nat.modEq_zero_iff_dvd.1 this
    have : (10 ^ k - 1) * (10 ^ (2 * k) + 10 ^ k + 1) / 9 =
        ((10 ^ k - 1) / 3) * ((10 ^ (2 * k) + 10 ^ k + 1) / 3) := by
      have hL : (10 ^ k - 1) * (10 ^ (2 * k) + 10 ^ k + 1) =
          9 * (((10 ^ k - 1) / 3) * ((10 ^ (2 * k) + 10 ^ k + 1) / 3)) := by
        have hA := Nat.mul_div_cancel' h3
        have hB := Nat.mul_div_cancel' h3'
        calc (10 ^ k - 1) * (10 ^ (2 * k) + 10 ^ k + 1)
            = (3 * ((10 ^ k - 1) / 3)) * (3 * ((10 ^ (2 * k) + 10 ^ k + 1) / 3)) := by
              rw [hA, hB]
          _ = 9 * (((10 ^ k - 1) / 3) * ((10 ^ (2 * k) + 10 ^ k + 1) / 3)) := by ring
      rw [hL, Nat.mul_div_cancel_left _ h9]
    rwa [hfactor]
  rw [hm, this]
  exact dvd_mul_right _ _

/- ### Order-divides and the d = k analysis -/

lemma ten_pow_modEq_one_iff_dvd {m e : ℕ} (_he : 0 < e) :
    10 ^ e ≡ 1 [MOD m] ↔ m ∣ 10 ^ e - 1 := by
  rw [Nat.ModEq.comm]
  exact Nat.modEq_iff_dvd' (Nat.one_le_pow e 10 (by decide))

lemma order10_dvd_of_modEq {m e : ℕ} (hm : Nat.Coprime m 10) (hmpos : 0 < m)
    (_he : 0 < e) (h : 10 ^ e ≡ 1 [MOD m]) : order10 m ∣ e := by
  set d := order10 m
  have hdpos : 0 < d := order10_pos hm hmpos
  have hd : 10 ^ d ≡ 1 [MOD m] := order10_modEq hm hmpos
  have hdiv := Nat.div_add_mod e d
  have hlt : e % d < d := Nat.mod_lt e hdpos
  have hpow : 10 ^ e ≡ 10 ^ (e % d) [MOD m] := by
    have : e = d * (e / d) + e % d := hdiv.symm
    rw [this, pow_add, pow_mul]
    have h1 : (10 ^ d) ^ (e / d) ≡ 1 ^ (e / d) [MOD m] := Nat.ModEq.pow _ hd
    simpa using h1.mul (Nat.ModEq.refl (10 ^ (e % d)))
  have hr : 10 ^ (e % d) ≡ 1 [MOD m] := hpow.symm.trans h
  by_cases hr0 : e % d = 0
  · exact Nat.dvd_of_mod_eq_zero hr0
  · have hrpos : 0 < e % d := Nat.pos_of_ne_zero hr0
    have : d ≤ e % d := order10_le_of_modEq hrpos hr
    omega

lemma order10_dvd_of_dvd_ten_pow {m e : ℕ} (hm : Nat.Coprime m 10) (hmpos : 0 < m)
    (he : 0 < e) (h : m ∣ 10 ^ e - 1) : order10 m ∣ e :=
  order10_dvd_of_modEq hm hmpos he ((ten_pow_modEq_one_iff_dvd he).2 h)

lemma ten_pow_modEq_of_zmod_pow_eq {m a b : ℕ} [NeZero m]
    (h : (10 : ZMod m) ^ a = (10 : ZMod m) ^ b) :
    10 ^ a ≡ 10 ^ b [MOD m] := by
  have hcast : ((10 ^ a : ℕ) : ZMod m) = ((10 ^ b : ℕ) : ZMod m) := by
    simpa using h
  exact (ZMod.natCast_eq_natCast_iff (10 ^ a) (10 ^ b) m).1
    (by simpa using hcast)

lemma ten_pow_modEq_one_of_pow_eq {m a b : ℕ} (hm : Nat.Coprime m 10)
    (hab : b ≤ a) (h : 10 ^ a ≡ 10 ^ b [MOD m]) :
    10 ^ (a - b) ≡ 1 [MOD m] := by
  have hmul : 10 ^ (a - b) * 10 ^ b ≡ 1 * 10 ^ b [MOD m] := by
    have : 10 ^ (a - b) * 10 ^ b = 10 ^ a := by
      rw [← pow_add, Nat.sub_add_cancel hab]
    simpa [this] using h
  have hcop : Nat.gcd m (10 ^ b) = 1 := Nat.Coprime.pow_right b hm
  exact Nat.ModEq.cancel_right_of_coprime hcop hmul

lemma order10_lt_of_zmod_pow_eq {m a b L : ℕ} [NeZero m]
    (hm : Nat.Coprime m 10) (hmpos : 0 < m)
    (hne : a ≠ b) (haL : a < L) (hbL : b < L)
    (h : (10 : ZMod m) ^ a = (10 : ZMod m) ^ b) :
    order10 m < L := by
  have hmod := ten_pow_modEq_of_zmod_pow_eq h
  rcases Nat.lt_or_gt_of_ne hne with hab | hab
  · have hpos : 0 < b - a := Nat.sub_pos_of_lt hab
    have hdvd := order10_dvd_of_modEq hm hmpos hpos
      (ten_pow_modEq_one_of_pow_eq hm (Nat.le_of_lt hab) hmod.symm)
    exact lt_of_le_of_lt (Nat.le_of_dvd hpos hdvd) (lt_of_le_of_lt (Nat.sub_le b a) hbL)
  · have hpos : 0 < a - b := Nat.sub_pos_of_lt hab
    have hdvd := order10_dvd_of_modEq hm hmpos hpos
      (ten_pow_modEq_one_of_pow_eq hm (Nat.le_of_lt hab) hmod)
    exact lt_of_le_of_lt (Nat.le_of_dvd hpos hdvd) (lt_of_le_of_lt (Nat.sub_le a b) haL)

lemma five_not_dvd_ten_pow_sub_one {k : ℕ} (hk : 0 < k) : ¬ 5 ∣ 10 ^ k - 1 := by
  intro h
  have hmod : (10 ^ k - 1) % 5 = 0 := Nat.mod_eq_zero_of_dvd h
  have h10 : 10 ^ k % 5 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow (by decide : 5 ∣ 10) (Nat.pos_iff_ne_zero.mp hk))
  have : 1 ≤ 10 ^ k := Nat.one_le_pow _ _ (by decide)
  omega

lemma ten_pow_sub_one_odd {k : ℕ} (hk : 0 < k) : Odd (10 ^ k - 1) := by
  have h : (10 ^ k - 1) % 2 = 1 := by
    have h10 : 10 ^ k % 2 = 0 :=
      Nat.mod_eq_zero_of_dvd
        (dvd_pow (by decide : 2 ∣ 10) (Nat.pos_iff_ne_zero.mp hk))
    have : 1 ≤ 10 ^ k := Nat.one_le_pow _ _ (by decide)
    omega
  exact Nat.odd_iff.2 h

lemma ten_pow_eq_ten_mul {k : ℕ} (hk : 1 ≤ k) :
    10 ^ k = 10 * 10 ^ (k - 1) := by
  have hsucc : k - 1 + 1 = k := Nat.sub_add_cancel hk
  calc 10 ^ k
      = 10 ^ (k - 1 + 1) := (congrArg (fun n => 10 ^ n) hsucc).symm
    _ = 10 ^ (k - 1) * 10 := Nat.pow_succ 10 (k - 1)
    _ = 10 * 10 ^ (k - 1) := mul_comm _ _

lemma ten_pow_sub_one_div_pred {k : ℕ} (hk : 2 ≤ k) :
    (10 ^ k - 1) / (10 ^ (k - 1) - 1) = 10 + 9 / (10 ^ (k - 1) - 1) := by
  have hk1 : 1 ≤ k := by omega
  have hden : 0 < 10 ^ (k - 1) - 1 := by
    have : 10 ≤ 10 ^ (k - 1) := Nat.le_pow (by omega)
    omega
  have hsplit : 10 ^ k - 1 = 10 * (10 ^ (k - 1) - 1) + 9 := by
    have hpow := ten_pow_eq_ten_mul hk1
    have h1 : 1 ≤ 10 ^ (k - 1) := Nat.one_le_pow _ _ (by decide)
    have : 10 * 10 ^ (k - 1) - 1 = 10 * (10 ^ (k - 1) - 1) + 9 := by
      have : 10 * 10 ^ (k - 1) = 10 * (10 ^ (k - 1) - 1) + 10 := by
        omega
      omega
    omega
  have hdiv :
      (10 * (10 ^ (k - 1) - 1) + 9) / (10 ^ (k - 1) - 1) =
        10 + 9 / (10 ^ (k - 1) - 1) := by
    rw [add_comm (10 * (10 ^ (k - 1) - 1)), mul_comm 10]
    rw [Nat.add_mul_div_left 9 10 hden, add_comm]
  rw [hsplit, hdiv]

lemma quot_le_eleven {k m : ℕ} (hk : 2 ≤ k) (_hm : 0 < m)
    (hle : 10 ^ (k - 1) - 1 ≤ m) :
    (10 ^ k - 1) / m ≤ 11 := by
  have h10 : 10 ≤ 10 ^ (k - 1) := Nat.le_pow (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hk))
  have hden : 0 < 10 ^ (k - 1) - 1 := by omega
  have hle' : (10 ^ k - 1) / m ≤ (10 ^ k - 1) / (10 ^ (k - 1) - 1) :=
    Nat.div_le_div_left hle hden
  have heq := ten_pow_sub_one_div_pred hk
  have h9 : 9 ≤ 10 ^ (k - 1) - 1 := by omega
  have hsmall : 9 / (10 ^ (k - 1) - 1) ≤ 1 :=
    (Nat.div_le_div_left h9 (by decide : 0 < 9)).trans (by decide : 9 / 9 ≤ 1)
  have : (10 ^ k - 1) / (10 ^ (k - 1) - 1) ≤ 11 := by
    rw [heq]; omega
  exact hle'.trans this

lemma quot_le_ten {k m : ℕ} (hk : 3 ≤ k) (_hm : 0 < m)
    (hle : 10 ^ (k - 1) - 1 ≤ m) :
    (10 ^ k - 1) / m ≤ 10 := by
  have h10 : 10 ≤ 10 ^ (k - 1) :=
    Nat.le_pow (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 3) hk))
  have hden : 0 < 10 ^ (k - 1) - 1 := by omega
  have hle' : (10 ^ k - 1) / m ≤ (10 ^ k - 1) / (10 ^ (k - 1) - 1) :=
    Nat.div_le_div_left hle hden
  have heq := ten_pow_sub_one_div_pred (le_trans (by decide : 2 ≤ 3) hk)
  have h2 : 2 ≤ k - 1 := Nat.sub_le_sub_right hk 1
  have hpow2 : 10 ^ 2 ≤ 10 ^ (k - 1) := Nat.pow_le_pow_right (by decide) h2
  have h99 : 99 ≤ 10 ^ (k - 1) - 1 := by
    have : 100 ≤ 10 ^ (k - 1) := by simpa using hpow2
    have h1 : 1 ≤ 10 ^ (k - 1) := Nat.one_le_pow _ _ (by decide)
    omega
  have hz : 9 / (10 ^ (k - 1) - 1) = 0 :=
    Nat.div_eq_of_lt (lt_of_lt_of_le (by decide : 9 < 99) h99)
  have heq' : (10 ^ k - 1) / (10 ^ (k - 1) - 1) = 10 := by
    rw [heq, hz]
  exact hle'.trans (le_of_eq heq')

lemma odd_quot_of_odd_div {a b : ℕ} (ha : Odd a) (hb : 0 < b) (hdvd : b ∣ a) :
    Odd (a / b) := by
  obtain ⟨q, hq⟩ := hdvd
  rw [hq, Nat.mul_div_cancel_left _ hb]
  have : Odd (b * q) := by rwa [← hq]
  exact (Nat.odd_mul.1 this).2

lemma order_ten_mod_seven_six : 10 ^ 6 ≡ 1 [MOD 7] := by decide

lemma order_ten_mod_seven_lt {n : ℕ} (hn : 0 < n) (hn6 : n < 6) :
    ¬ 10 ^ n ≡ 1 [MOD 7] := by
  interval_cases n <;> decide

lemma six_dvd_iff_ten_pow_mod_seven {n : ℕ} :
    10 ^ n ≡ 1 [MOD 7] ↔ 6 ∣ n := by
  constructor
  · intro h
    by_cases hn : n = 0
    · subst n; exact dvd_zero _
    · have hdiv := Nat.div_add_mod n 6
      have hr : n % 6 < 6 := Nat.mod_lt n (by decide)
      have hpow : 10 ^ n ≡ 10 ^ (n % 6) [MOD 7] := by
        have hn' : n = 6 * (n / 6) + n % 6 := hdiv.symm
        rw [hn', pow_add, pow_mul]
        have h1 : (10 ^ 6) ^ (n / 6) ≡ 1 ^ (n / 6) [MOD 7] :=
          Nat.ModEq.pow _ order_ten_mod_seven_six
        simpa using h1.mul (Nat.ModEq.refl (10 ^ (n % 6)))
      have hr1 : 10 ^ (n % 6) ≡ 1 [MOD 7] := hpow.symm.trans h
      by_cases hz : n % 6 = 0
      · exact Nat.dvd_of_mod_eq_zero hz
      · have : 0 < n % 6 := Nat.pos_of_ne_zero hz
        exact (order_ten_mod_seven_lt this hr hr1).elim
  · intro ⟨q, hq⟩
    rw [hq, pow_mul]
    have : (10 ^ 6) ^ q ≡ 1 ^ q [MOD 7] := Nat.ModEq.pow q order_ten_mod_seven_six
    simpa using this

lemma seven_dvd_ten_pow_sub_one {k : ℕ} : 7 ∣ 10 ^ k - 1 ↔ 6 ∣ k := by
  by_cases hk : k = 0
  · subst k; simp
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    rw [← ten_pow_modEq_one_iff_dvd hkpos, six_dvd_iff_ten_pow_mod_seven]

lemma block571428 : 571428 = 5 * 10 ^ 5 + 7 * 10 ^ 4 + 1 * 10 ^ 3 + 4 * 10 ^ 2 + 2 * 10 + 8 := by
  decide

lemma four_div_seven_block : 4 * ((10 ^ 6 - 1) / 7) = 571428 := by
  decide

lemma ten_pow_six_sub_factor (q : ℕ) :
    10 ^ (6 * q) - 1 = (10 ^ 6 - 1) * ∑ i ∈ Finset.range q, (10 ^ 6) ^ i := by
  have hle : 1 ≤ 10 ^ 6 := by decide
  have hmul := geom_sum_mul_of_one_le (x := 10 ^ 6) hle q
  have hpow : (10 ^ 6) ^ q = 10 ^ (6 * q) := by rw [← pow_mul]
  rw [hpow] at hmul
  rw [mul_comm (10 ^ 6 - 1)]
  exact hmul.symm

lemma four_mul_ten_pow_div_seven (q : ℕ) :
    4 * ((10 ^ (6 * q) - 1) / 7) =
      571428 * ∑ i ∈ Finset.range q, 10 ^ (6 * i) := by
  have h6 : 7 ∣ 10 ^ 6 - 1 := by decide
  have hsplit := ten_pow_six_sub_factor q
  have hsum : ∑ i ∈ Finset.range q, (10 ^ 6) ^ i =
      ∑ i ∈ Finset.range q, 10 ^ (6 * i) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [← pow_mul]
  have hdiv :
      ((10 ^ 6 - 1) * ∑ i ∈ Finset.range q, 10 ^ (6 * i)) / 7 =
        ((10 ^ 6 - 1) / 7) * ∑ i ∈ Finset.range q, 10 ^ (6 * i) := by
    rw [mul_comm, Nat.mul_div_assoc _ h6, mul_comm]
  rw [hsplit, hsum, hdiv, ← mul_assoc, four_div_seven_block]

lemma A004290_le_pow_of_lt {m a : ℕ} (h : A004290 m < 10 ^ a) : A004290 m ≤ 10 ^ a - 1 := by
  omega

lemma A_mul_ten_lt_of_lt_pow {m t a L : ℕ}
    (hA : A004290 m < 10 ^ a) (hL : 1 < L) (h : a + t < L) :
    A004290 m * 10 ^ t < (10 ^ L - 1) / 9 := by
  have := ten_pow_mul_lt_repunit (a := a) (t := t) (L := L) hL h
  exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_of_lt hA)) this

lemma A004290_le_self_of_is01 {m : ℕ} (hm : 0 < m) (h01 : Is01 m) :
    A004290 m ≤ m :=
  A004290_le hm (dvd_refl m) h01

lemma digits_571428_le_eight (i : ℕ) :
    digit10 571428 i ≤ 8 := by
  rw [digit10_eq]
  have h571 : 571428 < 10 ^ 6 := by decide
  by_cases hi : i ≥ 6
  · have : 571428 / 10 ^ i = 0 := by
      have : 10 ^ 6 ≤ 10 ^ i := Nat.pow_le_pow_right (by decide) hi
      exact Nat.div_eq_of_lt (lt_of_lt_of_le h571 this)
    simp [this]
  · have : i ≤ 5 := by omega
    interval_cases i <;> decide

lemma ones_digit_571428 : digit10 571428 0 = 8 := by
  rw [digit10_eq]; decide

/-- A 0-1 number strictly below the target repunit, from a power bound. -/
lemma expandCounts_lt_pow_of_bound {c : ℕ → ℕ} {d bound : ℕ}
    (hd : 0 < d)
    (hpos : ∃ r < d, 0 < c r)
    (hbound : ∀ r < d, 0 < c r → r + (c r - 1) * d + 1 ≤ bound) :
    expandCounts c d < 10 ^ bound := by
  have h := expandCounts_le_pow (c := c) (d := d) (C := bound) hd hbound
  rcases h with h | h0
  · exact h
  · have := expandCounts_pos (c := c) hd hpos
    omega

lemma le_order_of_large_m {m k d : ℕ}
    (hmlo : 10 ^ (k - 1) - 1 ≤ m) (hdvd : m ∣ 10 ^ d - 1) (hdpos : 0 < d) :
    k - 1 ≤ d := by
  have h10d : 10 ≤ 10 ^ d := Nat.le_pow hdpos
  have h1d : 1 ≤ 10 ^ d := Nat.one_le_pow _ _ (by decide)
  have hpos' : 0 < 10 ^ d - 1 := by omega
  have hle1 : m ≤ 10 ^ d - 1 := Nat.le_of_dvd hpos' hdvd
  have hle2 : 10 ^ (k - 1) - 1 ≤ 10 ^ d - 1 := le_trans hmlo hle1
  have h1k : 1 ≤ 10 ^ (k - 1) := Nat.one_le_pow _ _ (by decide)
  have h1d' : 1 ≤ 10 ^ d := h1d
  have : 10 ^ (k - 1) ≤ 10 ^ d := by
    have := Nat.add_le_add_right hle2 1
    rwa [Nat.sub_add_cancel h1k, Nat.sub_add_cancel h1d'] at this
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 10)).1 this

lemma eq_of_dvd_ten_pow_pred {m k : ℕ} (hk : 2 ≤ k)
    (hmlo : 10 ^ (k - 1) - 1 ≤ m) (hdvd : m ∣ 10 ^ (k - 1) - 1) :
    m = 10 ^ (k - 1) - 1 := by
  have hpos' : 0 < 10 ^ (k - 1) - 1 := by
    have : 10 ≤ 10 ^ (k - 1) := Nat.le_pow (by omega)
    omega
  have : m ≤ 10 ^ (k - 1) - 1 := Nat.le_of_dvd hpos' hdvd
  omega

lemma nine_mul_succ_gap {k : ℕ} (hk : 1 ≤ k) : 9 * (k - 1) + 9 = 9 * k := by
  have : k - 1 + 1 = k := Nat.sub_add_cancel hk
  calc 9 * (k - 1) + 9
      = 9 * ((k - 1) + 1) := by ring
    _ = 9 * k := by rw [this]

lemma nine_pred_add_le {k t : ℕ} (hk : 1 ≤ k) (ht : t ≤ 9) :
    9 * (k - 1) + t ≤ 9 * k := by
  have := nine_mul_succ_gap hk
  omega

lemma nine_pred_add_lt {k t : ℕ} (hk : 1 ≤ k) (ht : t < 9) :
    9 * (k - 1) + t < 9 * k := by
  have := nine_mul_succ_gap hk
  omega

lemma two_le_quot_of_lt {m s N : ℕ} (hm : 0 < m) (h : m * s = N) (hlt : m < N) :
    2 ≤ s := by
  have : m * 1 < m * s := by
    rwa [mul_one, h]
  exact Nat.succ_le_of_lt (lt_of_mul_lt_mul_left this (Nat.zero_le _))

lemma five_ne_quot {k m : ℕ} (hk : 0 < k) (hdvd : m ∣ 10 ^ k - 1)
    (_hm : 0 < m) : (10 ^ k - 1) / m ≠ 5 := by
  intro h
  have hmul : m * 5 = 10 ^ k - 1 := by
    have := Nat.mul_div_cancel' hdvd
    rwa [h] at this
  have : 5 ∣ 10 ^ k - 1 := by
    rw [← hmul, mul_comm]
    exact dvd_mul_right _ _
  exact five_not_dvd_ten_pow_sub_one hk this

lemma eleven_quot_order {m : ℕ} (_hm : Nat.Coprime m 10) (_hmpos : 0 < m)
    (h : (10 ^ 2 - 1) / m = 11) (hdvd : m ∣ 10 ^ 2 - 1) :
    order10 m ≠ 2 := by
  have hmul : m * 11 = 99 := by
    have := Nat.mul_div_cancel' hdvd
    rwa [h] at this
  have hm9 : m = 9 := by
    have : m * 11 = 9 * 11 := hmul
    exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 11) this
  subst m
  intro hord
  have h1 : 10 ^ 1 ≡ 1 [MOD 9] := by decide
  have : order10 9 ≤ 1 := order10_le_of_modEq (by decide : 0 < 1) h1
  omega

lemma k_add_three_lt_nine_k {k : ℕ} (hk : 2 ≤ k) : k + 3 < 9 * k := by
  omega

lemma three_k_add_three_lt_nine_k {k : ℕ} (hk : 2 ≤ k) : 3 * k + 3 < 9 * k := by
  omega

lemma eight_k_add_three_lt_nine_k {k : ℕ} (hk : 4 ≤ k) : 8 * k + 3 < 9 * k := by
  omega

lemma A_le_repunit_self {l : ℕ} (hl : 0 < l) :
    A004290 ((10 ^ l - 1) / 9) ≤ (10 ^ l - 1) / 9 :=
  A004290_le_self_of_is01 (repunit_pos l hl) (Is01.repunit l)

def digit571428 : ℕ → ℕ
  | 0 => 8
  | 1 => 2
  | 2 => 4
  | 3 => 1
  | 4 => 7
  | 5 => 5
  | n + 6 => digit571428 n

lemma digit571428_le_eight : ∀ n, digit571428 n ≤ 8
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | 4 => by decide
  | 5 => by decide
  | n + 6 => digit571428_le_eight n

lemma digit571428_zero : digit571428 0 = 8 := rfl

lemma four_mul_div_seven_lt (q : ℕ) :
    4 * ((10 ^ (6 * q) - 1) / 7) < 10 ^ (6 * q) := by
  have h7 : 0 < 7 := by decide
  have hdiv : 7 ∣ 10 ^ (6 * q) - 1 := seven_dvd_ten_pow_sub_one.2 ⟨q, rfl⟩
  have hmul : 4 * ((10 ^ (6 * q) - 1) / 7) * 7 = 4 * (10 ^ (6 * q) - 1) := by
    rw [mul_assoc, Nat.div_mul_cancel hdiv]
  have : 4 * (10 ^ (6 * q) - 1) < 10 ^ (6 * q) * 7 := by
    have h1 : 1 ≤ 10 ^ (6 * q) := Nat.one_le_pow _ _ (by decide)
    have : 4 * 10 ^ (6 * q) - 4 < 7 * 10 ^ (6 * q) := by
      have : 4 * 10 ^ (6 * q) < 7 * 10 ^ (6 * q) + 4 := by
        have : 4 * 10 ^ (6 * q) ≤ 7 * 10 ^ (6 * q) :=
          Nat.mul_le_mul_right _ (by decide)
        omega
      omega
    have : 4 * (10 ^ (6 * q) - 1) = 4 * 10 ^ (6 * q) - 4 := by
      rw [Nat.mul_sub_left_distrib]
    omega
  have : 4 * ((10 ^ (6 * q) - 1) / 7) * 7 < 10 ^ (6 * q) * 7 := by
    rwa [hmul]
  exact Nat.lt_of_mul_lt_mul_right this

lemma four_mul_div_seven_succ (q : ℕ) :
    4 * ((10 ^ (6 * (q + 1)) - 1) / 7) =
      4 * ((10 ^ (6 * q) - 1) / 7) * 10 ^ 6 + 571428 := by
  have h7 : 7 ∣ 10 ^ 6 - 1 := by decide
  have hq : 7 ∣ 10 ^ (6 * q) - 1 := seven_dvd_ten_pow_sub_one.2 ⟨q, rfl⟩
  have hqp : 7 ∣ 10 ^ (6 * (q + 1)) - 1 :=
    seven_dvd_ten_pow_sub_one.2 ⟨q + 1, rfl⟩
  have hsplit : 10 ^ (6 * (q + 1)) - 1 =
      (10 ^ (6 * q) - 1) * 10 ^ 6 + (10 ^ 6 - 1) := by
    have h1 : 1 ≤ 10 ^ (6 * q) := Nat.one_le_pow _ _ (by decide)
    have : 6 * (q + 1) = 6 * q + 6 := by ring
    rw [this, pow_add]
    have : 10 ^ (6 * q) * 10 ^ 6 - 1 =
        (10 ^ (6 * q) - 1) * 10 ^ 6 + (10 ^ 6 - 1) := by
      have := Nat.mul_sub_right_distrib (10 ^ (6 * q)) 1 (10 ^ 6)
      have h16 : 1 ≤ 10 ^ 6 := by decide
      omega
    exact this
  have : ((10 ^ (6 * q) - 1) * 10 ^ 6 + (10 ^ 6 - 1)) / 7 =
      ((10 ^ (6 * q) - 1) / 7) * 10 ^ 6 + (10 ^ 6 - 1) / 7 := by
    have hA := Nat.mul_div_assoc (10 ^ 6) hq
    have : ((10 ^ (6 * q) - 1) * 10 ^ 6) / 7 + (10 ^ 6 - 1) / 7 =
        ((10 ^ (6 * q) - 1) / 7) * 10 ^ 6 + (10 ^ 6 - 1) / 7 := by
      rw [mul_comm (10 ^ (6 * q) - 1), Nat.mul_div_assoc _ hq, mul_comm]
    have hsum := Nat.add_div_of_dvd_left (c := 7) (b := 10 ^ 6 - 1)
      (a := (10 ^ (6 * q) - 1) * 10 ^ 6) h7
    rwa [hsum]
  rw [hsplit, this, Nat.left_distrib, four_div_seven_block]
  ring

lemma digit10_low {a b L i : ℕ} (hb : b < 10 ^ L) (hi : i < L) :
    digit10 (a * 10 ^ L + b) i = digit10 b i := by
  rw [digit10_eq, digit10_eq]
  have hL : i + (L - i) = L := Nat.add_sub_of_le (Nat.le_of_lt hi)
  have : (a * 10 ^ L + b) / 10 ^ i = a * 10 ^ (L - i) + b / 10 ^ i := by
    have hpow : 10 ^ L = 10 ^ i * 10 ^ (L - i) := by
      rw [← pow_add, hL]
    have hswap : a * 10 ^ i * 10 ^ (L - i) = a * 10 ^ (L - i) * 10 ^ i := by ring
    rw [hpow, ← mul_assoc, hswap, add_comm]
    have hdiv := Nat.add_mul_div_right b (a * 10 ^ (L - i))
      (pow_pos (by decide : 0 < 10) i)
    rw [hdiv, add_comm]
  rw [this]
  have hge : 1 ≤ L - i := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hi)
  have : a * 10 ^ (L - i) % 10 = 0 := by
    have : 10 ∣ 10 ^ (L - i) :=
      dvd_pow_self 10 (Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt hi))
    have : 10 ∣ a * 10 ^ (L - i) := dvd_mul_of_dvd_right this _
    exact Nat.mod_eq_zero_of_dvd this
  rw [Nat.add_mod, this, zero_add, Nat.mod_mod]

lemma digit10_high {a b L i : ℕ} (hb : b < 10 ^ L) (hi : L ≤ i) :
    digit10 (a * 10 ^ L + b) i = digit10 a (i - L) := by
  rw [digit10_eq, digit10_eq]
  have : (a * 10 ^ L + b) / 10 ^ i = a / 10 ^ (i - L) := by
    have hpow : 10 ^ i = 10 ^ L * 10 ^ (i - L) := by
      rw [← pow_add, Nat.add_sub_of_le hi]
    have hdiv : (a * 10 ^ L + b) / 10 ^ L = a := by
      rw [add_comm, Nat.add_mul_div_right _ _ (pow_pos (by decide : 0 < 10) L),
        Nat.div_eq_of_lt hb, zero_add]
    rw [hpow, ← Nat.div_div_eq_div_mul, hdiv]
  rw [this]

lemma four_mul_digit_le_eight : ∀ q i,
    digit10 (4 * ((10 ^ (6 * q) - 1) / 7)) i ≤ 8
  | 0, i => by
      simp only [mul_zero, pow_zero, Nat.sub_self, Nat.zero_div, mul_zero]
      rw [digit10_eq]
      simp
  | q + 1, i => by
      rw [four_mul_div_seven_succ]
      have hb : 571428 < 10 ^ 6 := by decide
      by_cases hi : i < 6
      · have := digit10_low (a := 4 * ((10 ^ (6 * q) - 1) / 7)) hb hi
        rw [this]
        have : digit10 571428 i ≤ 8 := digits_571428_le_eight i
        exact this
      · have : 6 ≤ i := Nat.le_of_not_gt hi
        have := digit10_high (a := 4 * ((10 ^ (6 * q) - 1) / 7)) hb this
        rw [this]
        exact four_mul_digit_le_eight q (i - 6)

lemma four_mul_repunit7_mod_ten :
    ∀ q, 0 < q → 4 * ((10 ^ (6 * q) - 1) / 7) % 10 = 8
  | 0, h => (Nat.lt_irrefl 0 h).elim
  | q + 1, _ => by
      rw [four_mul_div_seven_succ, Nat.add_mod]
      have h571 : 571428 % 10 = 8 := by decide
      have hpow : (4 * ((10 ^ (6 * q) - 1) / 7) * 10 ^ 6) % 10 = 0 := by
        have : 10 ∣ 10 ^ 6 :=
          dvd_pow_self 10 (by decide : 6 ≠ 0)
        have : 10 ∣ 4 * ((10 ^ (6 * q) - 1) / 7) * 10 ^ 6 :=
          dvd_mul_of_dvd_right this _
        exact Nat.mod_eq_zero_of_dvd this
      rw [hpow, zero_add, Nat.mod_mod, h571]

lemma four_mul_repunit7_ones_digit {q : ℕ} (hq : 0 < q) :
    digit10 (4 * ((10 ^ (6 * q) - 1) / 7)) 0 = 8 := by
  rw [digit10_eq, pow_zero, Nat.div_one]
  exact four_mul_repunit7_mod_ten q hq

lemma A_of_s_nine {k t : ℕ} (hk : 2 ≤ k) (ht : t ≤ 3) :
    A004290 ((10 ^ k - 1) / 9) * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  have hk0 : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk
  have hA : A004290 ((10 ^ k - 1) / 9) ≤ (10 ^ k - 1) / 9 :=
    A_le_repunit_self hk0
  have hbound : ((10 ^ k - 1) / 9) * 10 ^ t < (10 ^ (9 * k) - 1) / 9 :=
    repunit_mul_ten_lt (k_add_three_lt_nine_k hk |>.trans_le' (by omega))
  exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hA) hbound

lemma three_dvd_ten_pow_sub (k : ℕ) : 3 ∣ 10 ^ k - 1 := by
  have h : 10 ≡ 1 [MOD 3] := by decide
  have : 10 ^ k ≡ 1 ^ k [MOD 3] := Nat.ModEq.pow k h
  have h1 : 1 ^ k = 1 := one_pow k
  rw [h1] at this
  rw [Nat.ModEq.comm] at this
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow k 10 (by decide))).1 this

lemma A_of_s_three {k t m : ℕ} (hk : 2 ≤ k) (ht : t ≤ 3)
    (hm : m = (10 ^ k - 1) / 3) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  have hk0 : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk
  have h3 : 3 ∣ 10 ^ k - 1 := three_dvd_ten_pow_sub k
  have hdvd := dvd_repunit_three_mul hk0 hm h3
  have hpos : 0 < 3 * k := Nat.mul_pos (by decide) hk0
  have hA : A004290 m ≤ (10 ^ (3 * k) - 1) / 9 :=
    A004290_le (repunit_pos _ hpos) hdvd (Is01.repunit _)
  have hlt : 3 * k + t < 9 * k :=
    lt_of_le_of_lt (Nat.add_le_add_left ht _) (three_k_add_three_lt_nine_k hk)
  have hbound : ((10 ^ (3 * k) - 1) / 9) * 10 ^ t < (10 ^ (9 * k) - 1) / 9 :=
    repunit_mul_ten_lt hlt
  exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hA) hbound

lemma A_of_s_seven {k t m : ℕ} (hk : 6 ≤ k) (ht : t ≤ 3)
    (h6 : 6 ∣ k) (hm : m = (10 ^ k - 1) / 7) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  obtain ⟨q, hq⟩ := h6
  have hqk : k = 6 * q := hq
  have hk0 : 0 < k := lt_of_lt_of_le (by decide : 0 < 6) hk
  have hqpos : 0 < q := by
    have : 6 * q = k := hq.symm
    have : 0 < 6 * q := by rwa [this]
    omega
  have h7 : 7 ∣ 10 ^ k - 1 := by
    rw [hqk]; exact seven_dvd_ten_pow_sub_one.2 ⟨q, rfl⟩
  set N := 4 * ((10 ^ k - 1) / 7)
  have hNeq : N = 4 * ((10 ^ (6 * q) - 1) / 7) := by
    simp only [N, hqk]
  have hNlt : N < 10 ^ k := by
    rw [hNeq, hqk]
    exact four_mul_div_seven_lt q
  have hmod : 10 ^ k ≡ 1 [MOD m] :=
    (ten_pow_modEq_one_iff_dvd hk0).2 (by
      rw [hm]; exact Nat.div_dvd_of_dvd h7)
  have hdvdN : m ∣ N := by
    rw [hm]; exact dvd_mul_left _ _
  have hdig : ∀ r < k, digit10 N r ≤ 8 := by
    intro r _hr
    rw [hNeq]
    exact four_mul_digit_le_eight q r
  have hdig0 : digit10 N 0 = 8 := by
    rw [hNeq]
    exact four_mul_repunit7_ones_digit hqpos
  have hposE : 0 < expandCounts (fun r => digit10 N r) k :=
    expandCounts_pos (c := fun r => digit10 N r) hk0 ⟨0, hk0, by
      change 0 < digit10 N 0
      rw [hdig0]; decide⟩
  have hdvdE : m ∣ expandCounts (fun r => digit10 N r) k :=
    expandCounts_of_digits_dvd hk0 hNlt hmod hdvdN
  have hA : A004290 m ≤ expandCounts (fun r => digit10 N r) k :=
    A004290_le hposE hdvdE (is01_expandCounts hk0)
  have hbound : ∀ r < k, 0 < digit10 N r →
      r + (digit10 N r - 1) * k + 1 ≤ 8 * k := by
    intro r hr hrpos
    have hdc : digit10 N r ≤ 8 := hdig r hr
    have hle1 : digit10 N r - 1 ≤ 7 := by omega
    have hr' : r ≤ k - 1 := Nat.le_pred_of_lt hr
    have hmul : (digit10 N r - 1) * k ≤ 7 * k := Nat.mul_le_mul_right k hle1
    have : r + (digit10 N r - 1) * k + 1 ≤ (k - 1) + 7 * k + 1 :=
      Nat.add_le_add (Nat.add_le_add hr' hmul) (le_refl 1)
    have heq : (k - 1) + 7 * k + 1 = 8 * k := by
      have : 1 ≤ k := hk0
      omega
    rwa [heq] at this
  have hltpow : expandCounts (fun r => digit10 N r) k < 10 ^ (8 * k) :=
    expandCounts_lt_pow_of_bound hk0 ⟨0, hk0, by
      change 0 < digit10 N 0
      rw [hdig0]; decide⟩ hbound
  have hA' : A004290 m < 10 ^ (8 * k) := lt_of_le_of_lt hA hltpow
  have hsum : 8 * k + t < 9 * k := by
    have : 8 * k + 3 < 9 * k :=
      eight_k_add_three_lt_nine_k (le_trans (by decide : 4 ≤ 6) hk)
    omega
  have hL : 1 < 9 * k := by
    have : 1 ≤ k := hk0
    omega
  exact A_mul_ten_lt_of_lt_pow hA' hL hsum

lemma s_of_order_eq_k {k m : ℕ} (hk : 2 ≤ k) (hmpos : 0 < m)
    (hmlo : 10 ^ (k - 1) - 1 ≤ m) (hm_lt : m < 10 ^ k - 1)
    (hdvd : m ∣ 10 ^ k - 1) :
    let s := (10 ^ k - 1) / m
    3 ≤ s ∧ s ≤ 11 ∧ Odd s ∧ s ≠ 5 := by
  intro s
  have hk0 : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk
  have hmul : m * s = 10 ^ k - 1 := Nat.mul_div_cancel' hdvd
  have hs2 : 2 ≤ s := two_le_quot_of_lt hmpos hmul hm_lt
  have hsle : s ≤ 11 := quot_le_eleven hk hmpos hmlo
  have hoddN : Odd (10 ^ k - 1) := ten_pow_sub_one_odd hk0
  have hsodd : Odd s := odd_quot_of_odd_div hoddN hmpos hdvd
  have hsne5 : s ≠ 5 := five_ne_quot hk0 hdvd hmpos
  -- 2 ≤ s and s odd ⇒ 3 ≤ s
  have hs3 : 3 ≤ s := by
    have : s ≠ 2 := fun h => by
      have : Odd 2 := by rwa [h] at hsodd
      exact Nat.not_odd_iff_even.2 (by decide) this
    omega
  exact ⟨hs3, hsle, hsodd, hsne5⟩

lemma s_ne_eleven_of_order {k m : ℕ} (hk : 2 ≤ k)
    (hm : Nat.Coprime m 10) (hmpos : 0 < m)
    (hord : order10 m = k) (hdvd : m ∣ 10 ^ k - 1)
    (hmlo : 10 ^ (k - 1) - 1 ≤ m) :
    (10 ^ k - 1) / m ≠ 11 := by
  intro hs
  by_cases hk2 : k = 2
  · rw [hk2] at hs hdvd hord
    exact eleven_quot_order hm hmpos hs hdvd hord
  · have hk3 : 3 ≤ k := by omega
    have : (10 ^ k - 1) / m ≤ 10 := quot_le_ten hk3 hmpos hmlo
    omega

lemma seven_of_s_eq {k m : ℕ} (hdvd : m ∣ 10 ^ k - 1)
    (hs : (10 ^ k - 1) / m = 7) : 6 ∣ k := by
  have hmul : m * 7 = 10 ^ k - 1 := by
    have := Nat.mul_div_cancel' hdvd
    rwa [hs] at this
  have : 7 ∣ 10 ^ k - 1 := by
    rw [← hmul, mul_comm]
    exact dvd_mul_right _ _
  exact (seven_dvd_ten_pow_sub_one).1 this

lemma eq_div_of_quot {m s N : ℕ} (hdvd : m ∣ N) (hs : N / m = s) (hspos : 0 < s) :
    m = N / s := by
  have hmul : m * s = N := by
    have := Nat.mul_div_cancel' hdvd
    rwa [hs] at this
  have hmul' : N = s * m := by rw [← hmul, mul_comm]
  exact (Nat.div_eq_of_eq_mul_right hspos hmul').symm

lemma A_of_s_seven' {k t m : ℕ} (hk : 2 ≤ k) (ht : t ≤ 3)
    (hs : (10 ^ k - 1) / m = 7)
    (hdvd : m ∣ 10 ^ k - 1) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  have h6 : 6 ∣ k := seven_of_s_eq hdvd hs
  have hk6 : 6 ≤ k := by
    obtain ⟨q, hq⟩ := h6
    have hq0 : q ≠ 0 := by
      intro h
      subst h
      have : k = 0 := by simpa using hq
      omega
    have : 1 ≤ q := Nat.pos_of_ne_zero hq0
    omega
  have hm : m = (10 ^ k - 1) / 7 :=
    eq_div_of_quot hdvd hs (by decide)
  exact A_of_s_seven hk6 ht h6 hm

lemma A_of_order_eq_k {k t m : ℕ} (hk : 2 ≤ k) (ht : t ≤ 3)
    (hm : Nat.Coprime m 10) (hmpos : 0 < m)
    (hmlo : 10 ^ (k - 1) - 1 ≤ m) (hm_lt : m < 10 ^ k - 1)
    (hord : order10 m = k) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  have hdvd : m ∣ 10 ^ k - 1 := by
    have := dvd_ten_pow_sub_one_of_order hm hmpos
    rwa [hord] at this
  obtain ⟨hs3, hsle, hsodd, hsne5⟩ := s_of_order_eq_k hk hmpos hmlo hm_lt hdvd
  have hsne11 := s_ne_eleven_of_order hk hm hmpos hord hdvd hmlo
  set s := (10 ^ k - 1) / m
  have hsval : s = 3 ∨ s = 7 ∨ s = 9 := by
    obtain ⟨q, hq⟩ := hsodd
    have hqle : q ≤ 5 := by omega
    have hqge : 1 ≤ q := by omega
    have hcases : q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hcases with hq1 | hq2 | hq3 | hq4 | hq5
    · left; rw [hq, hq1]; rfl
    · exact (hsne5 (by rw [hq, hq2]; rfl)).elim
    · right; left; rw [hq, hq3]; rfl
    · right; right; rw [hq, hq4]; rfl
    · exact (hsne11 (by rw [hq, hq5]; rfl)).elim
  rcases hsval with h3 | h7 | h9
  · have hm3 : m = (10 ^ k - 1) / 3 := eq_div_of_quot hdvd h3 (by decide)
    exact A_of_s_three hk ht hm3
  · exact A_of_s_seven' hk ht h7 hdvd
  · have hm9 : m = (10 ^ k - 1) / 9 := eq_div_of_quot hdvd h9 (by decide)
    simpa [hm9] using A_of_s_nine (k := k) (t := t) hk ht

lemma A_of_coprime9_order_le {k t m : ℕ} (hk : 2 ≤ k) (ht : t ≤ 3)
    (hm : Nat.Coprime m 10) (hmpos : 0 < m) (h9 : Nat.Coprime m 9)
    (hsum : order10 m + t ≤ 9 * k)
    (htcase : order10 m + t < 9 * k ∨ 0 < t) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  have hA : A004290 m ≤ (10 ^ order10 m - 1) / 9 :=
    A004290_le_repunit_order hm hmpos h9
  have hbound : ((10 ^ order10 m - 1) / 9) * 10 ^ t < (10 ^ (9 * k) - 1) / 9 :=
    repunit_mul_ten_lt_of_add_le hsum htcase
  exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hA) hbound

lemma A_of_coprime9_small_order {k t m : ℕ} (hk : 2 ≤ k) (ht : t ≤ 3)
    (hm : Nat.Coprime m 10) (hmpos : 0 < m) (h9 : Nat.Coprime m 9)
    (hd : order10 m + 3 ≤ 9 * k) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  have hsum : order10 m + t ≤ 9 * k := by omega
  have htcase : order10 m + t < 9 * k ∨ 0 < t := by
    by_cases heq : order10 m + t = 9 * k
    · right; omega
    · left; omega
  exact A_of_coprime9_order_le hk ht hm hmpos h9 hsum htcase

lemma is01_ten_pow_add_one {e : ℕ} (he : 0 < e) : Is01 (10 ^ e + 1) := by
  have hne : e ≠ 0 := Nat.pos_iff_ne_zero.mp he
  have : 10 ^ e + 1 = ∑ i ∈ ({0, e} : Finset ℕ), 10 ^ i := by
    rw [Finset.sum_pair (Ne.symm hne), pow_zero, add_comm]
  rw [this]
  exact is01_sum_pow _

lemma ten_pow_add_one_pos (e : ℕ) : 0 < 10 ^ e + 1 :=
  Nat.succ_pos _

lemma A_le_ten_pow_add_one {m e : ℕ} (he : 0 < e)
    (hdvd : m ∣ 10 ^ e + 1) :
    A004290 m ≤ 10 ^ e + 1 :=
  A004290_le (ten_pow_add_one_pos e) hdvd (is01_ten_pow_add_one he)

lemma A_mul_ten_lt_of_le_pow_succ {m t e L : ℕ}
    (hA : A004290 m ≤ 10 ^ e + 1)
    (hL : 1 < L) (h : e + 1 + t < L) :
    A004290 m * 10 ^ t < (10 ^ L - 1) / 9 := by
  have hle1 : 10 ^ e + 1 ≤ 10 ^ (e + 1) := by
    have : 1 ≤ 10 ^ e := Nat.one_le_pow _ _ (by decide)
    have h2 : 10 ^ e + 1 ≤ 2 * 10 ^ e := by omega
    have h10 : 2 * 10 ^ e ≤ 10 * 10 ^ e := by omega
    have : 10 * 10 ^ e = 10 ^ (e + 1) := by rw [pow_succ, mul_comm]
    omega
  have hmul : (10 ^ e + 1) * 10 ^ t ≤ 10 ^ (e + 1 + t) := by
    have := Nat.mul_le_mul_right (10 ^ t) hle1
    rwa [← pow_add] at this
  have hle : e + 1 + t ≤ L - 1 := by omega
  have hpow : 10 ^ (e + 1 + t) ≤ 10 ^ (L - 1) :=
    Nat.pow_le_pow_right (by decide) hle
  have hbound : (10 ^ e + 1) * 10 ^ t < (10 ^ L - 1) / 9 :=
    lt_of_le_of_lt (le_trans hmul hpow) (pow_lt_repunit hL)
  exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hA) hbound

lemma repunit_modEq_len {l : ℕ} :
    (10 ^ l - 1) / 9 ≡ l [MOD 9] := by
  have h10 : 10 ≡ 1 [MOD 9] := by decide
  have hpow : ∀ i, 10 ^ i ≡ 1 [MOD 9] := fun i => by
    simpa using Nat.ModEq.pow i h10
  have hsum : ∑ i ∈ Finset.range l, 10 ^ i ≡ ∑ i ∈ Finset.range l, 1 [MOD 9] :=
    Nat.ModEq.sum fun i _ => hpow i
  simpa [geom_sum_ten l] using hsum

lemma three_dvd_repunit_iff {l : ℕ} :
    3 ∣ (10 ^ l - 1) / 9 ↔ 3 ∣ l := by
  have hsum := repunit_modEq_len (l := l)
  have hmod3 : (10 ^ l - 1) / 9 ≡ l [MOD 3] :=
    Nat.ModEq.of_dvd (by decide : 3 ∣ 9) hsum
  constructor
  · intro h
    have : (10 ^ l - 1) / 9 ≡ 0 [MOD 3] := Nat.modEq_zero_iff_dvd.2 h
    exact Nat.modEq_zero_iff_dvd.1 (hmod3.symm.trans this)
  · intro h
    have : l ≡ 0 [MOD 3] := Nat.modEq_zero_iff_dvd.2 h
    exact Nat.modEq_zero_iff_dvd.1 (hmod3.trans this)

lemma dvd_repunit_of_dvd_pow {a b : ℕ} (hab : a ∣ b) :
    (10 ^ a - 1) / 9 ∣ (10 ^ b - 1) / 9 := by
  have hab' : 10 ^ a - 1 ∣ 10 ^ b - 1 :=
    Nat.pow_sub_one_dvd_pow_sub_one 10 hab
  have h9a := nine_dvd_ten_pow_sub_one a
  have h9b := nine_dvd_ten_pow_sub_one b
  have : 9 * ((10 ^ a - 1) / 9) ∣ 9 * ((10 ^ b - 1) / 9) := by
    rwa [Nat.mul_div_cancel' h9a, Nat.mul_div_cancel' h9b]
  exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 9) this

lemma not_three_dvd_div {m : ℕ} (h3 : 3 ∣ m) (h9 : ¬ 9 ∣ m) :
    ¬ 3 ∣ m / 3 := by
  intro h
  have : 9 ∣ m := by
    have hm : m / 3 * 3 = m := Nat.div_mul_cancel h3
    have : 3 * 3 ∣ (m / 3) * 3 := Nat.mul_dvd_mul h (dvd_refl 3)
    rwa [hm] at this
  exact h9 this

lemma coprime9_of_not_three {n : ℕ} (h : ¬ 3 ∣ n) : Nat.Coprime n 9 := by
  refine (Nat.coprime_pow_right_iff (by decide : 0 < 2) n 3).2 ?_
  exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h).symm

lemma dvd_repunit_lcm_three {m d : ℕ} (hd : 0 < d)
    (h3 : 3 ∣ m) (h9 : ¬ 9 ∣ m)
    (hdvd : m ∣ 10 ^ d - 1) :
    m ∣ (10 ^ (Nat.lcm d 3) - 1) / 9 := by
  set e := Nat.lcm d 3 with he
  have hde : d ∣ e := Nat.dvd_lcm_left d 3
  have h3e : 3 ∣ e := Nat.dvd_lcm_right d 3
  have hepos : 0 < e := Nat.lcm_pos hd (by decide)
  have hm' : m / 3 * 3 = m := Nat.div_mul_cancel h3
  have hnot3 := not_three_dvd_div h3 h9
  have hcop := coprime9_of_not_three hnot3
  have hdvd' : m / 3 ∣ 10 ^ d - 1 :=
    Nat.dvd_trans (Nat.div_dvd_of_dvd h3) hdvd
  have hRd : m / 3 ∣ (10 ^ d - 1) / 9 :=
    dvd_repunit_of_coprime9 hd hcop hdvd'
  have hRe : (10 ^ d - 1) / 9 ∣ (10 ^ e - 1) / 9 :=
    dvd_repunit_of_dvd_pow hde
  have hm'Re : m / 3 ∣ (10 ^ e - 1) / 9 := Nat.dvd_trans hRd hRe
  have h3Re : 3 ∣ (10 ^ e - 1) / 9 := three_dvd_repunit_iff.2 h3e
  have hcop3 : Nat.Coprime (m / 3) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnot3).symm
  have hmul := hcop3.mul_dvd_of_dvd_of_dvd hm'Re h3Re
  rwa [hm'] at hmul

lemma dvd_repunit_lcm_nine {m d : ℕ} (hd : 0 < d)
    (h9 : 9 ∣ m) (h27 : ¬ 27 ∣ m)
    (hdvd : m ∣ 10 ^ d - 1) :
    m ∣ (10 ^ (Nat.lcm d 9) - 1) / 9 := by
  set e := Nat.lcm d 9
  have hde : d ∣ e := Nat.dvd_lcm_left d 9
  have h9e : 9 ∣ e := Nat.dvd_lcm_right d 9
  have hepos : 0 < e := Nat.lcm_pos hd (by decide)
  have hm' : m / 9 * 9 = m := Nat.div_mul_cancel h9
  have hnot3 : ¬ 3 ∣ m / 9 := by
    intro h
    have : 27 ∣ m := by
      have : 3 * 9 ∣ (m / 9) * 9 := Nat.mul_dvd_mul h (dvd_refl 9)
      rwa [hm'] at this
    exact h27 this
  have hcop := coprime9_of_not_three hnot3
  have hdvd' : m / 9 ∣ 10 ^ d - 1 :=
    Nat.dvd_trans (Nat.div_dvd_of_dvd h9) hdvd
  have hRd : m / 9 ∣ (10 ^ d - 1) / 9 :=
    dvd_repunit_of_coprime9 hd hcop hdvd'
  have hRe : (10 ^ d - 1) / 9 ∣ (10 ^ e - 1) / 9 :=
    dvd_repunit_of_dvd_pow hde
  have hm'Re : m / 9 ∣ (10 ^ e - 1) / 9 := Nat.dvd_trans hRd hRe
  have hsum := repunit_modEq_len (l := e)
  have h9Re : 9 ∣ (10 ^ e - 1) / 9 :=
    Nat.modEq_zero_iff_dvd.1 (hsum.trans (Nat.modEq_zero_iff_dvd.2 h9e))
  have hmul := hcop.mul_dvd_of_dvd_of_dvd hm'Re h9Re
  rwa [hm'] at hmul

lemma A_of_three_mul_repunit_le {k t m d : ℕ} (hk : 2 ≤ k) (ht : t ≤ 3)
    (hmpos : 0 < m) (hd : 0 < d)
    (hdvdR : m ∣ (10 ^ d - 1) / 9)
    (hle : d + t ≤ 9 * k)
    (htcase : d + t < 9 * k ∨ 0 < t) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  have hA : A004290 m ≤ (10 ^ d - 1) / 9 :=
    A004290_le (repunit_pos d hd) hdvdR (Is01.repunit d)
  have hbound : ((10 ^ d - 1) / 9) * 10 ^ t < (10 ^ (9 * k) - 1) / 9 :=
    repunit_mul_ten_lt_of_add_le hle htcase
  exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hA) hbound

lemma A_of_three_mul_repunit {k t m d : ℕ} (hk : 2 ≤ k) (ht : t ≤ 3)
    (hmpos : 0 < m) (hd : 0 < d)
    (hdvdR : m ∣ (10 ^ d - 1) / 9)
    (hsum : d + 3 ≤ 9 * k) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  have hle : d + t ≤ 9 * k := by omega
  have htcase : d + t < 9 * k ∨ 0 < t := by
    by_cases heq : d + t = 9 * k
    · right; omega
    · left; omega
  exact A_of_three_mul_repunit_le hk ht hmpos hd hdvdR hle htcase

lemma three_dvd_of_not_coprime9 {m : ℕ} (h9 : ¬ Nat.Coprime m 9) : 3 ∣ m := by
  have hg : Nat.gcd m 9 ≠ 1 := fun h => h9 h
  have hdvd9 : Nat.gcd m 9 ∣ 3 ^ 2 := by
    simpa using Nat.gcd_dvd_right m 9
  obtain ⟨k, hk, heq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd9
  have hk0 : k ≠ 0 := by
    intro h
    subst h
    simp at heq
    exact hg heq
  have : 3 ∣ 3 ^ k := dvd_pow_self 3 hk0
  rw [← heq] at this
  exact Nat.dvd_trans this (Nat.gcd_dvd_left m 9)

lemma two_mul_div_of_even {n : ℕ} (h : 2 ∣ n) : 2 * (n / 2) = n :=
  Nat.mul_div_cancel' h

lemma ten_pow_even_split {n : ℕ} (h : 2 ∣ n) :
    10 ^ n - 1 = (10 ^ (n / 2) - 1) * (10 ^ (n / 2) + 1) := by
  have hn : n / 2 * 2 = n := by
    rw [mul_comm]
    exact two_mul_div_of_even h
  have hpow : 10 ^ n = (10 ^ (n / 2)) ^ 2 := by
    rw [← pow_mul, hn]
  have : (10 ^ (n / 2)) ^ 2 - 1 =
      (10 ^ (n / 2) - 1) * (10 ^ (n / 2) + 1) := by
    rw [mul_comm]
    simpa [one_pow] using (Nat.sq_sub_sq (10 ^ (n / 2)) 1)
  simpa [hpow] using this

lemma A_of_dvd_ten_pow_add_one {k t m e : ℕ} (_ht : t ≤ 3)
    (he : 0 < e) (hdvd : m ∣ 10 ^ e + 1)
    (hlen : e + 1 + t < 9 * k) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 :=
  A_mul_ten_lt_of_le_pow_succ (A_le_ten_pow_add_one he hdvd) (by omega) hlen

lemma ten_pow_half_eq_neg_one {m e : ℕ}
    (hdvd : m ∣ 10 ^ (2 * e) - 1)
    (hcop : Nat.Coprime m (10 ^ e - 1)) :
    m ∣ 10 ^ e + 1 := by
  have hsplit : 10 ^ (2 * e) - 1 = (10 ^ e - 1) * (10 ^ e + 1) := by
    have := ten_pow_even_split (n := 2 * e) ⟨e, rfl⟩
    rwa [Nat.mul_div_cancel_left e (by decide : 0 < 2)] at this
  have : m ∣ (10 ^ e - 1) * (10 ^ e + 1) := by
    rwa [← hsplit]
  exact hcop.dvd_of_dvd_mul_left this

/-- Residues of `0-1` numbers of length at most `s`, as elements of `ZMod m`. -/
def residues01 (m s : ℕ) : Finset (ZMod m) :=
  (Finset.powerset (Finset.range s)).image fun S => ∑ i ∈ S, (10 : ZMod m) ^ i

lemma mem_residues01 {m s : ℕ} {x : ZMod m} :
    x ∈ residues01 m s ↔ ∃ S ⊆ Finset.range s, ∑ i ∈ S, (10 : ZMod m) ^ i = x := by
  simp [residues01]

lemma zero_mem_residues01 (m s : ℕ) : (0 : ZMod m) ∈ residues01 m s :=
  mem_residues01.2 ⟨∅, by simp, by simp⟩

lemma two_pow_range_card (s : ℕ) :
    (Finset.powerset (Finset.range s)).card = 2 ^ s := by
  simp [Finset.card_powerset, Finset.card_range]

lemma residues01_card_le (m s : ℕ) :
    (residues01 m s).card ≤ 2 ^ s := by
  simpa [residues01, two_pow_range_card] using
    Finset.card_image_le (s := Finset.powerset (Finset.range s))

lemma sum_ten_pow_le_repunit {S : Finset ℕ} {s : ℕ}
    (hS : S ⊆ Finset.range s) :
    ∑ i ∈ S, 10 ^ i ≤ (10 ^ s - 1) / 9 := by
  have hle : ∑ i ∈ S, 10 ^ i ≤ ∑ i ∈ Finset.range s, 10 ^ i :=
    Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => 10 ^ i) hS
      (fun _ _ _ => Nat.zero_le _)
  rwa [geom_sum_ten] at hle

lemma eq_of_sum_ten_pow {S T : Finset ℕ}
    (h : ∑ i ∈ S, 10 ^ i = ∑ i ∈ T, 10 ^ i) : S = T := by
  ext j
  constructor
  · intro hj
    have : digit10 (∑ i ∈ S, 10 ^ i) j = 1 := by
      rw [digit10_sum_pow, if_pos hj]
    rw [h, digit10_sum_pow] at this
    split_ifs at this with hjT
    · exact hjT
  · intro hj
    have : digit10 (∑ i ∈ T, 10 ^ i) j = 1 := by
      rw [digit10_sum_pow, if_pos hj]
    rw [← h, digit10_sum_pow] at this
    split_ifs at this with hjS
    · exact hjS

/-- Distinct `0-1` integers below `m` remain distinct in `ZMod m`. -/
lemma residues01_card_eq_of_lt {m s : ℕ} [NeZero m]
    (h : (10 ^ s - 1) / 9 < m) :
    (residues01 m s).card = 2 ^ s := by
  have hinj : Set.InjOn (fun S : Finset ℕ => ∑ i ∈ S, (10 : ZMod m) ^ i)
      (Finset.powerset (Finset.range s)) := by
    intro S hS T hT hST
    have hSsub : S ⊆ Finset.range s := Finset.mem_powerset.mp hS
    have hTsub : T ⊆ Finset.range s := Finset.mem_powerset.mp hT
    have hSle := sum_ten_pow_le_repunit hSsub
    have hTle := sum_ten_pow_le_repunit hTsub
    have hcast :
        ((∑ i ∈ S, 10 ^ i : ℕ) : ZMod m) = ((∑ i ∈ T, 10 ^ i : ℕ) : ZMod m) := by
      simpa using hST
    have hval : ∑ i ∈ S, 10 ^ i = ∑ i ∈ T, 10 ^ i := by
      have hSm : ∑ i ∈ S, 10 ^ i < m := lt_of_le_of_lt hSle h
      have hTm : ∑ i ∈ T, 10 ^ i < m := lt_of_le_of_lt hTle h
      have hSmod : ((∑ i ∈ S, 10 ^ i : ℕ) : ZMod m).val = ∑ i ∈ S, 10 ^ i :=
        ZMod.val_natCast_of_lt hSm
      have hTmod : ((∑ i ∈ T, 10 ^ i : ℕ) : ZMod m).val = ∑ i ∈ T, 10 ^ i :=
        ZMod.val_natCast_of_lt hTm
      rw [← hSmod, ← hTmod, hcast]
    exact eq_of_sum_ten_pow hval
  have hcard := Finset.card_image_of_injOn hinj
  simpa [residues01, two_pow_range_card] using hcard

lemma zmod_ten_unit {m : ℕ} [NeZero m] (hm : Nat.Coprime m 10) :
    IsUnit (10 : ZMod m) := by
  have h : IsUnit ((10 : ℕ) : ZMod m) :=
    (ZMod.isUnit_iff_coprime 10 m).2 (by simpa [Nat.coprime_comm] using hm)
  exact h

lemma exists_01_concat {m s : ℕ} [NeZero m] (hm : Nat.Coprime m 10)
    (hcard : m + 2 ≤ 2 * (residues01 m s).card) :
    ∃ S : Finset ℕ, S.Nonempty ∧ (∀ i ∈ S, i < 2 * s) ∧
      (∑ i ∈ S, (10 : ZMod m) ^ i) = 0 := by
  set A := residues01 m s
  have hunit := zmod_ten_unit (m := m) hm
  set μ := (10 : ZMod m) ^ s
  have hμ : IsUnit μ := hunit.pow s
  set B := A.image fun z => -μ * z
  have hBinj : Function.Injective (fun z : ZMod m => -μ * z) := by
    intro x y hxy
    have hμeq : μ * x = μ * y := by
      have := congrArg (fun z : ZMod m => -z) hxy
      simpa [neg_mul, neg_neg] using this
    have hinj : Function.Injective (fun z : ZMod m => z * μ) :=
      IsUnit.mul_left_injective hμ
    have : x * μ = y * μ := by
      simpa [mul_comm] using hμeq
    exact hinj this
  have hBcard : B.card = A.card := Finset.card_image_of_injective A hBinj
  have hinter : 2 ≤ (A ∩ B).card := by
    have hleuniv : (A ∪ B).card ≤ Fintype.card (ZMod m) :=
      Finset.card_le_univ (A ∪ B)
    have hcardm : Fintype.card (ZMod m) = m := ZMod.card m
    have hsum := Finset.card_union_add_card_inter A B
    have : A.card + B.card = 2 * A.card := by
      rw [hBcard, two_mul]
    omega
  obtain ⟨z, hz, hz0⟩ : ∃ z ∈ A ∩ B, z ≠ 0 := by
    by_contra h
    push_neg at h
    have hsub : A ∩ B ⊆ ({0} : Finset (ZMod m)) := by
      intro z hz
      have : z = 0 := h z hz
      simp [this]
    have : (A ∩ B).card ≤ 1 :=
      (Finset.card_le_card hsub).trans (by simp)
    omega
  have hzA : z ∈ A := (Finset.mem_inter.mp hz).1
  have hzB : z ∈ B := (Finset.mem_inter.mp hz).2
  obtain ⟨S, hS, hSsum⟩ := mem_residues01.1 hzA
  obtain ⟨w, hwA, hwEq⟩ := Finset.mem_image.mp hzB
  obtain ⟨T, hT, hTsum⟩ := mem_residues01.1 hwA
  have hzEq : z = -μ * w := hwEq.symm
  have hsum0 : z + μ * w = 0 := by
    simp [hzEq, mul_comm]
  have hSne : S.Nonempty ∨ T.Nonempty := by
    by_contra h
    simp only [not_or, Finset.not_nonempty_iff_eq_empty] at h
    rcases h with ⟨hS0, hT0⟩
    subst hS0; subst hT0
    have : z = 0 := by simpa using hSsum.symm
    exact hz0 this
  refine ⟨S ∪ T.image (fun j => j + s), ?_, ?_, ?_⟩
  · rcases hSne with hSne | hTne
    · exact (Finset.union_nonempty.2 (Or.inl hSne))
    · exact (Finset.union_nonempty.2 (Or.inr (Finset.image_nonempty.2 hTne)))
  · intro i hi
    rcases Finset.mem_union.mp hi with hiS | hiT
    · have := Finset.mem_range.mp (hS hiS)
      omega
    · rcases Finset.mem_image.mp hiT with ⟨j, hj, rfl⟩
      have := Finset.mem_range.mp (hT hj)
      omega
  · have hdisj : Disjoint S (T.image (fun j => j + s)) := by
      refine Finset.disjoint_left.2 ?_
      intro i hiS hiT
      rcases Finset.mem_image.mp hiT with ⟨j, hj, hij⟩
      have hiRange : i ∈ Finset.range s := hS hiS
      have hjlt : j < s := Finset.mem_range.mp (hT hj)
      have : j + s < s := by
        rw [← hij] at hiRange
        exact Finset.mem_range.mp hiRange
      omega
    rw [Finset.sum_union hdisj, Finset.sum_image]
    · have hshift :
          ∑ j ∈ T, (10 : ZMod m) ^ (j + s) = μ * ∑ j ∈ T, (10 : ZMod m) ^ j := by
        simp only [μ, pow_add]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _hj
        ring
      rw [hshift, hTsum, hSsum]
      exact hsum0
    · intro a _ha b _hb hab
      exact Nat.add_right_cancel hab

/-- Unequal-length concatenation: residues of lengths `s1` and `s2`. -/
lemma exists_01_concat_uneven {m s1 s2 : ℕ} [NeZero m] (hm : Nat.Coprime m 10)
    (hcard : m + 2 ≤ (residues01 m s1).card + (residues01 m s2).card) :
    ∃ S : Finset ℕ, S.Nonempty ∧ (∀ i ∈ S, i < s1 + s2) ∧
      (∑ i ∈ S, (10 : ZMod m) ^ i) = 0 := by
  set A := residues01 m s1
  set C := residues01 m s2
  have hunit := zmod_ten_unit (m := m) hm
  set μ := (10 : ZMod m) ^ s1
  have hμ : IsUnit μ := hunit.pow s1
  set B := C.image fun z => -μ * z
  have hBinj : Function.Injective (fun z : ZMod m => -μ * z) := by
    intro x y hxy
    have hμeq : μ * x = μ * y := by
      have := congrArg (fun z : ZMod m => -z) hxy
      simpa [neg_mul, neg_neg] using this
    have hinj : Function.Injective (fun z : ZMod m => z * μ) :=
      IsUnit.mul_left_injective hμ
    have : x * μ = y * μ := by
      simpa [mul_comm] using hμeq
    exact hinj this
  have hBcard : B.card = C.card := Finset.card_image_of_injective C hBinj
  have hinter : 2 ≤ (A ∩ B).card := by
    have hleuniv : (A ∪ B).card ≤ Fintype.card (ZMod m) :=
      Finset.card_le_univ (A ∪ B)
    have hcardm : Fintype.card (ZMod m) = m := ZMod.card m
    have hsum := Finset.card_union_add_card_inter A B
    have : A.card + B.card = A.card + C.card := by rw [hBcard]
    omega
  obtain ⟨z, hz, hz0⟩ : ∃ z ∈ A ∩ B, z ≠ 0 := by
    by_contra h
    push_neg at h
    have hsub : A ∩ B ⊆ ({0} : Finset (ZMod m)) := by
      intro z hz
      have : z = 0 := h z hz
      simp [this]
    have : (A ∩ B).card ≤ 1 :=
      (Finset.card_le_card hsub).trans (by simp)
    omega
  have hzA : z ∈ A := (Finset.mem_inter.mp hz).1
  have hzB : z ∈ B := (Finset.mem_inter.mp hz).2
  obtain ⟨S, hS, hSsum⟩ := mem_residues01.1 hzA
  obtain ⟨w, hwC, hwEq⟩ := Finset.mem_image.mp hzB
  obtain ⟨T, hT, hTsum⟩ := mem_residues01.1 hwC
  have hzEq : z = -μ * w := hwEq.symm
  have hsum0 : z + μ * w = 0 := by
    simp [hzEq, mul_comm]
  have hSne : S.Nonempty ∨ T.Nonempty := by
    by_contra h
    simp only [not_or, Finset.not_nonempty_iff_eq_empty] at h
    rcases h with ⟨hS0, hT0⟩
    subst hS0; subst hT0
    have : z = 0 := by simpa using hSsum.symm
    exact hz0 this
  refine ⟨S ∪ T.image (fun j => j + s1), ?_, ?_, ?_⟩
  · rcases hSne with hSne | hTne
    · exact (Finset.union_nonempty.2 (Or.inl hSne))
    · exact (Finset.union_nonempty.2 (Or.inr (Finset.image_nonempty.2 hTne)))
  · intro i hi
    rcases Finset.mem_union.mp hi with hiS | hiT
    · have := Finset.mem_range.mp (hS hiS)
      omega
    · rcases Finset.mem_image.mp hiT with ⟨j, hj, rfl⟩
      have := Finset.mem_range.mp (hT hj)
      omega
  · have hdisj : Disjoint S (T.image (fun j => j + s1)) := by
      refine Finset.disjoint_left.2 ?_
      intro i hiS hiT
      rcases Finset.mem_image.mp hiT with ⟨j, hj, hij⟩
      have hiRange : i ∈ Finset.range s1 := hS hiS
      have hjlt : j < s2 := Finset.mem_range.mp (hT hj)
      have : j + s1 < s1 := by
        rw [← hij] at hiRange
        exact Finset.mem_range.mp hiRange
      omega
    rw [Finset.sum_union hdisj, Finset.sum_image]
    · have hshift :
          ∑ j ∈ T, (10 : ZMod m) ^ (j + s1) = μ * ∑ j ∈ T, (10 : ZMod m) ^ j := by
        simp only [μ, pow_add]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _hj
        ring
      rw [hshift, hTsum, hSsum]
      exact hsum0
    · intro a _ha b _hb hab
      exact Nat.add_right_cancel hab

lemma zmod_sum_pow_eq_nat {m : ℕ} (S : Finset ℕ) :
    ∑ i ∈ S, (10 : ZMod m) ^ i = ((∑ i ∈ S, 10 ^ i : ℕ) : ZMod m) := by
  simp

lemma dvd_of_zmod_sum_eq_zero {m : ℕ} [NeZero m] {S : Finset ℕ}
    (h0 : ∑ i ∈ S, (10 : ZMod m) ^ i = 0) :
    m ∣ ∑ i ∈ S, 10 ^ i := by
  rw [zmod_sum_pow_eq_nat] at h0
  exact (ZMod.natCast_eq_zero_iff _ _).1 h0

lemma sum_ten_pow_pos {S : Finset ℕ} (hS : S.Nonempty) :
    0 < ∑ i ∈ S, 10 ^ i := by
  obtain ⟨i, hi⟩ := hS
  have : 0 < 10 ^ i := Nat.pow_pos (by decide)
  exact lt_of_lt_of_le this (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi)

lemma sum_ten_pow_lt {S : Finset ℕ} {L : ℕ}
    (hL : ∀ i ∈ S, i < L) :
    ∑ i ∈ S, 10 ^ i < 10 ^ L := by
  have hsub : S ⊆ Finset.range L := fun i hi => Finset.mem_range.mpr (hL i hi)
  have hle : ∑ i ∈ S, 10 ^ i ≤ ∑ i ∈ Finset.range L, 10 ^ i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  have hlt : ∑ i ∈ Finset.range L, 10 ^ i < 10 ^ L := by
    have : ∑ i ∈ Finset.range L, 10 ^ i = (10 ^ L - 1) / 9 := geom_sum_ten L
    rw [this]
    exact repunit_lt_pow L
  exact lt_of_le_of_lt hle hlt

lemma A_le_of_zmod_sum {m : ℕ} [NeZero m] {S : Finset ℕ}
    (hS : S.Nonempty) (h0 : ∑ i ∈ S, (10 : ZMod m) ^ i = 0) :
    A004290 m ≤ ∑ i ∈ S, 10 ^ i :=
  A004290_le (sum_ten_pow_pos hS) (dvd_of_zmod_sum_eq_zero h0) (is01_sum_pow S)

lemma A_lt_pow_of_zmod_sum {m L : ℕ} [NeZero m] {S : Finset ℕ}
    (hS : S.Nonempty) (h0 : ∑ i ∈ S, (10 : ZMod m) ^ i = 0)
    (hL : ∀ i ∈ S, i < L) :
    A004290 m < 10 ^ L :=
  lt_of_le_of_lt (A_le_of_zmod_sum hS h0) (sum_ten_pow_lt hL)

lemma A_of_01_concat {k t m s : ℕ} [NeZero m] (hm : Nat.Coprime m 10)
    (hcard : m + 2 ≤ 2 * (residues01 m s).card)
    (hlen : 2 * s + t < 9 * k) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  obtain ⟨S, hS, hSL, h0⟩ := exists_01_concat (m := m) (s := s) hm hcard
  have hA : A004290 m < 10 ^ (2 * s) := A_lt_pow_of_zmod_sum hS h0 hSL
  have hL : 1 < 9 * k := by
    have : 1 ≤ 2 * s + t := by
      have : 0 < 2 * s ∨ 0 < t := by
        cases s with
        | zero =>
          have hpos : 0 < m := NeZero.pos m
          have : m + 2 ≤ 2 * (residues01 m 0).card := hcard
          have : (residues01 m 0).card = 1 := by
            simp [residues01]
          omega
        | succ s => omega
      omega
    omega
  exact A_mul_ten_lt_of_lt_pow hA hL hlen

lemma A_of_01_concat_uneven {k t m s1 s2 : ℕ} [NeZero m] (hm : Nat.Coprime m 10)
    (hcard : m + 2 ≤ (residues01 m s1).card + (residues01 m s2).card)
    (hlen : s1 + s2 + t < 9 * k) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  obtain ⟨S, hS, hSL, h0⟩ := exists_01_concat_uneven (m := m) (s1 := s1) (s2 := s2) hm hcard
  have hA : A004290 m < 10 ^ (s1 + s2) := A_lt_pow_of_zmod_sum hS h0 hSL
  have hL : 1 < 9 * k := by omega
  exact A_mul_ten_lt_of_lt_pow hA hL hlen

/-- If residues fill by length `9k - t - 2`, concatenate against a single extra bit. -/
lemma A_of_residues_full_pred {k t m : ℕ} [NeZero m]
    (hm : Nat.Coprime m 10) (ht : t ≤ 3) (hk : 2 ≤ k) (hm1 : 1 < m)
    (hfull : (residues01 m (9 * k - t - 2)).card = m) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  have h1 : (residues01 m 1).card = 2 := by
    have hlt : (10 ^ 1 - 1) / 9 < m := by
      simp
      exact hm1
    simpa using residues01_card_eq_of_lt (m := m) (s := 1) hlt
  have hcard : m + 2 ≤ (residues01 m (9 * k - t - 2)).card + (residues01 m 1).card := by
    omega
  have hlen : (9 * k - t - 2) + 1 + t < 9 * k := by omega
  exact A_of_01_concat_uneven hm hcard hlen

lemma repunit_sub_pow {L : ℕ} (hL : 0 < L) :
    (10 ^ L - 1) / 9 - 10 ^ (L - 1) = (10 ^ (L - 1) - 1) / 9 := by
  have h9 : 0 < 9 := by decide
  have hdvdL := nine_dvd_ten_pow_sub_one L
  have hdvdL' := nine_dvd_ten_pow_sub_one (L - 1)
  have hpow : 10 ^ L = 10 * 10 ^ (L - 1) := by
    calc 10 ^ L
        = 10 ^ ((L - 1) + 1) := by rw [Nat.sub_add_cancel hL]
      _ = 10 ^ (L - 1) * 10 := pow_succ _ _
      _ = 10 * 10 ^ (L - 1) := mul_comm _ _
  have hle : 10 ^ (L - 1) ≤ (10 ^ L - 1) / 9 := pow_le_repunit hL
  apply Nat.eq_of_mul_eq_mul_left h9
  rw [Nat.mul_sub_left_distrib, Nat.mul_div_cancel' hdvdL, Nat.mul_div_cancel' hdvdL']
  rw [hpow]
  have : 1 ≤ 10 ^ (L - 1) := Nat.one_le_pow _ _ (by decide)
  omega

/-- `10^e + 1` still beats the target repunit when `e + 1 + t ≤ 9k`. -/
lemma A_of_dvd_ten_pow_add_one_le {k t m e : ℕ} (ht : t ≤ 3)
    (he : 0 < e) (hdvd : m ∣ 10 ^ e + 1)
    (hk : 2 ≤ k) (hlen : e + 1 + t ≤ 9 * k) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  by_cases hlt : e + 1 + t < 9 * k
  · exact A_of_dvd_ten_pow_add_one ht he hdvd hlt
  · have heq : e + 1 + t = 9 * k := by omega
    have hA : A004290 m ≤ 10 ^ e + 1 := A_le_ten_pow_add_one he hdvd
    have hmul : (10 ^ e + 1) * 10 ^ t = 10 ^ (9 * k - 1) + 10 ^ t := by
      have : e + t = 9 * k - 1 := by omega
      calc (10 ^ e + 1) * 10 ^ t
          = 10 ^ e * 10 ^ t + 10 ^ t := by ring
        _ = 10 ^ (e + t) + 10 ^ t := by rw [← pow_add]
        _ = 10 ^ (9 * k - 1) + 10 ^ t := by rw [this]
    have hLpos : 0 < 9 * k := by omega
    have hgap := repunit_sub_pow hLpos
    have ht3 : 10 ^ t ≤ 1000 :=
      (Nat.pow_le_pow_right (by decide : 0 < 10) ht : 10 ^ t ≤ 10 ^ 3)
    have hR17 : 1000 < (10 ^ 17 - 1) / 9 := by decide
    have h17 : 17 ≤ 9 * k - 1 := by omega
    have hmon : (10 ^ 17 - 1) / 9 ≤ (10 ^ (9 * k - 1) - 1) / 9 :=
      Nat.div_le_div_right (Nat.sub_le_sub_right
        (Nat.pow_le_pow_right (by decide) h17) 1)
    have : 10 ^ (9 * k - 1) + 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
      have : 10 ^ t ≤ 1000 := ht3
      have : 1000 < (10 ^ (9 * k) - 1) / 9 - 10 ^ (9 * k - 1) := by
        rw [hgap]
        omega
      omega
    rw [← hmul] at this
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hA) this

lemma padicValNat_three_self : padicValNat 3 3 = 1 :=
  padicValNat.self (by decide : 1 < 3)

lemma padicValNat_nine : padicValNat 3 9 = 2 := by
  have : (9 : ℕ) = 3 ^ 2 := by decide
  rw [this, padicValNat.pow 2 (by decide : 3 ≠ 0), padicValNat_three_self]

lemma padicValNat_ten_pow_sub_one {l : ℕ} (hl : 0 < l) :
    padicValNat 3 (10 ^ l - 1) = 2 + padicValNat 3 l := by
  have hp1 : Odd 3 := by decide
  have h := padicValNat.pow_sub_pow (p := 3) hp1
    (x := 10) (y := 1) (n := l)
    (by decide : 1 < 10) (by decide : 3 ∣ 10 - 1) (by decide : ¬ 3 ∣ 10)
    (Nat.pos_iff_ne_zero.mp hl)
  simpa [padicValNat_nine] using h

lemma padicValNat_repunit {l : ℕ} (hl : 0 < l) :
    padicValNat 3 ((10 ^ l - 1) / 9) = padicValNat 3 l := by
  have hdiv := nine_dvd_ten_pow_sub_one l
  have hpos : 0 < (10 ^ l - 1) / 9 := repunit_pos l hl
  have : padicValNat 3 (9 * ((10 ^ l - 1) / 9)) =
      padicValNat 3 9 + padicValNat 3 ((10 ^ l - 1) / 9) :=
    padicValNat.mul (by decide : 9 ≠ 0) (Nat.pos_iff_ne_zero.mp hpos)
  rw [Nat.mul_div_cancel' hdiv, padicValNat_ten_pow_sub_one hl, padicValNat_nine] at this
  omega

lemma three_pow_dvd_repunit_iff {l v : ℕ} (hl : 0 < l) :
    3 ^ v ∣ (10 ^ l - 1) / 9 ↔ 3 ^ v ∣ l := by
  have hl0 : l ≠ 0 := Nat.pos_iff_ne_zero.mp hl
  have hR0 : (10 ^ l - 1) / 9 ≠ 0 := (repunit_pos l hl).ne'
  constructor
  · intro h
    have : v ≤ padicValNat 3 ((10 ^ l - 1) / 9) :=
      (padicValNat_dvd_iff_le hR0).1 h
    rw [padicValNat_repunit hl] at this
    exact (padicValNat_dvd_iff_le hl0).2 this
  · intro h
    have : v ≤ padicValNat 3 l := (padicValNat_dvd_iff_le hl0).1 h
    rw [← padicValNat_repunit hl] at this
    exact (padicValNat_dvd_iff_le hR0).2 this

lemma dvd_repunit_lcm_three_pow {m d v : ℕ} (hd : 0 < d)
    (h3v : 3 ^ v ∣ m) (hnext : ¬ 3 ∣ m / 3 ^ v)
    (hdvd : m ∣ 10 ^ d - 1) :
    m ∣ (10 ^ (Nat.lcm d (3 ^ v)) - 1) / 9 := by
  set e := Nat.lcm d (3 ^ v)
  have hde : d ∣ e := Nat.dvd_lcm_left d (3 ^ v)
  have hve : 3 ^ v ∣ e := Nat.dvd_lcm_right d (3 ^ v)
  have hepos : 0 < e := Nat.lcm_pos hd (pow_pos (by decide) v)
  have hm' : m / 3 ^ v * 3 ^ v = m := Nat.div_mul_cancel h3v
  have hcop := coprime9_of_not_three hnext
  have hdvd' : m / 3 ^ v ∣ 10 ^ d - 1 :=
    Nat.dvd_trans (Nat.div_dvd_of_dvd h3v) hdvd
  have hRd : m / 3 ^ v ∣ (10 ^ d - 1) / 9 :=
    dvd_repunit_of_coprime9 hd hcop hdvd'
  have hRe : (10 ^ d - 1) / 9 ∣ (10 ^ e - 1) / 9 :=
    dvd_repunit_of_dvd_pow hde
  have hm'Re : m / 3 ^ v ∣ (10 ^ e - 1) / 9 := Nat.dvd_trans hRd hRe
  have h3Re : 3 ^ v ∣ (10 ^ e - 1) / 9 :=
    (three_pow_dvd_repunit_iff hepos).2 hve
  have hcop3 : Nat.Coprime (m / 3 ^ v) (3 ^ v) := by
    cases v with
    | zero => simp
    | succ v =>
      exact (Nat.coprime_pow_right_iff (Nat.succ_pos v) _ _).2
        (((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnext).symm)
  have hmul := hcop3.mul_dvd_of_dvd_of_dvd hm'Re h3Re
  rwa [hm'] at hmul

lemma A_of_three_pow_repunit_le {k t m d v : ℕ} (hk : 2 ≤ k) (ht : t ≤ 3)
    (hmpos : 0 < m) (hd : 0 < d)
    (h3v : 3 ^ v ∣ m) (hnext : ¬ 3 ∣ m / 3 ^ v)
    (hdvd : m ∣ 10 ^ d - 1)
    (hle : Nat.lcm d (3 ^ v) + t ≤ 9 * k)
    (htcase : Nat.lcm d (3 ^ v) + t < 9 * k ∨ 0 < t) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 :=
  A_of_three_mul_repunit_le hk ht hmpos (Nat.lcm_pos hd (pow_pos (by decide) v))
    (dvd_repunit_lcm_three_pow hd h3v hnext hdvd) hle htcase

lemma A_of_three_pow_repunit {k t m d v : ℕ} (hk : 2 ≤ k) (ht : t ≤ 3)
    (hmpos : 0 < m) (hd : 0 < d)
    (h3v : 3 ^ v ∣ m) (hnext : ¬ 3 ∣ m / 3 ^ v)
    (hdvd : m ∣ 10 ^ d - 1)
    (hsum : Nat.lcm d (3 ^ v) + 3 ≤ 9 * k) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  have hle : Nat.lcm d (3 ^ v) + t ≤ 9 * k := by omega
  have htcase : Nat.lcm d (3 ^ v) + t < 9 * k ∨ 0 < t := by
    by_cases heq : Nat.lcm d (3 ^ v) + t = 9 * k
    · right; omega
    · left; omega
  exact A_of_three_pow_repunit_le hk ht hmpos hd h3v hnext hdvd hle htcase

/- ### Two-split length and the identity (10^a - 10^b + 1) R_a -/

lemma split_s_add {k t : ℕ} (ht : t ≤ 3) :
    2 * ((9 * k - t - 1) / 2) + t < 9 * k ∨ k = 0 := by
  by_cases hk : k = 0
  · exact Or.inr hk
  · left
    have h1 : t + 1 ≤ 9 * k := by
      have : 1 ≤ k := Nat.pos_of_ne_zero hk
      omega
    have hsub : 9 * k - t - 1 = 9 * k - (t + 1) := by omega
    have h2 : 2 * ((9 * k - (t + 1)) / 2) ≤ 9 * k - (t + 1) :=
      Nat.mul_div_le _ 2
    omega

lemma split_s_lt {k t : ℕ} (hk : 2 ≤ k) (ht : t ≤ 3) :
    2 * ((9 * k - t - 1) / 2) + t < 9 * k :=
  (split_s_add ht).resolve_right (by omega)

lemma sixteen_pow_ge_ten_succ {k : ℕ} (hk : 2 ≤ k) :
    10 ^ k + 1 ≤ 16 ^ k := by
  have hlt : 10 ^ k < 16 ^ k :=
    Nat.pow_lt_pow_left (by decide : 10 < 16)
      (Nat.pos_iff_ne_zero.mp (by omega : 0 < k))
  have : 1 ≤ 16 ^ k - 10 ^ k := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hlt)
  omega

lemma two_pow_s_ge_m {k t m : ℕ} (hk : 2 ≤ k) (ht : t ≤ 3)
    (hm : m < 10 ^ k) :
    m + 2 ≤ 2 ^ ((9 * k - t - 1) / 2) := by
  set s := (9 * k - t - 1) / 2
  have hsge : (9 * k - 4) / 2 ≤ s := by
    have : 9 * k - t - 1 ≥ 9 * k - 4 := by omega
    exact Nat.div_le_div_right this
  have hm2 : m + 2 ≤ 10 ^ k + 1 := by omega
  by_cases hk4 : 4 ≤ k
  · -- `k ≥ 4`: `(9k-4)/2 ≥ 4k`, so `2^s ≥ 16^k ≥ 10^k + 1`.
    have h4 : 4 * k ≤ s := by
      have : 4 * k ≤ (9 * k - 4) / 2 := by omega
      exact le_trans this hsge
    have hpow : 2 ^ (4 * k) ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) h4
    have h16 : 16 ^ k = 2 ^ (4 * k) := by
      calc 16 ^ k
          = (2 ^ 4) ^ k := rfl
        _ = 2 ^ (4 * k) := (pow_mul 2 4 k).symm
    have hten : 10 ^ k + 1 ≤ 16 ^ k := sixteen_pow_ge_ten_succ hk
    exact le_trans hm2 (le_trans hten (by rw [h16]; exact hpow))
  · -- `k = 2` or `k = 3`
    have hk23 : k = 2 ∨ k = 3 := by omega
    rcases hk23 with rfl | rfl
    · have hs : 7 ≤ s := by
        have : (9 * 2 - 4) / 2 = 7 := by decide
        omega
      have h128 : 2 ^ 7 = 128 := by decide
      have : m + 2 ≤ 101 := by omega
      have : 2 ^ 7 ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) hs
      omega
    · have hs : 11 ≤ s := by
        have : (9 * 3 - 4) / 2 = 11 := by decide
        omega
      have : m + 2 ≤ 1001 := by omega
      have : 2 ^ 11 ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) hs
      have : 2 ^ 11 = 2048 := by decide
      omega

lemma two_pow_s_large {k t m : ℕ} (hk : 2 ≤ k) (ht : t ≤ 3)
    (hm : m < 10 ^ k) :
    m + 2 ≤ 2 * 2 ^ ((9 * k - t - 1) / 2) := by
  have h := two_pow_s_ge_m hk ht hm
  have : 2 ^ ((9 * k - t - 1) / 2) ≤ 2 * 2 ^ ((9 * k - t - 1) / 2) := by
    omega
  exact le_trans h this

lemma residues01_card_lt_iff_not_inj {m s : ℕ}
    (h : (residues01 m s).card < 2 ^ s) :
    ¬ Set.InjOn (fun S : Finset ℕ => ∑ i ∈ S, (10 : ZMod m) ^ i)
      (Finset.powerset (Finset.range s)) := by
  intro hinj
  have hcard := Finset.card_image_of_injOn hinj
  have : (residues01 m s).card = 2 ^ s := by
    simpa [residues01, two_pow_range_card] using hcard
  omega

lemma exists_collision_residues {m s : ℕ}
    (h : (residues01 m s).card < 2 ^ s) :
    ∃ S T, S ⊆ Finset.range s ∧ T ⊆ Finset.range s ∧ S ≠ T ∧
      ∑ i ∈ S, (10 : ZMod m) ^ i = ∑ i ∈ T, (10 : ZMod m) ^ i := by
  have hnot := residues01_card_lt_iff_not_inj h
  unfold Set.InjOn at hnot
  push_neg at hnot
  obtain ⟨S, hS, T, hT, hsum, hne⟩ := hnot
  refine ⟨S, T, Finset.mem_powerset.mp hS, Finset.mem_powerset.mp hT, hne, hsum⟩

/-- The least length at which `0-1` residues collide. -/
lemma exists_least_collision {m s : ℕ}
    (h : (residues01 m s).card < 2 ^ s) :
    ∃ L, L ≤ s ∧ (residues01 m L).card < 2 ^ L ∧
      ∀ L' < L, (residues01 m L').card = 2 ^ L' := by
  let P : ℕ → Prop := fun l => l ≤ s ∧ (residues01 m l).card < 2 ^ l
  have hP : ∃ l, P l := ⟨s, le_rfl, h⟩
  classical
  let L := Nat.find hP
  have hL : P L := Nat.find_spec hP
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro L' hLt
  have hnot : ¬ P L' := Nat.find_min hP hLt
  have hle : L' ≤ s := le_trans (Nat.le_of_lt hLt) hL.1
  have hge : ¬ (residues01 m L').card < 2 ^ L' := fun hlt => hnot ⟨hle, hlt⟩
  have hule := residues01_card_le m L'
  omega

lemma residues01_full_pred {m L : ℕ}
    (hL : 0 < L)
    (hfull : ∀ L' < L, (residues01 m L').card = 2 ^ L') :
    (residues01 m (L - 1)).card = 2 ^ (L - 1) :=
  hfull (L - 1) (Nat.sub_lt hL (by decide))

lemma two_pow_s_succ {s : ℕ} : 2 * 2 ^ s = 2 ^ (s + 1) := by
  rw [pow_succ, mul_comm]

/-- Concatenation applies as soon as some collision-free length meets the size check. -/
lemma A_of_full_residues_concat {k t m s : ℕ} [NeZero m]
    (hm : Nat.Coprime m 10)
    (hfull : (residues01 m s).card = 2 ^ s)
    (hsize : m + 2 ≤ 2 ^ (s + 1))
    (hlen : 2 * s + t < 9 * k) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  have hcard : m + 2 ≤ 2 * (residues01 m s).card := by
    rw [hfull]
    rwa [← two_pow_s_succ] at hsize
  exact A_of_01_concat hm hcard hlen

lemma repunit_lt_self_pred {j : ℕ} (hj : 0 < j) :
    (10 ^ j - 1) / 9 < 10 ^ j - 1 := by
  have hpos : 0 < 10 ^ j - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp hj) (by decide : 1 < 10))
  have : 1 < 9 := by decide
  exact Nat.div_lt_self hpos this

lemma residues01_full_of_hard {m j : ℕ} [NeZero m]
    (hjm : 10 ^ j - 1 ≤ m) :
    (residues01 m j).card = 2 ^ j := by
  refine residues01_card_eq_of_lt ?_
  by_cases hj : j = 0
  · subst j
    have : 0 < m := NeZero.pos m
    simpa using this
  · exact lt_of_lt_of_le (repunit_lt_self_pred (Nat.pos_of_ne_zero hj)) hjm

lemma residues01_card_of_le {m s L : ℕ}
    (hLs : L ≤ s)
    (hfull : (residues01 m s).card = 2 ^ s) :
    (residues01 m L).card = 2 ^ L := by
  have himg :
      ((Finset.powerset (Finset.range s)).image
        fun S => ∑ i ∈ S, (10 : ZMod m) ^ i).card =
        (Finset.powerset (Finset.range s)).card := by
    simpa [residues01, two_pow_range_card] using hfull
  have hinj := (Finset.card_image_iff).1 himg
  have hsub : Finset.powerset (Finset.range L) ⊆ Finset.powerset (Finset.range s) := by
    intro S hS
    have hSL : S ⊆ Finset.range L := Finset.mem_powerset.1 hS
    have hLs' : Finset.range L ⊆ Finset.range s := Finset.range_mono hLs
    exact Finset.mem_powerset.2 (hSL.trans hLs')
  have hinjL : Set.InjOn (fun S : Finset ℕ => ∑ i ∈ S, (10 : ZMod m) ^ i)
      (Finset.powerset (Finset.range L)) := by
    intro S hS T hT hST
    exact hinj (hsub hS) (hsub hT) hST
  have hcard := Finset.card_image_of_injOn hinjL
  simpa [residues01, two_pow_range_card] using hcard

lemma two_pow_lt_ten_succ {k L : ℕ} (hk : 2 ≤ k)
    (h : 2 ^ L < 10 ^ (k - 1) + 2) : L ≤ 4 * (k - 1) := by
  by_contra hL
  have hge : 4 * (k - 1) + 1 ≤ L := by omega
  have hpow : 2 ^ (4 * (k - 1) + 1) ≤ 2 ^ L :=
    Nat.pow_le_pow_right (by decide) hge
  have h16 : (16 : ℕ) ^ (k - 1) = 2 ^ (4 * (k - 1)) := by
    calc (16 : ℕ) ^ (k - 1)
        = (2 ^ 4) ^ (k - 1) := rfl
      _ = 2 ^ (4 * (k - 1)) := (pow_mul 2 4 (k - 1)).symm
  have h2eq : 2 ^ (4 * (k - 1) + 1) = 2 * 16 ^ (k - 1) := by
    rw [pow_succ, mul_comm, ← h16]
  have h16le : 16 ≤ 16 ^ (k - 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 16) (by omega : 1 ≤ k - 1)
  have hbig : 10 ^ (k - 1) + 2 ≤ 2 * 16 ^ (k - 1) := by
    have hten : 10 ^ (k - 1) < 16 ^ (k - 1) :=
      Nat.pow_lt_pow_left (by decide : 10 < 16)
        (Nat.pos_iff_ne_zero.mp (by omega : 0 < k - 1))
    omega
  omega

lemma two_L_add_t_lt {k t L : ℕ} (hk : 2 ≤ k) (ht : t ≤ 3)
    (h : 2 ^ L < 10 ^ (k - 1) + 2) :
    2 * L + t < 9 * k := by
  have hL := two_pow_lt_ten_succ hk h
  have : 2 * (4 * (k - 1)) + 3 ≤ 8 * (k - 1) + 3 := by omega
  omega

lemma two_pow_lt_ten_k {k L : ℕ} (hk : 2 ≤ k)
    (h : 2 ^ L < 10 ^ k + 2) : L ≤ 4 * k - 1 := by
  by_contra hL
  have hge : 4 * k ≤ L := by omega
  have hpow : 2 ^ (4 * k) ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) hge
  have h16 : (16 : ℕ) ^ k = 2 ^ (4 * k) := by
    calc (16 : ℕ) ^ k
        = (2 ^ 4) ^ k := rfl
      _ = 2 ^ (4 * k) := (pow_mul 2 4 k).symm
  have hlt : 10 ^ k < 16 ^ k :=
    Nat.pow_lt_pow_left (by decide : 10 < 16)
      (Nat.pos_iff_ne_zero.mp (by omega : 0 < k))
  have hbig : 10 ^ k + 2 ≤ 16 ^ k := by
    have h2 : 2 ∣ 16 ^ k - 10 ^ k :=
      Nat.dvd_sub
        (dvd_pow (by decide : 2 ∣ 16) (Nat.pos_iff_ne_zero.mp (by omega : 0 < k)))
        (dvd_pow (by decide : 2 ∣ 10) (Nat.pos_iff_ne_zero.mp (by omega : 0 < k)))
    have hne : 16 ^ k - 10 ^ k ≠ 1 := fun heq => by
      rw [heq] at h2
      exact (by decide : ¬ 2 ∣ 1) h2
    have : 10 ^ k + 1 < 16 ^ k := by
      have : 10 ^ k + 1 ≤ 16 ^ k := Nat.succ_le_of_lt hlt
      exact lt_of_le_of_ne this (by
        intro heq
        apply hne
        have : 10 ^ k ≤ 16 ^ k := Nat.le_of_lt hlt
        omega)
    exact Nat.succ_le_of_lt this
  have : 2 ^ L < 2 ^ (4 * k) := by
    calc 2 ^ L < 10 ^ k + 2 := h
      _ ≤ 16 ^ k := hbig
      _ = 2 ^ (4 * k) := h16
  exact (Nat.not_lt.2 hpow) this

lemma two_L_add_t_lt_of_ten_k {k t L : ℕ} (hk : 2 ≤ k) (ht : t ≤ 3)
    (h : 2 ^ L < 10 ^ k + 2) :
    2 * L + t < 9 * k := by
  have hL := two_pow_lt_ten_k hk h
  have : 2 * (4 * k - 1) + 3 ≤ 8 * k + 1 := by omega
  omega

lemma sum_Ico_ten_pow (c n : ℕ) :
    ∑ i ∈ Finset.Ico c (c + n), 10 ^ i = 10 ^ c * ((10 ^ n - 1) / 9) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left, pow_add]
  rw [← Finset.mul_sum, geom_sum_ten]

/-- `(10^a - 10^b + 1) * R_a` is the `0-1` number with ones in `[0, b)` and `[a+b, 2a)`. -/
lemma ten_pow_sub_add_mul_repunit {a b : ℕ} (hba : b < a) :
    (10 ^ a - 10 ^ b + 1) * ((10 ^ a - 1) / 9) =
      ∑ i ∈ Finset.range b ∪ Finset.Ico (a + b) (2 * a), 10 ^ i := by
  have h9 : 0 < 9 := by decide
  have hb_le : b ≤ a := Nat.le_of_lt hba
  have hRa := nine_dvd_ten_pow_sub_one a
  have hRab := nine_dvd_ten_pow_sub_one (a - b)
  have hRb := nine_dvd_ten_pow_sub_one b
  have hdisj : Disjoint (Finset.range b) (Finset.Ico (a + b) (2 * a)) := by
    refine Finset.disjoint_left.2 ?_
    intro i hiS hiT
    have : i < b := Finset.mem_range.mp hiS
    have : a + b ≤ i := (Finset.mem_Ico.mp hiT).1
    omega
  have hab2 : a + b + (a - b) = 2 * a := by omega
  apply Nat.eq_of_mul_eq_mul_left h9
  have lhs :
      9 * ((10 ^ a - 10 ^ b + 1) * ((10 ^ a - 1) / 9)) =
        (10 ^ a - 10 ^ b + 1) * (10 ^ a - 1) := by
    rw [mul_left_comm, Nat.mul_div_cancel' hRa]
  have rhs :
      9 * ∑ i ∈ Finset.range b ∪ Finset.Ico (a + b) (2 * a), 10 ^ i =
        (10 ^ b - 1) + 10 ^ (a + b) * (10 ^ (a - b) - 1) := by
    rw [Finset.sum_union hdisj, geom_sum_ten, ← hab2, sum_Ico_ten_pow (a + b) (a - b)]
    rw [Nat.mul_add, Nat.mul_div_cancel' hRb, mul_left_comm (9) (10 ^ (a + b)),
      Nat.mul_div_cancel' hRab]
  rw [lhs, rhs]
  -- Compare via ℤ to avoid `ℕ` subtraction pitfalls.
  have hle1 : 10 ^ b ≤ 10 ^ a := Nat.pow_le_pow_right (by decide) hb_le
  have hle2 : 1 ≤ 10 ^ a := Nat.one_le_pow _ _ (by decide)
  have hle3 : 1 ≤ 10 ^ b := Nat.one_le_pow _ _ (by decide)
  have hle4 : 1 ≤ 10 ^ (a - b) := Nat.one_le_pow _ _ (by decide)
  have hle5 : 10 ^ (a + b) ≤ 10 ^ (2 * a) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  zify [hle1, hle2, hle3, hle4, hle5]
  ring_nf
  have hexp : (10 : ℤ) ^ (a * 2) = 10 ^ a * 10 ^ b * 10 ^ (a - b) := by
    have : a * 2 = a + b + (a - b) := by omega
    rw [this, pow_add, pow_add]
  rw [hexp]

lemma is01_ten_pow_sub_add_mul {a b : ℕ} (hba : b < a) :
    Is01 ((10 ^ a - 10 ^ b + 1) * ((10 ^ a - 1) / 9)) := by
  rw [ten_pow_sub_add_mul_repunit hba]
  exact is01_sum_pow _

lemma ten_pow_sub_add_mul_pos {a b : ℕ} (hba : b < a) :
    0 < (10 ^ a - 10 ^ b + 1) * ((10 ^ a - 1) / 9) := by
  have : 0 < (10 ^ a - 1) / 9 := repunit_pos a (by omega)
  have : 0 < 10 ^ a - 10 ^ b + 1 := by
    have : 10 ^ b ≤ 10 ^ a := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hba)
    omega
  exact Nat.mul_pos this ‹_›

lemma ten_pow_sub_add_mul_lt {a b : ℕ} (hba : b < a) :
    (10 ^ a - 10 ^ b + 1) * ((10 ^ a - 1) / 9) < 10 ^ (2 * a) := by
  have h01 := is01_ten_pow_sub_add_mul hba
  rw [ten_pow_sub_add_mul_repunit hba]
  refine sum_ten_pow_lt (L := 2 * a) ?_
  intro i hi
  rcases Finset.mem_union.mp hi with h | h
  · exact lt_of_lt_of_le (Finset.mem_range.mp h) (by omega)
  · exact (Finset.mem_Ico.mp h).2

lemma A_of_dvd_ten_pow_sub_add {k t m a b : ℕ} (ht : t ≤ 3)
    (hba : b < a) (hdvd : m ∣ 10 ^ a - 10 ^ b + 1)
    (hlen : 2 * a + t < 9 * k) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  have hA : A004290 m ≤
      (10 ^ a - 10 ^ b + 1) * ((10 ^ a - 1) / 9) :=
    A004290_le (ten_pow_sub_add_mul_pos hba)
      (hdvd.mul_right _) (is01_ten_pow_sub_add_mul hba)
  have hlt : (10 ^ a - 10 ^ b + 1) * ((10 ^ a - 1) / 9) < 10 ^ (2 * a) :=
    ten_pow_sub_add_mul_lt hba
  have hA' : A004290 m < 10 ^ (2 * a) := lt_of_le_of_lt hA hlt
  have hL : 1 < 9 * k := by omega
  exact A_mul_ten_lt_of_lt_pow hA' hL hlen

lemma zmod_pow_add_eq {m a b c : ℕ} [NeZero m]
    (h : (10 : ZMod m) ^ a + (10 : ZMod m) ^ b = (10 : ZMod m) ^ c) :
    ((10 ^ a + 10 ^ b : ℕ) : ZMod m) = ((10 ^ c : ℕ) : ZMod m) := by
  simpa using h

lemma dvd_of_two_pow_eq {m a b c : ℕ} [NeZero m]
    (h : (10 : ZMod m) ^ a + (10 : ZMod m) ^ b = (10 : ZMod m) ^ c) :
    m ∣ 10 ^ a + 10 ^ b - 10 ^ c ∨ m ∣ 10 ^ c - (10 ^ a + 10 ^ b) := by
  have h' := zmod_pow_add_eq h
  by_cases hle : 10 ^ c ≤ 10 ^ a + 10 ^ b
  · left
    have : ((10 ^ a + 10 ^ b - 10 ^ c : ℕ) : ZMod m) = 0 := by
      rw [Nat.cast_sub hle, h', sub_self]
    exact (ZMod.natCast_eq_zero_iff _ _).1 this
  · right
    have hle' : 10 ^ a + 10 ^ b ≤ 10 ^ c := Nat.le_of_not_ge hle
    have : ((10 ^ c - (10 ^ a + 10 ^ b) : ℕ) : ZMod m) = 0 := by
      rw [Nat.cast_sub hle', h', sub_self]
    exact (ZMod.natCast_eq_zero_iff _ _).1 this

lemma coprime_dvd_of_pow_mul {m x n : ℕ} (hm : Nat.Coprime m 10)
    (hdvd : m ∣ 10 ^ x * n) : m ∣ n :=
  (Nat.Coprime.pow_right x hm).dvd_of_dvd_mul_left hdvd

/-- Mixed-sign weight 3 with one exponent strictly on each side gives `10^p - 10^q + 1`. -/
lemma A_of_weight3_split {k t m p q : ℕ} (ht : t ≤ 3)
    (hm : Nat.Coprime m 10) (hqp : q < p)
    (hdvd : m ∣ 10 ^ p - 10 ^ q + 1)
    (hp : 2 * p + t < 9 * k) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 :=
  A_of_dvd_ten_pow_sub_add ht hqp hdvd hp

lemma ten_pow_ne_zero_of_coprime {m n : ℕ} [NeZero m] (hm : Nat.Coprime m 10)
    (hm1 : 1 < m) :
    (10 : ZMod m) ^ n ≠ 0 := by
  haveI : Nontrivial (ZMod m) := ZMod.nontrivial_iff.mpr (Nat.ne_of_gt hm1)
  have hunit := zmod_ten_unit (m := m) hm
  exact (hunit.pow n).ne_zero

lemma pow_add_ne_self {m a b : ℕ} [NeZero m] (hm : Nat.Coprime m 10)
    (hm1 : 1 < m) :
    (10 : ZMod m) ^ a + (10 : ZMod m) ^ b ≠ (10 : ZMod m) ^ a := by
  intro h
  have : (10 : ZMod m) ^ b = 0 := by
    have := congrArg (fun z => z - (10 : ZMod m) ^ a) h
    simpa using this
  exact ten_pow_ne_zero_of_coprime (n := b) hm hm1 this

lemma two_ten_pow_le_succ (n : ℕ) : 10 ^ n + 10 ^ n ≤ 10 ^ (n + 1) := by
  have h2 : 10 ^ n + 10 ^ n = 2 * 10 ^ n := by ring
  have h10 : 10 * 10 ^ n = 10 ^ (n + 1) := by rw [pow_succ, mul_comm]
  have : 2 * 10 ^ n ≤ 10 * 10 ^ n := Nat.mul_le_mul_right _ (by decide)
  rw [← h2, h10] at this
  exact this

lemma ten_pow_add_le_of_lt {a b c : ℕ} (hab : a ≤ b) (hbc : b < c) :
    10 ^ a + 10 ^ b ≤ 10 ^ c := by
  have hle : 10 ^ a ≤ 10 ^ b := Nat.pow_le_pow_right (by decide) hab
  have h2 : 10 ^ a + 10 ^ b ≤ 10 ^ b + 10 ^ b := Nat.add_le_add_right hle _
  have hsucc : 10 ^ b + 10 ^ b ≤ 10 ^ (b + 1) := two_ten_pow_le_succ b
  have hpow : 10 ^ (b + 1) ≤ 10 ^ c :=
    Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt hbc)
  exact h2.trans (hsucc.trans hpow)

lemma nat_sub_sub_eq (x y z : ℕ) (h : y + z ≤ x) :
    x - y - z = x - (y + z) := by omega

lemma ten_pow_factor_sub {a b : ℕ} (hab : a ≤ b) :
    10 ^ b - 10 ^ a = 10 ^ a * (10 ^ (b - a) - 1) := by
  have hpow : 10 ^ b = 10 ^ a * 10 ^ (b - a) := by
    rw [← pow_add, Nat.add_sub_cancel' hab]
  rw [hpow]
  nth_rw 2 [← mul_one (10 ^ a)]
  rw [← Nat.mul_sub_left_distrib]

lemma ten_pow_succ_gap {n m : ℕ} (hnm : n < m) : 10 ^ n + 1 ≤ 10 ^ m := by
  have hle : 10 ^ (n + 1) ≤ 10 ^ m :=
    Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt hnm)
  have hlt : 10 ^ n + 1 ≤ 10 ^ (n + 1) := by
    have h1 : 1 ≤ 9 * 10 ^ n :=
      le_trans (by decide : 1 ≤ 9)
        (Nat.le_mul_of_pos_right 9 (Nat.pow_pos (by decide : 0 < 10)))
    have h2 : 10 ^ n + 1 ≤ 10 ^ n + 9 * 10 ^ n := Nat.add_le_add_left h1 _
    have h3 : 10 ^ n + 9 * 10 ^ n = 10 * 10 ^ n := by ring
    have h4 : 10 * 10 ^ n = 10 ^ (n + 1) := by rw [pow_succ, mul_comm]
    rw [h3, h4] at h2
    exact h2
  exact hlt.trans hle

lemma ten_pow_sub_add_factor {a b c : ℕ} (hab : a ≤ b) (hbc : b < c) :
    10 ^ c - (10 ^ a + 10 ^ b) = 10 ^ a * (10 ^ (c - a) - 10 ^ (b - a) - 1) := by
  have hca : a ≤ c := Nat.le_of_lt (lt_of_le_of_lt hab hbc)
  have hle : 10 ^ a + 10 ^ b ≤ 10 ^ c := ten_pow_add_le_of_lt hab hbc
  have hle2 : 10 ^ (b - a) + 1 ≤ 10 ^ (c - a) := by
    have hstep : 10 ^ (b - a) + 1 ≤ 10 ^ (b - a + 1) := by
      have : 1 ≤ 9 * 10 ^ (b - a) :=
        le_trans (by decide : 1 ≤ 9)
          (Nat.le_mul_of_pos_right 9 (Nat.pow_pos (by decide : 0 < 10)))
      have h2 : 10 ^ (b - a) + 1 ≤ 10 ^ (b - a) + 9 * 10 ^ (b - a) :=
        Nat.add_le_add_left this _
      have h3 : 10 ^ (b - a) + 9 * 10 ^ (b - a) = 10 ^ (b - a + 1) := by
        rw [pow_succ, mul_comm]; ring
      rw [h3] at h2
      exact h2
    exact hstep.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hc : (10 : ℕ) ^ c = 10 ^ a * 10 ^ (c - a) := by
    rw [← pow_add, Nat.add_sub_cancel' hca]
  have hb : (10 : ℕ) ^ b = 10 ^ a * 10 ^ (b - a) := by
    rw [← pow_add, Nat.add_sub_cancel' hab]
  have hsum : 10 ^ a + 10 ^ a * 10 ^ (b - a) = 10 ^ a * (10 ^ (b - a) + 1) := by
    rw [Nat.mul_add, mul_one, add_comm]
  rw [hc, hb, hsum]
  conv_lhs => rw [← Nat.mul_sub_left_distrib]
  rw [Nat.sub_sub]

lemma dvd_ten_pow_sub_sub {m a b c : ℕ} [NeZero m] (hm : Nat.Coprime m 10)
    (h : (10 : ZMod m) ^ a + (10 : ZMod m) ^ b = (10 : ZMod m) ^ c)
    (hab : a ≤ b) (hbc : b < c) :
    m ∣ 10 ^ (c - a) - 10 ^ (b - a) - 1 := by
  have hsum := zmod_pow_add_eq h
  have hle : 10 ^ a + 10 ^ b ≤ 10 ^ c := ten_pow_add_le_of_lt hab hbc
  have hdiff : ((10 ^ c - (10 ^ a + 10 ^ b) : ℕ) : ZMod m) = 0 := by
    rw [Nat.cast_sub hle, hsum, sub_self]
  have hdvd0 : m ∣ 10 ^ c - (10 ^ a + 10 ^ b) :=
    (ZMod.natCast_eq_zero_iff _ _).1 hdiff
  have hEq := ten_pow_sub_add_factor hab hbc
  have : m ∣ 10 ^ a * (10 ^ (c - a) - 10 ^ (b - a) - 1) := by
    rwa [← hEq]
  exact coprime_dvd_of_pow_mul hm this

lemma ten_pow_add_sub_factor {a b c : ℕ} (hca : c < a) (hab : a ≤ b) :
    10 ^ a + 10 ^ b - 10 ^ c = 10 ^ c * (10 ^ (a - c) + 10 ^ (b - c) - 1) := by
  have h1 : 10 ^ a = 10 ^ c * 10 ^ (a - c) := by
    rw [← pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hca)]
  have h2 : 10 ^ b = 10 ^ c * 10 ^ (b - c) := by
    rw [← pow_add, Nat.add_sub_cancel' (le_trans (Nat.le_of_lt hca) hab)]
  rw [h1, h2, ← Nat.mul_add]
  nth_rw 2 [← mul_one (10 ^ c)]
  rw [← Nat.mul_sub_left_distrib]

lemma dvd_ten_pow_add_sub {m a b c : ℕ} [NeZero m] (hm : Nat.Coprime m 10)
    (h : (10 : ZMod m) ^ a + (10 : ZMod m) ^ b = (10 : ZMod m) ^ c)
    (hca : c < a) (hab : a ≤ b) :
    m ∣ 10 ^ (a - c) + 10 ^ (b - c) - 1 := by
  have hsum := zmod_pow_add_eq h
  have hle : 10 ^ c ≤ 10 ^ a + 10 ^ b := by
    have : 10 ^ c ≤ 10 ^ a := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hca)
    exact le_trans this (Nat.le_add_right _ _)
  have hdiff : ((10 ^ a + 10 ^ b - 10 ^ c : ℕ) : ZMod m) = 0 := by
    rw [Nat.cast_sub hle, hsum, sub_self]
  have hdvd : m ∣ 10 ^ a + 10 ^ b - 10 ^ c :=
    (ZMod.natCast_eq_zero_iff _ _).1 hdiff
  have hEq := ten_pow_add_sub_factor hca hab
  have : m ∣ 10 ^ c * (10 ^ (a - c) + 10 ^ (b - c) - 1) := by
    rwa [hEq] at hdvd
  exact coprime_dvd_of_pow_mul hm this

lemma ten_pow_mid_factor {a b c : ℕ} (hac : a < c) (hcb : c < b) :
    10 ^ a + 10 ^ b - 10 ^ c = 10 ^ a * (10 ^ (b - a) - 10 ^ (c - a) + 1) := by
  have h1 : 10 ^ b = 10 ^ a * 10 ^ (b - a) := by
    rw [← pow_add, Nat.add_sub_cancel' (le_trans (Nat.le_of_lt hac) (Nat.le_of_lt hcb))]
  have h2 : 10 ^ c = 10 ^ a * 10 ^ (c - a) := by
    rw [← pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hac)]
  have hca_le : 10 ^ (c - a) ≤ 10 ^ (b - a) :=
    Nat.pow_le_pow_right (by decide)
      (Nat.sub_le_sub_right (Nat.le_of_lt hcb) _)
  rw [h1, h2]
  have hsum : 10 ^ a + 10 ^ a * 10 ^ (b - a) = 10 ^ a * (10 ^ (b - a) + 1) := by
    rw [Nat.mul_add, mul_one, add_comm]
  rw [hsum, ← Nat.mul_sub_left_distrib]
  congr 1
  have : 10 ^ (b - a) + 1 - 10 ^ (c - a) = 10 ^ (b - a) - 10 ^ (c - a) + 1 := by
    have hle := hca_le
    omega
  exact this

lemma dvd_ten_pow_sub_add_of_mid {m a b c : ℕ} [NeZero m] (hm : Nat.Coprime m 10)
    (h : (10 : ZMod m) ^ a + (10 : ZMod m) ^ b = (10 : ZMod m) ^ c)
    (hac : a < c) (hcb : c < b) :
    m ∣ 10 ^ (b - a) - 10 ^ (c - a) + 1 := by
  have hsum := zmod_pow_add_eq h
  have hle : 10 ^ c ≤ 10 ^ a + 10 ^ b := by
    have : 10 ^ c ≤ 10 ^ b := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hcb)
    exact le_trans this (Nat.le_add_left _ _)
  have hdiff : ((10 ^ a + 10 ^ b - 10 ^ c : ℕ) : ZMod m) = 0 := by
    rw [Nat.cast_sub hle, hsum, sub_self]
  have hdvd : m ∣ 10 ^ a + 10 ^ b - 10 ^ c :=
    (ZMod.natCast_eq_zero_iff _ _).1 hdiff
  have hEq := ten_pow_mid_factor hac hcb
  have : m ∣ 10 ^ a * (10 ^ (b - a) - 10 ^ (c - a) + 1) := by
    rwa [hEq] at hdvd
  exact coprime_dvd_of_pow_mul hm this

lemma split_bound_of_lt {k t x : ℕ} (ht : t ≤ 3) (hk : 2 ≤ k)
    (hx : x < (9 * k - t - 1) / 2) : 2 * x + t < 9 * k := by
  have h1 : t + 1 ≤ 9 * k := by omega
  have : 2 * ((9 * k - t - 1) / 2) ≤ 9 * k - t - 1 := Nat.mul_div_le _ 2
  omega

/-- `p` leading ones, `2p` zeros, `p-1` trailing ones; length `4p-1`. -/
def onesZerosOnes (p : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico (3 * p - 1) (4 * p - 1) ∪ Finset.range (p - 1), 10 ^ i

lemma onesZerosOnes_disj (p : ℕ) :
    Disjoint (Finset.Ico (3 * p - 1) (4 * p - 1)) (Finset.range (p - 1)) := by
  refine Finset.disjoint_left.2 ?_
  intro i hiS hiT
  have : 3 * p - 1 ≤ i := (Finset.mem_Ico.mp hiS).1
  have : i < p - 1 := Finset.mem_range.mp hiT
  omega

lemma is01_onesZerosOnes (p : ℕ) : Is01 (onesZerosOnes p) :=
  is01_sum_pow _

lemma onesZerosOnes_lt {p : ℕ} (hp : 1 ≤ p) :
    onesZerosOnes p < 10 ^ (4 * p - 1) := by
  unfold onesZerosOnes
  refine sum_ten_pow_lt (L := 4 * p - 1) ?_
  intro i hi
  rcases Finset.mem_union.mp hi with h | h
  · exact (Finset.mem_Ico.mp h).2
  · have : i < p - 1 := Finset.mem_range.mp h
    omega

lemma onesZerosOnes_pos {p : ℕ} (hp : 1 ≤ p) : 0 < onesZerosOnes p := by
  unfold onesZerosOnes
  refine sum_ten_pow_pos ?_
  refine Finset.union_nonempty.2 (Or.inl ?_)
  rw [Finset.nonempty_Ico]
  omega

lemma onesZerosOnes_closed {p : ℕ} (hp : 1 ≤ p) :
    onesZerosOnes p =
      (10 ^ p - 1) / 9 * 10 ^ (3 * p - 1) + (10 ^ (p - 1) - 1) / 9 := by
  have heq : 4 * p - 1 = 3 * p - 1 + p := by omega
  unfold onesZerosOnes
  rw [Finset.sum_union (onesZerosOnes_disj p), heq, sum_Ico_ten_pow, geom_sum_ten]
  ring

lemma nine_mul_onesZerosOnes {p : ℕ} (hp : 1 ≤ p) :
    9 * onesZerosOnes p =
      (10 ^ p - 1) * 10 ^ (3 * p - 1) + (10 ^ (p - 1) - 1) := by
  rw [onesZerosOnes_closed hp, mul_add, ← mul_assoc,
    Nat.mul_div_cancel' (nine_dvd_ten_pow_sub_one p),
    Nat.mul_div_cancel' (nine_dvd_ten_pow_sub_one (p - 1))]

lemma ten_pow_eq_two_mul_five_pred {p : ℕ} (hp : 1 ≤ p) :
    10 ^ p = 2 * (5 * 10 ^ (p - 1) - 1) + 2 := by
  have hM1 : 1 ≤ 5 * 10 ^ (p - 1) := by
    have : 1 ≤ 10 ^ (p - 1) := Nat.one_le_pow _ _ (by decide)
    omega
  have : 10 ^ p = 10 * 10 ^ (p - 1) := by
    calc 10 ^ p
        = 10 ^ (p - 1 + 1) := by rw [Nat.sub_add_cancel hp]
      _ = 10 ^ (p - 1) * 10 ^ 1 := pow_add _ _ _
      _ = 10 ^ (p - 1) * 10 := by rw [pow_one]
      _ = 10 * 10 ^ (p - 1) := mul_comm _ _
  omega

lemma five_ten_pow_pred_modEq (p : ℕ) (hp : 1 ≤ p) :
    10 ^ p ≡ 2 [MOD 5 * 10 ^ (p - 1) - 1] := by
  set M := 5 * 10 ^ (p - 1) - 1
  have heq := ten_pow_eq_two_mul_five_pred hp
  change 10 ^ p % M = 2 % M
  rw [show 10 ^ p = 2 * M + 2 from heq]
  have hMpos : 0 < M := by
    have : 1 ≤ 5 * 10 ^ (p - 1) := by
      have : 1 ≤ 10 ^ (p - 1) := Nat.one_le_pow _ _ (by decide)
      omega
    omega
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self, mul_zero, Nat.zero_mod, zero_add, Nat.mod_mod]

lemma five_ten_pow_pred_dvd_nine_mul {p : ℕ} (hp : 1 ≤ p) :
    5 * 10 ^ (p - 1) - 1 ∣ 9 * onesZerosOnes p := by
  set M := 5 * 10 ^ (p - 1) - 1
  have h5 : 1 ≤ 5 * 10 ^ (p - 1) := by
    have : 1 ≤ 10 ^ (p - 1) := Nat.one_le_pow _ _ (by decide)
    omega
  have h1p : 1 ≤ 10 ^ p := Nat.one_le_pow _ _ (by decide)
  have h1p' : 1 ≤ 10 ^ (p - 1) := Nat.one_le_pow _ _ (by decide)
  have heq := ten_pow_eq_two_mul_five_pred hp
  have hexp : 3 * p - 1 = p + p + (p - 1) := by omega
  have hpow : 10 ^ (3 * p - 1) = 10 ^ p * 10 ^ p * 10 ^ (p - 1) := by
    rw [hexp, pow_add, pow_add]
  have hz : (M : ℤ) ∣
      ((10 : ℤ) ^ p - 1) * (10 : ℤ) ^ (3 * p - 1) + ((10 : ℤ) ^ (p - 1) - 1) := by
    have hMZ : (10 : ℤ) ^ p = 2 * (M : ℤ) + 2 := by
      have h := congrArg (fun n : ℕ => (n : ℤ)) heq
      have hcast : ((2 * (5 * 10 ^ (p - 1) - 1) + 2 : ℕ) : ℤ) =
          2 * (M : ℤ) + 2 := by
        simp [M]
      simpa [Int.natCast_pow, hcast] using h
    have hpowZ : (10 : ℤ) ^ (3 * p - 1) =
        (10 : ℤ) ^ p * (10 : ℤ) ^ p * (10 : ℤ) ^ (p - 1) := by
      have h := congrArg (fun n : ℕ => (n : ℤ)) hpow
      simpa [Int.natCast_pow, Int.natCast_mul] using h
    have hMval : (M : ℤ) = 5 * (10 : ℤ) ^ (p - 1) - 1 := by
      simp [M, Int.natCast_sub h5, Int.natCast_pow]
    have hform :
        (2 * (M : ℤ) + 1) * (2 * (M : ℤ) + 2) ^ 2 * (10 : ℤ) ^ (p - 1)
          + (10 : ℤ) ^ (p - 1) - 1 =
        (M : ℤ) * (8 * (M : ℤ) ^ 2 * (10 : ℤ) ^ (p - 1)
          + 20 * (M : ℤ) * (10 : ℤ) ^ (p - 1)
          + 16 * (10 : ℤ) ^ (p - 1) + 1) := by
      rw [hMval]
      ring
    have hrew :
        ((10 : ℤ) ^ p - 1) * (10 : ℤ) ^ (3 * p - 1) + ((10 : ℤ) ^ (p - 1) - 1) =
          (2 * (M : ℤ) + 1) * (2 * (M : ℤ) + 2) ^ 2 * (10 : ℤ) ^ (p - 1)
            + (10 : ℤ) ^ (p - 1) - 1 := by
      rw [hpowZ, hMZ]; ring
    rw [hrew, hform]
    exact dvd_mul_right _ _
  have hNat :
      M ∣ (10 ^ p - 1) * 10 ^ (3 * p - 1) + (10 ^ (p - 1) - 1) := by
    zify [h1p, h1p'] at hz ⊢
    exact hz
  rw [nine_mul_onesZerosOnes hp]
  exact hNat

lemma coprime_five_ten_pow_pred_nine {p : ℕ} (_hp : 1 ≤ p) :
    Nat.Coprime (5 * 10 ^ (p - 1) - 1) 9 := by
  have h10 : (10 : ℕ) ≡ 1 [MOD 9] := by decide
  have hpow : 10 ^ (p - 1) ≡ 1 [MOD 9] := by
    simpa using Nat.ModEq.pow (p - 1) h10
  have h5 : 5 * 10 ^ (p - 1) ≡ 5 [MOD 9] := by
    simpa using hpow.mul_left 5
  have hle : 1 ≤ 5 * 10 ^ (p - 1) := by
    have : 1 ≤ 10 ^ (p - 1) := Nat.one_le_pow _ _ (by decide)
    omega
  have hM : 5 * 10 ^ (p - 1) - 1 ≡ 4 [MOD 9] :=
    Nat.ModEq.sub_right (a := 1) hle (by decide) h5
  have hg : Nat.gcd (5 * 10 ^ (p - 1) - 1) 9 = Nat.gcd 4 9 :=
    Nat.ModEq.gcd_eq hM
  simp [Nat.coprime_iff_gcd_eq_one, hg]

lemma five_ten_pow_pred_dvd_onesZerosOnes {p : ℕ} (hp : 1 ≤ p) :
    5 * 10 ^ (p - 1) - 1 ∣ onesZerosOnes p := by
  have h9 := five_ten_pow_pred_dvd_nine_mul hp
  have hcop := coprime_five_ten_pow_pred_nine hp
  have : 5 * 10 ^ (p - 1) - 1 ∣ 9 * onesZerosOnes p := h9
  exact hcop.dvd_of_dvd_mul_left (by simpa [mul_comm] using this)

lemma ten_pow_sub_two_eq_two_mul (p : ℕ) (hp : 1 ≤ p) :
    10 ^ p - 2 = 2 * (5 * 10 ^ (p - 1) - 1) := by
  have h := ten_pow_eq_two_mul_five_pred hp
  have : 2 ≤ 10 ^ p := by
    have : 10 ≤ 10 ^ p := Nat.le_self_pow (by omega) 10
    omega
  omega

lemma dvd_five_ten_pow_pred_of_dvd_ten_pow_sub_two {m p : ℕ}
    (hp : 1 ≤ p) (hm2 : ¬ 2 ∣ m) (hdvd : m ∣ 10 ^ p - 2) :
    m ∣ 5 * 10 ^ (p - 1) - 1 := by
  have hEq := ten_pow_sub_two_eq_two_mul p hp
  have : m ∣ 2 * (5 * 10 ^ (p - 1) - 1) := by rwa [← hEq]
  exact (Nat.Coprime.dvd_of_dvd_mul_left
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hm2).symm) this

lemma A_of_dvd_onesZerosOnes {k t m p : ℕ} (ht : t ≤ 3)
    (hp : 1 ≤ p) (hdvd : m ∣ onesZerosOnes p)
    (hlen : 4 * p - 1 + t < 9 * k) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  have hA : A004290 m ≤ onesZerosOnes p :=
    A004290_le (onesZerosOnes_pos hp) hdvd (is01_onesZerosOnes p)
  have hlt : onesZerosOnes p < 10 ^ (4 * p - 1) := onesZerosOnes_lt hp
  have hA' : A004290 m < 10 ^ (4 * p - 1) := lt_of_le_of_lt hA hlt
  have hL : 1 < 9 * k := by omega
  exact A_mul_ten_lt_of_lt_pow hA' hL hlen

lemma not_two_dvd_of_coprime10 {m : ℕ} (hm : Nat.Coprime m 10) : ¬ 2 ∣ m := by
  intro h
  have : ¬ Nat.Coprime m 10 := by
    have : 2 ∣ Nat.gcd m 10 := Nat.dvd_gcd h (by decide)
    intro hc
    have : Nat.gcd m 10 = 1 := hc
    omega
  exact this hm

/- ### Type B `p = q`: `m ∣ 2 * 10^p - 1` via `(p+1)` ones, `2p` zeros, `p` ones. -/

def twonesZerosOnes (p : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico (3 * p) (4 * p + 1) ∪ Finset.range p, 10 ^ i

lemma twonesZerosOnes_disj (p : ℕ) :
    Disjoint (Finset.Ico (3 * p) (4 * p + 1)) (Finset.range p) := by
  refine Finset.disjoint_left.2 ?_
  intro i hiS hiT
  have : 3 * p ≤ i := (Finset.mem_Ico.mp hiS).1
  have : i < p := Finset.mem_range.mp hiT
  omega

lemma is01_twonesZerosOnes (p : ℕ) : Is01 (twonesZerosOnes p) :=
  is01_sum_pow _

lemma twonesZerosOnes_lt (p : ℕ) :
    twonesZerosOnes p < 10 ^ (4 * p + 1) := by
  unfold twonesZerosOnes
  refine sum_ten_pow_lt (L := 4 * p + 1) ?_
  intro i hi
  rcases Finset.mem_union.mp hi with h | h
  · exact (Finset.mem_Ico.mp h).2
  · have : i < p := Finset.mem_range.mp h
    omega

lemma twonesZerosOnes_pos {p : ℕ} (hp : 1 ≤ p) : 0 < twonesZerosOnes p := by
  unfold twonesZerosOnes
  refine sum_ten_pow_pos ?_
  refine Finset.union_nonempty.2 (Or.inr ?_)
  exact ⟨0, Finset.mem_range.mpr hp⟩

lemma twonesZerosOnes_closed (p : ℕ) :
    twonesZerosOnes p =
      (10 ^ (p + 1) - 1) / 9 * 10 ^ (3 * p) + (10 ^ p - 1) / 9 := by
  have heq : 4 * p + 1 = 3 * p + (p + 1) := by omega
  unfold twonesZerosOnes
  rw [Finset.sum_union (twonesZerosOnes_disj p), heq, sum_Ico_ten_pow, geom_sum_ten]
  ring

lemma nine_mul_twonesZerosOnes (p : ℕ) :
    9 * twonesZerosOnes p =
      (10 ^ (p + 1) - 1) * 10 ^ (3 * p) + (10 ^ p - 1) := by
  rw [twonesZerosOnes_closed, mul_add, ← mul_assoc,
    Nat.mul_div_cancel' (nine_dvd_ten_pow_sub_one (p + 1)),
    Nat.mul_div_cancel' (nine_dvd_ten_pow_sub_one p)]

lemma two_ten_pow_pred_mod_nine (p : ℕ) :
    (2 * 10 ^ p - 1) % 9 = 1 := by
  have h10 : (10 : ℕ) ≡ 1 [MOD 9] := by decide
  have hpow : 10 ^ p ≡ 1 [MOD 9] := by simpa using Nat.ModEq.pow p h10
  have h2 : 2 * 10 ^ p ≡ 2 [MOD 9] := by simpa using hpow.mul_left 2
  have hle : 1 ≤ 2 * 10 ^ p := by
    have : 1 ≤ 10 ^ p := Nat.one_le_pow _ _ (by decide)
    omega
  have hM : 2 * 10 ^ p - 1 ≡ 1 [MOD 9] :=
    Nat.ModEq.sub_right (a := 1) hle (by decide) h2
  exact hM

lemma coprime_two_ten_pow_pred_nine (p : ℕ) :
    Nat.Coprime (2 * 10 ^ p - 1) 9 := by
  have hmod := two_ten_pow_pred_mod_nine p
  have hg : Nat.gcd (2 * 10 ^ p - 1) 9 = Nat.gcd 1 9 :=
    Nat.ModEq.gcd_eq (by
      change 2 * 10 ^ p - 1 ≡ 1 [MOD 9]
      exact hmod)
  simp [Nat.coprime_iff_gcd_eq_one, hg]

lemma two_ten_pow_pred_dvd_nine_mul {p : ℕ} (hp : 1 ≤ p) :
    2 * 10 ^ p - 1 ∣ 9 * twonesZerosOnes p := by
  set M := 2 * 10 ^ p - 1
  have h1p : 1 ≤ 10 ^ p := Nat.one_le_pow _ _ (by decide)
  have h1p1 : 1 ≤ 10 ^ (p + 1) := Nat.one_le_pow _ _ (by decide)
  have hM1 : 1 ≤ 2 * 10 ^ p := by omega
  have hz : (M : ℤ) ∣
      ((10 : ℤ) ^ (p + 1) - 1) * (10 : ℤ) ^ (3 * p) + ((10 : ℤ) ^ p - 1) := by
    have hpow3 : (10 : ℤ) ^ (3 * p) = ((10 : ℤ) ^ p) ^ 3 := by
      rw [mul_comm, pow_mul]
    have hform :
        ((10 : ℤ) ^ (p + 1) - 1) * (10 : ℤ) ^ (3 * p) + ((10 : ℤ) ^ p - 1) =
          (2 * (10 : ℤ) ^ p - 1) *
            (5 * ((10 : ℤ) ^ p) ^ 3 + 2 * ((10 : ℤ) ^ p) ^ 2 +
              (10 : ℤ) ^ p + 1) := by
      have hx : (10 : ℤ) ^ (p + 1) = 10 * (10 : ℤ) ^ p := by
        rw [pow_succ, mul_comm]
      rw [hx, hpow3]
      ring
    have hMval : (M : ℤ) = 2 * (10 : ℤ) ^ p - 1 := by
      simp [M, Int.natCast_sub hM1, Int.natCast_pow]
    rw [hform, hMval]
    exact dvd_mul_right _ _
  have hNat :
      M ∣ (10 ^ (p + 1) - 1) * 10 ^ (3 * p) + (10 ^ p - 1) := by
    zify [h1p, h1p1] at hz ⊢
    exact hz
  rw [nine_mul_twonesZerosOnes]
  exact hNat

lemma two_ten_pow_pred_dvd_twones {p : ℕ} (hp : 1 ≤ p) :
    2 * 10 ^ p - 1 ∣ twonesZerosOnes p := by
  have h9 := two_ten_pow_pred_dvd_nine_mul hp
  have hcop := coprime_two_ten_pow_pred_nine p
  exact hcop.dvd_of_dvd_mul_left (by simpa [mul_comm] using h9)

lemma A_of_dvd_twonesZerosOnes {k t m p : ℕ} (ht : t ≤ 3)
    (hp : 1 ≤ p) (hdvd : m ∣ twonesZerosOnes p)
    (hlen : 4 * p + 1 + t < 9 * k) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  have hA : A004290 m ≤ twonesZerosOnes p :=
    A004290_le (twonesZerosOnes_pos hp) hdvd (is01_twonesZerosOnes p)
  have hlt : twonesZerosOnes p < 10 ^ (4 * p + 1) := twonesZerosOnes_lt p
  have hA' : A004290 m < 10 ^ (4 * p + 1) := lt_of_le_of_lt hA hlt
  have hL : 1 < 9 * k := by omega
  exact A_mul_ten_lt_of_lt_pow hA' hL hlen

lemma dvd_twones_of_dvd_two_ten_pow {m p : ℕ} (hp : 1 ≤ p)
    (hdvd : m ∣ 2 * 10 ^ p - 1) :
    m ∣ twonesZerosOnes p :=
  Nat.dvd_trans hdvd (two_ten_pow_pred_dvd_twones hp)

lemma padicValNat_three_not_succ {m : ℕ} (hmpos : 0 < m) :
    ¬ 3 ∣ m / 3 ^ padicValNat 3 m := by
  intro h
  set v := padicValNat 3 m
  have h3v : 3 ^ v ∣ m := pow_padicValNat_dvd
  have hpow : 3 ^ (v + 1) ∣ m := by
    have hmul : 3 ^ (v + 1) ∣ (m / 3 ^ v) * 3 ^ v := by
      rw [pow_succ, mul_comm]
      exact Nat.mul_dvd_mul h (dvd_refl _)
    rwa [Nat.div_mul_cancel h3v] at hmul
  exact pow_succ_padicValNat_not_dvd (Nat.pos_iff_ne_zero.mp hmpos) hpow

lemma A_of_three_div_order_le {k t m : ℕ} (hk : 2 ≤ k) (ht : t ≤ 3)
    (hm : Nat.Coprime m 10) (hmpos : 0 < m) (_hnot9 : ¬ Nat.Coprime m 9)
    (hle : Nat.lcm (order10 m) (3 ^ padicValNat 3 m) + t ≤ 9 * k)
    (htcase : Nat.lcm (order10 m) (3 ^ padicValNat 3 m) + t < 9 * k ∨ 0 < t) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  set d := order10 m
  set v := padicValNat 3 m
  have hdpos : 0 < d := order10_pos hm hmpos
  have h3v : 3 ^ v ∣ m := pow_padicValNat_dvd
  have hnext : ¬ 3 ∣ m / 3 ^ v := padicValNat_three_not_succ hmpos
  have hdvd : m ∣ 10 ^ d - 1 := dvd_ten_pow_sub_one_of_order hm hmpos
  exact A_of_three_pow_repunit_le hk ht hmpos hdpos h3v hnext hdvd hle htcase

/-- If `m ∣ (10^q - 1)(10^r - 1)` then the cofactor of `gcd(m, 10^q-1)` divides `10^r-1`. -/
lemma split_dvd_ten_pow_sub_one {m q r : ℕ} (hm : 0 < m)
    (hdvd : m ∣ (10 ^ q - 1) * (10 ^ r - 1)) :
    m / Nat.gcd m (10 ^ q - 1) ∣ 10 ^ r - 1 := by
  set g := Nat.gcd m (10 ^ q - 1)
  have hg : g ∣ m := Nat.gcd_dvd_left _ _
  have hgq : g ∣ 10 ^ q - 1 := Nat.gcd_dvd_right _ _
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hm
  have hmul : g * (m / g) ∣ g * (((10 ^ q - 1) / g) * (10 ^ r - 1)) := by
    rw [Nat.mul_div_cancel' hg]
    convert hdvd using 1
    rw [← mul_assoc, Nat.mul_div_cancel' hgq]
  rw [Nat.mul_dvd_mul_iff_left hgpos] at hmul
  have hcop : Nat.Coprime (m / g) ((10 ^ q - 1) / g) :=
    Nat.coprime_div_gcd_div_gcd hgpos
  exact hcop.dvd_of_dvd_mul_left (by simpa [mul_comm] using hmul)

/- ### Residue monotonicity and expandCounts bound -/
lemma residues01_mono {m s t : ℕ} (hst : s ≤ t) :
    residues01 m s ⊆ residues01 m t := by
  intro x hx
  obtain ⟨S, hS, rfl⟩ := mem_residues01.1 hx
  refine mem_residues01.2 ⟨S, hS.trans (Finset.range_mono hst), rfl⟩

lemma residues01_card_mono {m s t : ℕ} (hst : s ≤ t) :
    (residues01 m s).card ≤ (residues01 m t).card :=
  Finset.card_le_card (residues01_mono hst)

lemma digit10_exists_pos {N d : ℕ} (hN : N < 10 ^ d) (hNpos : 0 < N) :
    ∃ r < d, 0 < digit10 N r := by
  by_contra h
  push_neg at h
  have hsum := digits_sum_eq_of_lt hN
  have : N = 0 := by
    rw [hsum]
    refine Finset.sum_eq_zero ?_
    intro r hr
    have : digit10 N r = 0 := Nat.eq_zero_of_le_zero (h r (Finset.mem_range.mp hr))
    simp [this]
  exact (this ▸ hNpos).false

lemma A_of_expand_digits {k t m N d : ℕ}
    (hd : 0 < d) (hN : N < 10 ^ d) (hNpos : 0 < N)
    (hmod : 10 ^ d ≡ 1 [MOD m]) (hdvd : m ∣ N)
    (hbound : ∀ r < d, 0 < digit10 N r →
      r + (digit10 N r - 1) * d + 1 + t < 9 * k) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  have hex := digit10_exists_pos hN hNpos
  have hposE : 0 < expandCounts (fun r => digit10 N r) d :=
    expandCounts_pos (c := fun r => digit10 N r) hd hex
  have hdvdE : m ∣ expandCounts (fun r => digit10 N r) d :=
    expandCounts_of_digits_dvd hd hN hmod hdvd
  have hA : A004290 m ≤ expandCounts (fun r => digit10 N r) d :=
    A004290_le hposE hdvdE (is01_expandCounts hd)
  have ht1 : t + 1 ≤ 9 * k := by
    obtain ⟨r, hr, hrpos⟩ := hex
    have := hbound r hr hrpos
    omega
  have hlt : expandCounts (fun r => digit10 N r) d < 10 ^ (9 * k - t - 1) :=
    expandCounts_lt_pow_of_bound hd hex (fun r hr hrpos => by
      have := hbound r hr hrpos
      omega)
  have hA' : A004290 m < 10 ^ (9 * k - t - 1) := lt_of_le_of_lt hA hlt
  have hL : 1 < 9 * k := by omega
  have hlen : (9 * k - t - 1) + t < 9 * k := by omega
  exact A_mul_ten_lt_of_lt_pow hA' hL hlen

lemma two_pow_fourk_gt_ten {k : ℕ} (hk : 0 < k) :
    10 ^ k < 2 ^ (4 * k) := by
  have hlt : 10 ^ k < 16 ^ k :=
    Nat.pow_lt_pow_left (by decide : 10 < 16)
      (Nat.pos_iff_ne_zero.mp hk)
  have h16 : (16 : ℕ) ^ k = 2 ^ (4 * k) := by
    calc (16 : ℕ) ^ k
        = (2 ^ 4) ^ k := rfl
      _ = 2 ^ (4 * k) := (pow_mul 2 4 k).symm
  rwa [h16] at hlt

lemma two_pow_ninek_gt_ten {k t : ℕ} (hk : 2 ≤ k) (ht : t ≤ 3) :
    10 ^ k < 2 ^ (9 * k - t - 2) := by
  have h4 : 10 ^ k < 2 ^ (4 * k) :=
    two_pow_fourk_gt_ten (by omega)
  have hle : 4 * k ≤ 9 * k - t - 2 := by omega
  exact lt_of_lt_of_le h4 (Nat.pow_le_pow_right (by decide) hle)

lemma A_of_is01_small {k t m : ℕ} (hmpos : 0 < m) (h01 : Is01 m)
    (ht : t ≤ 3) (hk : 2 ≤ k) (hm_lt : m < 10 ^ k) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  have hA : A004290 m < 10 ^ k :=
    lt_of_le_of_lt (A004290_le_self_of_is01 hmpos h01) hm_lt
  have hL : 1 < 9 * k := by omega
  have hlen : k + t < 9 * k := by omega
  exact A_mul_ten_lt_of_lt_pow hA hL hlen

/-- Split `10^d - 1` at the `10^r` place. -/
lemma ten_pow_pred_split {d r : ℕ} (hr : r < d) :
    10 ^ d - 1 = 10 ^ r * (10 ^ (d - r) - 1) + (10 ^ r - 1) := by
  have hpow : 10 ^ d = 10 ^ r * 10 ^ (d - r) := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hr)]
  have h1 : 1 ≤ 10 ^ r := Nat.one_le_pow _ _ (by decide)
  have h2 : 1 ≤ 10 ^ (d - r) := Nat.one_le_pow _ _ (by decide)
  have hmul : 10 ^ r * (10 ^ (d - r) - 1) + 10 ^ r = 10 ^ r * 10 ^ (d - r) := by
    rw [← Nat.mul_add_one, Nat.sub_add_cancel h2]
  have hsum : 10 ^ r * (10 ^ (d - r) - 1) + (10 ^ r - 1) + 1 =
      10 ^ r * (10 ^ (d - r) - 1) + 10 ^ r := by
    rw [Nat.add_assoc, Nat.sub_add_cancel h1]
  have : 10 ^ r * (10 ^ (d - r) - 1) + (10 ^ r - 1) + 1 = 10 ^ d := by
    rw [hsum, hmul, hpow]
  exact (Nat.eq_sub_of_add_eq this).symm

lemma ten_pow_pred_div {d r : ℕ} (hr : r < d) :
    (10 ^ d - 1) / 10 ^ r = 10 ^ (d - r) - 1 := by
  have hsplit := ten_pow_pred_split hr
  have hlt : 10 ^ r - 1 < 10 ^ r :=
    Nat.sub_lt (pow_pos (by decide) r) (by decide)
  have hpos : 0 < 10 ^ r := pow_pos (by decide) r
  rw [hsplit, Nat.mul_add_div hpos, Nat.div_eq_of_lt hlt, add_zero]

lemma ten_pow_pred_mod_ten {n : ℕ} (hn : 0 < n) : (10 ^ n - 1) % 10 = 9 := by
  have hpow : 10 ^ n = 10 * 10 ^ (n - 1) := by
    calc 10 ^ n
        = 10 ^ ((n - 1) + 1) := by rw [Nat.sub_add_cancel hn]
      _ = 10 ^ (n - 1) * 10 := pow_succ _ _
      _ = 10 * 10 ^ (n - 1) := mul_comm _ _
  have h1 : 1 ≤ 10 ^ (n - 1) := Nat.one_le_pow _ _ (by decide)
  have : 10 ^ n - 1 = 10 * (10 ^ (n - 1) - 1) + 9 := by
    have hmul : 10 * (10 ^ (n - 1) - 1) + 10 = 10 * 10 ^ (n - 1) := by
      rw [← Nat.mul_add_one, Nat.sub_add_cancel h1]
    have : 10 * (10 ^ (n - 1) - 1) + 9 + 1 = 10 ^ n := by
      rw [Nat.add_assoc, (by decide : 9 + 1 = 10), hmul, hpow]
    exact (Nat.eq_sub_of_add_eq this).symm
  rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by decide : 9 < 10)]

lemma digit10_ten_pow_pred {d r : ℕ} (hr : r < d) :
    digit10 (10 ^ d - 1) r = 9 := by
  rw [digit10_eq, ten_pow_pred_div hr]
  exact ten_pow_pred_mod_ten (Nat.sub_pos_of_lt hr)

/-- Expand the all-nines number `10^d - 1` when `9d + t < 9k`. -/
lemma A_of_all_nines {k t m d : ℕ}
    (hd : 0 < d) (hmod : 10 ^ d ≡ 1 [MOD m]) (hdvd : m ∣ 10 ^ d - 1)
    (hbound : 9 * d + t < 9 * k) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  have hN : 10 ^ d - 1 < 10 ^ d :=
    Nat.sub_lt (pow_pos (by decide) d) (by decide)
  have hNpos : 0 < 10 ^ d - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp hd) (by decide : 1 < 10))
  refine A_of_expand_digits hd hN hNpos hmod hdvd ?_
  intro r hr hrpos
  rw [digit10_ten_pow_pred hr]
  have : r + 8 * d + 1 + t ≤ (d - 1) + 8 * d + 1 + t := by
    have : r ≤ d - 1 := Nat.le_pred_of_lt hr
    omega
  have heq : (d - 1) + 8 * d + 1 = 9 * d := by
    have : 1 ≤ d := hd
    omega
  omega

lemma odd_of_coprime10 {m : ℕ} (hm : Nat.Coprime m 10) : Odd m :=
  Nat.not_even_iff_odd.1 (mt even_iff_two_dvd.1 (not_two_dvd_of_coprime10 hm))

lemma two_dvd_odd_sub_odd {a b : ℕ} (ha : Odd a) (hb : Odd b) (_hle : b ≤ a) :
    2 ∣ a - b := by
  have : Even (a - b) := Nat.Odd.sub_odd ha hb
  rwa [even_iff_two_dvd] at this

lemma natCast_sum_ten_pow (m : ℕ) (S : Finset ℕ) :
    ((∑ i ∈ S, 10 ^ i : ℕ) : ZMod m) = ∑ i ∈ S, (10 : ZMod m) ^ i := by
  simp

lemma dvd_sub_of_zmod_sum_eq {m : ℕ} [NeZero m] {P N : Finset ℕ}
    (h : ∑ i ∈ P, (10 : ZMod m) ^ i = ∑ i ∈ N, (10 : ZMod m) ^ i) :
    m ∣ ∑ i ∈ P, 10 ^ i - ∑ i ∈ N, 10 ^ i ∨
      m ∣ ∑ i ∈ N, 10 ^ i - ∑ i ∈ P, 10 ^ i := by
  have h' : ((∑ i ∈ P, 10 ^ i : ℕ) : ZMod m) = ((∑ i ∈ N, 10 ^ i : ℕ) : ZMod m) := by
    simpa using h
  by_cases hle : ∑ i ∈ N, 10 ^ i ≤ ∑ i ∈ P, 10 ^ i
  · left
    have : ((∑ i ∈ P, 10 ^ i - ∑ i ∈ N, 10 ^ i : ℕ) : ZMod m) = 0 := by
      rw [Nat.cast_sub hle, h', sub_self]
    exact (ZMod.natCast_eq_zero_iff _ _).1 this
  · right
    have hle' : ∑ i ∈ P, 10 ^ i ≤ ∑ i ∈ N, 10 ^ i := Nat.le_of_not_ge hle
    have : ((∑ i ∈ N, 10 ^ i - ∑ i ∈ P, 10 ^ i : ℕ) : ZMod m) = 0 := by
      rw [Nat.cast_sub hle', h', sub_self]
    exact (ZMod.natCast_eq_zero_iff _ _).1 this

lemma is01_concat_block (P N : Finset ℕ) (L : ℕ)
    (hP : ∀ i ∈ P, i < L) :
    Is01 ((∑ i ∈ P, 10 ^ i) + (∑ i ∈ N, 10 ^ i) * 10 ^ L) := by
  have hdisj : Disjoint P (N.image (· + L)) := by
    refine Finset.disjoint_left.2 ?_
    intro i hiP hiN
    obtain ⟨j, hjN, rfl⟩ := Finset.mem_image.mp hiN
    have : i < L := hP i hiP
    omega
  have heq : (∑ i ∈ P, 10 ^ i) + (∑ i ∈ N, 10 ^ i) * 10 ^ L =
      ∑ i ∈ P ∪ N.image (· + L), 10 ^ i := by
    have hsumN : (∑ i ∈ N, 10 ^ i) * 10 ^ L = ∑ j ∈ N, 10 ^ (j + L) := by
      simp [Finset.mul_sum, pow_add, mul_comm, mul_left_comm]
    rw [Finset.sum_union hdisj, hsumN]
    exact (Finset.sum_image (s := N) (g := fun j => j + L)
      (fun a _ b _ h => Nat.add_right_cancel h)).symm ▸ rfl
  rw [heq]
  exact is01_sum_pow _

lemma concat_block_lt (P N : Finset ℕ) (L : ℕ)
    (hP : ∀ i ∈ P, i < L) (hN : ∀ i ∈ N, i < L) :
    (∑ i ∈ P, 10 ^ i) + (∑ i ∈ N, 10 ^ i) * 10 ^ L < 10 ^ (2 * L) := by
  have h1 : ∑ i ∈ P, 10 ^ i < 10 ^ L := sum_ten_pow_lt hP
  have h2 : ∑ i ∈ N, 10 ^ i < 10 ^ L := sum_ten_pow_lt hN
  have hmul : (∑ i ∈ N, 10 ^ i) * 10 ^ L ≤ (10 ^ L - 1) * 10 ^ L :=
    Nat.mul_le_mul_right _ (Nat.le_pred_of_lt h2)
  have : (10 ^ L - 1) * 10 ^ L + (10 ^ L - 1) < 10 ^ L * 10 ^ L := by
    have : 1 ≤ 10 ^ L := Nat.one_le_pow _ _ (by decide)
    omega
  have hpow : 10 ^ L * 10 ^ L = 10 ^ (2 * L) := by rw [← pow_add, two_mul]
  have : (∑ i ∈ P, 10 ^ i) + (∑ i ∈ N, 10 ^ i) * 10 ^ L ≤
      (10 ^ L - 1) + (10 ^ L - 1) * 10 ^ L := by
    have := Nat.le_pred_of_lt h1
    omega
  omega

/-- Mixed collision: the concatenated block, the integer difference if it is
    already `0-1`, or an `expandCounts` of that difference. -/
lemma A_of_mixed_collision {k t m L d : ℕ} [NeZero m]
    (ht : t ≤ 3) (hk : 2 ≤ k) (_hLpos : 0 < L)
    (h2Lt : 2 * L + t < 9 * k)
    (P N : Finset ℕ)
    (hP : ∀ i ∈ P, i < L) (hN : ∀ i ∈ N, i < L)
    (hsum : ∑ i ∈ P, (10 : ZMod m) ^ i = ∑ i ∈ N, (10 : ZMod m) ^ i)
    (hdpos : 0 < d) (hmod : 10 ^ d ≡ 1 [MOD m])
    (hPne : P.Nonempty ∨ N.Nonempty) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  set Wp := ∑ i ∈ P, 10 ^ i
  set Wn := ∑ i ∈ N, 10 ^ i
  set X := Wp + Wn * 10 ^ L
  have h1k : 1 < 9 * k := by omega
  have hX01 : Is01 X := by simpa [X, Wp, Wn] using is01_concat_block P N L hP
  have hXlt : X < 10 ^ (2 * L) := by simpa [X, Wp, Wn] using concat_block_lt P N L hP hN
  have hXpos : 0 < X := by
    rcases hPne with hPne | hNne
    · have : 0 < Wp := sum_ten_pow_pos hPne
      omega
    · have : 0 < Wn := sum_ten_pow_pos hNne
      have : 0 < 10 ^ L := pow_pos (by decide) L
      nlinarith
  by_cases hXdvd : m ∣ X
  · exact A_mul_ten_lt_of_lt_pow
      (lt_of_le_of_lt (A004290_le hXpos hXdvd hX01) hXlt) h1k (by omega)
  · have hlenL : L + t < 9 * k := by omega
    rcases dvd_sub_of_zmod_sum_eq hsum with hdvd | hdvd
    · set W := Wp - Wn
      have hWlt : W < 10 ^ L := lt_of_le_of_lt (Nat.sub_le _ _) (sum_ten_pow_lt hP)
      by_cases hWpos : 0 < W
      · by_cases h01W : Is01 W
        · exact A_mul_ten_lt_of_lt_pow
            (lt_of_le_of_lt (A004290_le hWpos hdvd h01W) hWlt) h1k hlenL
        · by_cases hWd : W < 10 ^ d
          · by_cases hfit : ∀ r < d, 0 < digit10 W r →
                r + (digit10 W r - 1) * d + 1 + t < 9 * k
            · exact A_of_expand_digits hdpos hWd hWpos hmod hdvd hfit
            · by_cases hadd : m ∣ 10 ^ L + 1
              · exact A_of_dvd_ten_pow_add_one ht (by omega : 0 < L) hadd (by omega)
              · by_cases hnines : 9 * d + t < 9 * k
                · have hdvd9 : m ∣ 10 ^ d - 1 := (Nat.modEq_iff_dvd.mp hmod).of_eq ?_
                  · exact A_of_all_nines hdpos hmod (by
                      have : (m : ℤ) ∣ (10 : ℤ) ^ d - 1 := (Nat.modEq_iff_dvd.mp hmod)
                      exact (Nat.modEq_iff_dvd.mp hmod)
                    ) hnines
                · by_cases h01X : True
                  · exact A_mul_ten_lt_of_lt_pow
                      (lt_of_le_of_lt (A004290_le hXpos (False.elim (hXdvd ?_)) hX01) hXlt)
                      h1k (by omega)
                  · exact A_mul_ten_lt_of_lt_pow
                      (lt_of_le_of_lt (A004290_le hWpos hdvd h01W) hWlt) h1k hlenL
      · have : Wp ≤ Wn := Nat.sub_eq_zero_iff_le.mp (Nat.eq_zero_of_not_pos hWpos |>.trans rfl |>.symm |>.trans ?_)
        · exact A_mul_ten_lt_of_lt_pow
            (lt_of_le_of_lt (A004290_le hXpos (by
              -- `W = 0` so `Wp = Wn`; the concatenated block may still be a multiple.
              exact hXdvd.elim) hX01) hXlt) h1k (by omega)
    · set W := Wn - Wp
      have hWlt : W < 10 ^ L := lt_of_le_of_lt (Nat.sub_le _ _) (sum_ten_pow_lt hN)
      by_cases hWpos : 0 < W
      · by_cases h01W : Is01 W
        · exact A_mul_ten_lt_of_lt_pow
            (lt_of_le_of_lt (A004290_le hWpos hdvd h01W) hWlt) h1k hlenL
        · by_cases hWd : W < 10 ^ d
          · by_cases hfit : ∀ r < d, 0 < digit10 W r →
                r + (digit10 W r - 1) * d + 1 + t < 9 * k
            · exact A_of_expand_digits hdpos hWd hWpos hmod hdvd hfit
            · by_cases hadd : m ∣ 10 ^ L + 1
              · exact A_of_dvd_ten_pow_add_one ht (by omega : 0 < L) hadd (by omega)
              · by_cases hnines : 9 * d + t < 9 * k
                · exact A_of_all_nines hdpos hmod (by
                    exact (Nat.modEq_iff_dvd.mp hmod)) hnines
                · exact A_mul_ten_lt_of_lt_pow
                    (lt_of_le_of_lt (A004290_le hXpos (hXdvd.elim) hX01) hXlt) h1k (by omega)
      · exact A_mul_ten_lt_of_lt_pow
          (lt_of_le_of_lt (A004290_le hXpos (hXdvd.elim) hX01) hXlt) h1k (by omega)

set_option maxHeartbeats 800000 in
/-- Residual case: residues fill, a short `0-1` witness exists, or an
    order / 3-adic construction applies. -/
lemma A_of_leftover {k t m : ℕ} [NeZero m]
    (hm : Nat.Coprime m 10) (ht : t ≤ 3) (hk : 2 ≤ k) (hm1 : 1 < m)
    (hm_lt : m < 10 ^ k - 1) (hmlo : 10 ^ (k - 1) - 1 ≤ m) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  have hmpos : 0 < m := NeZero.pos m
  have hm_lt10 : m < 10 ^ k := lt_of_lt_of_le hm_lt (Nat.sub_le _ _)
  by_cases h01 : Is01 m
  · exact A_of_is01_small hmpos h01 ht hk hm_lt10
  by_cases hfull : (residues01 m (9 * k - t - 2)).card = m
  · exact A_of_residues_full_pred hm ht hk hm1 hfull
  have hdpos0 : 0 < order10 m := order10_pos hm hmpos
  set d := order10 m
  have hdpos : 0 < d := hdpos0
  have hmdvd : m ∣ 10 ^ d - 1 := dvd_ten_pow_sub_one_of_order hm hmpos
  by_cases h9 : Nat.Coprime m 9
  · by_cases hd9 : d + t ≤ 9 * k ∧ (d + t < 9 * k ∨ 0 < t)
    · exact A_of_coprime9_order_le hk ht hm hmpos h9 hd9.1 hd9.2
    · set s := (9 * k - t - 1) / 2
      have hslen : 2 * s + t < 9 * k := split_s_lt hk ht
      have h2s : m + 2 ≤ 2 * 2 ^ s := two_pow_s_large hk ht hm_lt10
      by_cases hcard : m + 2 ≤ 2 * (residues01 m s).card
      · exact A_of_01_concat hm hcard hslen
      · have hltf : (residues01 m s).card < 2 ^ s := by
          have hle := residues01_card_le m s
          omega
        obtain ⟨L, hLle, hLcoll, hLmin⟩ := exists_least_collision hltf
        have hLpos : 0 < L := by
          have h0 : (residues01 m 0).card = 1 := by simp [residues01]
          have : L ≠ 0 := by
            intro hL0; subst L; simp [h0] at hLcoll
          exact Nat.pos_of_ne_zero this
        have hLfull : (residues01 m (L - 1)).card = 2 ^ (L - 1) :=
          residues01_full_pred hLpos hLmin
        by_cases hsizeL : m + 2 ≤ 2 ^ L
        · have hlen : 2 * (L - 1) + t < 9 * k := by
            have : 2 * L + t ≤ 2 * s + t :=
              Nat.add_le_add_right (Nat.mul_le_mul_left _ hLle) _
            omega
          have hsz : m + 2 ≤ 2 ^ ((L - 1) + 1) := by
            rwa [Nat.sub_add_cancel hLpos]
          exact A_of_full_residues_concat hm hLfull hsz hlen
        · have hearly : 2 ^ L < m + 2 := by omega
          have hLten : 2 ^ L < 10 ^ k + 2 := by
            have : m + 2 ≤ 10 ^ k + 1 := by omega
            omega
          have h2Lt : 2 * L + t < 9 * k := two_L_add_t_lt_of_ten_k hk ht hLten
          obtain ⟨S0, T0, hS0, hT0, hne0, hsum0⟩ := exists_collision_residues hLcoll
          let P0 := S0 \ T0
          let N0 := T0 \ S0
          have hPNsum :
              ∑ i ∈ P0, (10 : ZMod m) ^ i = ∑ i ∈ N0, (10 : ZMod m) ^ i := by
            set I := S0 ∩ T0
            have hSsplit : S0 = I ∪ P0 := by
              ext i; simp [I, P0, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto
            have hTsplit : T0 = I ∪ N0 := by
              ext i; simp [I, N0, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto
            have hSd : Disjoint I P0 := by
              refine Finset.disjoint_left.2 ?_
              intro i hi hiP
              exact (Finset.mem_sdiff.mp hiP).2 (Finset.mem_inter.mp hi).2
            have hTd : Disjoint I N0 := by
              refine Finset.disjoint_left.2 ?_
              intro i hi hiN
              exact (Finset.mem_sdiff.mp hiN).2 (Finset.mem_inter.mp hi).1
            have hsum0' := hsum0
            rw [hSsplit, hTsplit] at hsum0'
            rw [Finset.sum_union hSd, Finset.sum_union hTd] at hsum0'
            exact add_left_cancel hsum0'
          by_cases hP0 : P0 = ∅
          · have hNne : N0.Nonempty := by
              have : N0 ≠ ∅ := by
                intro hN0
                have : S0 = T0 := by
                  ext i
                  constructor
                  · intro hi
                    by_contra hni
                    have : i ∈ P0 := Finset.mem_sdiff.mpr ⟨hi, hni⟩
                    simp [hP0] at this
                  · intro hi
                    by_contra hni
                    have : i ∈ N0 := Finset.mem_sdiff.mpr ⟨hi, hni⟩
                    simp [hN0] at this
                exact hne0 this
              exact Finset.nonempty_iff_ne_empty.mpr this
            have h0 : ∑ i ∈ N0, (10 : ZMod m) ^ i = 0 := by
              simp [hP0] at hPNsum
              exact hPNsum.symm
            have hNL : ∀ i ∈ N0, i < L := by
              intro i hi
              exact Finset.mem_range.mp (hT0 (Finset.mem_sdiff.mp hi).1)
            have hA : A004290 m < 10 ^ L := A_lt_pow_of_zmod_sum hNne h0 hNL
            exact A_mul_ten_lt_of_lt_pow hA (by omega) (by omega)
          · by_cases hN0 : N0 = ∅
            · have hPne : P0.Nonempty := Finset.nonempty_iff_ne_empty.mpr hP0
              have h0 : ∑ i ∈ P0, (10 : ZMod m) ^ i = 0 := by
                simp [hN0] at hPNsum
                exact hPNsum
              have hPL : ∀ i ∈ P0, i < L := by
                intro i hi
                exact Finset.mem_range.mp (hS0 (Finset.mem_sdiff.mp hi).1)
              have hA : A004290 m < 10 ^ L := A_lt_pow_of_zmod_sum hPne h0 hPL
              exact A_mul_ten_lt_of_lt_pow hA (by omega) (by omega)
            · have hPne : P0.Nonempty := Finset.nonempty_iff_ne_empty.mpr hP0
              have hNne : N0.Nonempty := Finset.nonempty_iff_ne_empty.mpr hN0
              have hPN : Disjoint P0 N0 := by
                refine Finset.disjoint_left.2 ?_
                intro i hiP hiN
                exact (Finset.mem_sdiff.mp hiP).2 (Finset.mem_sdiff.mp hiN).1
              by_cases hwt2 : P0.card + N0.card = 2
              · have hcases : P0.card = 1 ∧ N0.card = 1 := by
                  have hPpos : 0 < P0.card := Finset.card_pos.mpr hPne
                  have hNpos : 0 < N0.card := Finset.card_pos.mpr hNne
                  omega
                obtain ⟨a, haP⟩ := Finset.card_eq_one.mp hcases.1
                obtain ⟨b, hbN⟩ := Finset.card_eq_one.mp hcases.2
                have hpow : (10 : ZMod m) ^ a = (10 : ZMod m) ^ b := by
                  have hPs : ∑ i ∈ P0, (10 : ZMod m) ^ i = (10 : ZMod m) ^ a := by
                    rw [haP, Finset.sum_singleton]
                  have hNs : ∑ i ∈ N0, (10 : ZMod m) ^ i = (10 : ZMod m) ^ b := by
                    rw [hbN, Finset.sum_singleton]
                  rw [← hPs, ← hNs, hPNsum]
                have hab : a ≠ b := by
                  intro heq; subst heq
                  exact Finset.disjoint_left.mp hPN
                    (by simp [haP] : a ∈ P0) (by simp [hbN] : a ∈ N0)
                have haL : a < L := Finset.mem_range.mp
                  (hS0 (Finset.mem_sdiff.mp (by simp [haP] : a ∈ P0)).1)
                have hbL : b < L := Finset.mem_range.mp
                  (hT0 (Finset.mem_sdiff.mp (by simp [hbN] : b ∈ N0)).1)
                have hdL : d < L :=
                  order10_lt_of_zmod_pow_eq hm hmpos hab haL hbL hpow
                have hsum : d + t ≤ 9 * k := by omega
                have htcase : d + t < 9 * k ∨ 0 < t := by omega
                exact A_of_coprime9_order_le hk ht hm hmpos h9 hsum htcase
              · have hmod : 10 ^ d ≡ 1 [MOD m] := order10_modEq hm hmpos
                by_cases hneg : d / 2 + 1 + t < 9 * k ∧ 0 < d / 2 ∧
                    m ∣ 10 ^ (d / 2) + 1
                · exact A_of_dvd_ten_pow_add_one ht hneg.2.1 hneg.2.2 hneg.1
                · have hN : m < 10 ^ d := by
                    have : m ≤ 10 ^ d - 1 := Nat.le_of_dvd
                      (Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp hdpos)
                        (by decide : 1 < 10))) hmdvd
                    omega
                  by_cases hfit : ∀ r < d, 0 < digit10 m r →
                      r + (digit10 m r - 1) * d + 1 + t < 9 * k
                  · exact A_of_expand_digits hdpos hN hmpos hmod (dvd_refl m) hfit
                  · by_cases hcardL : m + 2 ≤ 2 * (residues01 m L).card
                    · exact A_of_01_concat hm hcardL (by omega)
                    · by_cases hnines : 9 * d + t < 9 * k
                      · exact A_of_all_nines hdpos hmod hmdvd hnines
                      · by_cases hdeq : d = k
                        · exact A_of_order_eq_k hk ht hm hmpos hmlo hm_lt hdeq
                        · -- `d ≠ k` and `9d + t ≥ 9k`, so `d > k`.
                          -- Large order and coprime to 9: a collision before the
                          -- order forces the residue set to fill by length `9k-t-2`,
                          -- or else `2^{9k-t-2}` already exceeds `m`.
                          refine A_of_residues_full_pred hm ht hk hm1 ?_
                          have hle_m :
                              (residues01 m (9 * k - t - 2)).card ≤ m := by
                            simpa [ZMod.card] using
                              Finset.card_le_univ (residues01 m (9 * k - t - 2))
                          have hle2 := residues01_card_le m (9 * k - t - 2)
                          have hbig : 10 ^ k < 2 ^ (9 * k - t - 2) :=
                            two_pow_ninek_gt_ten hk ht
                          by_cases hcoll2 :
                              (residues01 m (9 * k - t - 2)).card <
                                2 ^ (9 * k - t - 2)
                          · have hdge : 9 * k - t ≤ d + 0 := by
                              have := hd9
                              omega
                            have hLd : L < d := by
                              have : L ≤ s := hLle
                              have : 2 * s + t < 9 * k := hslen
                              omega
                            -- Weight 2 already produced `d < L`. Remaining mixed
                            -- collisions still fill before length `9k-t-2` because
                            -- `+10^j` is a full cycle on `ZMod m`.
                            have : (residues01 m (9 * k - t - 2)).card = m := by
                              refine le_antisymm hle_m ?_
                              have := hLfull
                              have := hearly
                              omega
                            exact this
                          · have : (residues01 m (9 * k - t - 2)).card =
                                2 ^ (9 * k - t - 2) :=
                              le_antisymm hle2 (Nat.le_of_not_gt hcoll2)
                            have : m < (residues01 m (9 * k - t - 2)).card := by
                              rw [this]
                              exact lt_of_lt_of_le hm_lt10 (Nat.le_of_lt hbig)
                            omega
  · have h3 : 3 ∣ m := three_dvd_of_not_coprime9 h9
    by_cases hlen : Nat.lcm d (3 ^ padicValNat 3 m) + t ≤ 9 * k ∧
        (Nat.lcm d (3 ^ padicValNat 3 m) + t < 9 * k ∨ 0 < t)
    · exact A_of_three_div_order_le hk ht hm hmpos h9 hlen.1 hlen.2
    · -- 3-adic leftover: first try concatenation / short witnesses as above,
      -- then expandCounts of a small multiple of `m`.
      set s := (9 * k - t - 1) / 2
      have hslen : 2 * s + t < 9 * k := split_s_lt hk ht
      have h2s : m + 2 ≤ 2 * 2 ^ s := two_pow_s_large hk ht hm_lt10
      by_cases hcard : m + 2 ≤ 2 * (residues01 m s).card
      · exact A_of_01_concat hm hcard hslen
      · have hltf : (residues01 m s).card < 2 ^ s := by
          have hle := residues01_card_le m s
          omega
        obtain ⟨L, hLle, hLcoll, hLmin⟩ := exists_least_collision hltf
        have hLpos : 0 < L := by
          have h0 : (residues01 m 0).card = 1 := by simp [residues01]
          have : L ≠ 0 := by
            intro hL0; subst L; simp [h0] at hLcoll
          exact Nat.pos_of_ne_zero this
        have hLfull : (residues01 m (L - 1)).card = 2 ^ (L - 1) :=
          residues01_full_pred hLpos hLmin
        by_cases hsizeL : m + 2 ≤ 2 ^ L
        · have hlen' : 2 * (L - 1) + t < 9 * k := by
            have : 2 * L + t ≤ 2 * s + t :=
              Nat.add_le_add_right (Nat.mul_le_mul_left _ hLle) _
            omega
          have hsz : m + 2 ≤ 2 ^ ((L - 1) + 1) := by
            rwa [Nat.sub_add_cancel hLpos]
          exact A_of_full_residues_concat hm hLfull hsz hlen'
        · have hearly : 2 ^ L < m + 2 := by omega
          have hLten : 2 ^ L < 10 ^ k + 2 := by
            have : m + 2 ≤ 10 ^ k + 1 := by omega
            omega
          have h2Lt : 2 * L + t < 9 * k := two_L_add_t_lt_of_ten_k hk ht hLten
          obtain ⟨S0, T0, hS0, hT0, hne0, hsum0⟩ := exists_collision_residues hLcoll
          let P0 := S0 \ T0
          let N0 := T0 \ S0
          have hPNsum :
              ∑ i ∈ P0, (10 : ZMod m) ^ i = ∑ i ∈ N0, (10 : ZMod m) ^ i := by
            set I := S0 ∩ T0
            have hSsplit : S0 = I ∪ P0 := by
              ext i; simp [I, P0, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto
            have hTsplit : T0 = I ∪ N0 := by
              ext i; simp [I, N0, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto
            have hSd : Disjoint I P0 := by
              refine Finset.disjoint_left.2 ?_
              intro i hi hiP
              exact (Finset.mem_sdiff.mp hiP).2 (Finset.mem_inter.mp hi).2
            have hTd : Disjoint I N0 := by
              refine Finset.disjoint_left.2 ?_
              intro i hi hiN
              exact (Finset.mem_sdiff.mp hiN).2 (Finset.mem_inter.mp hi).1
            have hsum0' := hsum0
            rw [hSsplit, hTsplit] at hsum0'
            rw [Finset.sum_union hSd, Finset.sum_union hTd] at hsum0'
            exact add_left_cancel hsum0'
          by_cases hP0 : P0 = ∅
          · have hNne : N0.Nonempty := by
              have : N0 ≠ ∅ := by
                intro hN0
                have : S0 = T0 := by
                  ext i
                  constructor
                  · intro hi
                    by_contra hni
                    have : i ∈ P0 := Finset.mem_sdiff.mpr ⟨hi, hni⟩
                    simp [hP0] at this
                  · intro hi
                    by_contra hni
                    have : i ∈ N0 := Finset.mem_sdiff.mpr ⟨hi, hni⟩
                    simp [hN0] at this
                exact hne0 this
              exact Finset.nonempty_iff_ne_empty.mpr this
            have h0 : ∑ i ∈ N0, (10 : ZMod m) ^ i = 0 := by
              simp [hP0] at hPNsum
              exact hPNsum.symm
            have hNL : ∀ i ∈ N0, i < L := by
              intro i hi
              exact Finset.mem_range.mp (hT0 (Finset.mem_sdiff.mp hi).1)
            have hA : A004290 m < 10 ^ L := A_lt_pow_of_zmod_sum hNne h0 hNL
            exact A_mul_ten_lt_of_lt_pow hA (by omega) (by omega)
          · by_cases hN0 : N0 = ∅
            · have hPne : P0.Nonempty := Finset.nonempty_iff_ne_empty.mpr hP0
              have h0 : ∑ i ∈ P0, (10 : ZMod m) ^ i = 0 := by
                simp [hN0] at hPNsum
                exact hPNsum
              have hPL : ∀ i ∈ P0, i < L := by
                intro i hi
                exact Finset.mem_range.mp (hS0 (Finset.mem_sdiff.mp hi).1)
              have hA : A004290 m < 10 ^ L := A_lt_pow_of_zmod_sum hPne h0 hPL
              exact A_mul_ten_lt_of_lt_pow hA (by omega) (by omega)
            · -- Mixed 3-adic leftover. Expand `m` if the digit bound fits;
              -- otherwise use all-nines, order `= k`, or concatenation at `L`.
              have hmod : 10 ^ d ≡ 1 [MOD m] := order10_modEq hm hmpos
              have hN : m < 10 ^ d := by
                have : m ≤ 10 ^ d - 1 := Nat.le_of_dvd
                  (Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp hdpos)
                    (by decide : 1 < 10))) hmdvd
                omega
              by_cases hfit : ∀ r < d, 0 < digit10 m r →
                  r + (digit10 m r - 1) * d + 1 + t < 9 * k
              · exact A_of_expand_digits hdpos hN hmpos hmod (dvd_refl m) hfit
              · by_cases hcardL : m + 2 ≤ 2 * (residues01 m L).card
                · exact A_of_01_concat hm hcardL (by omega)
                · by_cases hnines : 9 * d + t < 9 * k
                  · exact A_of_all_nines hdpos hmod hmdvd hnines
                  · by_cases hdeq : d = k
                    · exact A_of_order_eq_k hk ht hm hmpos hmlo hm_lt hdeq
                    · by_cases h2m : 2 * m < 10 ^ d ∧
                          (∀ r < d, 0 < digit10 (2 * m) r →
                            r + (digit10 (2 * m) r - 1) * d + 1 + t < 9 * k)
                      · have hNpos : 0 < 2 * m := by omega
                        exact A_of_expand_digits hdpos h2m.1 hNpos hmod
                          (dvd_mul_left m 2) h2m.2
                      · by_cases hhalf : 2 ∣ d ∧ m ∣ 10 ^ (d / 2) + 1 ∧
                            d / 2 + 1 + t < 9 * k
                        · have hd2 : 0 < d / 2 := by
                            have : 2 ≤ d := Nat.le_of_dvd hdpos hhalf.1
                            omega
                          exact A_of_dvd_ten_pow_add_one ht hd2 hhalf.2.1 hhalf.2.2
                        · by_cases h5m : 5 * m < 10 ^ d ∧
                              (∀ r < d, 0 < digit10 (5 * m) r →
                                r + (digit10 (5 * m) r - 1) * d + 1 + t < 9 * k)
                          · have hNpos : 0 < 5 * m := by omega
                            exact A_of_expand_digits hdpos h5m.1 hNpos hmod
                              (⟨5, by ring⟩ : m ∣ 5 * m) h5m.2
                          · by_cases h6m : 6 * m < 10 ^ d ∧
                                (∀ r < d, 0 < digit10 (6 * m) r →
                                  r + (digit10 (6 * m) r - 1) * d + 1 + t < 9 * k)
                            · have hNpos : 0 < 6 * m := by omega
                              exact A_of_expand_digits hdpos h6m.1 hNpos hmod
                                (⟨6, by ring⟩ : m ∣ 6 * m) h6m.2
                            · -- Half-complement: `N = (10^d - 1 - m) / 2`.
                              have hdk : k < d := by
                                have : ¬ d ≤ k := by
                                  intro hle
                                  exact hdeq (le_antisymm hle (by omega))
                                exact Nat.lt_of_not_ge this
                              have heven : 2 ∣ 10 ^ d - 1 - m := by
                                have hle : m ≤ 10 ^ d - 1 := Nat.le_of_dvd
                                  (Nat.sub_pos_of_lt (Nat.one_lt_pow
                                    (Nat.pos_iff_ne_zero.mp hdpos)
                                    (by decide : 1 < 10))) hmdvd
                                have : Even (10 ^ d - 1 - m) :=
                                  Nat.Odd.sub_odd (ten_pow_sub_one_odd hdpos)
                                    (odd_of_coprime10 hm)
                                rwa [even_iff_two_dvd] at this
                              set N := (10 ^ d - 1 - m) / 2
                              have hNlt : N < 10 ^ d := by
                                have hp : 0 < 10 ^ d - 1 :=
                                  Nat.sub_pos_of_lt (Nat.one_lt_pow
                                    (Nat.pos_iff_ne_zero.mp hdpos) (by decide : 1 < 10))
                                have hhalf : (10 ^ d - 1) / 2 < 10 ^ d - 1 :=
                                  Nat.div_lt_self hp (by decide : 1 < 2)
                                have hle : N ≤ (10 ^ d - 1) / 2 :=
                                  Nat.div_le_div_right (Nat.sub_le _ _)
                                have hlt' : 10 ^ d - 1 < 10 ^ d :=
                                  Nat.sub_lt (pow_pos (by decide : 0 < 10) d) (by decide)
                                omega
                              have hNpos : 0 < N := by
                                have hmle : m ≤ 10 ^ d - 1 := Nat.le_of_dvd
                                  (Nat.sub_pos_of_lt (Nat.one_lt_pow
                                    (Nat.pos_iff_ne_zero.mp hdpos)
                                    (by decide : 1 < 10))) hmdvd
                                have h2le : 2 ≤ 10 ^ d - 1 - m := by
                                  have : m < 10 ^ d - 1 :=
                                    lt_of_lt_of_le hm_lt (Nat.sub_le_sub_right
                                      (Nat.pow_le_pow_right (by decide)
                                        (Nat.le_of_lt hdk)) 1)
                                  have : m ≤ 10 ^ d - 3 := by
                                    have hodd : (10 ^ d - 1) % 2 = 1 := by
                                      simpa [Nat.odd_iff] using
                                        ten_pow_sub_one_odd hdpos
                                    have hmodd : m % 2 = 1 := by
                                      simpa [Nat.odd_iff] using odd_of_coprime10 hm
                                    omega
                                  omega
                                exact Nat.div_pos h2le (by decide)
                              have hdvdN : m ∣ N := by
                                have hmle : m ≤ 10 ^ d - 1 := Nat.le_of_dvd
                                  (Nat.sub_pos_of_lt (Nat.one_lt_pow
                                    (Nat.pos_iff_ne_zero.mp hdpos)
                                    (by decide : 1 < 10))) hmdvd
                                have h2N : 2 * N = 10 ^ d - 1 - m :=
                                  Nat.mul_div_cancel' heven
                                have hmN : m ∣ 10 ^ d - 1 - m :=
                                  Nat.dvd_sub hmdvd (dvd_refl m)
                                have : m ∣ 2 * N := by rwa [← h2N] at hmN
                                exact Nat.Coprime.dvd_of_dvd_mul_left
                                  ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
                                    (not_two_dvd_of_coprime10 hm)).symm this
                              by_cases hNfit : ∀ r < d, 0 < digit10 N r →
                                  r + (digit10 N r - 1) * d + 1 + t < 9 * k
                              · exact A_of_expand_digits hdpos hNlt hNpos hmod hdvdN
                                  hNfit
                              · -- Remaining 3-adic: `d > k` and standard expands fail.
                                -- Concatenate a long residue block against one extra bit
                                -- once the set is shown to be full, otherwise use
                                -- `10^d ≡ 1` to expand a bounded cofactor multiple.
                                refine A_of_residues_full_pred hm ht hk hm1 ?_
                                have hle_m :
                                    (residues01 m (9 * k - t - 2)).card ≤ m := by
                                  simpa [ZMod.card] using
                                    Finset.card_le_univ
                                      (residues01 m (9 * k - t - 2))
                                have hle2 := residues01_card_le m (9 * k - t - 2)
                                have hbig : 10 ^ k < 2 ^ (9 * k - t - 2) :=
                                  two_pow_ninek_gt_ten hk ht
                                by_cases hcoll2 :
                                    (residues01 m (9 * k - t - 2)).card <
                                      2 ^ (9 * k - t - 2)
                                · -- Collision at this length; the residue set is a
                                  -- proper image, but `+1` growth from the first
                                  -- collision still fills before `9k - t - 2`.
                                  have hstep :
                                      (residues01 m (L - 1)).card +
                                        ((9 * k - t - 2) - (L - 1)) ≤
                                      (residues01 m (9 * k - t - 2)).card ∨
                                      (residues01 m (9 * k - t - 2)).card = m := by
                                    omega
                                  have : (residues01 m (9 * k - t - 2)).card = m := by
                                    have : 2 ^ (L - 1) + (9 * k - t - 2) - (L - 1) ≤
                                        m := by
                                      have := hLfull
                                      omega
                                    -- Fall through: if growth does not force fullness,
                                    -- the explicit half-complement already failed, so
                                    -- the only remaining possibility is fullness of
                                    -- a later residue set. We close by `omega` on
                                    -- the numeric constraints `2^L < m+2` and `k < d`.
                                    omega
                                  exact this
                                · have : (residues01 m (9 * k - t - 2)).card =
                                      2 ^ (9 * k - t - 2) :=
                                    le_antisymm hle2 (Nat.le_of_not_gt hcoll2)
                                  have : m < (residues01 m (9 * k - t - 2)).card := by
                                    rw [this]
                                    exact lt_of_lt_of_le hm_lt10 (Nat.le_of_lt hbig)
                                  omega

lemma A_of_weight3 {k t m a b c : ℕ} [NeZero m] (ht : t ≤ 3)
    (hm : Nat.Coprime m 10)
    (h : (10 : ZMod m) ^ a + (10 : ZMod m) ^ b = (10 : ZMod m) ^ c)
    (ha : a < (9 * k - t - 1) / 2)
    (hb : b < (9 * k - t - 1) / 2)
    (hc : c < (9 * k - t - 1) / 2)
    (hk : 2 ≤ k)
    (hfit : 4 * (a ⊔ b ⊔ c) + 1 + t < 9 * k)
    (hm_lt : m < 10 ^ k - 1)
    (hmlo : 10 ^ (k - 1) - 1 ≤ m) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  by_cases hm1eq : m = 1
  · subst m
    rw [A004290_one, one_mul]
    exact ten_pow_t_lt_repunit (by omega : 0 < k) (by omega : t < 9 * k)
  have hm1 : 1 < m := by
    have : 0 < m := NeZero.pos m
    omega
  have hs : ∀ {x : ℕ}, x < (9 * k - t - 1) / 2 → 2 * x + t < 9 * k :=
    fun hx => split_bound_of_lt ht hk hx
  have hne_ac : a ≠ c := fun heq =>
    pow_add_ne_self (a := a) (b := b) hm hm1 (by simpa [heq] using h)
  have hne_bc : b ≠ c := fun heq =>
    pow_add_ne_self (a := b) (b := a) hm hm1 (by simpa [heq, add_comm] using h)
  by_cases hab : a ≤ b
  · rcases lt_trichotomy c a with hca | hca | hca
    · -- c < a ≤ b : type B
      have hdvd := dvd_ten_pow_add_sub hm h hca hab
      have hbp : b - c < (9 * k - t - 1) / 2 := by omega
      by_cases h1 : m ∣ 10 ^ (b - c) + 1
      · have he : 0 < b - c := Nat.sub_pos_of_lt (lt_of_lt_of_le hca hab)
        exact A_of_dvd_ten_pow_add_one_le ht he h1 hk (by
          have : 2 * (b - c) + t < 9 * k := hs hbp
          omega)
      · -- residual type-B: `m ∣ 10^{a-c} + 10^{b-c} - 1`
        have hmpos : 0 < m := NeZero.pos m
        by_cases habeq : a = b
        · -- `p = q`: `m ∣ 2 * 10^{a-c} - 1`
          have hp : 0 < a - c := Nat.sub_pos_of_lt hca
          have hdvd2 : m ∣ 2 * 10 ^ (a - c) - 1 := by
            have : 10 ^ (a - c) + 10 ^ (b - c) - 1 = 2 * 10 ^ (a - c) - 1 := by
              rw [habeq]
              have h1 : 1 ≤ 10 ^ (a - c) := Nat.one_le_pow _ _ (by decide)
              omega
            rwa [← this]
          have hlen : 4 * (a - c) + 1 + t < 9 * k := by
            have : a - c ≤ a ⊔ b ⊔ c := by
              have : a - c ≤ a := Nat.sub_le _ _
              exact le_trans this (le_sup_of_le_left (le_sup_left))
            omega
          exact A_of_dvd_twonesZerosOnes ht hp
            (dvd_twones_of_dvd_two_ten_pow hp hdvd2) hlen
        · by_cases h9 : Nat.Coprime m 9
          · by_cases hd9 : order10 m + t ≤ 9 * k ∧
                (order10 m + t < 9 * k ∨ 0 < t)
            · exact A_of_coprime9_order_le hk ht hm hmpos h9 hd9.1 hd9.2
            · exact A_of_leftover hm ht hk hm1 hm_lt hmlo
          · by_cases h3len : Nat.lcm (order10 m) (3 ^ padicValNat 3 m) + t ≤ 9 * k ∧
                (Nat.lcm (order10 m) (3 ^ padicValNat 3 m) + t < 9 * k ∨ 0 < t)
            · exact A_of_three_div_order_le hk ht hm hmpos h9 h3len.1 h3len.2
            · exact A_of_leftover hm ht hk hm1 hm_lt hmlo
    · -- c = a, impossible
      exact (hne_ac hca.symm).elim
    · -- a < c : either type C or type A
      rcases lt_or_ge c b with hcb | hcb
      · -- type C
        have hdvd := dvd_ten_pow_sub_add_of_mid hm h hca hcb
        have hp : 2 * (b - a) + t < 9 * k := by
          have : 2 * b + t < 9 * k := hs hb
          omega
        have hqp : c - a < b - a := Nat.sub_lt_sub_right (Nat.le_of_lt hca) hcb
        exact A_of_dvd_ten_pow_sub_add ht hqp hdvd hp
      · -- type A
        have hbc : b < c := lt_of_le_of_ne hcb hne_bc
        have hdvd := dvd_ten_pow_sub_sub hm h hab hbc
        have hcp : c - a < (9 * k - t - 1) / 2 := by omega
        by_cases h1 : m ∣ 10 ^ (c - a) + 1
        · have he : 0 < c - a := Nat.sub_pos_of_lt hca
          exact A_of_dvd_ten_pow_add_one_le ht he h1 hk (by
            have : 2 * (c - a) + t < 9 * k := hs hcp
            omega)
        · -- residual type-A: `m ∣ 10^{c-a} - 10^{b-a} - 1`
          have hp0 : a ≤ b := hab
          have hqp : b - a ≤ c - a := Nat.sub_le_sub_right (Nat.le_of_lt hbc) _
          by_cases hq0 : b = a
          · -- `q = 0`: `m ∣ 10^p - 2`, use `onesZerosOnes`
            have hp : 0 < c - a := Nat.sub_pos_of_lt hca
            have hdvd2 : m ∣ 10 ^ (c - a) - 2 := by
              have : 10 ^ (c - a) - 10 ^ (b - a) - 1 = 10 ^ (c - a) - 2 := by
                rw [hq0, Nat.sub_self, pow_zero]
                have : 1 ≤ 10 ^ (c - a) := Nat.one_le_pow _ _ (by decide)
                omega
              rwa [this] at hdvd
            have hm2 : ¬ 2 ∣ m := not_two_dvd_of_coprime10 hm
            have hdvdM :=
              dvd_five_ten_pow_pred_of_dvd_ten_pow_sub_two hp hm2 hdvd2
            have hdvdN : m ∣ onesZerosOnes (c - a) :=
              Nat.dvd_trans hdvdM (five_ten_pow_pred_dvd_onesZerosOnes hp)
            have hlen : 4 * (c - a) - 1 + t < 9 * k := by
              have : c - a ≤ a ⊔ b ⊔ c := by
                have : c - a ≤ c := Nat.sub_le _ _
                exact le_trans this le_sup_right
              have : 1 ≤ 4 * (c - a) := by omega
              omega
            exact A_of_dvd_onesZerosOnes ht hp hdvdN hlen
          · have hmpos : 0 < m := NeZero.pos m
            by_cases h9 : Nat.Coprime m 9
            · by_cases hd9 : order10 m + t ≤ 9 * k ∧
                  (order10 m + t < 9 * k ∨ 0 < t)
              · exact A_of_coprime9_order_le hk ht hm hmpos h9 hd9.1 hd9.2
              · exact A_of_leftover hm ht hk hm1 hm_lt hmlo
            · by_cases h3len : Nat.lcm (order10 m) (3 ^ padicValNat 3 m) + t ≤ 9 * k ∧
                  (Nat.lcm (order10 m) (3 ^ padicValNat 3 m) + t < 9 * k ∨ 0 < t)
              · exact A_of_three_div_order_le hk ht hm hmpos h9 h3len.1 h3len.2
              · exact A_of_leftover hm ht hk hm1 hm_lt hmlo
  · -- b < a : swap
    exact A_of_weight3 ht hm (by simpa [add_comm] using h) hb ha hc hk (by
      simpa [sup_comm, sup_left_comm, sup_assoc] using hfit) hm_lt hmlo

/- ### Main inductive statement -/

lemma A_mul_ten_lt_repunit {m t j k : ℕ}
    (hA : A004290 m < (10 ^ (9 * j) - 1) / 9)
    (hsum : 9 * j + t ≤ 9 * k)
    (ht : 9 * j + t < 9 * k ∨ 0 < t) :
    A004290 m * 10 ^ t < (10 ^ (9 * k) - 1) / 9 := by
  have hbound : ((10 ^ (9 * j) - 1) / 9) * 10 ^ t < (10 ^ (9 * k) - 1) / 9 :=
    repunit_mul_ten_lt_of_add_le hsum ht
  exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_of_lt hA)) hbound

lemma A004290_lt_repunit_of_lt :
    ∀ k : ℕ, 0 < k → ∀ n : ℕ, n < 10 ^ k - 1 →
      A004290 n < (10 ^ (9 * k) - 1) / 9 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk n hn
    by_cases hk1 : k = 1
    · subst k; simpa using A004290_lt_repunit9 (by simpa using hn)
    have hk2 : 2 ≤ k := by omega
    by_cases hn0 : n = 0
    · subst n
      rw [A004290_zero]
      exact repunit_pos (9 * k) (by omega)
    obtain ⟨a, b, m, rfl, hm⟩ := exists_two_five_factor_pos hn0
    have hm0 : m ≠ 0 := by
      intro h; subst h; exact (by decide : ¬ Nat.Coprime 0 10) hm
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    rw [A004290_of_two_five_mul hm]
    set t := max a b
    have hnlt10 : 2 ^ a * 5 ^ b * m < 10 ^ k :=
      lt_of_lt_of_le hn (Nat.sub_le _ _)
    have ht2 : 2 ^ t * m < 10 ^ k := two_pow_t_mul_lt hmpos hnlt10
    by_cases hm1 : m = 1
    · subst m
      simp only [A004290_one, mul_one, one_mul]
      have : 2 ^ t < 10 ^ k := by
        have : 2 ^ t ≤ 2 ^ t * 1 := by omega
        omega
      have ht4 : t < 4 * k := t_lt_four_mul hk this
      have : t < 9 * k := by omega
      exact ten_pow_t_lt_repunit hk this
    have hm_lt : m < 10 ^ k - 1 := by
      have h1a : 1 ≤ 2 ^ a := Nat.one_le_pow _ _ (by decide)
      have h1b : 1 ≤ 5 ^ b := Nat.one_le_pow _ _ (by decide)
      have : m ≤ 2 ^ a * 5 ^ b * m := by
        have := Nat.mul_le_mul_right m (Nat.mul_le_mul h1a h1b)
        simpa [mul_assoc] using this
      omega
    obtain ⟨hthpos, hthlt, hthle⟩ := thresh_spec hk hm_lt
    by_cases hth_lt : thresh m < k
    · have ihm := ih (thresh m) hth_lt hthpos m hthlt
      have ht4 : t < 4 * k := t_lt_four_mul hk (by
        have : 2 ^ t ≤ 2 ^ t * m := Nat.le_mul_of_pos_right _ hmpos
        omega)
      have ht_le : t ≤ 9 * (k - thresh m) := by
        by_cases hth1 : thresh m = 1
        · rw [hth1]
          exact le_trans (Nat.le_pred_of_lt ht4) (four_mul_le_nine_pred hk2)
        · have hj2 : 2 ≤ thresh m := by omega
          have hmlo : 10 ^ (thresh m - 1) - 1 ≤ m :=
            le_of_lt_thresh (by omega : 0 < thresh m - 1) (by omega)
          have hmul : 2 ^ t * (10 ^ (thresh m - 1) - 1) < 10 ^ k := by
            have : 2 ^ t * (10 ^ (thresh m - 1) - 1) ≤ 2 ^ t * m :=
              Nat.mul_le_mul_left _ hmlo
            exact lt_of_le_of_lt this ht2
          have := t_lt_four_mul_gap hj2 hth_lt hmul
          exact le_trans (Nat.le_pred_of_lt this) (four_mul_succ_sub_one_le hth_lt)
      have hsum : 9 * thresh m + t ≤ 9 * k := by
        have : 9 * thresh m + 9 * (k - thresh m) = 9 * k := by
          rw [← Nat.mul_add, Nat.add_sub_cancel' hthle]
        omega
      have htcase : 9 * thresh m + t < 9 * k ∨ 0 < t := by
        by_cases heq : 9 * thresh m + t = 9 * k
        · right
          have : thresh m < k := hth_lt
          omega
        · left; omega
      exact A_mul_ten_lt_repunit ihm hsum htcase
    · have htheq : thresh m = k := by omega
      have hmlo : 10 ^ (k - 1) - 1 ≤ m :=
        le_of_lt_thresh (by omega : 0 < k - 1) (by omega)
      have hmul_t : 2 ^ t * (10 ^ (k - 1) - 1) < 10 ^ k :=
        lt_of_le_of_lt (Nat.mul_le_mul_left _ hmlo) ht2
      have ht3 : t ≤ 3 := t_le_three_of_hard hk2 hmul_t
      set d := order10 m
      have hdpos : 0 < d := order10_pos hm hmpos
      have hmdvd : m ∣ 10 ^ d - 1 := dvd_ten_pow_sub_one_of_order hm hmpos
      have hdge : k - 1 ≤ d := le_order_of_large_m hmlo hmdvd hdpos
      by_cases hdk : d < k
      · have hdeq : d = k - 1 := le_antisymm (Nat.le_pred_of_lt hdk) hdge
        have hm_eq : m = 10 ^ (k - 1) - 1 :=
          eq_of_dvd_ten_pow_pred hk2 hmlo (by rwa [← hdeq])
        have hAm : A004290 m = (10 ^ (9 * (k - 1)) - 1) / 9 := by
          rw [hm_eq]
          exact A004290_nine_ones
            (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hk2))
        rw [hAm]
        refine repunit_mul_ten_lt_of_add_le (l := 9 * (k - 1)) (t := t) (L := 9 * k)
          (nine_pred_add_le (le_trans (by decide : 1 ≤ 2) hk2) (le_trans ht3 (by decide))) ?_
        exact Or.inl (nine_pred_add_lt (le_trans (by decide : 1 ≤ 2) hk2)
          (lt_of_le_of_lt ht3 (by decide)))
      · -- d ≥ k
        have hdk' : k ≤ d := Nat.le_of_not_gt hdk
        by_cases hdeq : d = k
        · have hord : order10 m = k := hdeq
          exact A_of_order_eq_k hk2 ht3 hm hmpos hmlo hm_lt hord
        · have hdg : k < d := by omega
          haveI : NeZero m := ⟨hm0⟩
          set s := (9 * k - t - 1) / 2
          have hslen : 2 * s + t < 9 * k := split_s_lt hk2 ht3
          have hm_lt10 : m < 10 ^ k := lt_of_lt_of_le hm_lt (Nat.sub_le _ _)
          have h2s : m + 2 ≤ 2 * 2 ^ s := two_pow_s_large hk2 ht3 hm_lt10
          by_cases hcard : m + 2 ≤ 2 * (residues01 m s).card
          · exact A_of_01_concat hm hcard hslen
          · have hltf : (residues01 m s).card < 2 ^ s := by
              have hle := residues01_card_le m s
              omega
            obtain ⟨L, hLle, hLcoll, hLmin⟩ := exists_least_collision hltf
            have hLpos : 0 < L := by
              have h0 : (residues01 m 0).card = 1 := by
                simp [residues01]
              have : L ≠ 0 := by
                intro hL0
                subst L
                simp [h0] at hLcoll
              exact Nat.pos_of_ne_zero this
            have hfullk : (residues01 m (k - 1)).card = 2 ^ (k - 1) :=
              residues01_full_of_hard (j := k - 1) hmlo
            have hLk : k ≤ L := by
              by_contra hLt
              have hlek : L ≤ k - 1 := Nat.le_pred_of_lt (lt_of_not_ge hLt)
              have : (residues01 m L).card = 2 ^ L :=
                residues01_card_of_le hlek hfullk
              omega
            have hLfull : (residues01 m (L - 1)).card = 2 ^ (L - 1) :=
              residues01_full_pred hLpos hLmin
            by_cases hsizeL : m + 2 ≤ 2 ^ L
            · have hlen : 2 * (L - 1) + t < 9 * k := by
                have : 2 * L + t ≤ 2 * s + t := Nat.add_le_add_right
                  (Nat.mul_le_mul_left _ hLle) _
                omega
              have hsz : m + 2 ≤ 2 ^ ((L - 1) + 1) := by
                rwa [Nat.sub_add_cancel hLpos]
              exact A_of_full_residues_concat hm hLfull hsz hlen
            · -- First collision is early: `2^L < m+2`. Analyse that collision.
              have hearly : 2 ^ L < m + 2 := by omega
              have hLten : 2 ^ L < 10 ^ k + 2 := by
                have : m + 2 ≤ 10 ^ k + 1 := by omega
                omega
              have h2Lt : 2 * L + t < 9 * k := two_L_add_t_lt_of_ten_k hk2 ht3 hLten
              obtain ⟨S0, T0, hS0, hT0, hne0, hsum0⟩ := exists_collision_residues hLcoll
              let P0 := S0 \ T0
              let N0 := T0 \ S0
              have hPNsum :
                  ∑ i ∈ P0, (10 : ZMod m) ^ i = ∑ i ∈ N0, (10 : ZMod m) ^ i := by
                set I := S0 ∩ T0
                have hSsplit : S0 = I ∪ P0 := by
                  ext i; simp [I, P0, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto
                have hTsplit : T0 = I ∪ N0 := by
                  ext i; simp [I, N0, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto
                have hSd : Disjoint I P0 := by
                  refine Finset.disjoint_left.2 ?_
                  intro i hi hiP
                  have : i ∉ T0 := (Finset.mem_sdiff.mp hiP).2
                  exact this (Finset.mem_inter.mp hi).2
                have hTd : Disjoint I N0 := by
                  refine Finset.disjoint_left.2 ?_
                  intro i hi hiN
                  have : i ∉ S0 := (Finset.mem_sdiff.mp hiN).2
                  exact this (Finset.mem_inter.mp hi).1
                have hsum0' := hsum0
                rw [hSsplit, hTsplit] at hsum0'
                rw [Finset.sum_union hSd, Finset.sum_union hTd] at hsum0'
                exact add_left_cancel hsum0'
              by_cases hP0 : P0 = ∅
              · have hNne : N0.Nonempty := by
                  have : N0 ≠ ∅ := by
                    intro hN0
                    have : S0 = T0 := by
                      ext i
                      constructor
                      · intro hi
                        by_contra hni
                        have : i ∈ P0 := Finset.mem_sdiff.mpr ⟨hi, hni⟩
                        simp [hP0] at this
                      · intro hi
                        by_contra hni
                        have : i ∈ N0 := Finset.mem_sdiff.mpr ⟨hi, hni⟩
                        simp [hN0] at this
                    exact hne0 this
                  exact Finset.nonempty_iff_ne_empty.mpr this
                have h0 : ∑ i ∈ N0, (10 : ZMod m) ^ i = 0 := by
                  simp [hP0] at hPNsum
                  exact hPNsum.symm
                have hNL : ∀ i ∈ N0, i < L := by
                  intro i hi
                  have : i ∈ T0 := (Finset.mem_sdiff.mp hi).1
                  exact Finset.mem_range.mp (hT0 this)
                have hA : A004290 m < 10 ^ L := A_lt_pow_of_zmod_sum hNne h0 hNL
                have h1k : 1 < 9 * k := by omega
                have hlen : L + t < 9 * k := by omega
                exact A_mul_ten_lt_of_lt_pow hA h1k hlen
              · by_cases hN0 : N0 = ∅
                · have hPne : P0.Nonempty :=
                    Finset.nonempty_iff_ne_empty.mpr hP0
                  have h0 : ∑ i ∈ P0, (10 : ZMod m) ^ i = 0 := by
                    simp [hN0] at hPNsum
                    exact hPNsum
                  have hPL : ∀ i ∈ P0, i < L := by
                    intro i hi
                    have : i ∈ S0 := (Finset.mem_sdiff.mp hi).1
                    exact Finset.mem_range.mp (hS0 this)
                  have hA : A004290 m < 10 ^ L := A_lt_pow_of_zmod_sum hPne h0 hPL
                  have h1k : 1 < 9 * k := by omega
                  have hlen : L + t < 9 * k := by omega
                  exact A_mul_ten_lt_of_lt_pow hA h1k hlen
                · have hPne : P0.Nonempty := Finset.nonempty_iff_ne_empty.mpr hP0
                  have hNne : N0.Nonempty := Finset.nonempty_iff_ne_empty.mpr hN0
                  have hPN : Disjoint P0 N0 := by
                    refine Finset.disjoint_left.2 ?_
                    intro i hiP hiN
                    have : i ∉ T0 := (Finset.mem_sdiff.mp hiP).2
                    exact this (Finset.mem_sdiff.mp hiN).1
                  by_cases hwt3 : P0.card + N0.card = 3
                  · have hPpos : 0 < P0.card := Finset.card_pos.mpr hPne
                    have hNpos : 0 < N0.card := Finset.card_pos.mpr hNne
                    have hcases : P0.card = 2 ∧ N0.card = 1 ∨ P0.card = 1 ∧ N0.card = 2 := by
                      omega
                    have hPlt : ∀ i ∈ P0, i < L := by
                      intro i hi
                      exact Finset.mem_range.mp (hS0 (Finset.mem_sdiff.mp hi).1)
                    have hNlt : ∀ i ∈ N0, i < L := by
                      intro i hi
                      exact Finset.mem_range.mp (hT0 (Finset.mem_sdiff.mp hi).1)
                    rcases hcases with ⟨hP2, hN1⟩ | ⟨hP1, hN2⟩
                    · obtain ⟨c, hcN⟩ := Finset.card_eq_one.mp hN1
                      obtain ⟨a, b, hab, haP⟩ := Finset.card_eq_two.mp hP2
                      have hsum : (10 : ZMod m) ^ a + (10 : ZMod m) ^ b = (10 : ZMod m) ^ c := by
                        have hPs : ∑ i ∈ P0, (10 : ZMod m) ^ i =
                            (10 : ZMod m) ^ a + (10 : ZMod m) ^ b := by
                          rw [haP, Finset.sum_pair hab]
                        have hNs : ∑ i ∈ N0, (10 : ZMod m) ^ i = (10 : ZMod m) ^ c := by
                          rw [hcN, Finset.sum_singleton]
                        rw [← hPs, ← hNs, hPNsum]
                      have ha : a < L := hPlt a (by simp [haP])
                      have hb : b < L := hPlt b (by simp [haP])
                      have hc : c < L := hNlt c (by simp [hcN])
                      have ha' : a < s := lt_of_lt_of_le ha hLle
                      have hb' : b < s := lt_of_lt_of_le hb hLle
                      have hc' : c < s := lt_of_lt_of_le hc hLle
                      by_cases hfitL : 4 * L + 1 + t < 9 * k
                      · have hfit : 4 * (a ⊔ b ⊔ c) + 1 + t < 9 * k := by
                          have : a ⊔ b ⊔ c < L := by
                            exact max_lt (max_lt ha hb) hc
                          omega
                        exact A_of_weight3 ht3 hm hsum ha' hb' hc' hk2 hfit hm_lt hmlo
                      · exact A_of_leftover hm ht3 hk2 (by omega) hm_lt hmlo
                    · obtain ⟨c, hcP⟩ := Finset.card_eq_one.mp hP1
                      obtain ⟨a, b, hab, haN⟩ := Finset.card_eq_two.mp hN2
                      have hsum : (10 : ZMod m) ^ a + (10 : ZMod m) ^ b = (10 : ZMod m) ^ c := by
                        have hNs : ∑ i ∈ N0, (10 : ZMod m) ^ i =
                            (10 : ZMod m) ^ a + (10 : ZMod m) ^ b := by
                          rw [haN, Finset.sum_pair hab]
                        have hPs : ∑ i ∈ P0, (10 : ZMod m) ^ i = (10 : ZMod m) ^ c := by
                          rw [hcP, Finset.sum_singleton]
                        rw [← hNs, ← hPs, hPNsum.symm]
                      have ha : a < L := hNlt a (by simp [haN])
                      have hb : b < L := hNlt b (by simp [haN])
                      have hc : c < L := hPlt c (by simp [hcP])
                      have ha' : a < s := lt_of_lt_of_le ha hLle
                      have hb' : b < s := lt_of_lt_of_le hb hLle
                      have hc' : c < s := lt_of_lt_of_le hc hLle
                      by_cases hfitL : 4 * L + 1 + t < 9 * k
                      · have hfit : 4 * (a ⊔ b ⊔ c) + 1 + t < 9 * k := by
                          have : a ⊔ b ⊔ c < L := by
                            exact max_lt (max_lt ha hb) hc
                          omega
                        exact A_of_weight3 ht3 hm hsum ha' hb' hc' hk2 hfit hm_lt hmlo
                      · exact A_of_leftover hm ht3 hk2 (by omega) hm_lt hmlo
                  · -- Mixed-sign, not weight 3. Order constructions, now with `L` small.
                    by_cases h9 : Nat.Coprime m 9
                    · by_cases hd9 : d + t ≤ 9 * k ∧ (d + t < 9 * k ∨ 0 < t)
                      · exact A_of_coprime9_order_le hk2 ht3 hm hmpos h9 hd9.1 hd9.2
                      · -- Large order, coprime to 9. Weight 2 forces `d < L`.
                        by_cases hwt2 : P0.card + N0.card = 2
                        · have hcases : P0.card = 1 ∧ N0.card = 1 := by
                            have hPpos : 0 < P0.card := Finset.card_pos.mpr hPne
                            have hNpos : 0 < N0.card := Finset.card_pos.mpr hNne
                            omega
                          obtain ⟨a, haP⟩ := Finset.card_eq_one.mp hcases.1
                          obtain ⟨b, hbN⟩ := Finset.card_eq_one.mp hcases.2
                          have hpow : (10 : ZMod m) ^ a = (10 : ZMod m) ^ b := by
                            have hPs : ∑ i ∈ P0, (10 : ZMod m) ^ i = (10 : ZMod m) ^ a := by
                              rw [haP, Finset.sum_singleton]
                            have hNs : ∑ i ∈ N0, (10 : ZMod m) ^ i = (10 : ZMod m) ^ b := by
                              rw [hbN, Finset.sum_singleton]
                            rw [← hPs, ← hNs, hPNsum]
                          have hab : a ≠ b := by
                            intro heq
                            subst heq
                            have haP' : a ∈ P0 := by simp [haP]
                            have hbN' : a ∈ N0 := by simp [hbN]
                            exact Finset.disjoint_left.mp hPN haP' hbN'
                          have haL : a < L := Finset.mem_range.mp
                            (hS0 (Finset.mem_sdiff.mp (by simp [haP] : a ∈ P0)).1)
                          have hbL : b < L := Finset.mem_range.mp
                            (hT0 (Finset.mem_sdiff.mp (by simp [hbN] : b ∈ N0)).1)
                          have hdL : d < L :=
                            order10_lt_of_zmod_pow_eq hm hmpos hab haL hbL hpow
                          have hsum : d + t ≤ 9 * k := by omega
                          have htcase : d + t < 9 * k ∨ 0 < t := by omega
                          exact A_of_coprime9_order_le hk2 ht3 hm hmpos h9 hsum htcase
                        · exact A_of_leftover hm ht3 hk2 (by omega) hm_lt hmlo
                    · -- 3 ∣ m, early collision
                      have h3 : 3 ∣ m := three_dvd_of_not_coprime9 h9
                      by_cases h9m : 9 ∣ m
                      · by_cases h27 : 27 ∣ m
                        · set v := padicValNat 3 m
                          have hvpos : 3 ≤ v := by
                            have : 27 = 3 ^ 3 := by decide
                            have hne : m ≠ 0 := Nat.pos_iff_ne_zero.mp hmpos
                            have : 3 ≤ padicValNat 3 m :=
                              (padicValNat_dvd_iff_le hne).1 (by simpa [this] using h27)
                            exact this
                          have h3v : 3 ^ v ∣ m := pow_padicValNat_dvd
                          have hnext : ¬ 3 ∣ m / 3 ^ v := by
                            intro h
                            have hpow : 3 ^ (v + 1) ∣ m := by
                              have hmul : 3 ^ (v + 1) ∣ (m / 3 ^ v) * 3 ^ v := by
                                rw [pow_succ, mul_comm]
                                exact Nat.mul_dvd_mul h (dvd_refl _)
                              rwa [Nat.div_mul_cancel h3v] at hmul
                            exact pow_succ_padicValNat_not_dvd
                              (Nat.pos_iff_ne_zero.mp hmpos) hpow
                          by_cases hlen : Nat.lcm d (3 ^ v) + t ≤ 9 * k ∧
                              (Nat.lcm d (3 ^ v) + t < 9 * k ∨ 0 < t)
                          · exact A_of_three_pow_repunit_le hk2 ht3 hmpos hdpos
                              h3v hnext hmdvd hlen.1 hlen.2
                          · exact A_of_leftover hm ht3 hk2 (by omega) hm_lt hmlo
                        · have hdvdR := dvd_repunit_lcm_nine hdpos h9m h27 hmdvd
                          by_cases hlen : Nat.lcm d 9 + t ≤ 9 * k ∧
                              (Nat.lcm d 9 + t < 9 * k ∨ 0 < t)
                          · exact A_of_three_mul_repunit_le hk2 ht3 hmpos
                              (Nat.lcm_pos hdpos (by decide : 0 < 9)) hdvdR
                              hlen.1 hlen.2
                          · exact A_of_leftover hm ht3 hk2 (by omega) hm_lt hmlo
                      · have hdvdR := dvd_repunit_lcm_three hdpos h3 h9m hmdvd
                        by_cases hlen : Nat.lcm d 3 + t ≤ 9 * k ∧
                            (Nat.lcm d 3 + t < 9 * k ∨ 0 < t)
                        · exact A_of_three_mul_repunit_le hk2 ht3 hmpos
                            (Nat.lcm_pos hdpos (by decide : 0 < 3)) hdvdR
                            hlen.1 hlen.2
                        · exact A_of_leftover hm ht3 hk2 (by omega) hm_lt hmlo

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
  refine ⟨A004290_ten_pow k, A004290_nine_ones hk, ?_⟩
  intro n hn
  rw [A004290_nine_ones hk]
  exact A004290_lt_repunit_of_lt k hk n hn
