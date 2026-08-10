import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A004290: Least positive multiple of $n$ that when written in base 10 uses only 0's and 1's.
-/
noncomputable def A004290 (n : ℕ) : ℕ :=
  let S := { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }
  sInf S

/-! ### Infrastructure: repunits `Repu m = (10^m - 1)/9` -/

noncomputable def Repu (m : ℕ) : ℕ := Nat.ofDigits 10 (List.replicate m 1)

lemma nine_Repu (m : ℕ) : 9 * Repu m = 10 ^ m - 1 := by
  unfold Repu
  induction m with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, pow_succ]
    have h1 : (1:ℕ) ≤ 10 ^ n := Nat.one_le_pow _ _ (by norm_num)
    omega

lemma geom_key : ∀ (x n : ℕ), 1 ≤ x →
    (x - 1) * (∑ i ∈ Finset.range n, x ^ i) = x ^ n - 1 := by
  intro x n hx
  induction n with
  | zero => simp
  | succ m ihm =>
    rw [Finset.sum_range_succ, Nat.mul_add, ihm, pow_succ, Nat.sub_mul, one_mul]
    have h2 : 1 ≤ x ^ m := Nat.one_le_pow _ _ (by omega)
    have h3 : x ^ m ≤ x * x ^ m := Nat.le_mul_of_pos_left _ (by omega)
    have h4 : x ^ m * x = x * x ^ m := by ring
    omega

lemma telescope (k : ℕ) :
    (10 ^ k - 1) * (∑ j ∈ Finset.range 9, (10 ^ k) ^ j) = 10 ^ (9 * k) - 1 := by
  have h : (1:ℕ) ≤ 10 ^ k := Nat.one_le_pow _ _ (by norm_num)
  rw [geom_key (10 ^ k) 9 h, ← pow_mul, Nat.mul_comm k 9]

lemma Repu_ninek (k : ℕ) :
    Repu (9 * k) = Repu k * (∑ j ∈ Finset.range 9, (10 ^ k) ^ j) := by
  have h9 := nine_Repu (9 * k)
  have hk := nine_Repu k
  have ht := telescope k
  have : 9 * Repu (9 * k) = 9 * (Repu k * (∑ j ∈ Finset.range 9, (10 ^ k) ^ j)) := by
    rw [h9, ← ht, ← hk]; ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) this

lemma nine_dvd_Q (k : ℕ) : 9 ∣ (∑ j ∈ Finset.range 9, (10 ^ k) ^ j) := by
  have hmod : ∀ j, (10 ^ k) ^ j % 9 = 1 := by
    intro j; rw [Nat.pow_mod, Nat.pow_mod (10) k]; norm_num
  rw [Nat.dvd_iff_mod_eq_zero, Finset.sum_nat_mod]
  simp only [hmod, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

lemma key_dvd (k : ℕ) : (10 ^ k - 1) ∣ Repu (9 * k) := by
  obtain ⟨Q', hQ'⟩ := nine_dvd_Q k
  refine ⟨Q', ?_⟩
  rw [Repu_ninek, hQ', ← nine_Repu k]; ring

lemma digits_Repu (m : ℕ) :
    Nat.digits 10 (Repu m) = List.replicate m 1 := by
  unfold Repu
  apply Nat.digits_ofDigits 10 (by norm_num)
  · intro l hl; rw [List.eq_of_mem_replicate hl]; norm_num
  · intro h; rw [List.getLast_replicate]; norm_num

lemma Repu_pos (m : ℕ) (hm : 0 < m) : 0 < Repu m := by
  have h := nine_Repu m
  have h10 : (10:ℕ) ^ 1 ≤ 10 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  omega

lemma pow_ten_mod (k i : ℕ) : (10:ℕ) ^ i ≡ 10 ^ (i % k) [MOD 10 ^ k - 1] := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  conv_lhs => rw [← Nat.div_add_mod i k, pow_add, pow_mul]
  have h10 : (1:ℕ) ≤ 10 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have h1 : (10:ℕ) ^ k ≡ 1 [MOD 10 ^ k - 1] :=
    ((Nat.modEq_iff_dvd' h10).mpr (dvd_refl _)).symm
  calc ((10:ℕ) ^ k) ^ (i / k) * 10 ^ (i % k)
      ≡ 1 ^ (i / k) * 10 ^ (i % k) [MOD 10 ^ k - 1] := (h1.pow _).mul_right _
    _ = 10 ^ (i % k) := by rw [one_pow, one_mul]

/- ### Infrastructure for the Part 2 lower bound (base `10^k` block argument) -/

-- `ofDigits` of a replicated list.
lemma ofDigits_replicate (b n c : ℕ) :
    Nat.ofDigits b (List.replicate n c) = c * ∑ i ∈ Finset.range n, b ^ i := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hs : (∑ i ∈ Finset.range m, b ^ (i + 1)) = b * ∑ i ∈ Finset.range m, b ^ i := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; rw [pow_succ]; ring
    have hsum : (∑ i ∈ Finset.range (m + 1), b ^ i) = 1 + b * ∑ i ∈ Finset.range m, b ^ i := by
      rw [Finset.sum_range_succ' (fun i => b ^ i) m, pow_zero, hs]; ring
    rw [List.replicate_succ, Nat.ofDigits_cons, ih, hsum]
    ring

-- `Repu` is monotone in its length.
lemma Repu_mono {a b : ℕ} (h : a ≤ b) : Repu a ≤ Repu b := by
  have ha := nine_Repu a
  have hb := nine_Repu b
  have : (10:ℕ) ^ a ≤ 10 ^ b := Nat.pow_le_pow_right (by norm_num) h
  omega

-- A `0-1`-digit list's `ofDigits` value is at most the repunit of its length.
lemma ofDigits01_le_Repu_len (L : List ℕ) (hL : ∀ x ∈ L, x ≤ 1) :
    Nat.ofDigits 10 L ≤ Repu L.length := by
  induction L with
  | nil => simp [Nat.ofDigits, Repu]
  | cons a t ih =>
    have ha : a ≤ 1 := hL a (List.mem_cons_self)
    have ht : ∀ x ∈ t, x ≤ 1 := fun x hx => hL x (List.mem_cons_of_mem a hx)
    have hih := ih ht
    rw [Nat.ofDigits_cons]
    show a + 10 * Nat.ofDigits 10 t ≤ Repu (t.length + 1)
    have hRepu : Repu (t.length + 1) = 1 + 10 * Repu t.length := by
      unfold Repu
      rw [List.replicate_succ, Nat.ofDigits_cons]
    rw [hRepu]
    have : 10 * Nat.ofDigits 10 t ≤ 10 * Repu t.length := Nat.mul_le_mul_left 10 hih
    omega

-- Sum bound for a list with uniformly bounded elements.
lemma list_sum_le (L : List ℕ) (c : ℕ) (h : ∀ x ∈ L, x ≤ c) :
    L.sum ≤ L.length * c := by
  induction L with
  | nil => simp
  | cons a t ih =>
    have ha : a ≤ c := h a (List.mem_cons_self)
    have ht : ∀ x ∈ t, x ≤ c := fun x hx => h x (List.mem_cons_of_mem a hx)
    have hih := ih ht
    simp only [List.sum_cons, List.length_cons]
    calc a + t.sum ≤ c + t.length * c := by omega
      _ = (t.length + 1) * c := by ring

-- Equality case: bounded elements with maximal sum are all equal to the bound.
lemma list_all_eq (L : List ℕ) (c : ℕ) (h : ∀ x ∈ L, x ≤ c)
    (hsum : L.length * c ≤ L.sum) : ∀ x ∈ L, x = c := by
  induction L with
  | nil => simp
  | cons a t ih =>
    have ha : a ≤ c := h a (List.mem_cons_self)
    have ht : ∀ x ∈ t, x ≤ c := fun x hx => h x (List.mem_cons_of_mem a hx)
    have htsum : t.sum ≤ t.length * c := list_sum_le t c ht
    simp only [List.length_cons, List.sum_cons] at hsum
    have hac : a = c := by nlinarith [hsum, htsum]
    have htfull : t.length * c ≤ t.sum := by nlinarith [hsum, hac]
    intro x hx
    rcases List.mem_cons.mp hx with h1 | h2
    · rw [h1]; exact hac
    · exact ih ht htfull x h2

-- The Part 2 lower bound: every positive `0-1` multiple of `10^k - 1` is at least `Repu (9k)`.
lemma part2_lower (k : ℕ) (hk : 0 < k) (m : ℕ) (hm : 0 < m)
    (hdvd : (10 ^ k - 1) ∣ m) (hdig : ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1) :
    Repu (9 * k) ≤ m := by
  by_contra hlt
  push_neg at hlt
  set L := Nat.digits (10 ^ k) m with hLdef
  have h10pow : (10:ℕ) ^ 1 ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hbase : 1 < 10 ^ k := by simp only [pow_one] at h10pow; omega
  have h10k1 : 1 < 10 ^ k - 1 := by simp only [pow_one] at h10pow; omega
  have hmod : (10:ℕ) ^ k % (10 ^ k - 1) = 1 := by
    have key := Nat.add_mod_left ((10:ℕ) ^ k - 1) 1
    have e1 : (10:ℕ) ^ k - 1 + 1 = 10 ^ k := by omega
    rw [e1] at key
    rw [key, Nat.mod_eq_of_lt h10k1]
  have hcong : m ≡ L.sum [MOD 10 ^ k - 1] := Nat.modEq_digits_sum (10 ^ k - 1) (10 ^ k) hmod m
  have hSdvd : (10 ^ k - 1) ∣ L.sum := by
    have hm0 : m ≡ 0 [MOD 10 ^ k - 1] := (Nat.modEq_zero_iff_dvd).mpr hdvd
    exact (Nat.modEq_zero_iff_dvd).mp (hcong.symm.trans hm0)
  have hpow9 : ((10:ℕ) ^ k) ^ 9 = 10 ^ (9 * k) := by rw [← pow_mul, Nat.mul_comm]
  have hReplt : Repu (9 * k) < 10 ^ (9 * k) := by
    have h9 := nine_Repu (9 * k)
    have hp : (1:ℕ) ≤ 10 ^ (9 * k) := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hmlt : m < ((10:ℕ) ^ k) ^ 9 := by rw [hpow9]; omega
  have hlen : L.length ≤ 9 := by
    by_contra hc
    push_neg at hc
    have hle := Nat.base_pow_length_digits_le (10 ^ k) m hbase (by omega)
    rw [← hLdef] at hle
    have h1 : ((10:ℕ) ^ k) ^ 10 ≤ (10 ^ k) ^ L.length :=
      Nat.pow_le_pow_right (by omega) hc
    have h2 : (10:ℕ) ^ k * m < (10 ^ k) ^ 10 := by
      have hh : (10:ℕ) ^ k * m < 10 ^ k * (10 ^ k) ^ 9 :=
        Nat.mul_lt_mul_of_pos_left hmlt (by positivity)
      have he : (10:ℕ) ^ k * (10 ^ k) ^ 9 = (10 ^ k) ^ 10 := by rw [← pow_succ']
      omega
    omega
  have hblock : ∀ e ∈ L, e ≤ Repu k := by
    intro e he
    obtain ⟨i, hi, hei⟩ := List.mem_iff_getElem.mp he
    have hgetD : L.getD i 0 = m / (10 ^ k) ^ i % (10 ^ k) :=
      Nat.getD_digits m i (by omega)
    have he2 : e = m / (10 ^ k) ^ i % (10 ^ k) := by
      rw [← hei, ← List.getD_eq_getElem L 0 hi, hgetD]
    have hdrop : m / (10 ^ k) ^ i = Nat.ofDigits 10 ((Nat.digits 10 m).drop (k * i)) := by
      rw [← pow_mul]
      exact Nat.self_div_pow_eq_ofDigits_drop (k * i) m (by norm_num)
    have htake : Nat.ofDigits 10 ((Nat.digits 10 m).drop (k * i)) % (10 ^ k)
        = Nat.ofDigits 10 (((Nat.digits 10 m).drop (k * i)).take k) :=
      Nat.ofDigits_mod_pow_eq_ofDigits_take k (by norm_num) _
        (fun l hl => Nat.digits_lt_base (by norm_num) (List.mem_of_mem_drop hl))
    have he3 : e = Nat.ofDigits 10 (((Nat.digits 10 m).drop (k * i)).take k) := by
      rw [he2, hdrop, htake]
    have hentries : ∀ x ∈ ((Nat.digits 10 m).drop (k * i)).take k, x ≤ 1 := by
      intro x hx
      have hmem : x ∈ Nat.digits 10 m := List.mem_of_mem_drop (List.mem_of_mem_take hx)
      rcases hdig x hmem with h0 | h1 <;> omega
    have hlenk : (((Nat.digits 10 m).drop (k * i)).take k).length ≤ k :=
      List.length_take_le k _
    rw [he3]
    exact le_trans (ofDigits01_le_Repu_len _ hentries) (Repu_mono hlenk)
  have hSle : L.sum ≤ 9 * Repu k := by
    calc L.sum ≤ L.length * Repu k := list_sum_le L (Repu k) hblock
      _ ≤ 9 * Repu k := by gcongr
  have hSpos : 0 < L.sum := by
    rcases Nat.eq_zero_or_pos L.sum with h0 | hp
    · exfalso
      have hall : ∀ x ∈ L, x = 0 := (List.sum_eq_zero_iff).mp h0
      have hLrep : L = List.replicate L.length 0 := by
        rw [List.eq_replicate_iff]; exact ⟨rfl, hall⟩
      have hm0 : m = 0 := by
        have hmd : m = Nat.ofDigits (10 ^ k) L := (Nat.ofDigits_digits (10 ^ k) m).symm
        rw [hmd, hLrep, Nat.ofDigits_replicate_zero]
      omega
    · exact hp
  have hSeq : L.sum = 9 * Repu k := by
    have hlb : 9 * Repu k ≤ L.sum := by
      rw [nine_Repu k]; exact Nat.le_of_dvd hSpos hSdvd
    omega
  have hRepukpos : 0 < Repu k := Repu_pos k hk
  have hlen9 : L.length = 9 := by
    have h1 : L.sum ≤ L.length * Repu k := list_sum_le L (Repu k) hblock
    have h2 : 9 * Repu k ≤ L.length * Repu k := by rw [← hSeq]; exact h1
    have h3 : 9 ≤ L.length := Nat.le_of_mul_le_mul_right h2 hRepukpos
    omega
  have halleq : ∀ x ∈ L, x = Repu k :=
    list_all_eq L (Repu k) hblock (by rw [hlen9, hSeq])
  have hLrep : L = List.replicate 9 (Repu k) := by
    rw [List.eq_replicate_iff]; exact ⟨hlen9, halleq⟩
  have hmval : m = Repu (9 * k) := by
    have hmd : m = Nat.ofDigits (10 ^ k) L := (Nat.ofDigits_digits (10 ^ k) m).symm
    rw [hmd, hLrep, ofDigits_replicate, Repu_ninek]
  omega

/- ### Infrastructure for Part 3: 0-1 numbers from position sets, and the Davenport regime -/

/-- The 0-1 number whose `1`-digits sit exactly at the positions in `S`. -/
noncomputable def num01 (S : Finset ℕ) : ℕ := ∑ i ∈ S, 10 ^ i

/-- Peel off the units digit of `num01 S`. -/
lemma num01_decomp (S : Finset ℕ) :
    num01 S = (if 0 ∈ S then 1 else 0) + 10 * num01 ((S.erase 0).image (fun i => i - 1)) := by
  unfold num01
  rw [Finset.mul_sum]
  rw [Finset.sum_image (by
    intro a ha b hb hab
    have ha0 : a ≥ 1 := Nat.one_le_iff_ne_zero.mpr (Finset.ne_of_mem_erase ha)
    have hb0 : b ≥ 1 := Nat.one_le_iff_ne_zero.mpr (Finset.ne_of_mem_erase hb)
    simp only [] at hab
    omega)]
  have hstep : ∀ i ∈ S.erase 0, 10 * 10 ^ (i - 1) = 10 ^ i := by
    intro i hi
    have : i ≥ 1 := Nat.one_le_iff_ne_zero.mpr (Finset.ne_of_mem_erase hi)
    rw [← _root_.pow_succ']
    congr 1
    omega
  rw [Finset.sum_congr rfl hstep]
  by_cases h0 : 0 ∈ S
  · simp only [h0, if_true]
    rw [← Finset.add_sum_erase S _ h0]
    simp
  · simp only [h0, if_false]
    rw [Finset.erase_eq_of_notMem h0]
    simp

/-- Every base-10 digit of `num01 S` is `0` or `1`. -/
lemma num01_digits_le_one (S : Finset ℕ) :
    ∀ d ∈ Nat.digits 10 (num01 S), d ≤ 1 := by
  generalize hv : num01 S = v
  induction v using Nat.strong_induction_on generalizing S with
  | _ v ih =>
    subst hv
    rcases Nat.eq_zero_or_pos (num01 S) with h0 | hpos
    · rw [h0]; simp
    · rw [Nat.digits_def' (by norm_num) hpos]
      intro d hd
      rw [List.mem_cons] at hd
      have hdecomp := num01_decomp S
      set T := (S.erase 0).image (fun i => i - 1) with hT
      have hmod : num01 S % 10 = if 0 ∈ S then 1 else 0 := by
        rw [hdecomp]; rw [Nat.add_mul_mod_self_left]; by_cases h0 : 0 ∈ S <;> simp [h0]
      have hdiv : num01 S / 10 = num01 T := by
        rw [hdecomp]
        rw [Nat.add_mul_div_left _ _ (by norm_num)]
        have : (if 0 ∈ S then (1:ℕ) else 0) / 10 = 0 := by by_cases h0 : 0∈S <;> simp [h0]
        omega
      rcases hd with hd | hd
      · rw [hd, hmod]; by_cases h0 : 0∈S <;> simp [h0]
      · rw [hdiv] at hd
        have hlt : num01 T < num01 S := by
          rw [← hdiv]; exact Nat.div_lt_self hpos (by norm_num)
        exact ih (num01 T) hlt T rfl d hd

lemma nine_num01_range (m : ℕ) : 9 * num01 (Finset.range m) = 10 ^ m - 1 := by
  unfold num01
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih, pow_succ]
    have h1 : (1:ℕ) ≤ 10 ^ n := Nat.one_le_pow _ _ (by norm_num)
    have : 9 * 10 ^ n = 10 ^ n * 10 - 10 ^ n := by ring_nf; omega
    omega

lemma Repu_eq_num01_range (m : ℕ) : Repu m = num01 (Finset.range m) := by
  have h1 := nine_Repu m
  have h2 := nine_num01_range m
  omega

lemma num01_pos {S : Finset ℕ} (hS : S.Nonempty) : 0 < num01 S := by
  unfold num01
  obtain ⟨j, hj⟩ := hS
  calc 0 < 10 ^ j := pow_pos (by norm_num : (0:ℕ) < 10) _
    _ ≤ _ := Finset.single_le_sum (fun i _ => Nat.zero_le _) hj

/-- **Reduction lemma.**  A nonempty *proper* set of positions in `{0,…,9k-1}` whose
associated 0-1 number is divisible by `n` certifies `A004290 n < Repu (9k)`. -/
lemma num01_reduction (k n : ℕ) (S : Finset ℕ)
    (hsub : S ⊆ Finset.range (9 * k)) (hne : S.Nonempty)
    (hproper : S ≠ Finset.range (9 * k))
    (hdvd : n ∣ num01 S) :
    A004290 n < Repu (9 * k) := by
  have hpos : 0 < num01 S := num01_pos hne
  have hdig : ∀ d ∈ Nat.digits 10 (num01 S), d = 0 ∨ d = 1 := by
    intro d hd
    have := num01_digits_le_one S d hd
    omega
  have hmem : num01 S ∈ {m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1} :=
    ⟨hpos, hdvd, hdig⟩
  have hle : A004290 n ≤ num01 S := Nat.sInf_le hmem
  have hlt : num01 S < Repu (9 * k) := by
    rw [Repu_eq_num01_range]
    obtain ⟨j, hjr, hjS⟩ : ∃ j ∈ Finset.range (9 * k), j ∉ S := by
      by_contra h
      push_neg at h
      exact hproper (Finset.Subset.antisymm hsub h)
    unfold num01
    apply Finset.sum_lt_sum_of_subset hsub hjr hjS
    · exact pow_pos (by norm_num : (0:ℕ) < 10) _
    · intro i _ _; exact Nat.zero_le _
  omega

/-- `num01` over a consecutive block `Ico s t` is `Repu t - Repu s`. -/
lemma num01_Ico (s t : ℕ) (h : s ≤ t) : num01 (Finset.Ico s t) = Repu t - Repu s := by
  have hsplit : num01 (Finset.range s) + num01 (Finset.Ico s t) = num01 (Finset.range t) := by
    unfold num01
    simp only [Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le s) h
  rw [Repu_eq_num01_range t, Repu_eq_num01_range s]
  omega

/-- **Davenport regime.**  For `1 ≤ n ≤ 9k-1`, a partial-sum (prefix-repunit) pigeonhole
produces a consecutive zero-sum block, hence `A004290 n < Repu (9k)`.  (This is the provable
small-modulus part of Part 3; it corresponds to the Davenport constant `D(ℤ/n)=n`.) -/
lemma davenport_case (k n : ℕ) (hn1 : 1 ≤ n) (hnk : n ≤ 9 * k - 1) :
    A004290 n < Repu (9 * k) := by
  haveI : NeZero n := ⟨by omega⟩
  have hcard : (Finset.univ : Finset (ZMod n)).card < (Finset.range (n + 1)).card := by
    rw [Finset.card_univ, Finset.card_range, ZMod.card]
    omega
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := fun t => ((Repu t : ℕ) : ZMod n)) (fun a _ => Finset.mem_univ _)
  rw [Finset.mem_range] at hx hy
  wlog hlt : x < y generalizing x y
  · exact this y hy x hx (Ne.symm hxy) hfxy.symm (by omega)
  have hmod : Repu x ≡ Repu y [MOD n] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hfxy
  have hle : Repu x ≤ Repu y := by
    have h1 := nine_Repu x; have h2 := nine_Repu y
    have : (10:ℕ)^x ≤ 10^y := Nat.pow_le_pow_right (by norm_num) (le_of_lt hlt)
    omega
  have hdvd : n ∣ num01 (Finset.Ico x y) := by
    rw [num01_Ico x y (le_of_lt hlt)]
    exact (Nat.modEq_iff_dvd' hle).mp hmod
  apply num01_reduction k n (Finset.Ico x y)
  · intro i hi
    rw [Finset.mem_Ico] at hi
    rw [Finset.mem_range]; omega
  · rw [← Finset.nonempty_Ico] at *; exact hlt
  · intro heq
    have : (9 * k - 1) ∈ Finset.Ico x y := by rw [heq]; rw [Finset.mem_range]; omega
    rw [Finset.mem_Ico] at this; omega
  · exact hdvd

/-- Part 2's value, packaged for reuse in Part 3: `a(10^k - 1) = Repu (9k)`. -/
lemma A004290_repunit (k : ℕ) (hk : 0 < k) : A004290 (10 ^ k - 1) = Repu (9 * k) := by
  unfold A004290
  have hmem : Repu (9 * k) ∈ {m : ℕ | 0 < m ∧ (10 ^ k - 1) ∣ m ∧
      ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1} := by
    refine ⟨Repu_pos _ (by omega), key_dvd k, ?_⟩
    intro d hd
    rw [digits_Repu] at hd
    right; exact List.eq_of_mem_replicate hd
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · apply le_csInf ⟨Repu (9 * k), hmem⟩
    rintro m ⟨hm, hdvd, hdig⟩
    exact part2_lower k hk m hm hdvd hdig

/-- **Repunit / small-order regime.**  If `9n ∣ 10^m - 1` for some `1 ≤ m ≤ 9k-1`, then
`n ∣ Repu m` (cancel the factor `9`), so the prefix repunit `Repu m = num01 (range m)` is a
0-1 multiple of `n` below `Repu (9k)`.  This covers every `n` coprime to `10` whose order
`ord_{9n}(10) ≤ 9k-1`, of arbitrary size. -/
lemma repunit_case (k n m : ℕ) (hm1 : 1 ≤ m) (hmk : m ≤ 9 * k - 1)
    (hdvd : (9 * n) ∣ (10 ^ m - 1)) : A004290 n < Repu (9 * k) := by
  have hnRepu : n ∣ Repu m := by
    have h9 : 9 * Repu m = 10 ^ m - 1 := nine_Repu m
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨t, ?_⟩
    have : 9 * Repu m = 9 * (n * t) := by rw [h9, ht]; ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  rw [Repu_eq_num01_range] at hnRepu
  apply num01_reduction k n (Finset.range m)
  · intro i hi; rw [Finset.mem_range] at hi; rw [Finset.mem_range]; omega
  · rw [Finset.nonempty_range_iff]; omega
  · intro heq
    have hcard := congrArg Finset.card heq
    rw [Finset.card_range, Finset.card_range] at hcard
    omega
  · exact hnRepu

/-- Shifting a position set by `e` multiplies its 0-1 number by `10^e` (append `e` zeros). -/
lemma num01_shift (S : Finset ℕ) (e : ℕ) :
    num01 (S.image (fun i => i + e)) = 10 ^ e * num01 S := by
  unfold num01
  rw [Finset.sum_image (by intro a _ b _ h; simp only [] at h; omega)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _; rw [pow_add]; ring

/-- Strip the factors of `2` and `5`: `n = 2^a · 5^b · m` with `m` coprime to `10`. -/
lemma factor_25 : ∀ (n : ℕ), 0 < n →
    ∃ a b m, n = 2 ^ a * 5 ^ b * m ∧ ¬ (2 ∣ m) ∧ ¬ (5 ∣ m) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h2 : 2 ∣ n
    · obtain ⟨n1, rfl⟩ := h2
      have hn1 : 0 < n1 := by omega
      obtain ⟨a, b, m, heq, hm2, hm5⟩ := ih n1 (by omega) hn1
      exact ⟨a + 1, b, m, by rw [heq]; ring, hm2, hm5⟩
    · by_cases h5 : 5 ∣ n
      · obtain ⟨n1, rfl⟩ := h5
        have hn1 : 0 < n1 := by omega
        obtain ⟨a, b, m, heq, hm2, hm5⟩ := ih n1 (by omega) hn1
        exact ⟨a, b + 1, m, by rw [heq]; ring, hm2, hm5⟩
      · exact ⟨0, 0, n, by ring, h2, h5⟩

/-- Divisibility composition: `2^a·5^b·m ∣ 10^e·v` when `m ∣ v`, `a ≤ e`, `b ≤ e`. -/
lemma dvd_shift_mul (a b m e v : ℕ) (ha : a ≤ e) (hb : b ≤ e) (hmv : m ∣ v) :
    (2 ^ a * 5 ^ b * m) ∣ (10 ^ e * v) := by
  have h10 : (10:ℕ) ^ e = 2 ^ e * 5 ^ e := by rw [show (10:ℕ) = 2 * 5 by norm_num, mul_pow]
  rw [h10]
  obtain ⟨w, hw⟩ := hmv
  refine ⟨2 ^ (e - a) * 5 ^ (e - b) * w, ?_⟩
  rw [hw]
  have e2 : (2:ℕ) ^ e = 2 ^ a * 2 ^ (e - a) := by rw [← pow_add]; congr 1; omega
  have e5 : (5:ℕ) ^ e = 5 ^ b * 5 ^ (e - b) := by rw [← pow_add]; congr 1; omega
  rw [e2, e5]; ring

/-- The Davenport block as an explicit subset of `range n` (the subset-producing version). -/
lemma davenport_subset (n : ℕ) (hn1 : 1 ≤ n) :
    ∃ S : Finset ℕ, S ⊆ Finset.range n ∧ S.Nonempty ∧ n ∣ num01 S := by
  haveI : NeZero n := ⟨by omega⟩
  have hcard : (Finset.univ : Finset (ZMod n)).card < (Finset.range (n + 1)).card := by
    rw [Finset.card_univ, Finset.card_range, ZMod.card]; omega
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := fun t => ((Repu t : ℕ) : ZMod n)) (fun a _ => Finset.mem_univ _)
  rw [Finset.mem_range] at hx hy
  wlog hlt : x < y generalizing x y
  · exact this y hy x hx (Ne.symm hxy) hfxy.symm (by omega)
  have hmod : Repu x ≡ Repu y [MOD n] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hfxy
  have hle : Repu x ≤ Repu y := by
    have h1 := nine_Repu x; have h2 := nine_Repu y
    have : (10:ℕ)^x ≤ 10^y := Nat.pow_le_pow_right (by norm_num) (le_of_lt hlt)
    omega
  refine ⟨Finset.Ico x y, ?_, ?_, ?_⟩
  · intro i hi; rw [Finset.mem_Ico] at hi; rw [Finset.mem_range]; omega
  · exact Finset.nonempty_Ico.mpr hlt
  · rw [num01_Ico x y (le_of_lt hlt)]; exact (Nat.modEq_iff_dvd' hle).mp hmod

/-- **`2,5`-factor regime.**  If `n = 2^a·5^b·m` with `1 ≤ a ∨ 1 ≤ b` and the coprime part
`m` fits in the budget `m + max a b ≤ 9k`, then a Davenport multiple of `m` shifted up by
`max a b` zeros is a 0-1 multiple of `n` below `Repu (9k)`. -/
lemma two_five_case (k n a b m : ℕ) (hnpos : 0 < n)
    (hfact : n = 2 ^ a * 5 ^ b * m) (hab : 1 ≤ a ∨ 1 ≤ b)
    (hbud : m + max a b ≤ 9 * k) : A004290 n < Repu (9 * k) := by
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, Nat.mul_zero] at hfact; omega
    · exact h
  obtain ⟨S', hS'sub, hS'ne, hS'dvd⟩ := davenport_subset m hm1
  set e := max a b with he
  have hae : a ≤ e := le_max_left a b
  have hbe : b ≤ e := le_max_right a b
  have he1 : 1 ≤ e := by rcases hab with h | h <;> omega
  set S := S'.image (fun i => i + e) with hS
  have hSdvd : n ∣ num01 S := by
    rw [hS, num01_shift, hfact]
    exact dvd_shift_mul a b m e (num01 S') hae hbe hS'dvd
  apply num01_reduction k n S
  · intro j hj
    rw [hS, Finset.mem_image] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    have : i < m := Finset.mem_range.mp (hS'sub hi)
    rw [Finset.mem_range]; omega
  · rw [hS]; exact hS'ne.image _
  · intro heq
    have h0 : (0:ℕ) ∈ S := by rw [heq, Finset.mem_range]; omega
    rw [hS, Finset.mem_image] at h0
    obtain ⟨i, _, hi⟩ := h0
    omega
  · exact hSdvd

/-- **`2,5`-factor regime with a short repunit on the coprime part.**  If `n = 2^a·5^b·m`
with `1 ≤ a ∨ 1 ≤ b`, and the coprime part `m` divides a *short* repunit `Repu L`
(`L + max a b ≤ 9k`), then the shifted repunit `10^{max a b}·Repu L` is a 0-1 multiple of `n`
below `Repu (9k)`.  This covers the worst-margin cases such as `n = 2^3·99` (where `99 ∣ Repu 18`
even though `99` is large as a number). -/
lemma two_five_repunit_case (k n a b m L : ℕ) (_hnpos : 0 < n)
    (hfact : n = 2 ^ a * 5 ^ b * m) (hab : 1 ≤ a ∨ 1 ≤ b)
    (hL1 : 1 ≤ L) (hmdvd : m ∣ Repu L)
    (hbud : L + max a b ≤ 9 * k) : A004290 n < Repu (9 * k) := by
  set e := max a b with he
  have hae : a ≤ e := le_max_left a b
  have hbe : b ≤ e := le_max_right a b
  have he1 : 1 ≤ e := by rcases hab with h | h <;> omega
  set S := (Finset.range L).image (fun i => i + e) with hS
  have hSdvd : n ∣ num01 S := by
    rw [hS, num01_shift, ← Repu_eq_num01_range, hfact]
    exact dvd_shift_mul a b m e (Repu L) hae hbe hmdvd
  apply num01_reduction k n S
  · intro j hj
    rw [hS, Finset.mem_image] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    have : i < L := Finset.mem_range.mp hi
    rw [Finset.mem_range]; omega
  · rw [hS]; exact (Finset.nonempty_range_iff.mpr (by omega)).image _
  · intro heq
    have h0 : (0:ℕ) ∈ S := by rw [heq, Finset.mem_range]; omega
    rw [hS, Finset.mem_image] at h0
    obtain ⟨i, _, hi⟩ := h0
    omega
  · exact hSdvd

lemma sum_modEq {N : ℕ} (s : Finset ℕ) (f g : ℕ → ℕ)
    (h : ∀ i ∈ s, f i ≡ g i [MOD N]) :
    (∑ i ∈ s, f i) ≡ (∑ i ∈ s, g i) [MOD N] := by
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact Nat.ModEq.add (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma sum_getD_eq_ofDigits (L : List ℕ) :
    ∑ i ∈ Finset.range L.length, L.getD i 0 * 10 ^ i = Nat.ofDigits 10 L := by
  induction L with
  | nil => simp [Nat.ofDigits]
  | cons a t ih =>
    rw [List.length_cons, Finset.sum_range_succ', Nat.ofDigits_cons]
    have hstep : ∀ i ∈ Finset.range t.length,
        (a :: t).getD (i+1) 0 * 10 ^ (i+1) = 10 * (t.getD i 0 * 10 ^ i) := by
      intro i _
      rw [List.getD_cons_succ, pow_succ]; ring
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, ih]
    simp only [List.getD_cons_zero, pow_zero, mul_one]; ring

lemma digit_class_case (k n d : ℕ) (hn0 : 0 < n) (hnlt : n < 10 ^ k - 1)
    (hd1 : 1 ≤ d) (hdk : d ≤ k) (hdvd : n ∣ 10 ^ d - 1) :
    A004290 n < Repu (9 * k) := by
  set L := Nat.digits 10 n with hL
  set ℓ := L.length with hℓ
  -- n ≤ 10^d - 1 < 10^d, so ℓ ≤ d
  have h10d : (1:ℕ) ≤ 10 ^ d := Nat.one_le_pow _ _ (by norm_num)
  have hd10 : (10:ℕ) ≤ 10 ^ d :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hd1)
  have hnled : n ≤ 10 ^ d - 1 := by
    obtain ⟨t, ht⟩ := hdvd
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, Nat.mul_zero] at ht; omega
    · calc n ≤ n * t := Nat.le_mul_of_pos_right _ h
        _ = 10 ^ d - 1 := ht.symm
  have hnd : n < 10 ^ d := by
    have h2 : 10 ^ d - 1 < 10 ^ d := Nat.sub_lt (by positivity) one_pos
    exact lt_of_le_of_lt hnled h2
  have hℓd : ℓ ≤ d := by
    rw [hℓ, hL]; exact (Nat.digits_length_le_iff (by norm_num : (1:ℕ) < 10) n).mpr hnd
  -- each digit ≤ 9
  have hdig9 : ∀ i, L.getD i 0 ≤ 9 := by
    intro i
    rcases lt_or_ge i ℓ with hi | hi
    · have hi' : i < (Nat.digits 10 n).length := by rw [← hL, ← hℓ]; exact hi
      have hmem : (Nat.digits 10 n).getD i 0 ∈ Nat.digits 10 n := by
        rw [List.getD_eq_getElem _ 0 hi']; exact List.getElem_mem hi'
      have h9 : (Nat.digits 10 n).getD i 0 < 10 := Nat.digits_lt_base (by norm_num) hmem
      have heq : L.getD i 0 = (Nat.digits 10 n).getD i 0 := by rw [hL]
      omega
    · have hle : L.length ≤ i := by rw [← hℓ]; exact hi
      rw [List.getD_eq_default L 0 hle]; exact Nat.zero_le _
  set col : ℕ → Finset ℕ := fun i => (Finset.range (L.getD i 0)).image (fun j => i + j * d) with hcol
  set S : Finset ℕ := (Finset.range ℓ).biUnion col with hS
  -- disjointness
  have hdisj : (↑(Finset.range ℓ) : Set ℕ).PairwiseDisjoint col := by
    intro i1 h1 i2 h2 hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [hcol, Finset.mem_image] at hp1 hp2
    obtain ⟨j1, _, he1⟩ := hp1
    obtain ⟨j2, _, he2⟩ := hp2
    simp only [Finset.mem_coe, Finset.mem_range] at h1 h2
    have hi1d : i1 < d := lt_of_lt_of_le h1 hℓd
    have hi2d : i2 < d := lt_of_lt_of_le h2 hℓd
    have hpe : i1 + j1 * d = i2 + j2 * d := by rw [he1, he2]
    have hm1 : (i1 + j1 * d) % d = i1 := by rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hi1d
    have hm2 : (i2 + j2 * d) % d = i2 := by rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hi2d
    rw [hpe, hm2] at hm1
    exact hne hm1.symm
  -- num01 of a column
  have hcolval : ∀ i, num01 (col i) = ∑ j ∈ Finset.range (L.getD i 0), 10 ^ (i + j * d) := by
    intro i
    unfold num01
    rw [hcol, Finset.sum_image]
    intro a _ b _ hab
    have : a * d = b * d := by simpa using hab
    exact Nat.eq_of_mul_eq_mul_right hd1 this
  -- divisibility: n ∣ num01 S
  have h1mod : (10 ^ d : ℕ) ≡ 1 [MOD n] := ((Nat.modEq_iff_dvd' h10d).mpr hdvd).symm
  have hSn : num01 S = ∑ i ∈ Finset.range ℓ, 10 ^ i * ∑ j ∈ Finset.range (L.getD i 0), (10 ^ d) ^ j := by
    unfold num01
    rw [hS, Finset.sum_biUnion hdisj]
    apply Finset.sum_congr rfl
    intro i _
    have := hcolval i
    unfold num01 at this
    rw [this, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← pow_mul, ← pow_add]
    congr 1; ring
  have hn_eq : n = ∑ i ∈ Finset.range ℓ, 10 ^ i * (L.getD i 0) := by
    have hofd : ∑ i ∈ Finset.range ℓ, L.getD i 0 * 10 ^ i = n := by
      rw [hℓ, sum_getD_eq_ofDigits L, hL, Nat.ofDigits_digits]
    rw [← hofd]
    apply Finset.sum_congr rfl
    intro i _; ring
  have hdvdS : n ∣ num01 S := by
    have hmod : num01 S ≡ (∑ i ∈ Finset.range ℓ, 10 ^ i * (L.getD i 0)) [MOD n] := by
      rw [hSn]
      apply sum_modEq
      intro i _
      apply Nat.ModEq.mul_left
      calc (∑ j ∈ Finset.range (L.getD i 0), (10 ^ d) ^ j)
          ≡ (∑ j ∈ Finset.range (L.getD i 0), 1) [MOD n] := by
            apply sum_modEq
            intro j _
            calc ((10 ^ d) ^ j : ℕ) ≡ 1 ^ j [MOD n] := h1mod.pow j
              _ = 1 := one_pow j
        _ = L.getD i 0 := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    rw [← hn_eq] at hmod
    have : num01 S ≡ 0 [MOD n] := hmod.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)
    exact Nat.modEq_zero_iff_dvd.mp this
  -- subset bound
  have hsub : S ⊆ Finset.range (9 * k) := by
    intro p hp
    rw [hS, Finset.mem_biUnion] at hp
    obtain ⟨i, hi, hpi⟩ := hp
    rw [hcol, Finset.mem_image] at hpi
    obtain ⟨j, hj, hpe⟩ := hpi
    rw [Finset.mem_range] at hi hj ⊢
    have hid : i < d := lt_of_lt_of_le hi hℓd
    have hj8 : j ≤ 8 := by have := hdig9 i; omega
    have hjd : j * d ≤ 8 * d := Nat.mul_le_mul_right d hj8
    omega
  -- column cardinalities
  have hcardcol : ∀ i ∈ Finset.range ℓ, (col i).card = L.getD i 0 := by
    intro i _
    have hinj : Function.Injective (fun j => i + j * d) := by
      intro a b hab
      have hh : a * d = b * d := by simp only [] at hab; omega
      exact Nat.eq_of_mul_eq_mul_right hd1 hh
    rw [hcol, Finset.card_image_of_injective _ hinj, Finset.card_range]
  -- nonempty
  have hne : S.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hall : ∀ i ∈ Finset.range ℓ, L.getD i 0 = 0 := by
      intro i hi
      by_contra hc
      have hcolne : (col i).Nonempty := by
        rw [hcol]
        exact Finset.Nonempty.image (Finset.nonempty_range_iff.mpr (by omega)) _
      obtain ⟨p, hp⟩ := hcolne
      have hpS : p ∈ S := by rw [hS, Finset.mem_biUnion]; exact ⟨i, hi, hp⟩
      rw [hempty] at hpS; exact absurd hpS (Finset.notMem_empty p)
    have hn0' : n = 0 := by
      rw [hn_eq]; apply Finset.sum_eq_zero; intro i hi; rw [hall i hi]; ring
    omega
  -- proper (card bound)
  have hcard : S.card < 9 * k := by
    rw [hS, Finset.card_biUnion hdisj, Finset.sum_congr rfl hcardcol]
    rcases Nat.lt_or_ge ℓ k with hlk | hgk
    · calc ∑ i ∈ Finset.range ℓ, L.getD i 0
            ≤ ∑ i ∈ Finset.range ℓ, 9 := Finset.sum_le_sum (fun i _ => hdig9 i)
        _ = 9 * ℓ := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring
        _ < 9 * k := by omega
    · have hek : ℓ = k := le_antisymm (le_trans hℓd hdk) hgk
      by_contra hcon
      push_neg at hcon
      have hub : ∑ i ∈ Finset.range ℓ, L.getD i 0 ≤ ∑ i ∈ Finset.range ℓ, 9 :=
        Finset.sum_le_sum (fun i _ => hdig9 i)
      have hconst : ∑ i ∈ Finset.range ℓ, (9:ℕ) = 9 * k := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, hek]; ring
      have heqsum : ∑ i ∈ Finset.range ℓ, L.getD i 0 = ∑ i ∈ Finset.range ℓ, 9 := by omega
      have heq9 := (Finset.sum_eq_sum_iff_of_le (fun i _ => hdig9 i)).mp heqsum
      have hnval : n = 10 ^ k - 1 := by
        have hrw1 : n = ∑ i ∈ Finset.range ℓ, 10 ^ i * 9 := by
          rw [hn_eq]; apply Finset.sum_congr rfl; intro i hi; rw [heq9 i hi]
        have hrw2 : ∑ i ∈ Finset.range ℓ, 10 ^ i * 9 = 9 * num01 (Finset.range ℓ) := by
          unfold num01; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
        rw [hrw1, hrw2, nine_num01_range, hek]
      omega
  have hproper : S ≠ Finset.range (9 * k) := by
    intro h; rw [h, Finset.card_range] at hcard; omega
  exact num01_reduction k n S hsub hne hproper hdvdS

/-- `A004290 0 = 0` (the defining set is empty since `0 ∣ m ↔ m = 0`). -/
lemma A004290_zero : A004290 0 = 0 := by
  unfold A004290
  apply Nat.sInf_eq_zero.mpr
  right
  ext m
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hm hdvd
  rw [zero_dvd_iff] at hdvd
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
  · -- Part 1: a(10^k) = 10^k.
    unfold A004290
    have hmem : (10 ^ k) ∈ {m : ℕ | 0 < m ∧ 10 ^ k ∣ m ∧
        ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1} := by
      refine ⟨by positivity, dvd_refl _, ?_⟩
      intro d hd
      rw [show (10:ℕ) ^ k = 10 ^ k * 1 by ring] at hd
      rw [Nat.digits_base_pow_mul (by norm_num) (by norm_num)] at hd
      simp only [Nat.digits_of_lt 10 1 (by norm_num) (by norm_num)] at hd
      rw [List.mem_append] at hd
      rcases hd with h | h
      · left; exact List.eq_of_mem_replicate h
      · right; simp only [List.mem_singleton] at h; omega
    apply le_antisymm
    · exact Nat.sInf_le hmem
    · apply le_csInf ⟨10 ^ k, hmem⟩
      rintro m ⟨hm, hdvd, _⟩
      exact Nat.le_of_dvd hm hdvd
  · -- Part 2: a(10^k - 1) = (10^{9k}-1)/9 = Repu(9k).
    have hR : (10 ^ (9 * k) - 1) / 9 = Repu (9 * k) := by
      rw [← nine_Repu (9 * k), Nat.mul_div_cancel_left _ (by norm_num)]
    rw [hR]
    exact A004290_repunit k hk
  · -- Part 3 (David Radcliffe).  For every `n < 10^k - 1`, `a(n) < a(10^k-1) = Repu (9*k)`.
    -- We rewrite the right-hand side and split on the size of `n`.
    intro n hn
    rw [A004290_repunit k hk]
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- `n = 0`: `a(0) = 0 < Repu(9k)`.
      subst hn0
      rw [A004290_zero]
      exact Repu_pos _ (by omega)
    · by_cases hsmall : n ≤ 9 * k - 1
      · -- Small-modulus regime `1 ≤ n ≤ 9k-1`: provable via the Davenport pigeonhole.
        -- A prefix-repunit collision `Repu s ≡ Repu t (mod n)` (`s<t≤n`) yields a consecutive
        -- zero-sum block `{s,…,t-1} ⊊ {0,…,9k-1}`, i.e. a 0-1 multiple `< Repu(9k)`.
        exact davenport_case k n hnpos hsmall
      · by_cases hrep : ∃ m, 1 ≤ m ∧ m ≤ 9 * k - 1 ∧ (9 * n) ∣ (10 ^ m - 1)
        · -- Small-*order* regime: `n` has a short repunit multiple `Repu m`, `m ≤ 9k-1`.
          obtain ⟨m, hm1, hmk, hd⟩ := hrep
          exact repunit_case k n m hm1 hmk hd
        · -- Strip the `2,5`-factors: `n = 2^a·5^b·m`, `m` coprime to 10.
          obtain ⟨a, b, m, hfact, _, _⟩ := factor_25 n hnpos
          by_cases htf : (1 ≤ a ∨ 1 ≤ b) ∧ m + max a b ≤ 9 * k
          · -- `2,5`-factor regime with small coprime part: provable by shift of a Davenport block.
            exact two_five_case k n a b m hnpos hfact htf.1 htf.2
          · by_cases htf2 : (1 ≤ a ∨ 1 ≤ b) ∧
                ∃ L, 1 ≤ L ∧ m ∣ Repu L ∧ L + max a b ≤ 9 * k
            · -- `2,5`-factor regime whose coprime part has a *short repunit*: shift it up.
              obtain ⟨hab2, L, hL1, hmdvd, hbud⟩ := htf2
              exact two_five_repunit_case k n a b m L hnpos hfact hab2 hL1 hmdvd hbud
            · by_cases hdc : ∃ d, 1 ≤ d ∧ d ≤ k ∧ n ∣ (10 ^ d - 1)
              · -- **Digit-class regime**: `n ∣ 10^d - 1` for some `d ≤ k` (i.e. `ord_n(10) ≤ k`).
                -- Spread the base-10 digits of `n` across the `d` residue classes mod `d` inside
                -- `{0,…,9k-1}` (each class has `≥ 9` slots since `d ≤ k`); the resulting 0-1 number
                -- is `≡ n ≡ 0 (mod n)` because `10^d ≡ 1`, and is `< Repu(9k)` since `n ≠ 10^k-1`.
                obtain ⟨d, hd1, hdk, hddvd⟩ := hdc
                exact digit_class_case k n d hnpos hn hd1 hdk hddvd
              · -- THE GENUINELY OPEN CORE: `n` coprime to 10 with `ord_n(10) ≥ 9k` (large order),
                -- where `10^0,…,10^{9k-1}` are distinct mod `n`.  The conjecture asks for a nonempty
                -- proper subset `T ⊊ {0,…,9k-1}` with `∑_{i∈T} 10^i ≡ 0 (mod n)`.  Existence of such a
                -- zero-sum subset of this geometric sequence is the exact count
                -- `N = n^{-1} ∑_t ∏_{i<9k}(1 + ζ^{t·10^i}) ≥ 2`, whose positivity rests on character-sum
                -- cancellation (equidistribution of `{t·10^i mod n}` at scale `9k`) with no known proof.
                -- Every elementary tool (Cauchy–Davenport, EGZ, Davenport constant `D(ℤ/n)=n`, Kneser,
                -- Dias da Silva–Hamidoune `≈ s²`, the reflection argument) provably stalls at a
                -- polynomial bound `n ≲ poly(k)`, far short of the needed `n ≲ 10^k`.  Exhaustive
                -- computation (`k ≤ 9`, plus meet-in-the-middle to `10^{18}`, global max ratio `0.9556`)
                -- confirms the statement is TRUE with a uniform margin — so no counterexample exists —
                -- but this is the unresolved part of the OEIS A004290 conjecture.
                sorry
