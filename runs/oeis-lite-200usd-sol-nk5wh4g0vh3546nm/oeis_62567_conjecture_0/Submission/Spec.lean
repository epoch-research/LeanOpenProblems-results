import FormalConjectures.Util.ProblemImports

set_option Elab.async false


open Nat Classical

/-- The number whose digits in base 10 are $n$'s digits reversed. -/
def reverse_nat (k : ℕ) : ℕ :=
  ofDigits 10 (digits 10 k).reverse

/--
A062567: First multiple of $n$ whose reverse is also divisible by $n$, or 0 if no such multiple exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- P(k) is the predicate for the multiplier k: k > 0 and n divides the reverse of (k*n).
    let P (k : ℕ) : Prop := k > 0 ∧ n ∣ reverse_nat (k * n)

    -- We check if a solution exists (using classical reasoning, since P is decidable).
    if h_ex : ∃ k, P k then
      -- Nat.find requires a DecidablePred instance, which holds for this property on ℕ.
      have HP : DecidablePred P := by infer_instance
      -- k_min is the smallest multiplier k >= 1.
      let k_min : ℕ := Nat.find h_ex
      k_min * n
    else
      0

/--
Conjecture A062567: It seems that only for n=2,3 & 4 we have a($3^n$) = $10^{3^{n-2}} - 1$.
(Formalized for $n \ge 2$ so that $n-2$ is a natural number exponent.)
-/
private def palBlock : List ℕ := [6, 8, 8, 9, 9, 1, 9, 9, 8, 8, 6]

private def palBlocks (t : ℕ) : List ℕ :=
  (List.replicate t palBlock).flatten

private def palNum (t : ℕ) : ℕ :=
  ofDigits 10 (palBlocks t)

private def blockSum : ℕ → ℕ
  | 0 => 0
  | t + 1 => 1 + 10 ^ 11 * blockSum t

private lemma palBlocks_reverse (t : ℕ) :
    (palBlocks t).reverse = palBlocks t := by
  simp [palBlocks, palBlock, List.reverse_flatten]


private lemma blockSum_pos {t : ℕ} (ht : 0 < t) : 0 < blockSum t := by
  cases t with
  | zero => exact (Nat.not_lt_zero 0 ht).elim
  | succ u => simp [blockSum]

private lemma palNum_reverse {t : ℕ} (ht : 0 < t) :
    reverse_nat (palNum t) = palNum t := by
  have hd : ∀ d ∈ palBlocks t, d < 10 := by
    intro d hd
    simp [palBlocks, palBlock, Nat.ne_of_gt ht] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hl : ∀ h : palBlocks t ≠ [], (palBlocks t).getLast h ≠ 0 := by
    intro h
    have heq : (palBlocks t).getLast? = some 6 := by
      rw [palBlocks, List.getLast?_flatten_replicate (Nat.ne_of_gt ht)]
      norm_num [palBlock]
    have hlast := List.getLast?_eq_getLast h
    rw [heq] at hlast
    simp at hlast
    rw [← hlast]
    norm_num
  rw [reverse_nat, palNum, Nat.digits_ofDigits 10 (by norm_num) _ hd hl,
    palBlocks_reverse]

private lemma palNum_succ (t : ℕ) :
    palNum (t + 1) = 68899199886 + 10 ^ 11 * palNum t := by
  rw [show t + 1 = t.succ by omega]
  simp only [palNum, palBlocks, List.replicate_succ, List.flatten_cons,
    Nat.ofDigits_append]
  have hb : ofDigits 10 palBlock = 68899199886 := by
    decide
  rw [hb]
  norm_num [palBlock]

private lemma palNum_eq (t : ℕ) :
    palNum t = 68899199886 * blockSum t := by
  induction t with
  | zero => simp [palNum, palBlocks, blockSum]
  | succ t ih =>
      rw [palNum_succ, ih]
      simp only [blockSum]
      ring

private lemma blockSum_add (u v : ℕ) :
    blockSum (u + v) = blockSum u + (10 ^ 11) ^ u * blockSum v := by
  induction u with
  | zero => simp [blockSum]
  | succ u ih =>
      simp only [Nat.succ_add, blockSum, ih]
      rw [pow_succ]
      ring

private lemma blockSum_three (t : ℕ) :
    blockSum (3 * t) =
      blockSum t * (1 + (10 ^ 11) ^ t + (10 ^ 11) ^ (2 * t)) := by
  rw [show 3 * t = t + (t + t) by omega, blockSum_add, blockSum_add]
  have hp : (10 ^ 11) ^ (2 * t) = (10 ^ 11) ^ t * (10 ^ 11) ^ t := by
    rw [show 2 * t = t + t by omega, pow_add]
  rw [hp]
  ring

private lemma three_dvd_blockFactor (t : ℕ) :
    3 ∣ 1 + (10 ^ 11) ^ t + (10 ^ 11) ^ (2 * t) := by
  rw [Nat.dvd_iff_mod_eq_zero]
  simp [Nat.add_mod, Nat.pow_mod]

private lemma pow_three_dvd_blockSum (k : ℕ) :
    3 ^ k ∣ blockSum (3 ^ k) := by
  induction k with
  | zero => simp [blockSum]
  | succ k ih =>
      rw [pow_succ']
      rw [blockSum_three]
      simpa [Nat.mul_comm] using
        Nat.mul_dvd_mul (three_dvd_blockFactor (3 ^ k)) ih

private lemma palBlocks_length (t : ℕ) :
    (palBlocks t).length = 11 * t := by
  simp [palBlocks, palBlock, Nat.mul_comm]

private lemma palNum_lt_pow (t : ℕ) : palNum t < 10 ^ (11 * t) := by
  rw [palNum]
  convert Nat.ofDigits_lt_base_pow_length (b := 10) (l := palBlocks t) (by norm_num) ?_
  · exact (palBlocks_length t).symm
  · intro d hd
    by_cases ht : t = 0
    · simp [palBlocks, ht] at hd
    · simp [palBlocks, palBlock, ht] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

private lemma a_le_of_witness {N m : ℕ} (hN : N ≠ 0) (hm : N ∣ m)
    (hr : N ∣ reverse_nat m) (hm0 : 0 < m) : a N ≤ m := by
  rcases hm with ⟨k, rfl⟩
  have hk : 0 < k := by
    by_contra hk
    simp at hk
    simp [hk] at hm0
  let P (j : ℕ) : Prop := j > 0 ∧ N ∣ reverse_nat (j * N)
  have hPk : P k := ⟨hk, by simpa [Nat.mul_comm] using hr⟩
  have hex : ∃ j, P j := ⟨k, hPk⟩
  rw [a]
  simp only [hN, if_false]
  rw [dif_pos hex]
  rw [Nat.mul_comm N k]
  apply Nat.mul_le_mul_right
  apply Nat.find_min'
  exact hPk

private lemma a_eq_of_min {N k : ℕ} (hN : N ≠ 0) (hk : 0 < k)
    (hr : N ∣ reverse_nat (k * N))
    (hmin : ∀ j < k, ¬(j > 0 ∧ N ∣ reverse_nat (j * N))) :
    a N = k * N := by
  let P (j : ℕ) : Prop := j > 0 ∧ N ∣ reverse_nat (j * N)
  have hPk : P k := ⟨hk, hr⟩
  have hex : ∃ j, P j := ⟨k, hPk⟩
  rw [a]

  simp only [hN, if_false]
  rw [dif_pos hex]
  congr 1
  exact (Nat.find_eq_iff hex).2 ⟨hPk, hmin⟩

private lemma reverse_mod_aux (D : List ℕ) :
    10 * ofDigits 10 D.reverse ≡ 10 ^ D.length * ofDigits 73 D [MOD 81] := by
  induction D with
  | nil => exact Nat.ModEq.refl 0
  | cons d L ih =>
    have hu : 10 * 73 ≡ 1 [MOD 81] := by norm_num [Nat.ModEq]
    have hs0 := hu.mul (Nat.ModEq.refl (10 ^ L.length * ofDigits 73 L))
    have hs : 10 ^ (L.length + 1) * (73 * ofDigits 73 L) ≡
        10 ^ L.length * ofDigits 73 L [MOD 81] := by
      convert hs0 using 1 <;> ring
    have hd : 10 * 10 ^ L.length * d ≡ 10 * 10 ^ L.length * d [MOD 81] :=
      Nat.ModEq.refl _
    have h := (ih.add hd).trans (hs.symm.add hd)
    simp only [pow_succ] at h
    rw [Nat.ofDigits_reverse_cons]
    simp only [Nat.ofDigits_cons, List.length_cons]
    convert h using 1 <;> ring

private lemma reverse_mod_nine_digits (D : List ℕ) (hl : D.length = 9) :
    ofDigits 10 D.reverse ≡ 73 * ofDigits 73 D [MOD 81] := by
  have h := reverse_mod_aux D
  rw [hl] at h
  have hc : 10 ^ 9 ≡ 10 * 73 [MOD 81] := by norm_num [Nat.ModEq]
  have hh := h.trans (hc.mul (Nat.ModEq.refl (ofDigits 73 D)))
  have hh' : 10 * ofDigits 10 D.reverse ≡
      10 * (73 * ofDigits 73 D) [MOD 81] := by
    convert hh using 1 <;> ring
  exact Nat.ModEq.cancel_left_of_coprime (by norm_num) hh'

private lemma digit_tail_mod (A B : ℕ) (h : A ≡ B [MOD 9]) :
    10 * A + 73 * 73 * B ≡ A + 73 * B [MOD 81] := by
  have h9 : 9 * A ≡ 9 * B [MOD 81] := h.mul_left' 9
  have hz : 9 * B + 5256 * B ≡ 0 [MOD 81] := by
    rw [Nat.modEq_zero_iff_dvd]
    exact ⟨65 * B, by ring⟩
  have ht := (h9.add (Nat.ModEq.refl (5256 * B))).trans hz
  have hc := (Nat.ModEq.refl (A + 73 * B)).add ht
  convert hc using 1 <;> ring

private lemma digits_combo_mod (D : List ℕ) (hl : D.length ≤ 9) :
    ofDigits 10 D + 73 * ofDigits 73 D ≡ 74 * D.sum [MOD 81] := by
  induction D with
  | nil => exact Nat.ModEq.refl 0
  | cons d L ih =>
    have hlen : L.length ≤ 9 := by simp at hl; omega
    have hi := ih hlen
    have hb : ofDigits 10 L ≡ ofDigits 73 L [MOD 9] :=
      Nat.ofDigits_modEq' 10 73 9 (by norm_num [Nat.ModEq]) L
    have ht := digit_tail_mod (ofDigits 10 L) (ofDigits 73 L) hb
    have hh := (Nat.ModEq.refl (74 * d)).add (ht.trans hi)
    simp only [Nat.ofDigits_cons, List.sum_cons]
    convert hh using 1 <;> ring

private lemma eq_nines_of_sum {D : List ℕ} (hlen : D.length = 9)
    (hdigits : ∀ d ∈ D, d < 10) (hsum : D.sum = 81) :
    D = List.replicate 9 9 := by
  apply List.eq_replicate_iff.2
  refine ⟨hlen, ?_⟩
  intro d hd
  obtain ⟨l₁, l₂, rfl⟩ := List.mem_iff_append.mp hd
  have h₁ : l₁.sum ≤ l₁.length * 9 := by
    simpa using List.sum_le_card_nsmul l₁ 9 (by
      intro x hx
      have := hdigits x (by simp [hx])
      omega)
  have h₂ : l₂.sum ≤ l₂.length * 9 := by
    simpa using List.sum_le_card_nsmul l₂ 9 (by
      intro x hx
      have := hdigits x (by simp [hx])
      omega)
  simp only [List.length_append, List.length_cons] at hlen
  simp only [List.sum_append, List.sum_cons] at hsum
  have hdle := hdigits d (by simp)
  omega

private lemma dvd_le_81_cases {s : ℕ} (hd : 81 ∣ s) (hle : s ≤ 81) :
    s = 0 ∨ s = 81 := by
  rcases hd with ⟨q, rfl⟩
  omega

private lemma no_reversible_multiple_below_nines (j : ℕ) (hj : j < 12345679)
    (hp : j > 0 ∧ 81 ∣ reverse_nat (j * 81)) : False := by
  let m := j * 81
  let L := digits 10 m
  have hmpos : 0 < m := Nat.mul_pos hp.1 (by norm_num)
  have hmtarget : m < 999999999 := by
    dsimp only [m]
    simpa using (Nat.mul_lt_mul_right (by norm_num : 0 < 81)).2 hj
  have hmlt : m < 10 ^ 9 := hmtarget.trans (by norm_num)
  have hLlen : L.length ≤ 9 := by
    apply (Nat.digits_length_le_iff (by norm_num) m).2
    exact hmlt
  let D := L ++ List.replicate (9 - L.length) 0
  have hDlen : D.length = 9 := by
    simp [D, Nat.add_sub_of_le hLlen]
  have hDdigits : ∀ d ∈ D, d < 10 := by
    intro d hd
    dsimp [D] at hd
    simp at hd
    rcases hd with hd | ⟨_, rfl⟩
    · exact Nat.digits_lt_base (by norm_num) hd
    · norm_num
  have hDm : ofDigits 10 D = m := by
    simp [D, L, Nat.ofDigits_digits]
  have hmdiv : 81 ∣ ofDigits 10 D := by
    rw [hDm]
    exact ⟨j, by simp [m, Nat.mul_comm]⟩
  have hrevdiv : 81 ∣ ofDigits 10 D.reverse := by
    dsimp only [D]
    rw [List.reverse_append, List.reverse_replicate]
    simp only [Nat.ofDigits_append, Nat.ofDigits_replicate_zero,
      List.length_replicate, zero_add]
    exact dvd_mul_of_dvd_right hp.2 _
  have hr := reverse_mod_nine_digits D hDlen
  have h73mul : 81 ∣ 73 * ofDigits 73 D := by
    rw [← Nat.modEq_zero_iff_dvd] at hrevdiv ⊢
    exact hr.symm.trans hrevdiv
  have h73 : 81 ∣ ofDigits 73 D :=
    (by norm_num : Nat.Coprime 81 73).dvd_of_dvd_mul_left h73mul
  have hc := digits_combo_mod D (by omega)
  have hsumMul : 81 ∣ 74 * D.sum := by
    rw [← Nat.modEq_zero_iff_dvd] at hmdiv h73 ⊢
    exact hc.symm.trans (hmdiv.add ((Nat.ModEq.refl 73).mul h73))
  have hsumdiv : 81 ∣ D.sum :=
    (by norm_num : Nat.Coprime 81 74).dvd_of_dvd_mul_left hsumMul
  have hsumle : D.sum ≤ 81 := by
    have := List.sum_le_card_nsmul D 9 (by
      intro d hd
      have := hDdigits d hd
      omega)
    simpa [hDlen] using this
  have hsum_cases := dvd_le_81_cases hsumdiv hsumle
  rcases hsum_cases with hzero | heq
  · have hz : ∀ d ∈ D, d = 0 := List.sum_eq_zero_iff.mp hzero
    have hDz : D = List.replicate D.length 0 := List.eq_replicate_of_mem hz
    rw [hDz] at hDm
    simp at hDm
    exact (Nat.ne_of_gt hmpos) hDm.symm
  · have hDnines := eq_nines_of_sum hDlen hDdigits heq
    have hval : ofDigits 10 D = 999999999 := by
      rw [hDnines]
      norm_num [List.replicate, Nat.ofDigits]
    exact (Nat.ne_of_lt hmtarget) (hDm.symm.trans hval)

private lemma eq_three_nines_of_sum {D : List ℕ} (hlen : D.length = 3)
    (hdigits : ∀ d ∈ D, d < 10) (hsum : D.sum = 27) :
    D = List.replicate 3 9 := by
  apply List.eq_replicate_iff.2
  refine ⟨hlen, ?_⟩
  intro d hd
  obtain ⟨l₁, l₂, rfl⟩ := List.mem_iff_append.mp hd
  have h₁ : l₁.sum ≤ l₁.length * 9 := by
    simpa using List.sum_le_card_nsmul l₁ 9 (by
      intro x hx
      have := hdigits x (by simp [hx])
      omega)
  have h₂ : l₂.sum ≤ l₂.length * 9 := by
    simpa using List.sum_le_card_nsmul l₂ 9 (by
      intro x hx
      have := hdigits x (by simp [hx])
      omega)
  simp only [List.length_append, List.length_cons] at hlen
  simp only [List.sum_append, List.sum_cons] at hsum
  have hdle := hdigits d (by simp)
  omega


private lemma dvd_le_27_cases {s : ℕ} (hd : 27 ∣ s) (hle : s ≤ 27) :
    s = 0 ∨ s = 27 := by
  rcases hd with ⟨q, rfl⟩
  omega

private lemma no_reversible_multiple_below_999 (j : ℕ) (hj : j < 37)
    (hp : j > 0 ∧ 27 ∣ reverse_nat (j * 27)) : False := by
  let m := j * 27
  let L := digits 10 m
  have hmpos : 0 < m := Nat.mul_pos hp.1 (by norm_num)
  have hmtarget : m < 999 := by
    dsimp only [m]
    simpa using (Nat.mul_lt_mul_right (by norm_num : 0 < 27)).2 hj
  have hmlt : m < 10 ^ 3 := hmtarget.trans (by norm_num)
  have hLlen : L.length ≤ 3 :=
    (Nat.digits_length_le_iff (by norm_num) m).2 hmlt
  let D := L ++ List.replicate (3 - L.length) 0
  have hDlen : D.length = 3 := by
    simp [D, Nat.add_sub_of_le hLlen]
  have hDdigits : ∀ d ∈ D, d < 10 := by
    intro d hd
    dsimp [D] at hd
    simp at hd
    rcases hd with hd | ⟨_, rfl⟩
    · exact Nat.digits_lt_base (by norm_num) hd
    · norm_num
  have hDm : ofDigits 10 D = m := by simp [D, L, Nat.ofDigits_digits]
  have hmdiv : 27 ∣ ofDigits 10 D := by
    rw [hDm]
    exact ⟨j, by simp [m, Nat.mul_comm]⟩
  have hrevdiv : 27 ∣ ofDigits 10 D.reverse := by
    dsimp only [D]
    rw [List.reverse_append, List.reverse_replicate]
    simp only [Nat.ofDigits_append, Nat.ofDigits_replicate_zero,
      List.length_replicate, zero_add]
    exact dvd_mul_of_dvd_right hp.2 _
  have hr0 := (reverse_mod_aux D).of_dvd (by norm_num : 27 ∣ 81)
  rw [hDlen] at hr0
  have hcoeff : 10 ^ 3 ≡ 10 * 73 [MOD 27] := by norm_num [Nat.ModEq]
  have hr1 := hr0.trans (hcoeff.mul (Nat.ModEq.refl (ofDigits 73 D)))
  have hr : ofDigits 10 D.reverse ≡ 73 * ofDigits 73 D [MOD 27] := by
    have hr2 : 10 * ofDigits 10 D.reverse ≡
        10 * (73 * ofDigits 73 D) [MOD 27] := by
      convert hr1 using 1 <;> ring
    exact Nat.ModEq.cancel_left_of_coprime (by norm_num) hr2
  have h73mul : 27 ∣ 73 * ofDigits 73 D := by
    rw [← Nat.modEq_zero_iff_dvd] at hrevdiv ⊢
    exact hr.symm.trans hrevdiv
  have h73 : 27 ∣ ofDigits 73 D :=
    (by norm_num : Nat.Coprime 27 73).dvd_of_dvd_mul_left h73mul
  have hc := (digits_combo_mod D (by omega)).of_dvd (by norm_num : 27 ∣ 81)
  have hsumMul : 27 ∣ 74 * D.sum := by
    rw [← Nat.modEq_zero_iff_dvd] at hmdiv h73 ⊢
    exact hc.symm.trans (hmdiv.add ((Nat.ModEq.refl 73).mul h73))
  have hsumdiv : 27 ∣ D.sum :=
    (by norm_num : Nat.Coprime 27 74).dvd_of_dvd_mul_left hsumMul
  have hsumle : D.sum ≤ 27 := by
    have h := List.sum_le_card_nsmul D 9 (by
      intro d hd
      exact Nat.le_pred_of_lt (hDdigits d hd))
    simpa [hDlen] using h
  have hsum_cases := dvd_le_27_cases hsumdiv hsumle
  rcases hsum_cases with hzero | heq
  · have hz : ∀ d ∈ D, d = 0 := List.sum_eq_zero_iff.mp hzero
    have hDz : D = List.replicate D.length 0 := List.eq_replicate_of_mem hz
    rw [hDz] at hDm
    simp at hDm
    exact (Nat.ne_of_gt hmpos) hDm.symm
  · have hDnines := eq_three_nines_of_sum hDlen hDdigits heq
    have hval : ofDigits 10 D = 999 := by
      rw [hDnines]
      norm_num [List.replicate, Nat.ofDigits]
    exact (Nat.ne_of_lt hmtarget) (hDm.symm.trans hval)



private lemma a_nine : a 9 = 9 := by
  apply a_eq_of_min (N := 9) (k := 1) (by norm_num) (by norm_num)
  · norm_num [reverse_nat, Nat.digits, Nat.digitsAux, Nat.ofDigits]
  · omega

private lemma a_twentySeven : a 27 = 999 := by
  apply a_eq_of_min (N := 27) (k := 37) (by norm_num) (by norm_num)
  · norm_num [reverse_nat, Nat.digits, Nat.digitsAux, Nat.ofDigits]
  · intro j hj hP
    exact no_reversible_multiple_below_999 j hj hP

private lemma a_eightyOne : a 81 = 999999999 := by
  apply a_eq_of_min (N := 81) (k := 12345679) (by norm_num) (by norm_num)
  · norm_num [reverse_nat, Nat.digits, Nat.digitsAux, Nat.ofDigits]
  · intro j hj hP
    exact no_reversible_multiple_below_nines j hj hP

private lemma conjecture_false_side {n : ℕ} (hn : 5 ≤ n) :
    a (3 ^ n) ≠ 10 ^ (3 ^ (n - 2)) - 1 := by
  by_cases hn12 : n < 12
  · have hnle : n ≤ 12 := Nat.le_of_lt hn12
    have hdvd12 : 3 ^ 12 ∣ palNum 1 := by
      rw [palNum_eq]
      norm_num [blockSum]
    have hdvd : 3 ^ n ∣ palNum 1 :=
      (Nat.pow_dvd_pow 3 hnle).trans hdvd12
    have hr : 3 ^ n ∣ reverse_nat (palNum 1) := by
      rw [palNum_reverse (t := 1) (by norm_num)]
      exact hdvd
    have hmpos : 0 < palNum 1 := by
      rw [palNum_eq]
      norm_num [blockSum]
    have hle : a (3 ^ n) ≤ palNum 1 :=
      a_le_of_witness (pow_ne_zero _ (by norm_num)) hdvd hr hmpos
    have hexp : 27 ≤ 3 ^ (n - 2) := by
      have he : 3 ≤ n - 2 := Nat.le_sub_of_add_le hn
      convert Nat.pow_le_pow_right (n := 3) (by norm_num) he using 1 <;> norm_num
    have hbase : palNum 1 < 10 ^ 27 - 1 := by
      rw [palNum_eq]
      norm_num [blockSum]
    have hpows : 10 ^ 27 ≤ 10 ^ (3 ^ (n - 2)) :=
      Nat.pow_le_pow_right (by norm_num) hexp
    have htarget : palNum 1 < 10 ^ (3 ^ (n - 2)) - 1 :=
      hbase.trans_le (Nat.sub_le_sub_right hpows 1)
    exact Nat.ne_of_lt (hle.trans_lt htarget)
  · have hn12' : 12 ≤ n := Nat.le_of_not_gt hn12
    let k := n - 12
    let t := 3 ^ k
    have hn_eq : n = 12 + k := by simp [k, hn12']
    have hdvdS : 3 ^ k ∣ blockSum t := pow_three_dvd_blockSum k
    have hdvdP : 3 ^ 12 ∣ 68899199886 := by norm_num
    have hdvd : 3 ^ n ∣ palNum t := by
      rw [palNum_eq, hn_eq, pow_add]
      exact Nat.mul_dvd_mul hdvdP hdvdS
    have ht : 0 < t := pow_pos (by norm_num) _
    have hr : 3 ^ n ∣ reverse_nat (palNum t) := by
      rw [palNum_reverse ht]
      exact hdvd
    have hsumpos : 0 < blockSum t := blockSum_pos ht
    have hmpos : 0 < palNum t := by
      rw [palNum_eq]
      positivity
    have hle : a (3 ^ n) ≤ palNum t :=
      a_le_of_witness (pow_ne_zero _ (by norm_num)) hdvd hr hmpos
    have hexp : 11 * t < 3 ^ (n - 2) := by
      rw [hn_eq]
      have hsub : 12 + k - 2 = 10 + k := by omega
      rw [hsub, pow_add]
      dsimp only [t]
      norm_num
    have hpow : palNum t < 10 ^ (3 ^ (n - 2)) - 1 := by
      have h₁ := palNum_lt_pow t
      have h₂ : 10 ^ (11 * t) < 10 ^ (3 ^ (n - 2)) :=
        Nat.pow_lt_pow_right (by norm_num) hexp
      apply Nat.lt_sub_of_add_lt
      exact (Nat.succ_le_iff.2 h₁).trans_lt h₂
    exact Nat.ne_of_lt (hle.trans_lt hpow)

/--
Conjecture A062567: It seems that only for n=2,3 & 4 we have a($3^n$) = $10^{3^{n-2}} - 1$.
(Formalized for $n \ge 2$ so that $n-2$ is a natural number exponent.)
-/
theorem oeis_62567_conjecture_0 (n : ℕ) :
  2 ≤ n → (a (3^n) = 10 ^ (3 ^ (n - 2)) - 1 ↔ n = 2 ∨ n = 3 ∨ n = 4) := by
  intro hn
  constructor
  · intro heq
    by_contra h
    have : 5 ≤ n := by omega
    exact conjecture_false_side this heq
  · intro h
    rcases h with rfl | rfl | rfl
    · norm_num [a_nine]
    · norm_num [a_twentySeven]
    · norm_num [a_eightyOne]
