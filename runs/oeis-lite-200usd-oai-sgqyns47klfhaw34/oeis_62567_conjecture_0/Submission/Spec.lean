import FormalConjectures.Util.ProblemImports

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

noncomputable section

lemma a_le_of {n k : ℕ} (hn : n ≠ 0) (hk : 0 < k) (hd : n ∣ reverse_nat (k * n)) :
    a n ≤ k * n := by
  unfold a
  simp [hn]
  let P : ℕ → Prop := fun k => k > 0 ∧ n ∣ reverse_nat (k * n)
  have hex : ∃ k, P k := ⟨k, hk, hd⟩
  change (if h_ex : ∃ k, P k then Nat.find h_ex * n else 0) ≤ k * n
  by_cases h_ex : ∃ k, P k
  · simp [h_ex]
    exact Nat.mul_le_mul_right n (Nat.find_min' h_ex (show P k from ⟨hk, hd⟩))
  · exact False.elim (h_ex hex)

lemma a_le_of_multiple {n x : ℕ} (hn : n ≠ 0) (hxpos : 0 < x)
    (hnx : n ∣ x) (hrx : n ∣ reverse_nat x) : a n ≤ x := by
  rcases hnx with ⟨k, rfl⟩
  have hk : 0 < k := by
    by_contra hk0
    have : k = 0 := Nat.eq_zero_of_not_pos hk0
    subst k
    simp at hxpos
  simpa [mul_comm] using a_le_of hn hk (by simpa [mul_comm] using hrx)

lemma a_eq_of_min {n kt : ℕ} (hn : n ≠ 0) (hkt : 0 < kt)
    (hd : n ∣ reverse_nat (kt * n))
    (hmin : ∀ k, 0 < k → k < kt → ¬ n ∣ reverse_nat (k * n)) :
    a n = kt * n := by
  unfold a
  simp [hn]
  let P : ℕ → Prop := fun k => k > 0 ∧ n ∣ reverse_nat (k * n)
  have hex : ∃ k, P k := ⟨kt, hkt, hd⟩
  change (if h_ex : ∃ k, P k then Nat.find h_ex * n else 0) = kt * n
  by_cases h_ex : ∃ k, P k
  · simp [h_ex]
    have hle : Nat.find h_ex ≤ kt := Nat.find_min' h_ex (show P kt from ⟨hkt, hd⟩)
    have hge : kt ≤ Nat.find h_ex := by
      by_contra hnot
      have hlt : Nat.find h_ex < kt := Nat.lt_of_not_ge hnot
      have hs := Nat.find_spec h_ex
      exact (hmin (Nat.find h_ex) hs.1 hlt) hs.2
    have heq : Nat.find h_ex = kt := Nat.le_antisymm hle hge
    simp [heq]
  · exact False.elim (h_ex hex)


def wsum : List ℕ → ℕ
  | [] => 0
  | _ :: tl => wsum tl + tl.sum

lemma wsum_append (l₁ l₂ : List ℕ) :
    wsum (l₁ ++ l₂) = wsum l₁ + wsum l₂ + l₁.length * l₂.sum := by
  induction l₁ with
  | nil => simp [wsum]
  | cons d tl ih =>
      simp [wsum, ih, List.sum_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.succ_mul]

lemma wsum_reverse_add (l : List ℕ) :
    (wsum l : ℤ) + (wsum l.reverse : ℤ) = ((l.length : ℤ) - 1) * (l.sum : ℤ) := by
  induction l with
  | nil => simp [wsum]
  | cons d tl ih =>
      rw [List.reverse_cons, wsum_append]
      simp [wsum]
      rw [show (List.map Nat.cast tl).sum = (tl.sum : ℤ) by simp]
      nlinarith

lemma ofDigits_zmodEq_sum_wsum81 (l : List ℕ) :
    (ofDigits 10 l : ℤ) ≡ (l.sum : ℤ) + 9 * (wsum l : ℤ) [ZMOD 81] := by
  induction l with
  | nil => rfl
  | cons d tl ih =>
      simp [ofDigits, wsum, List.sum_cons]
      have hmul := ih.mul_left 10
      have hright : (10 : ℤ) * ((tl.sum : ℤ) + 9 * (wsum tl : ℤ)) ≡
          (tl.sum : ℤ) + 9 * ((wsum tl : ℤ) + (tl.sum : ℤ)) [ZMOD 81] := by
        rw [Int.modEq_iff_dvd]
        use -(wsum tl : ℤ)
        ring
      simpa [mul_comm, mul_left_comm, mul_assoc, add_assoc, add_comm, add_left_comm] using
        (Int.ModEq.refl (d : ℤ)).add (hmul.trans hright)

lemma ofDigits_zmodEq_sum_wsum27 (l : List ℕ) :
    (ofDigits 10 l : ℤ) ≡ (l.sum : ℤ) + 9 * (wsum l : ℤ) [ZMOD 27] := by
  induction l with
  | nil => rfl
  | cons d tl ih =>
      simp [ofDigits, wsum, List.sum_cons]
      have hmul := ih.mul_left 10
      have hright : (10 : ℤ) * ((tl.sum : ℤ) + 9 * (wsum tl : ℤ)) ≡
          (tl.sum : ℤ) + 9 * ((wsum tl : ℤ) + (tl.sum : ℤ)) [ZMOD 27] := by
        rw [Int.modEq_iff_dvd]
        use -3 * (wsum tl : ℤ)
        ring
      simpa [mul_comm, mul_left_comm, mul_assoc, add_assoc, add_comm, add_left_comm] using
        (Int.ModEq.refl (d : ℤ)).add (hmul.trans hright)

lemma lin_dvd81_of_digits_dvd {l : List ℕ} (h : 81 ∣ ofDigits 10 l) :
    (81 : ℤ) ∣ (l.sum : ℤ) + 9 * (wsum l : ℤ) := by
  have hz : (81 : ℤ) ∣ (ofDigits 10 l : ℤ) := by exact_mod_cast h
  have hm := ofDigits_zmodEq_sum_wsum81 l
  rw [Int.modEq_iff_dvd] at hm
  have H := dvd_add hm hz
  convert H using 1
  ring

lemma lin_dvd27_of_digits_dvd {l : List ℕ} (h : 27 ∣ ofDigits 10 l) :
    (27 : ℤ) ∣ (l.sum : ℤ) + 9 * (wsum l : ℤ) := by
  have hz : (27 : ℤ) ∣ (ofDigits 10 l : ℤ) := by exact_mod_cast h
  have hm := ofDigits_zmodEq_sum_wsum27 l
  rw [Int.modEq_iff_dvd] at hm
  have H := dvd_add hm hz
  convert H using 1
  ring

lemma sum_dvd81_of_both {l : List ℕ} (hlen : l.length ≤ 9)
    (h1 : 81 ∣ ofDigits 10 l) (h2 : 81 ∣ ofDigits 10 l.reverse) :
    81 ∣ l.sum := by
  have A := lin_dvd81_of_digits_dvd (l:=l) h1
  have B := lin_dvd81_of_digits_dvd (l:=l.reverse) h2
  have C : (81 : ℤ) ∣ (2 * (l.sum : ℤ) + 9 * (((l.length : ℤ)-1) * (l.sum : ℤ))) := by
    have AB := dvd_add A B
    convert AB using 1
    rw [List.sum_reverse]
    have hr := wsum_reverse_add l
    ring_nf at hr ⊢
    linarith
  have C' : (81 : ℤ) ∣ ((9 * (l.length : ℤ) - 7) * (l.sum : ℤ)) := by
    convert C using 1
    ring
  have hcop : IsCoprime (81 : ℤ) (9 * (l.length : ℤ) - 7) := by
    interval_cases l.length <;> norm_num
  have Hint : (81 : ℤ) ∣ (l.sum : ℤ) := hcop.dvd_of_dvd_mul_left C'
  exact_mod_cast Hint

lemma sum_dvd27_of_both {l : List ℕ} (hlen : l.length ≤ 3)
    (h1 : 27 ∣ ofDigits 10 l) (h2 : 27 ∣ ofDigits 10 l.reverse) :
    27 ∣ l.sum := by
  have A := lin_dvd27_of_digits_dvd (l:=l) h1
  have B := lin_dvd27_of_digits_dvd (l:=l.reverse) h2
  have C : (27 : ℤ) ∣ (2 * (l.sum : ℤ) + 9 * (((l.length : ℤ)-1) * (l.sum : ℤ))) := by
    have AB := dvd_add A B
    convert AB using 1
    rw [List.sum_reverse]
    have hr := wsum_reverse_add l
    ring_nf at hr ⊢
    linarith
  have C' : (27 : ℤ) ∣ ((9 * (l.length : ℤ) - 7) * (l.sum : ℤ)) := by
    convert C using 1
    ring
  have hcop : IsCoprime (27 : ℤ) (9 * (l.length : ℤ) - 7) := by
    interval_cases l.length <;> norm_num
  have Hint : (27 : ℤ) ∣ (l.sum : ℤ) := hcop.dvd_of_dvd_mul_left C'
  exact_mod_cast Hint

lemma sum_digits_le (l : List ℕ) (hd : ∀ d ∈ l, d < 10) : l.sum ≤ 9 * l.length := by
  induction l with
  | nil => simp
  | cons d tl ih =>
      have hd0 : d ≤ 9 := Nat.le_of_lt_succ (hd d (by simp))
      have iht : tl.sum ≤ 9 * tl.length := ih (by intro x hx; exact hd x (by simp [hx]))
      simp [List.sum_cons]
      nlinarith

lemma eq_replicate_9_of_sum_max {l : List ℕ}
    (hd : ∀ d ∈ l, d ≤ 9) (hs : l.sum = 9 * l.length) :
    l = List.replicate l.length 9 := by
  induction l with
  | nil => simp
  | cons d tl ih =>
      have hd_d : d ≤ 9 := hd d (by simp)
      have hd_t : ∀ x ∈ tl, x ≤ 9 := by intro x hx; exact hd x (by simp [hx])
      have hle_t := sum_digits_le tl (by intro x hx; exact Nat.lt_succ_of_le (hd_t x hx))
      simp [List.sum_cons] at hs
      have hd_eq : d = 9 := by nlinarith
      have htl_sum : tl.sum = 9 * tl.length := by nlinarith
      rw [hd_eq, ih hd_t htl_sum]
      simp [List.replicate_succ]

lemma digits_sum_eq_mod_all {M L : ℕ} {l : List ℕ} (hML : M = 9 * L)
    (hlen : l.length ≤ L) (hd : ∀ d ∈ l, d < 10) (hdiv : M ∣ l.sum) (hpos : 0 < l.sum) :
    l.sum = M := by
  subst M
  have hle : l.sum ≤ 9 * L := by
    have := sum_digits_le l hd
    nlinarith
  rcases hdiv with ⟨c, hc⟩
  have hcpos : 0 < c := by
    by_contra h
    have : c = 0 := Nat.eq_zero_of_not_pos h
    subst c
    nlinarith
  have hc_le : c ≤ 1 := by nlinarith
  have hc_eq : c = 1 := by omega
  subst c
  simpa using hc

lemma all_digits_9_of_sum {L : ℕ} {l : List ℕ} (hlen : l.length ≤ L)
    (hd : ∀ d ∈ l, d < 10) (hsum : l.sum = 9 * L) : l = List.replicate L 9 := by
  have hlenL : l.length = L := by
    have hsumle := sum_digits_le l hd
    nlinarith
  have hsmax : l.sum = 9 * l.length := by rw [hsum, hlenL]
  have hdle : ∀ d ∈ l, d ≤ 9 := by intro d h; exact Nat.le_of_lt_succ (hd d h)
  simpa [hlenL] using eq_replicate_9_of_sum_max hdle hsmax

lemma no_small81 {x : ℕ} (hxpos : 0 < x) (hxlt : x < 999999999)
    (h1 : 81 ∣ x) (h2 : 81 ∣ reverse_nat x) : False := by
  let l := digits 10 x
  have hlen : l.length ≤ 9 := by
    have := (digits_length_le_iff (b:=10) (k:=9) (by norm_num) x).2 (by norm_num at hxlt ⊢; omega)
    simpa [l] using this
  have hd : ∀ d ∈ l, d < 10 := by intro d hdmem; exact digits_lt_base (by norm_num) hdmem
  have h1l : 81 ∣ ofDigits 10 l := by simpa [l, ofDigits_digits] using h1
  have h2l : 81 ∣ ofDigits 10 l.reverse := by simpa [reverse_nat, l] using h2
  have hsdiv : 81 ∣ l.sum := sum_dvd81_of_both hlen h1l h2l
  have hsumpos : 0 < l.sum := by
    have hne : l ≠ [] := by simpa [l] using (digits_ne_nil_iff_ne_zero.mpr hxpos.ne')
    have hlastne := Nat.getLast_digit_ne_zero 10 (m := x) hxpos.ne'
    have hlastne' : l.getLast hne ≠ 0 := by simpa [l] using hlastne
    have hmem : l.getLast hne ∈ l := List.getLast_mem hne
    have hposdigit : 0 < l.getLast hne := Nat.pos_of_ne_zero hlastne'
    exact lt_of_lt_of_le hposdigit (List.single_le_sum (by intro y hy; exact Nat.zero_le y) _ hmem)
  have hsum81 : l.sum = 81 := digits_sum_eq_mod_all (M:=81) (L:=9) (by norm_num) hlen hd hsdiv hsumpos
  have hl : l = List.replicate 9 9 := all_digits_9_of_sum hlen hd (by simpa using hsum81)
  have hx : x = 999999999 := by
    calc
      x = ofDigits 10 l := by simp [l, ofDigits_digits]
      _ = ofDigits 10 (List.replicate 9 9) := by rw [hl]
      _ = 999999999 := by norm_num [List.replicate, ofDigits]
  omega

lemma no_small27 {x : ℕ} (hxpos : 0 < x) (hxlt : x < 999)
    (h1 : 27 ∣ x) (h2 : 27 ∣ reverse_nat x) : False := by
  let l := digits 10 x
  have hlen : l.length ≤ 3 := by
    have := (digits_length_le_iff (b:=10) (k:=3) (by norm_num) x).2 (by norm_num at hxlt ⊢; omega)
    simpa [l] using this
  have hd : ∀ d ∈ l, d < 10 := by intro d hdmem; exact digits_lt_base (by norm_num) hdmem
  have h1l : 27 ∣ ofDigits 10 l := by simpa [l, ofDigits_digits] using h1
  have h2l : 27 ∣ ofDigits 10 l.reverse := by simpa [reverse_nat, l] using h2
  have hsdiv : 27 ∣ l.sum := sum_dvd27_of_both hlen h1l h2l
  have hsumpos : 0 < l.sum := by
    have hne : l ≠ [] := by simpa [l] using (digits_ne_nil_iff_ne_zero.mpr hxpos.ne')
    have hlastne := Nat.getLast_digit_ne_zero 10 (m := x) hxpos.ne'
    have hlastne' : l.getLast hne ≠ 0 := by simpa [l] using hlastne
    have hmem : l.getLast hne ∈ l := List.getLast_mem hne
    have hposdigit : 0 < l.getLast hne := Nat.pos_of_ne_zero hlastne'
    exact lt_of_lt_of_le hposdigit (List.single_le_sum (by intro y hy; exact Nat.zero_le y) _ hmem)
  have hsum27 : l.sum = 27 := digits_sum_eq_mod_all (M:=27) (L:=3) (by norm_num) hlen hd hsdiv hsumpos
  have hl : l = List.replicate 3 9 := all_digits_9_of_sum hlen hd (by simpa using hsum27)
  have hx : x = 999 := by
    calc
      x = ofDigits 10 l := by simp [l, ofDigits_digits]
      _ = ofDigits 10 (List.replicate 3 9) := by rw [hl]
      _ = 999 := by norm_num [List.replicate, ofDigits]
  omega

lemma rev_rep9 {m : ℕ} (hm : m ≠ 0) : reverse_nat (ofDigits 10 (List.replicate m 9)) = ofDigits 10 (List.replicate m 9) := by
  unfold reverse_nat
  rw [digits_ofDigits]
  · simp
  · norm_num
  · intro d hd
    simp at hd
    rcases hd with ⟨_, rfl⟩
    norm_num
  · intro h
    have hlast : (List.replicate m 9).getLast h = 9 := by rw [List.getLast_replicate]
    omega

lemma rev9 : reverse_nat 9 = 9 := by
  convert rev_rep9 (m:=1) (by norm_num) <;> norm_num [List.replicate, ofDigits]
lemma rev999 : reverse_nat 999 = 999 := by
  convert rev_rep9 (m:=3) (by norm_num) <;> norm_num [List.replicate, ofDigits]
lemma rev999999999 : reverse_nat 999999999 = 999999999 := by
  convert rev_rep9 (m:=9) (by norm_num) <;> norm_num [List.replicate, ofDigits]

lemma min27 : ∀ k, 0 < k → k < 37 → ¬ (27 ∣ reverse_nat (k * 27)) := by
  intro k hk0 hklt hd
  exact no_small27 (by positivity) (by nlinarith) (by exact dvd_mul_left 27 k) hd

lemma min81 : ∀ k, 0 < k → k < 12345679 → ¬ (81 ∣ reverse_nat (k * 81)) := by
  intro k hk0 hklt hd
  exact no_small81 (by positivity) (by nlinarith) (by exact dvd_mul_left 81 k) hd

lemma a9 : a 9 = 9 := by
  simpa using (a_eq_of_min (n := 9) (kt := 1) (by norm_num) (by norm_num)
    (by rw [rev9]) (by intro k hk hlt; omega))

lemma a27 : a 27 = 999 := by
  simpa using (a_eq_of_min (n := 27) (kt := 37) (by norm_num) (by norm_num)
    (by rw [show 37 * 27 = 999 by norm_num, rev999]; norm_num) min27)

lemma a81 : a 81 = 999999999 := by
  simpa using (a_eq_of_min (n := 81) (kt := 12345679) (by norm_num) (by norm_num)
    (by rw [show 12345679 * 81 = 999999999 by norm_num, rev999999999]; norm_num) min81)

open Finset

def block : List ℕ := [7,8,9,9,9,9,9,9,8,4]
def rblock : List ℕ := block.reverse

def blocks (T : ℕ) : List ℕ := (List.replicate T block).flatten
def rblocks (T : ℕ) : List ℕ := (List.replicate T rblock).flatten

def geom (B T : ℕ) : ℕ := ∑ i ∈ Finset.range T, B^i

lemma block_len : block.length = 10 := by norm_num [block]
lemma rblock_len : rblock.length = 10 := by norm_num [rblock, block]
lemma block_val : ofDigits 10 block = 4899999987 := by norm_num [block, ofDigits]
lemma rblock_val : ofDigits 10 rblock = 7899999984 := by norm_num [rblock, block, ofDigits]

lemma blocks_len (T : ℕ) : (blocks T).length = T * 10 := by
  simp [blocks, block_len]

lemma ofDigits_blocks (T : ℕ) : ofDigits 10 (blocks T) = 4899999987 * geom (10^10) T := by
  induction T with
  | zero => simp [blocks, geom]
  | succ T ih =>
      rw [blocks, List.replicate_succ, List.flatten_cons, ofDigits_append]
      have ih' : ofDigits 10 (List.replicate T block).flatten = 4899999987 * geom (10 ^ 10) T := by
        simpa [blocks] using ih
      rw [block_len, block_val, ih']
      simp [geom, Finset.sum_range_succ', pow_succ, Nat.mul_add, Finset.mul_sum,
        mul_comm, mul_left_comm, add_comm]

lemma ofDigits_rblocks (T : ℕ) : ofDigits 10 (rblocks T) = 7899999984 * geom (10^10) T := by
  induction T with
  | zero => simp [rblocks, geom]
  | succ T ih =>
      rw [rblocks, List.replicate_succ, List.flatten_cons, ofDigits_append]
      have ih' : ofDigits 10 (List.replicate T rblock).flatten = 7899999984 * geom (10 ^ 10) T := by
        simpa [rblocks] using ih
      rw [rblock_len, rblock_val, ih']
      simp [geom, Finset.sum_range_succ', pow_succ, Nat.mul_add, Finset.mul_sum,
        mul_comm, mul_left_comm, add_comm]

lemma blocks_rev (T : ℕ) : (blocks T).reverse = rblocks T := by
  unfold blocks rblocks rblock
  simp [List.reverse_flatten]

lemma all_digits_blocks (T : ℕ) : ∀ l ∈ blocks T, l < 10 := by
  intro l hl
  unfold blocks at hl
  simp only [List.mem_flatten, List.mem_replicate] at hl
  rcases hl with ⟨a, ⟨hT, rfl⟩, hmem⟩
  simp [block] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

lemma last_blocks_ne_zero {T : ℕ} (hT : T ≠ 0) : ∀ h : blocks T ≠ [], (blocks T).getLast h ≠ 0 := by
  intro h
  have hlast? : (blocks T).getLast? = some 4 := by
    unfold blocks block
    simpa using (List.getLast?_flatten_replicate (n := T) hT [7,8,9,9,9,9,9,9,8,4])
  have hget : some ((blocks T).getLast h) = (blocks T).getLast? := by
    exact (List.getLast?_eq_getLast h).symm
  rw [← hget] at hlast?
  injection hlast? with hh
  omega

lemma reverse_ofDigits_blocks {T : ℕ} (hT : T ≠ 0) :
    reverse_nat (ofDigits 10 (blocks T)) = ofDigits 10 (rblocks T) := by
  unfold reverse_nat
  rw [digits_ofDigits]
  · rw [blocks_rev]
  · norm_num
  · exact all_digits_blocks T
  · exact last_blocks_ne_zero hT

lemma geom_mul_10 (T : ℕ) : (10^10 - 1) * geom (10^10) T = (10^10)^T - 1 := by
  apply Int.ofNat.inj
  have hZ := mul_geom_sum ((10 : ℤ)^10) T
  unfold geom
  norm_num at hZ ⊢
  exact hZ

lemma geom_pos (B : ℕ) (hB : 0 < B) {T : ℕ} (hT : T ≠ 0) : 0 < geom B T := by
  unfold geom
  exact Finset.sum_pos (fun i hi => pow_pos hB i) (by simpa using hT)

lemma geom_dvd_pow3 (t : ℕ) : 3^t ∣ geom (10^10) (3^t) := by
  let B : ℕ := 10^10
  let T : ℕ := 3^t
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hT0 : T ≠ 0 := by simp [T]
  have hdivBT : B - 1 ∣ B^T - 1 := by
    refine ⟨geom B T, ?_⟩
    simpa [B, mul_comm] using (geom_mul_10 T).symm
  have hvalBT : padicValNat 3 (B^T - 1) = padicValNat 3 (B - 1) + padicValNat 3 T := by
    have h := padicValNat.pow_sub_pow (p := 3) (x := B) (y := 1) (by decide : Odd 3)
      (by norm_num [B] : 1 < B) (by norm_num [B] : 3 ∣ B - 1)
      (by norm_num [B] : ¬ 3 ∣ B) hT0
    simpa using h
  have hvalT : padicValNat 3 T = t := by simp [T]
  have hgeom0 : geom B T ≠ 0 := by exact Nat.ne_of_gt (geom_pos B (by norm_num [B]) hT0)
  have hvalGeom : padicValNat 3 (geom B T) = t := by
    have hdivval := padicValNat.div_of_dvd (p := 3) hdivBT
    have hquot : (B^T - 1) / (B - 1) = geom B T := by
      apply Nat.div_eq_of_eq_mul_left
      · norm_num [B]
      · simpa [B, mul_comm] using (geom_mul_10 T).symm
    rw [hquot] at hdivval
    rw [hvalBT, hvalT] at hdivval
    simpa [Nat.add_sub_cancel_left] using hdivval
  have htval : t ≤ padicValNat 3 (geom B T) := by rw [hvalGeom]
  exact (padicValNat_dvd_iff_le hgeom0).2 htval

lemma pow3_mul_geom_dvd (n : ℕ) (hn : 5 ≤ n) :
    3^n ∣ 4899999987 * geom (10^10) (3^(n-5)) := by
  have hbase : 3^5 ∣ 4899999987 := by norm_num
  have hgeom : 3^(n-5) ∣ geom (10^10) (3^(n-5)) := geom_dvd_pow3 (n-5)
  have h := mul_dvd_mul hbase hgeom
  have hnadd : 5 + (n - 5) = n := by omega
  convert h using 1
  rw [← pow_add, hnadd]

lemma pow3_mul_rgeom_dvd (n : ℕ) (hn : 5 ≤ n) :
    3^n ∣ 7899999984 * geom (10^10) (3^(n-5)) := by
  have hbase : 3^5 ∣ 7899999984 := by norm_num
  have hgeom : 3^(n-5) ∣ geom (10^10) (3^(n-5)) := geom_dvd_pow3 (n-5)
  have h := mul_dvd_mul hbase hgeom
  have hnadd : 5 + (n - 5) = n := by omega
  convert h using 1
  rw [← pow_add, hnadd]

lemma tail_witness_lt (n : ℕ) (hn : 5 ≤ n) :
    ofDigits 10 (blocks (3^(n-5))) < 10 ^ (3 ^ (n - 2)) - 1 := by
  let T := 3^(n-5)
  have hTpos : 0 < T := by simp [T]
  have hdigits := ofDigits_lt_base_pow_length (b := 10) (l := blocks T) (by norm_num) (all_digits_blocks T)
  have hlen : (blocks T).length = T * 10 := blocks_len T
  have hltpow : ofDigits 10 (blocks T) < 10 ^ (T * 10) := by simpa [hlen] using hdigits
  have hpoweq : 3 ^ (n - 2) = T * 27 := by
    have hnsub : n - 2 = (n - 5) + 3 := by omega
    simp [T, hnsub, pow_add, mul_comm, mul_left_comm, mul_assoc]
  have hexp : T * 10 + 1 ≤ 3 ^ (n - 2) := by
    rw [hpoweq]
    nlinarith [hTpos]
  have hpowle : 10 ^ (T * 10 + 1) ≤ 10 ^ (3 ^ (n - 2)) :=
    Nat.pow_le_pow_right (by norm_num) hexp
  have hgap : 10 ^ (T * 10) + 1 < 10 ^ (T * 10 + 1) := by
    rw [pow_succ]
    have hp : 0 < 10 ^ (T * 10) := pow_pos (by norm_num) _
    nlinarith
  have hsum : ofDigits 10 (blocks T) + 1 < 10 ^ (3 ^ (n - 2)) := by
    nlinarith
  exact (Nat.lt_sub_iff_add_lt).2 hsum

lemma tail_ne (n : ℕ) (hn : 5 ≤ n) :
    a (3^n) ≠ 10 ^ (3 ^ (n - 2)) - 1 := by
  let T := 3^(n-5)
  let x := ofDigits 10 (blocks T)
  have hT0 : T ≠ 0 := by simp [T]
  have hxpos : 0 < x := by
    change 0 < ofDigits 10 (blocks T)
    rw [ofDigits_blocks]
    exact mul_pos (by norm_num) (geom_pos (10^10) (by norm_num) hT0)
  have hxdvd : 3^n ∣ x := by
    change 3^n ∣ ofDigits 10 (blocks T)
    rw [ofDigits_blocks]
    exact pow3_mul_geom_dvd n hn
  have hrdvd : 3^n ∣ reverse_nat x := by
    change 3^n ∣ reverse_nat (ofDigits 10 (blocks T))
    rw [reverse_ofDigits_blocks hT0, ofDigits_rblocks]
    exact pow3_mul_rgeom_dvd n hn
  have hN0 : 3^n ≠ 0 := by positivity
  have hale : a (3^n) ≤ x := a_le_of_multiple hN0 hxpos hxdvd hrdvd
  have hxlt : x < 10 ^ (3 ^ (n - 2)) - 1 := by
    simpa [x, T] using tail_witness_lt n hn
  intro heq
  rw [heq] at hale
  omega

/--
Conjecture A062567: It seems that only for n=2,3 & 4 we have a($3^n$) = $10^{3^{n-2}} - 1$.
(Formalized for $n \ge 2$ so that $n-2$ is a natural number exponent.)
-/
theorem oeis_62567_conjecture_0 (n : ℕ) :
  2 ≤ n → (a (3^n) = 10 ^ (3 ^ (n - 2)) - 1 ↔ n = 2 ∨ n = 3 ∨ n = 4) :=
by
  intro hn2
  constructor
  · intro h
    by_cases h2 : n = 2
    · exact Or.inl h2
    by_cases h3 : n = 3
    · exact Or.inr (Or.inl h3)
    by_cases h4 : n = 4
    · exact Or.inr (Or.inr h4)
    have hn5 : 5 ≤ n := by omega
    exact False.elim ((tail_ne n hn5) h)
  · intro h
    rcases h with rfl | rfl | rfl
    · norm_num [a9]
    · norm_num [a27]
    · norm_num [a81]
