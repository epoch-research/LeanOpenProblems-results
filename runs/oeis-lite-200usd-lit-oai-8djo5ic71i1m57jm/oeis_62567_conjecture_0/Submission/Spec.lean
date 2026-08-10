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

/--
Conjecture A062567: It seems that only for n=2,3 & 4 we have a($3^n$) = $10^{3^{n-2}} - 1$.
(Formalized for $n \ge 2$ so that $n-2$ is a natural number exponent.)
-/

private def oeisP (m k : ℕ) : Prop := k > 0 ∧ m ∣ reverse_nat (k * m)

private instance (m k : ℕ) : Decidable (oeisP m k) := by
  unfold oeisP
  infer_instance

private lemma a_le_of_P {m k : ℕ} (hm : m ≠ 0) (hk : oeisP m k) : a m ≤ k * m := by
  unfold a
  simp [hm]
  let Q : ℕ → Prop := fun j => j > 0 ∧ m ∣ reverse_nat (j * m)
  have h_ex : ∃ j, Q j := ⟨k, hk⟩
  rw [dif_pos h_ex]
  exact Nat.mul_le_mul_right m (Nat.find_min' h_ex hk)

private lemma a_eq_of_min {m k : ℕ} (hm : m ≠ 0) (hk : oeisP m k)
    (hmin : ∀ j < k, ¬ oeisP m j) : a m = k * m := by
  unfold a
  simp [hm]
  let Q : ℕ → Prop := fun j => j > 0 ∧ m ∣ reverse_nat (j * m)
  have h_ex : ∃ j, Q j := ⟨k, hk⟩
  rw [dif_pos h_ex]
  congr 1
  exact (Nat.find_eq_iff h_ex).2 ⟨hk, hmin⟩

private def checkRange (m stop i : ℕ) : Bool :=
  if i < stop then
    if decide (oeisP m i) then false else checkRange m stop (i+1)
  else true
termination_by stop - i
decreasing_by omega

private lemma checkRange_sound (m stop i : ℕ) (hchk : checkRange m stop i = true) :
    ∀ k, i ≤ k → k < stop → ¬ oeisP m k := by
  rw [checkRange] at hchk
  split at hchk
  · rename_i hi
    split at hchk
    · simp at hchk
    · rename_i hp
      intro k hik hks hP
      by_cases hki : k = i
      · subst k
        have hpf : decide (oeisP m i) = false := Bool.eq_false_iff.mpr hp
        exact (of_decide_eq_false hpf) hP
      · have hik' : i + 1 ≤ k := by omega
        exact checkRange_sound m stop (i+1) hchk k hik' hks hP
  · rename_i hi
    intro k hik hks hP
    omega
termination_by stop - i
decreasing_by omega

private def wsum : List ℕ → ℕ
| [] => 0
| _ :: tl => wsum tl + tl.sum

private lemma wsum_append (A B : List ℕ) : wsum (A ++ B) = wsum A + wsum B + A.length * B.sum := by
  induction A with
  | nil => simp [wsum]
  | cons a A ih =>
      simp [wsum, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      ring

private lemma wsum_reverse_add (L : List ℕ) : wsum L + wsum L.reverse = (L.length - 1) * L.sum := by
  induction L with
  | nil => simp [wsum]
  | cons a tl ih =>
      cases tl with
      | nil => simp [wsum]
      | cons b tl =>
          have ih' := ih
          simp [wsum, wsum_append] at ih' ⊢
          ring_nf at ih' ⊢
          omega

private lemma ofDigits_zmod_sum_wsum (L : List ℕ) :
    (Nat.ofDigits (10 : ZMod 81) L) = (L.sum : ZMod 81) + 9 * (wsum L : ZMod 81) := by
  induction L with
  | nil => simp [Nat.ofDigits, wsum]
  | cons d tl ih =>
      rw [Nat.ofDigits]
      simp [List.sum_cons, wsum, ih]
      ring_nf
      have h : (90 : ZMod 81) = (9 : ZMod 81) := by decide
      rw [h]


private lemma list_sum_le_nine_mul_length {L : List ℕ} (h : ∀ d ∈ L, d ≤ 9) : L.sum ≤ 9 * L.length := by
  induction L with
  | nil => simp
  | cons a tl ih =>
      have ha : a ≤ 9 := h a (by simp)
      have htl : ∀ d ∈ tl, d ≤ 9 := by intro d hd; exact h d (by simp [hd])
      have := ih htl
      simp [List.sum_cons]
      nlinarith

private lemma list_sum_pos_of_mem_pos {L : List ℕ} {a : ℕ} (ha : 0 < a) (hm : a ∈ L) : 0 < L.sum := by
  induction L with
  | nil => simp at hm
  | cons b tl ih =>
      simp at hm
      rcases hm with rfl | hm
      · simp [ha]
      · have := ih hm
        simp [List.sum_cons]
        omega

private lemma list_eq_replicate_of_sum_eq_nine_mul_length {L : List ℕ}
    (h : ∀ d ∈ L, d ≤ 9) (hsum : L.sum = 9 * L.length) :
    L = List.replicate L.length 9 := by
  induction L with
  | nil => simp
  | cons a tl ih =>
      have ha : a ≤ 9 := h a (by simp)
      have htl : ∀ d ∈ tl, d ≤ 9 := by intro d hd; exact h d (by simp [hd])
      have hsumtl_le := list_sum_le_nine_mul_length htl
      have ha9 : a = 9 := by
        simp [List.sum_cons] at hsum
        nlinarith
      have hsumtl : tl.sum = 9 * tl.length := by
        simp [List.sum_cons, ha9] at hsum
        nlinarith
      have ihEq := ih htl hsumtl
      rw [ha9, ihEq]
      simp [List.replicate_succ]

private lemma coeff_dvd (l S : ℕ) (hl1 : 1 ≤ l) (hl9 : l ≤ 9)
    (h : (((2 + 9*(l-1)) * S : ℕ) : ZMod 81) = 0) : 81 ∣ S := by
  have hdvd : 81 ∣ (2 + 9*(l-1)) * S := (ZMod.natCast_eq_zero_iff _ _).1 h
  have hc : Nat.Coprime 81 (2 + 9*(l-1)) := by
    interval_cases l <;> norm_num
  exact (hc.dvd_mul_left).1 hdvd

private lemma sum_digits_dvd81_of_both (x : ℕ) (hxpos : 0 < x) (hxlt : x < 10^9) (hx81 : 81 ∣ x)
    (hr81 : 81 ∣ Nat.ofDigits 10 (Nat.digits 10 x).reverse) :
    81 ∣ (Nat.digits 10 x).sum := by
  let L := Nat.digits 10 x
  let S := L.sum
  let T := wsum L
  let TR := wsum L.reverse
  have hx0 : (x : ZMod 81) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hx81
  have hr0 : ((Nat.ofDigits 10 L.reverse : ℕ) : ZMod 81) = 0 := by
    dsimp [L]
    exact (ZMod.natCast_eq_zero_iff _ _).2 hr81
  have hxval : Nat.ofDigits 10 L = x := Nat.ofDigits_digits 10 x
  have e1 : (S : ZMod 81) + 9 * (T : ZMod 81) = 0 := by
    have hz := ofDigits_zmod_sum_wsum L
    have this : ((Nat.ofDigits (10 : ℕ) L : ℕ) : ZMod 81) = (L.sum : ZMod 81) + 9 * (wsum L : ZMod 81) :=
      (Nat.coe_ofDigits (ZMod 81) 10 L).trans hz
    have hxvalZ : ((Nat.ofDigits 10 L : ℕ) : ZMod 81) = (x : ZMod 81) := congrArg (fun y : ℕ => (y : ZMod 81)) hxval
    rw [hxvalZ, hx0] at this
    exact this.symm
  have e2 : (S : ZMod 81) + 9 * (TR : ZMod 81) = 0 := by
    have hz := ofDigits_zmod_sum_wsum L.reverse
    have this : ((Nat.ofDigits (10 : ℕ) L.reverse : ℕ) : ZMod 81) = (L.reverse.sum : ZMod 81) + 9 * (wsum L.reverse : ZMod 81) :=
      (Nat.coe_ofDigits (ZMod 81) 10 L.reverse).trans hz
    simp only [List.sum_reverse] at this
    rw [hr0] at this
    dsimp [S, TR]
    exact this.symm
  have hsum : ((2 + 9 * (L.length - 1)) * S : ℕ) = S + S + 9 * (T + TR) := by
    have hw := wsum_reverse_add L
    dsimp [S, T, TR]
    rw [hw]
    ring
  have hcast : (((2 + 9 * (L.length - 1)) * S : ℕ) : ZMod 81) = 0 := by
    rw [hsum]
    push_cast
    change (S : ZMod 81) + (S : ZMod 81) + 9 * ((T : ZMod 81) + (TR : ZMod 81)) = 0
    have hadd : ((S : ZMod 81) + 9 * (T : ZMod 81)) + ((S : ZMod 81) + 9 * (TR : ZMod 81)) = 0 := by
      rw [e1, e2]
      simp
    convert hadd using 1
    ring
  have hlen1 : 1 ≤ L.length := by
    have hne : L ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
    have hpos : 0 < L.length := by
      cases hL : L with
      | nil => exfalso; exact hne hL
      | cons a tl => simp
    exact hpos
  have hlen9 : L.length ≤ 9 := by
    exact (Nat.digits_length_le_iff (by norm_num : 1 < 10) x).2 hxlt
  exact coeff_dvd L.length S hlen1 hlen9 hcast

private lemma no_81_both_lt_repunit (x : ℕ) (hxpos : 0 < x) (hxlt : x < 999999999)
    (hx81 : 81 ∣ x) (hr81 : 81 ∣ Nat.ofDigits 10 (Nat.digits 10 x).reverse) : False := by
  let L := Nat.digits 10 x
  let S := L.sum
  have hxlt9 : x < 10^9 := by norm_num at hxlt ⊢; omega
  have hSdvd : 81 ∣ S := by
    dsimp [S, L]
    exact sum_digits_dvd81_of_both x hxpos hxlt9 hx81 hr81
  have hDigitLe : ∀ d ∈ L, d ≤ 9 := by
    intro d hd
    exact Nat.le_of_lt_succ (Nat.digits_lt_base (by norm_num : 1 < 10) hd)
  have hlen9 : L.length ≤ 9 := by
    dsimp [L]
    exact (Nat.digits_length_le_iff (by norm_num : 1 < 10) x).2 hxlt9
  have hSle : S ≤ 81 := by
    have := list_sum_le_nine_mul_length hDigitLe
    dsimp [S]
    nlinarith
  have hne : L ≠ [] := by
    dsimp [L]
    exact Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  have hlastne : L.getLast hne ≠ 0 := by
    dsimp [L]
    exact Nat.getLast_digit_ne_zero 10 (by omega)
  have hSpos : 0 < S := by
    dsimp [S]
    exact list_sum_pos_of_mem_pos (Nat.pos_of_ne_zero hlastne) (List.getLast_mem hne)
  have hS81 : S = 81 := by
    rcases hSdvd with ⟨c, hc⟩
    omega
  have hlen : L.length = 9 := by
    have hSle_len := list_sum_le_nine_mul_length hDigitLe
    dsimp [S] at hS81
    omega
  have hsummax : L.sum = 9 * L.length := by
    dsimp [S] at hS81
    rw [hS81, hlen]
  have hLrep : L = List.replicate L.length 9 := list_eq_replicate_of_sum_eq_nine_mul_length hDigitLe hsummax
  have hxval : Nat.ofDigits 10 L = x := by
    dsimp [L]
    exact Nat.ofDigits_digits 10 x
  have hxEq : x = 999999999 := by
    rw [← hxval, hLrep, hlen]
    norm_num [Nat.ofDigits, List.replicate]
  omega

private lemma noP_before_9 : ∀ j < 1, ¬ oeisP 9 j := by
  intro j hj h
  interval_cases j
  norm_num [oeisP] at h
private lemma noP_before_27 : ∀ j < 37, ¬ oeisP 27 j := by
  intro j hj h
  interval_cases j <;> norm_num [oeisP, reverse_nat, Nat.ofDigits] at h

private lemma noP_before_81 : ∀ j < 12345679, ¬ oeisP 81 j := by
  intro j hj hP
  have hxpos : 0 < j * 81 := Nat.mul_pos hP.1 (by norm_num)
  have hxlt : j * 81 < 999999999 := by nlinarith [hj]
  have hx81 : 81 ∣ j * 81 := by exact dvd_mul_left 81 j
  exact no_81_both_lt_repunit (j * 81) hxpos hxlt hx81 hP.2

private lemma a_9 : a 9 = 9 := by
  exact a_eq_of_min (by norm_num [oeisP, reverse_nat, Nat.ofDigits]) (by norm_num [oeisP, reverse_nat, Nat.ofDigits]) noP_before_9

private lemma a_27 : a 27 = 999 := by
  simpa using (a_eq_of_min (m:=27) (k:=37) (by norm_num [oeisP, reverse_nat, Nat.ofDigits]) (by norm_num [oeisP, reverse_nat, Nat.ofDigits]) noP_before_27)

private lemma a_81 : a 81 = 999999999 := by
  simpa using (a_eq_of_min (m:=81) (k:=12345679) (by norm_num [oeisP, reverse_nat, Nat.ofDigits]) (by norm_num [oeisP, reverse_nat, Nat.ofDigits]) noP_before_81)

private def block : List ℕ := [6,8,8,9,9,1,9,9,8,8,6]
private def blocks : ℕ → List ℕ
| 0 => []
| t+1 => block ++ blocks t
private def pal (t : ℕ) : ℕ := Nat.ofDigits 10 (blocks t)
private def geom (b : ℕ) : ℕ → ℕ
| 0 => 0
| t+1 => 1 + b * geom b t

private lemma block_eval : Nat.ofDigits 10 block = 68899199886 := by norm_num [block, Nat.ofDigits]
private lemma block_len : block.length = 11 := by norm_num [block]
private lemma block_rev : block.reverse = block := by norm_num [block]
private lemma block_digits_lt : ∀ d ∈ block, d < 10 := by norm_num [block]
private lemma block_pos : ∀ d ∈ block, d ≠ 0 := by norm_num [block]

private lemma blocks_append_block (t) : blocks t ++ block = block ++ blocks t := by
  induction t with
  | zero => simp [blocks]
  | succ t ih => simp [blocks, List.append_assoc, ih]

private lemma blocks_rev (t) : (blocks t).reverse = blocks t := by
  induction t with
  | zero => simp [blocks]
  | succ t ih => simp [blocks, List.reverse_append, ih, block_rev, blocks_append_block]

private lemma blocks_digits_lt (t) : ∀ d ∈ blocks t, d < 10 := by
  induction t with
  | zero => simp [blocks]
  | succ t ih =>
      intro d hd
      simp [blocks] at hd
      rcases hd with hd | hd
      · exact block_digits_lt d hd
      · exact ih d hd

private lemma blocks_pos (t) : ∀ d ∈ blocks t, d ≠ 0 := by
  induction t with
  | zero => simp [blocks]
  | succ t ih =>
      intro d hd
      simp [blocks] at hd
      rcases hd with hd | hd
      · exact block_pos d hd
      · exact ih d hd

private lemma blocks_ne_nil {t : ℕ} (ht : 0 < t) : blocks t ≠ [] := by
  cases t with
  | zero => omega
  | succ t => simp [blocks, block]

private lemma blocks_last_ne {t : ℕ} (h : blocks t ≠ []) : (blocks t).getLast h ≠ 0 := by
  exact blocks_pos t ((blocks t).getLast h) (List.getLast_mem h)

private lemma reverse_pal (t : ℕ) : reverse_nat (pal t) = pal t := by
  unfold reverse_nat pal
  have hdig : Nat.digits 10 (Nat.ofDigits 10 (blocks t)) = blocks t := by
    apply Nat.digits_ofDigits
    · norm_num
    · exact blocks_digits_lt t
    · intro h
      exact blocks_last_ne h
  rw [hdig, blocks_rev]

private lemma pal_eval (t : ℕ) : pal t = 68899199886 * geom (10^11) t := by
  induction t with
  | zero => simp [pal, blocks, geom]
  | succ t ih =>
      unfold pal at ih
      simp [pal, blocks, Nat.ofDigits_append, block_eval, block_len, ih, geom]
      ring

private lemma geom_add (b m n : ℕ) : geom b (m+n) = geom b m + b^m * geom b n := by
  induction m with
  | zero => simp [geom]
  | succ m ih =>
      simp [geom, Nat.succ_add, ih, pow_succ]
      ring

private lemma geom_three (b m : ℕ) : geom b (m*3) = geom b m * (1 + b^m + b^(2*m)) := by
  rw [show m*3 = m + (m + m) by ring]
  rw [geom_add, geom_add]
  ring

private lemma factor3 (m : ℕ) : 3 ∣ (1 + (10^11)^m + (10^11)^(2*m)) := by
  rw [← Nat.modEq_zero_iff_dvd]
  have h : (10^11 : ℕ) ≡ 1 [MOD 3] := by norm_num [oeisP, reverse_nat, Nat.ofDigits]
  have h1 : (10^11 : ℕ)^m ≡ 1^m [MOD 3] := h.pow m
  have h2 : (10^11 : ℕ)^(2*m) ≡ 1^(2*m) [MOD 3] := h.pow (2*m)
  have hsum : 1 + (10^11)^m + (10^11)^(2*m) ≡ 1 + 1^m + 1^(2*m) [MOD 3] := by
    exact (Nat.ModEq.add (Nat.ModEq.add (Nat.ModEq.refl 1) h1) h2)
  simpa using hsum

private lemma geom_dvd_pow3 (r : ℕ) : 3^r ∣ geom (10^11) (3^r) := by
  induction r with
  | zero => simp [geom]
  | succ r ih =>
      rw [show 3^(r+1) = 3^r * 3 by ring]
      rw [geom_three]
      exact Nat.mul_dvd_mul ih (factor3 (3^r))

private lemma geom_pos {b t : ℕ} (ht : 0 < t) : 0 < geom b t := by
  cases t with
  | zero => omega
  | succ t => simp [geom]

private lemma pal_pos {t : ℕ} (ht : 0 < t) : 0 < pal t := by
  rw [pal_eval]
  exact Nat.mul_pos (by norm_num [oeisP, reverse_nat, Nat.ofDigits]) (geom_pos ht)

private lemma blocks_len (t : ℕ) : (blocks t).length = 11 * t := by
  induction t with
  | zero => simp [blocks]
  | succ t ih =>
      simp [blocks, block_len, ih, Nat.mul_succ]
      omega

private lemma pal_lt_pow_len (t : ℕ) : pal t < 10 ^ (11 * t) := by
  unfold pal
  simpa [blocks_len] using (Nat.ofDigits_lt_base_pow_length (b:=10) (l:=blocks t) (by norm_num) (blocks_digits_lt t))


private lemma a_le_fixed_pal_5_12 (n : ℕ) (h5 : 5 ≤ n) (h12 : n ≤ 12) :
    a (3^n) ≤ 68899199886 := by
  interval_cases n
  · have hP : oeisP 243 (68899199886 / 243) := by norm_num [oeisP, reverse_nat, Nat.ofDigits]
    have hmul : (68899199886 / 243) * 243 = 68899199886 := by norm_num [oeisP, reverse_nat, Nat.ofDigits]
    simpa [hmul] using (a_le_of_P (m:=243) (k:=68899199886/243) (by norm_num [oeisP, reverse_nat, Nat.ofDigits]) hP)
  · have hP : oeisP 729 (68899199886 / 729) := by norm_num [oeisP, reverse_nat, Nat.ofDigits]
    have hmul : (68899199886 / 729) * 729 = 68899199886 := by norm_num [oeisP, reverse_nat, Nat.ofDigits]
    simpa [hmul] using (a_le_of_P (m:=729) (k:=68899199886/729) (by norm_num [oeisP, reverse_nat, Nat.ofDigits]) hP)
  · have hP : oeisP 2187 (68899199886 / 2187) := by norm_num [oeisP, reverse_nat, Nat.ofDigits]
    have hmul : (68899199886 / 2187) * 2187 = 68899199886 := by norm_num [oeisP, reverse_nat, Nat.ofDigits]
    simpa [hmul] using (a_le_of_P (m:=2187) (k:=68899199886/2187) (by norm_num [oeisP, reverse_nat, Nat.ofDigits]) hP)
  · have hP : oeisP 6561 (68899199886 / 6561) := by norm_num [oeisP, reverse_nat, Nat.ofDigits]
    have hmul : (68899199886 / 6561) * 6561 = 68899199886 := by norm_num [oeisP, reverse_nat, Nat.ofDigits]
    simpa [hmul] using (a_le_of_P (m:=6561) (k:=68899199886/6561) (by norm_num [oeisP, reverse_nat, Nat.ofDigits]) hP)
  · have hP : oeisP 19683 (68899199886 / 19683) := by norm_num [oeisP, reverse_nat, Nat.ofDigits]
    have hmul : (68899199886 / 19683) * 19683 = 68899199886 := by norm_num [oeisP, reverse_nat, Nat.ofDigits]
    simpa [hmul] using (a_le_of_P (m:=19683) (k:=68899199886/19683) (by norm_num [oeisP, reverse_nat, Nat.ofDigits]) hP)
  · have hP : oeisP 59049 (68899199886 / 59049) := by norm_num [oeisP, reverse_nat, Nat.ofDigits]
    have hmul : (68899199886 / 59049) * 59049 = 68899199886 := by norm_num [oeisP, reverse_nat, Nat.ofDigits]
    simpa [hmul] using (a_le_of_P (m:=59049) (k:=68899199886/59049) (by norm_num [oeisP, reverse_nat, Nat.ofDigits]) hP)
  · have hP : oeisP 177147 (68899199886 / 177147) := by norm_num [oeisP, reverse_nat, Nat.ofDigits]
    have hmul : (68899199886 / 177147) * 177147 = 68899199886 := by norm_num [oeisP, reverse_nat, Nat.ofDigits]
    simpa [hmul] using (a_le_of_P (m:=177147) (k:=68899199886/177147) (by norm_num [oeisP, reverse_nat, Nat.ofDigits]) hP)
  · have hP : oeisP 531441 (68899199886 / 531441) := by norm_num [oeisP, reverse_nat, Nat.ofDigits]
    have hmul : (68899199886 / 531441) * 531441 = 68899199886 := by norm_num [oeisP, reverse_nat, Nat.ofDigits]
    simpa [hmul] using (a_le_of_P (m:=531441) (k:=68899199886/531441) (by norm_num [oeisP, reverse_nat, Nat.ofDigits]) hP)

private lemma fixed_pal_lt_rhs_5_12 (n : ℕ) (h5 : 5 ≤ n) (h12 : n ≤ 12) :
    68899199886 < 10 ^ (3 ^ (n - 2)) - 1 := by
  have he : 11 < 3 ^ (n - 2) := by
    interval_cases n <;> norm_num
  have hpow : 10 ^ 11 < 10 ^ (3 ^ (n - 2)) := Nat.pow_lt_pow_right (by norm_num) he
  have hconst : 68899199886 < 10 ^ 11 - 1 := by norm_num
  have hpos : 0 < 10 ^ (3 ^ (n - 2)) := by positivity
  omega


private lemma pow3_dvd_pal_large (n : ℕ) (hn : 13 ≤ n) : 3^n ∣ pal (3^(n-12)) := by
  rw [pal_eval]
  have hP : 3^12 ∣ 68899199886 := by norm_num [oeisP, reverse_nat, Nat.ofDigits]
  have hg : 3^(n-12) ∣ geom (10^11) (3^(n-12)) := geom_dvd_pow3 (n-12)
  have hmul := Nat.mul_dvd_mul hP hg
  convert hmul using 1
  rw [← pow_add]
  congr 1
  omega

private lemma a_le_pal_large (n : ℕ) (hn : 13 ≤ n) : a (3^n) ≤ pal (3^(n-12)) := by
  let m := 3^n
  let t := 3^(n-12)
  have ht : 0 < t := by exact pow_pos (by norm_num) _
  have hdiv : m ∣ pal t := by
    dsimp [m, t]
    exact pow3_dvd_pal_large n hn
  let k := pal t / m
  have hmul : k * m = pal t := by
    dsimp [k]
    exact Nat.div_mul_cancel hdiv
  have hkpos : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    have : pal t = 0 := by simpa [hk0] using hmul.symm
    exact (pal_pos ht).ne' this
  have hk : oeisP m k := by
    constructor
    · exact hkpos
    · rw [hmul, reverse_pal t]
      exact hdiv
  simpa [m, hmul] using (a_le_of_P (m:=m) (k:=k) (by dsimp [m]; exact pow_ne_zero n (by norm_num)) hk)

private lemma pal_large_lt_rhs (n : ℕ) (hn : 13 ≤ n) :
    pal (3^(n-12)) < 10 ^ (3 ^ (n - 2)) - 1 := by
  let t := 3^(n-12)
  have hpal : pal t < 10 ^ (11 * t) := pal_lt_pow_len t
  have htpos : 0 < t := by exact pow_pos (by norm_num) _
  have hexp : 11 * t < 3 ^ (n - 2) := by
    have hn2 : n - 2 = (n - 12) + 10 := by omega
    have hpoweq : 3 ^ (n - 2) = t * 59049 := by
      dsimp [t]
      rw [hn2, pow_add]
      norm_num
    rw [hpoweq]
    nlinarith [htpos]
  have hpowlt : 10 ^ (11 * t) < 10 ^ (3 ^ (n - 2)) := by
    exact Nat.pow_lt_pow_right (by norm_num) hexp
  have hsucc : pal t + 1 < 10 ^ (3 ^ (n - 2)) := by
    exact (Nat.succ_le_of_lt hpal).trans_lt hpowlt
  exact Nat.lt_sub_iff_add_lt.mpr hsucc

private lemma a_ne_rhs_of_ge5 (n : ℕ) (hn : 5 ≤ n) :
    a (3^n) ≠ 10 ^ (3 ^ (n - 2)) - 1 := by
  by_cases h12 : n ≤ 12
  · have hle := a_le_fixed_pal_5_12 n hn h12
    have hlt := fixed_pal_lt_rhs_5_12 n hn h12
    omega
  · have hn13 : 13 ≤ n := by omega
    have hle := a_le_pal_large n hn13
    have hlt := pal_large_lt_rhs n hn13
    omega



theorem oeis_62567_conjecture_0 (n : ℕ) :
  2 ≤ n → (a (3^n) = 10 ^ (3 ^ (n - 2)) - 1 ↔ n = 2 ∨ n = 3 ∨ n = 4) := by
  intro hn
  constructor
  · intro heq
    by_cases hsmall : n = 2 ∨ n = 3 ∨ n = 4
    · exact hsmall
    · have hn5 : 5 ≤ n := by omega
      exact False.elim ((a_ne_rhs_of_ge5 n hn5) heq)
  · intro hsmall
    rcases hsmall with rfl | rfl | rfl
    · simp [a_9]
    · simp [a_27]
    · simp [a_81]
