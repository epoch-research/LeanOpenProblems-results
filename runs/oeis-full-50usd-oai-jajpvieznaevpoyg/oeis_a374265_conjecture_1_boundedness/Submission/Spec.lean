import FormalConjectures.Util.ProblemImports

open Nat Finset

-- The function that removes all '0' digits from a number
def remove_zeros (n : ℕ) : ℕ :=
  -- Nat.digits returns the list of digits in reverse order.
  let digits := (Nat.digits 10 n).filter (fun d => d ≠ 0)
  -- Nat.ofDigits interprets the list from most significant digit first if the base is 10
  ofDigits 10 digits

/--
The set of all possible values $f(n)$ resulting from a sequence of choices
where $f(0)=1$ and $f(i) = \operatorname{OpNoz}_i(i \cdot f(i-1))$,
with $\operatorname{OpNoz}_i(x)$ being either $x$ or $remove\_zeros(x)$.
We use `biUnion` for the union of sets.
-/
def reachable_zeroless_factorials : ℕ → Finset ℕ
  | 0 => {1}
  | n + 1 =>
    let prev_set := reachable_zeroless_factorials n
    prev_set.biUnion fun m =>
      let prod := (n + 1) * m
      {prod, remove_zeros prod}

-- The set of reachable values is always nonempty.
lemma reachable_nonempty (n : ℕ) : (reachable_zeroless_factorials n).Nonempty := by
  induction n with
  | zero => exact Finset.singleton_nonempty 1
  | succ n ih =>
    rcases ih with ⟨m, hm⟩ -- Get a guaranteed element m from the previous set
    let prod := (n + 1) * m
    -- We show that `prod` is an element of the current set using `mem_biUnion`.
    -- prod is in {prod, ...} and m is in the previous set, so prod is in the overall union.
    exact ⟨prod, Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_insert_self prod _⟩⟩

/--
A374265: Minimized zeroless factorials.
$a(n)$ is the smallest $f(n)$ such that $f(0) = 1$ and for $i > 0$,
$f(i) = \operatorname{OpNoz}_i(i \cdot f(i-1))$, where $\operatorname{OpNoz}_i$
is a function that either removes zeros or keeps the value unchanged.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (reachable_zeroless_factorials n).min' (reachable_nonempty n)

/--
Conjecture from OEIS A374265: Is this sequence bounded?
Formalization of the affirmative claim: The sequence `a` is bounded.
The sequence $a(n)$ is bounded if there exists an upper bound $B$ in $\mathbb{N}$
such that $a(n) \leq B$ for all $n$.
-/


abbrev dsum (n : ℕ) := (Nat.digits 10 n).sum

lemma dsum_eq (n : ℕ) : dsum n = n % 10 + dsum (n / 10) := by
  by_cases h : n = 0
  · subst h; simp [dsum, Nat.digits_zero]
  · rw [dsum, Nat.digits_eq_cons_digits_div (by norm_num : 1 < 10) h]
    simp [dsum]

lemma carry_eq (a b : ℕ) : (a % 10 + b % 10) / 10 = (if 10 ≤ a % 10 + b % 10 then 1 else 0) := by
  have hlt : a % 10 + b % 10 < 20 := by
    have h1 := Nat.mod_lt a (by norm_num : 0 < 10)
    have h2 := Nat.mod_lt b (by norm_num : 0 < 10)
    omega
  split_ifs with h
  · apply Nat.div_eq_of_lt_le
    · omega
    · omega
  · exact Nat.div_eq_of_lt (by omega)

lemma div10_add_eq (a b : ℕ) : (a + b) / 10 = a / 10 + b / 10 + (a % 10 + b % 10) / 10 := by
  rw [Nat.add_div (by norm_num : 0 < 10), carry_eq]

lemma mod10_add_eq (a b : ℕ) : (a + b) % 10 = (a % 10 + b % 10) % 10 := by
  rw [Nat.add_mod]

lemma small_carry_dsum_le (r : ℕ) (hr : r < 20) : r % 10 + dsum (r / 10) ≤ r := by
  have hds : dsum (r / 10) ≤ r / 10 := Nat.digit_sum_le 10 (r / 10)
  have hcase : r / 10 = 0 ∨ r / 10 = 1 := by omega
  rcases hcase with h0 | h1 <;> omega

lemma dsum_add_le (a b : ℕ) : dsum (a + b) ≤ dsum a + dsum b := by
  induction' h : a + b using Nat.strong_induction_on with s IH generalizing a b
  subst h
  rw [dsum_eq (a+b), dsum_eq a, dsum_eq b]
  rw [div10_add_eq, mod10_add_eq]
  set r := a % 10 + b % 10
  have hr : r < 20 := by
    dsimp [r]
    have h1 := Nat.mod_lt a (by norm_num : 0 < 10)
    have h2 := Nat.mod_lt b (by norm_num : 0 < 10)
    omega
  have hsmall : a / 10 + b / 10 + r / 10 < a + b ∨ a + b = 0 := by
    by_cases hs : a + b = 0
    · exact Or.inr hs
    · left
      have : (a + b) / 10 < a + b := Nat.div_lt_self (Nat.pos_of_ne_zero hs) (by norm_num : 1 < 10)
      rwa [div10_add_eq, show a % 10 + b % 10 = r by rfl] at this
  have hIH1 : dsum (a / 10 + b / 10 + r / 10) ≤ dsum (a / 10 + b / 10) + dsum (r / 10) := by
    rcases hsmall with hslt | hzero
    · exact IH _ hslt (a / 10 + b / 10) (r / 10) rfl
    · have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      subst ha0; subst hb0
      simp [dsum]
  have hqsum_lt : a / 10 + b / 10 < a + b ∨ a + b = 0 := by
    by_cases hs : a + b = 0
    · exact Or.inr hs
    · left
      have hle : a / 10 + b / 10 ≤ (a+b)/10 := Nat.add_div_le_add_div a b 10
      have hlt : (a+b)/10 < a+b := Nat.div_lt_self (Nat.pos_of_ne_zero hs) (by norm_num : 1 < 10)
      exact lt_of_le_of_lt hle hlt
  have hIH2 : dsum (a / 10 + b / 10) ≤ dsum (a / 10) + dsum (b / 10) := by
    rcases hqsum_lt with hslt | hzero
    · exact IH _ hslt (a/10) (b/10) rfl
    · have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      subst ha0; subst hb0
      simp [dsum]
  have hcarry : r % 10 + dsum (r / 10) ≤ r := small_carry_dsum_le r hr
  omega

lemma dsum_mod_add_div_pow (P x : ℕ) (hhi : 0 < x / 10 ^ P) :
    dsum x = dsum (x % 10 ^ P) + dsum (x / 10 ^ P) := by
  let lo := x % 10 ^ P
  let hi := x / 10 ^ P
  have hbase : 1 < 10 := by norm_num
  have hqpos : 0 < 10 ^ P := pow_pos (by norm_num : 0 < 10) _
  have hlo : lo < 10 ^ P := Nat.mod_lt x hqpos
  have hlen : (Nat.digits 10 lo).length ≤ P := by
    exact (Nat.digits_length_le_iff hbase lo).mpr hlo
  have hpow : 10 ^ ((Nat.digits 10 lo).length + (P - (Nat.digits 10 lo).length)) = 10 ^ P := by
    rw [Nat.add_sub_cancel' hlen]
  have hd := Nat.digits_append_zeroes_append_digits (b := 10) (k := P - (Nat.digits 10 lo).length)
      (m := hi) (n := lo) hbase hhi
  have hxeq : lo + 10 ^ ((Nat.digits 10 lo).length + (P - (Nat.digits 10 lo).length)) * hi = x := by
    rw [hpow]
    exact Nat.mod_add_div x (10 ^ P)
  rw [hxeq] at hd
  calc
    dsum x = (Nat.digits 10 lo ++ List.replicate (P - (Nat.digits 10 lo).length) 0 ++ Nat.digits 10 hi).sum := by
      rw [dsum, ← hd]
    _ = dsum lo + dsum hi := by
      simp [dsum]

lemma ofDigits_replicate_9 (P : ℕ) : Nat.ofDigits 10 (List.replicate P 9) = 10 ^ P - 1 := by
  induction P with
  | zero => simp
  | succ P ih =>
      rw [List.replicate_succ, Nat.ofDigits_cons, ih]
      rw [pow_succ]
      have hp : 1 ≤ 10 ^ P := Nat.one_le_pow P 10 (by norm_num)
      have hsub : 10 * (10 ^ P - 1) = 10 * 10 ^ P - 10 := Nat.mul_sub_left_distrib 10 (10 ^ P) 1
      rw [hsub]
      omega

lemma dsum_repunit (P : ℕ) : dsum (10 ^ P - 1) = 9 * P := by
  have hmem : List.replicate P 9 ∈ {L : List ℕ | L.length = P ∧ ∀ x ∈ L, x < 10} := by
    constructor
    · simp
    · intro x hx
      simp at hx
      omega
  have h := Nat.sum_digits_ofDigits_eq_sum (b := 10) (l := P) (L := List.replicate P 9) (by norm_num : 1 < 10) hmem
  rw [ofDigits_replicate_9] at h
  rw [dsum, h]
  simp
  omega

lemma dsum_ge_of_repunit_dvd (P x : ℕ) (hP : 0 < P) (hxpos : 0 < x)
    (hdvd : 10 ^ P - 1 ∣ x) : 9 * P ≤ dsum x := by
  let d := 10 ^ P - 1
  have hdpos : 0 < d := by
    dsimp [d]
    have h10P : 1 < 10 ^ P := one_lt_pow₀ (by norm_num : 1 < 10) hP.ne'
    omega
  induction' x using Nat.strong_induction_on with x IH
  by_cases hxlt : x < 10 ^ P
  · rcases hdvd with ⟨c, rfl⟩
    have hcpos : 0 < c := by
      by_contra hc
      have : c = 0 := by omega
      subst c
      simp at hxpos
    have hc1 : c = 1 := by
      by_contra hcne
      have hcge : 2 ≤ c := by omega
      have hqge : 2 ≤ 10 ^ P := by
        have hqgt : 1 < 10 ^ P := one_lt_pow₀ (by norm_num : 1 < 10) hP.ne'
        omega
      have h2 : 10 ^ P ≤ d * 2 := by
        dsimp [d]
        omega
      have hlarge : 10 ^ P ≤ d * c := by
        exact le_trans h2 (Nat.mul_le_mul_left d hcge)
      dsimp [d] at hlarge
      exact (not_lt_of_ge hlarge) hxlt
    subst c
    simpa using le_of_eq (dsum_repunit P).symm
  · have hqpos : 0 < 10 ^ P := pow_pos (by norm_num : 0 < 10) _
    let lo := x % 10 ^ P
    let hi := x / 10 ^ P
    let y := lo + hi
    have hhi_pos : 0 < hi := by
      dsimp [hi]
      exact Nat.div_pos (Nat.le_of_not_gt hxlt) hqpos
    have hypos : 0 < y := by dsimp [y]; omega
    have hsplit : x = lo + 10 ^ P * hi := by
      dsimp [lo, hi]
      exact (Nat.mod_add_div x (10 ^ P)).symm
    have hxdiff : x = y + d * hi := by
      rw [hsplit]
      dsimp [y, d]
      have hone : 1 + (10 ^ P - 1) = 10 ^ P := by
        have hqpos' : 0 < 10 ^ P := pow_pos (by norm_num : 0 < 10) P
        omega
      calc
        lo + 10 ^ P * hi = lo + (1 + (10 ^ P - 1)) * hi := by rw [hone]
        _ = lo + hi + (10 ^ P - 1) * hi := by ring
    have hylt : y < x := by
      rw [hxdiff]
      have : 0 < d * hi := Nat.mul_pos hdpos hhi_pos
      omega
    have hydvd : d ∣ y := by
      rw [hxdiff] at hdvd
      exact (Nat.dvd_add_left (dvd_mul_right d hi)).mp hdvd
    have hIH := IH y hylt hypos hydvd
    have hds_split := dsum_mod_add_div_pow P x hhi_pos
    have hadd := dsum_add_le lo hi
    dsimp [y] at hIH hadd
    rw [hds_split]
    exact le_trans hIH hadd

lemma sum_filter_ne_zero (l : List ℕ) : (l.filter (fun d => d ≠ 0)).sum = l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      by_cases ha : a = 0
      · subst a
        simpa using ih
      · have ih' : (t.filter (fun d => !decide (d = 0))).sum = t.sum := by
          simpa [ne_eq] using ih
        simp [ha, ih']

lemma dsum_remove_zeros (x : ℕ) : dsum (remove_zeros x) = dsum x := by
  let L := (Nat.digits 10 x).filter (fun d => d ≠ 0)
  have hmem : L ∈ {L : List ℕ | L.length = L.length ∧ ∀ a ∈ L, a < 10} := by
    constructor
    · rfl
    · intro a ha
      dsimp [L] at ha
      exact Nat.digits_lt_base (by norm_num : 1 < 10) (List.mem_of_mem_filter ha)
  have h := Nat.sum_digits_ofDigits_eq_sum (b := 10) (l := L.length) (L := L) (by norm_num : 1 < 10) hmem
  rw [show remove_zeros x = Nat.ofDigits 10 L by rfl]
  rw [dsum, h, dsum]
  exact sum_filter_ne_zero (Nat.digits 10 x)

lemma list_sum_le_nine_mul_length {l : List ℕ} (h : ∀ a ∈ l, a < 10) : l.sum ≤ 9 * l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have ha : a < 10 := h a (by simp)
      have ht : ∀ b ∈ t, b < 10 := by
        intro b hb; exact h b (by simp [hb])
      have hit := ih ht
      simp
      omega

lemma dsum_le_nine_mul_length_digits (y : ℕ) : dsum y ≤ 9 * (Nat.digits 10 y).length := by
  exact list_sum_le_nine_mul_length (fun a ha => Nat.digits_lt_base (by norm_num : 1 < 10) ha)

lemma dsum_le_of_le (y B : ℕ) (hy : y ≤ B) : dsum y ≤ 9 * (Nat.digits 10 B).length := by
  exact (dsum_le_nine_mul_length_digits y).trans (Nat.mul_le_mul_left 9 (Nat.le_digits_len_le 10 y B hy))

lemma ofDigits_pos_of_pos_mem {L : List ℕ} {a : ℕ} (ha : a ∈ L) (hapos : 0 < a) :
    0 < Nat.ofDigits 10 L := by
  induction L with
  | nil => simp at ha
  | cons h t ih =>
      simp at ha
      rcases ha with rfl | ht
      · simp [Nat.ofDigits, hapos]
      · have := ih ht
        simp [Nat.ofDigits]
        omega

lemma remove_zeros_pos {x : ℕ} (hx : 0 < x) : 0 < remove_zeros x := by
  unfold remove_zeros
  let L := Nat.digits 10 x
  have hne : L ≠ [] := by
    dsimp [L]
    exact Nat.digits_ne_nil_iff_ne_zero.mpr (Nat.ne_of_gt hx)
  let a := L.getLast hne
  have ha_mem : a ∈ L := List.getLast_mem hne
  have ha_ne : a ≠ 0 := by
    dsimp [a, L]
    exact Nat.getLast_digit_ne_zero 10 (Nat.ne_of_gt hx)
  have ha_f : a ∈ L.filter (fun d => d ≠ 0) := by
    exact List.mem_filter.mpr ⟨ha_mem, by simpa using ha_ne⟩
  exact ofDigits_pos_of_pos_mem ha_f (Nat.pos_of_ne_zero ha_ne)

lemma reachable_pos {n m : ℕ} (hm : m ∈ reachable_zeroless_factorials n) : 0 < m := by
  induction n generalizing m with
  | zero =>
      simp [reachable_zeroless_factorials] at hm
      omega
  | succ n ih =>
      rw [reachable_zeroless_factorials] at hm
      rcases Finset.mem_biUnion.mp hm with ⟨u, hu, hmem⟩
      have hupos : 0 < u := ih hu
      have hprod : 0 < (n + 1) * u := Nat.mul_pos (Nat.succ_pos n) hupos
      simp at hmem
      rcases hmem with h | h
      · subst h
        exact hprod
      · subst h
        exact remove_zeros_pos hprod


theorem oeis_a374265_conjecture_1_boundedness.disproof :
    ¬ (∃ B : ℕ, ∀ n : ℕ, a n ≤ B) := by
  rintro ⟨B, hB⟩
  let L := (Nat.digits 10 B).length
  let P := L + 1
  let n := 10 ^ P - 1
  have hPpos : 0 < P := by dsimp [P]; omega
  have hBltpowL : B < 10 ^ L := Nat.lt_base_pow_length_digits (b := 10) (m := B) (by norm_num : 1 < 10)
  have hpowL_lt_n : 10 ^ L < n := by
    dsimp [n, P]
    rw [pow_succ]
    have hpowpos : 0 < 10 ^ L := pow_pos (by norm_num : 0 < 10) L
    have hle : 10 ^ L + 1 ≤ 10 ^ L * 10 := by nlinarith
    omega
  have hBlt_n : B < n := lt_trans hBltpowL hpowL_lt_n
  have hnpos : 0 < n := by omega
  let y := a n
  have hy_le : y ≤ B := hB n
  have hy_mem : y ∈ reachable_zeroless_factorials n := by
    dsimp [y, a]
    exact Finset.min'_mem _ _
  have hypos : 0 < y := reachable_pos hy_mem
  have hy_mem_succ : y ∈ reachable_zeroless_factorials ((n - 1) + 1) := by
    rwa [Nat.sub_add_cancel hnpos]
  rw [reachable_zeroless_factorials] at hy_mem_succ
  rcases Finset.mem_biUnion.mp hy_mem_succ with ⟨m, hm_prev, hmval⟩
  have hmpos : 0 < m := reachable_pos hm_prev
  simp at hmval
  rcases hmval with hkeep | hrem
  · have hsucc : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
    have hn_le_y : n ≤ y := by
      rw [hkeep, hsucc]
      exact Nat.le_mul_of_pos_right n hmpos
    omega
  · have hsucc : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
    have hrem' : y = remove_zeros (n * m) := by simpa [hsucc] using hrem
    let x := n * m
    have hxpos : 0 < x := Nat.mul_pos hnpos hmpos
    have hdvd : 10 ^ P - 1 ∣ x := by
      dsimp [x, n]
      exact dvd_mul_right (10 ^ P - 1) m
    have hlower : 9 * P ≤ dsum x := dsum_ge_of_repunit_dvd P x hPpos hxpos hdvd
    have hxy : dsum x = dsum y := by
      dsimp [x]
      rw [hrem', dsum_remove_zeros]
    have hupper : dsum y ≤ 9 * L := dsum_le_of_le y B hy_le
    rw [hxy] at hlower
    have : 9 * P ≤ 9 * L := le_trans hlower hupper
    dsimp [P] at this
    omega
