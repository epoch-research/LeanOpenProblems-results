import FormalConjectures.Util.ProblemImports
open List Nat Function Set

set_option linter.unusedVariables false

def half_ceil (m : ℕ) : ℕ := (m + 1) / 2
def half_floor (m : ℕ) : ℕ := m / 2
def trim (l : List ℕ) : List ℕ := (List.reverse l).dropWhile (fun x => x = 0) |>.reverse
def rawWith (c : ℕ) : List ℕ → List ℕ
| [] => [c]
| a::l => (half_ceil a + c) :: rawWith (half_floor a) l
def ca_step (config : List ℕ) : List ℕ :=
  let base_masses := config.map half_ceil ++ [0]
  let received_masses := 0 :: config.map half_floor
  let next_config_long := List.zipWith Nat.add base_masses received_masses
  trim next_config_long
def S (n t : ℕ) : List ℕ := (List.range t).foldl (fun acc _ => ca_step acc) [n]
def tailSum (l : List ℕ) (i : ℕ) : ℕ := (l.drop i).sum

def F : ℕ → ℕ → ℕ → ℕ
| n, 0, 0 => n
| _, 0, _+1 => 0
| n, _+1, 0 => n
| n, t+1, i+1 => (F n t i + F n t (i+1))/2

lemma S_succ (n t) : S n (t+1) = ca_step (S n t) := by
  simp [S, List.range_succ, List.foldl_append]
lemma F_zero (n t) : F n t 0 = n := by cases t <;> rfl
lemma F_step_succ (n t i) : F n (t+1) (i+1) = (F n t i + F n t (i+1))/2 := rfl


lemma ceil_add_floor (a : ℕ) : half_ceil a + half_floor a = a := by
  unfold half_ceil half_floor
  omega

lemma rawWith_eq (c : ℕ) (l : List ℕ) :
    rawWith c l = List.zipWith Nat.add (l.map half_ceil ++ [0]) (c :: l.map half_floor) := by
  induction l generalizing c with
  | nil => simp [rawWith]
  | cons a l ih => simp [rawWith, ih]

lemma sum_rawWith (c : ℕ) (l : List ℕ) : (rawWith c l).sum = c + l.sum := by
  induction l generalizing c with
  | nil => simp [rawWith]
  | cons a l ih =>
      simp [rawWith, ih]
      have h := ceil_add_floor a
      omega

lemma ca_step_eq_rawWith (l : List ℕ) : ca_step l = trim (rawWith 0 l) := by
  unfold ca_step
  rw [rawWith_eq]

lemma tailSum_append_zero (l : List ℕ) (i : ℕ) : tailSum (l ++ [0]) i = tailSum l i := by
  induction l generalizing i with
  | nil => cases i <;> simp [tailSum]
  | cons a l ih =>
      cases i with
      | zero => simp [tailSum]
      | succ i => simpa [tailSum] using ih i

lemma trim_append_zero (l : List ℕ) : trim (l ++ [0]) = trim l := by
  simp [trim]
lemma trim_append_ne_zero (l : List ℕ) {x : ℕ} (hx : x ≠ 0) : trim (l ++ [x]) = l ++ [x] := by
  simp [trim, List.reverse_append, hx]
lemma tailSum_trim (l : List ℕ) (i : ℕ) : tailSum (trim l) i = tailSum l i := by
  induction l using List.reverseRecOn generalizing i with
  | nil => simp [tailSum, trim]
  | append_singleton xs x ih =>
      by_cases hx : x = 0
      · subst x
        rw [trim_append_zero, ih, tailSum_append_zero]
      · rw [trim_append_ne_zero xs hx]

lemma dropWhile_append_of_neg {α} (p : α → Bool) (xs : List α) {a : α} (ha : p a = false) :
    (xs ++ [a]).dropWhile p = xs.dropWhile p ++ [a] := by
  induction xs with
  | nil => simp [ha]
  | cons b xs ih =>
      by_cases hb : p b = true
      · simp [List.dropWhile, hb, ih]
      · have hb' : p b = false := by cases h : p b <;> simp_all
        simp [List.dropWhile, hb']

lemma trim_cons_ne_zero {a : ℕ} (l : List ℕ) (ha : a ≠ 0) : trim (a::l) = a :: trim l := by
  unfold trim
  simp [List.reverse_cons]
  rw [dropWhile_append_of_neg]
  simp [ha]

lemma tailSum_rawWith_succ_carry (c : ℕ) (l : List ℕ) (i : ℕ) :
    tailSum (rawWith c l) (i+1) = tailSum (rawWith 0 l) (i+1) := by
  induction l generalizing c i with
  | nil => cases i <;> simp [tailSum, rawWith]
  | cons a l ih =>
      cases i with
      | zero => simp [tailSum, rawWith, sum_rawWith]
      | succ i => simp [tailSum, rawWith, ih]

lemma tail_rawWith_zero (l : List ℕ) (i : ℕ) :
    tailSum (rawWith 0 l) (i+1) = (tailSum l i + tailSum l (i+1))/2 := by
  induction l generalizing i with
  | nil => cases i <;> simp [tailSum, rawWith]
  | cons a l ih =>
      cases i with
      | zero =>
          simp [tailSum, rawWith, sum_rawWith]
          unfold half_floor
          rw [show a + l.sum + l.sum = a + 2 * l.sum by omega]
          rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
      | succ i =>
          simp [tailSum, rawWith]
          change tailSum (rawWith (half_floor a) l) (i+1) = (tailSum l i + tailSum l (i+1)) / 2
          rw [tailSum_rawWith_succ_carry]
          exact ih i

lemma tail_ca_step_succ (l : List ℕ) (i : ℕ) :
    tailSum (ca_step l) (i+1) = (tailSum l i + tailSum l (i+1))/2 := by
  rw [ca_step_eq_rawWith]
  simp [tailSum_trim, tail_rawWith_zero]

lemma sum_ca_step (l : List ℕ) : (ca_step l).sum = l.sum := by
  rw [ca_step_eq_rawWith]
  simpa [tailSum, tailSum_trim, sum_rawWith] using tailSum_trim (rawWith 0 l) 0

lemma tailS_eq_F (n t i : ℕ) : tailSum (S n t) i = F n t i := by
  induction t generalizing i with
  | zero =>
      cases i <;> simp [S, tailSum, F]
  | succ t ih =>
      cases i with
      | zero =>
          rw [S_succ]
          simp [tailSum]
          rw [sum_ca_step]
          have h0 : (S n t).sum = F n t 0 := by simpa [tailSum] using ih 0
          exact h0.trans (F_zero n t)
      | succ i =>
          rw [S_succ, tail_ca_step_succ, ih i, ih (i+1)]
          rfl

lemma sum_S (n t : ℕ) : (S n t).sum = n := by
  have h := tailS_eq_F n t 0
  simpa [tailSum, F_zero] using h

lemma pos_trim_rawWith_of_pos {l : List ℕ} (h : ∀ x ∈ l, 0 < x) (c : ℕ) :
    ∀ x ∈ trim (rawWith c l), 0 < x := by
  induction l generalizing c with
  | nil =>
      intro x hx
      by_cases hc : c = 0
      · subst c
        simp [trim, rawWith] at hx
      · simp [trim, rawWith, hc] at hx
        omega
  | cons a l ih =>
      intro x hx
      have ha : 0 < half_ceil a + c := by
        have hpa : 0 < a := h a (by simp)
        unfold half_ceil
        omega
      unfold rawWith at hx
      rw [trim_cons_ne_zero _ (by omega : half_ceil a + c ≠ 0)] at hx
      simp at hx
      rcases hx with hx | hx
      · subst x
        exact ha
      · exact ih (by intro y hy; exact h y (by simp [hy])) (half_floor a) x hx
lemma pos_ca_step_of_pos {l : List ℕ} (h : ∀ x ∈ l, 0 < x) : ∀ x ∈ ca_step l, 0 < x := by
  rw [ca_step_eq_rawWith]
  exact pos_trim_rawWith_of_pos h 0

lemma pos_S {n : ℕ} (hn : 0 < n) (t : ℕ) : ∀ x ∈ S n t, 0 < x := by
  induction t with
  | zero => intro x hx; simp [S] at hx; omega
  | succ t ih =>
      rw [S_succ]
      exact pos_ca_step_of_pos ih

lemma length_le_sum_of_pos {l : List ℕ} (hpos : ∀ x ∈ l, 0 < x) : l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : 0 < a := hpos a (by simp)
      have hp : ∀ x ∈ l, 0 < x := by intro x hx; exact hpos x (by simp [hx])
      have hle := ih hp
      simp
      omega

lemma tail_pos_lt_length {l : List ℕ} {k : ℕ} (h : 0 < tailSum l k) : k < l.length := by
  by_contra hnot
  have hle : l.length ≤ k := by omega
  have hd := List.drop_eq_nil_of_le (as:=l) hle
  simp [tailSum, hd] at h

lemma all_one_of_pos_sum_eq_length {l : List ℕ} (hpos : ∀ x ∈ l, 0 < x) (hs : l.sum = l.length) :
    ∀ x ∈ l, x = 1 := by
  induction l with
  | nil => intro x hx; simp at hx
  | cons a l ih =>
      have ha : 0 < a := hpos a (by simp)
      have hp : ∀ x ∈ l, 0 < x := by intro x hx; exact hpos x (by simp [hx])
      have hle := length_le_sum_of_pos hp
      simp at hs
      have ha1 : a = 1 := by omega
      have hsl : l.sum = l.length := by omega
      intro x hx
      simp at hx
      rcases hx with rfl | hx
      · exact ha1
      · exact ih hp hsl x hx

lemma stable_of_tail_pos {n t : ℕ} (hn : 0 < n) (h : 0 < F n t (n-1)) :
    S n t = List.replicate n 1 := by
  have htail : 0 < tailSum (S n t) (n-1) := by simpa [tailS_eq_F] using h
  have hlen_ge : n ≤ (S n t).length := by
    have := tail_pos_lt_length htail
    omega
  have hpos := pos_S hn t
  have hlen_le : (S n t).length ≤ n := by
    have hle := length_le_sum_of_pos hpos
    have hs := sum_S n t
    omega
  have hlen : (S n t).length = n := by omega
  have hall : ∀ x ∈ S n t, x = 1 := by
    apply all_one_of_pos_sum_eq_length hpos
    rw [sum_S, hlen]
  exact (List.eq_replicate_iff).2 ⟨hlen, hall⟩

lemma tail_pos_of_stable {n t : ℕ} (hn : 0 < n) (h : S n t = List.replicate n 1) :
    0 < F n t (n-1) := by
  rw [← tailS_eq_F]
  rw [h]
  cases n with
  | zero => omega
  | succ n =>
      simp [tailSum]
lemma half_le_self_of_le {x n : ℕ} (hx : x ≤ n) : (n + x)/2 ≤ n := by
  rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 2)]; omega
lemma half_succ_le_self_of_le {x n : ℕ} (hx : x ≤ n) : (n + 1 + x)/2 ≤ n := by
  rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 2)]; omega
lemma div2_lt_of_add_two_le {s y : ℕ} (h : s + 2 ≤ y) : s/2 < y/2 := by
  rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]; omega
lemma div2_lt_of_boundary {x y : ℕ} (hpos : 0 < x) (h : x + 1 + x/2 ≤ y) : x/2 < y/2 := by
  rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]; omega

lemma F_mono_index (n t i) : F n t (i+1) ≤ F n t i := by
  induction t generalizing i with
  | zero => cases i <;> simp [F]
  | succ t ih =>
      cases i with
      | zero => rw [F_zero, F_step_succ, F_zero]; exact half_le_self_of_le (by simpa [F_zero] using ih 0)
      | succ i => rw [F_step_succ, F_step_succ]; exact Nat.div_le_div_right (Nat.add_le_add (ih i) (ih (i+1)))

lemma F_mono_n (n t i) : F n t i ≤ F (n+1) t i := by
  induction t generalizing i with
  | zero => cases i <;> simp [F]
  | succ t ih =>
      cases i with
      | zero => simp [F_zero]
      | succ i => rw [F_step_succ, F_step_succ]; exact Nat.div_le_div_right (Nat.add_le_add (ih i) (ih (i+1)))

lemma half_shift_le (n t i) : F n t i / 2 ≤ F (n+1) (t+1) (i+1) := by
  rw [F_step_succ]
  exact le_trans (Nat.div_le_div_right (F_mono_n n t i)) (Nat.div_le_div_right (by omega : F (n+1) t i ≤ F (n+1) t i + F (n+1) t (i+1)))

lemma lower_shift (n t i) : F (n+1) (t+1) (i+1) ≤ F n t i := by
  induction t generalizing i with
  | zero =>
      cases i with
      | zero => rw [F_step_succ, F_zero]; simp [F]; rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 2)]; omega
      | succ i => simp [F]
  | succ t ih =>
      cases i with
      | zero => rw [F_step_succ, F_zero]; exact half_succ_le_self_of_le (by simpa [F_zero] using ih 0)
      | succ i => rw [F_step_succ, F_step_succ]; exact Nat.div_le_div_right (Nat.add_le_add (ih i) (ih (i+1)))

lemma strict_shift (n t i) : F n t i = 0 ∨ F n t i < F (n+1) (t+1) i := by
  induction t generalizing i with
  | zero =>
      cases i with
      | zero => right; simp [F]
      | succ i => left; simp [F]
  | succ t ih =>
      cases i with
      | zero => right; rw [F_zero, F_zero]; omega
      | succ i =>
          rw [F_step_succ, F_step_succ]
          by_cases hnext : F n t (i+1) = 0
          · by_cases hcur0 : F n t i = 0
            · left; simp [hcur0, hnext]
            · right
              have hcurpos : 0 < F n t i := Nat.pos_of_ne_zero hcur0
              have hyi : F n t i < F (n+1) (t+1) i := by
                rcases ih i with hz | hp
                · exact (hcur0 hz).elim
                · exact hp
              have hbd := half_shift_le n t i
              rw [hnext, add_zero]
              have hsum : F n t i + 1 + F n t i / 2 ≤ F (n+1) (t+1) i + F (n+1) (t+1) (i+1) := by omega
              exact div2_lt_of_boundary hcurpos hsum
          · right
            have hyi : F n t i < F (n+1) (t+1) i := by
              rcases ih i with hz | hp
              · have hm := F_mono_index n t i; omega
              · exact hp
            have hyip : F n t (i+1) < F (n+1) (t+1) (i+1) := by
              rcases ih (i+1) with hz | hp
              · omega
              · exact hp
            have hsum : F n t i + F n t (i+1) + 2 ≤ F (n+1) (t+1) i + F (n+1) (t+1) (i+1) := by omega
            exact div2_lt_of_add_two_le hsum

lemma upper_pos_shift (n t i) (h : 0 < F n t i) : 0 < F (n+1) (t+2) (i+1) := by
  have hs := strict_shift n t i
  have hy : F n t i < F (n+1) (t+1) i := by
    rcases hs with hz | hp
    · omega
    · exact hp
  rw [F_step_succ]
  have : 2 ≤ F (n+1) (t+1) i + F (n+1) (t+1) (i+1) := by omega
  rw [Nat.lt_div_iff_mul_lt (by norm_num : 0 < 2)]
  omega

lemma eventual_pos : ∀ n : ℕ, 0 < n → 0 < F n (2*(n-1)) (n-1)
| 0, hn => by omega
| 1, hn => by simp [F]
| k+2, hn => by
    have ih : 0 < F (k+1) (2*((k+1)-1)) ((k+1)-1) := eventual_pos (k+1) (by omega)
    have h := upper_pos_shift (k+1) (2*k) k (by simpa using ih)
    simpa [show 2 * (k + 2 - 1) = 2*k + 2 by omega, show k + 2 - 1 = k+1 by omega] using h

noncomputable def A (n : ℕ) : ℕ := if n = 0 then 0 else sInf {k | S n k = List.replicate n 1}

lemma A_pos_def {n : ℕ} (hn : n ≠ 0) : A n = sInf {k | S n k = List.replicate n 1} := by simp [A, hn]

lemma stable_nonempty {n : ℕ} (hn : 0 < n) : ({k | S n k = List.replicate n 1} : Set ℕ).Nonempty := by
  refine ⟨2*(n-1), ?_⟩
  exact stable_of_tail_pos hn (eventual_pos n hn)

lemma A_mem_stable {n : ℕ} (hn : 0 < n) : S n (A n) = List.replicate n 1 := by
  rw [A_pos_def (by omega : n ≠ 0)]
  exact Nat.sInf_mem (stable_nonempty hn)

lemma A_le_of_stable {n t : ℕ} (hn : 0 < n) (h : S n t = List.replicate n 1) : A n ≤ t := by
  rw [A_pos_def (by omega : n ≠ 0)]
  exact Nat.sInf_le h

lemma A_diff_one_or_two : ∀ n : ℕ, 1 ≤ n → A (n+1) = A n + 1 ∨ A (n+1) = A n + 2 := by
  intro n hn
  have hnpos : 0 < n := by omega
  have hn1pos : 0 < n+1 := by omega
  have hstabn := A_mem_stable hnpos
  have htailn := tail_pos_of_stable hnpos hstabn
  have htail_up := upper_pos_shift n (A n) (n-1) (by simpa using htailn)
  have hstab_up : S (n+1) (A n + 2) = List.replicate (n+1) 1 := by
    have : 0 < F (n+1) (A n + 2) n := by
      simpa [show n - 1 + 1 = n by omega] using htail_up
    exact stable_of_tail_pos hn1pos (by simpa [show n + 1 - 1 = n by omega] using this)
  have hupper : A (n+1) ≤ A n + 2 := A_le_of_stable hn1pos hstab_up
  have hstabnp1 := A_mem_stable hn1pos
  have htailnp1 := tail_pos_of_stable hn1pos hstabnp1
  have hlower : A n + 1 ≤ A (n+1) := by
    cases hk : A (n+1) with
    | zero =>
        have : F (n+1) 0 n = 0 := by
          cases n with
          | zero => omega
          | succ n => simp [F]
        have hbad : 0 < F (n+1) 0 n := by simpa [hk, show n+1-1 = n by omega] using htailnp1
        omega
    | succ t =>
        have hpos : 0 < F (n+1) (t+1) n := by simpa [hk, show n+1-1 = n by omega] using htailnp1
        have hle0 := lower_shift n t (n-1)
        have hle : F (n+1) (t+1) n ≤ F n t (n-1) := by simpa [show n - 1 + 1 = n by omega] using hle0
        have htail : 0 < F n t (n-1) := by omega
        have hstab : S n t = List.replicate n 1 := stable_of_tail_pos hnpos htail
        have hAle : A n ≤ t := A_le_of_stable hnpos hstab
        omega
  omega


