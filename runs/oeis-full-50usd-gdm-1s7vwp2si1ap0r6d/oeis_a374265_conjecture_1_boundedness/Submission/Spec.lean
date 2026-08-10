import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000000
set_option maxHeartbeats 100000000

open Nat Finset

def ofDigitsNat (b : ℕ) : List ℕ → ℕ
  | [] => 0
  | h :: t => h + b * ofDigitsNat b t

def digitsNat (b : ℕ) (gas : ℕ) (n : ℕ) : List ℕ :=
  match gas with
  | 0 => []
  | gas + 1 =>
    if n = 0 then []
    else (n % b) :: digitsNat b gas (n / b)

-- The function that removes all '0' digits from a number
def remove_zeros (n : ℕ) : ℕ :=
  let digits := (digitsNat 10 (n + 1) n).filter (fun d => d ≠ 0)
  ofDigitsNat 10 digits

lemma ofDigitsNat_eq_ofDigits (b : ℕ) (l : List ℕ) : ofDigitsNat b l = ofDigits b l := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    unfold ofDigitsNat ofDigits
    simp only [Nat.cast_id, ih]


lemma ten_pow_succ_gt_self (n : ℕ) : n < 10^(n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h_mul : 10^(n + 2) = 10^(n + 1) * 10 := by ring
    rw [h_mul]
    omega

lemma digitsNat_eq_digits (gas : ℕ) (n : ℕ) (h_gas : n < 10^gas) :
    digitsNat 10 gas n = Nat.digits 10 n := by
  induction gas generalizing n with
  | zero =>
    have : n = 0 := by omega
    subst this
    rw [Nat.digits_zero 10]
    rfl
  | succ g ih =>
    by_cases hn : n = 0
    · subst hn
      rw [Nat.digits_zero 10]
      rfl
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      have h_red : digitsNat 10 (g + 1) n = (n % 10) :: digitsNat 10 g (n / 10) := by
        change (if n = 0 then [] else (n % 10) :: digitsNat 10 g (n / 10)) = (n % 10) :: digitsNat 10 g (n / 10)
        simp only [hn, ↓reduceIte]
      rw [h_red]
      have h_lt : n / 10 < 10^g := by
        have h_mul : 10^(g + 1) = 10^g * 10 := by ring
        rw [h_mul] at h_gas
        omega
      rw [ih (n / 10) h_lt]
      rw [Nat.digits_of_two_le_of_pos (by decide) hn_pos]

lemma digitsNat_eq_digits_self (n : ℕ) : digitsNat 10 (n + 1) n = Nat.digits 10 n :=
  digitsNat_eq_digits (n + 1) n (ten_pow_succ_gt_self n)

lemma remove_zeros_eq_old (n : ℕ) :
    remove_zeros n = ofDigits 10 ((Nat.digits 10 n).filter (fun d => d ≠ 0)) := by
  unfold remove_zeros
  rw [digitsNat_eq_digits_self]
  rw [ofDigitsNat_eq_ofDigits]

def reachable_zeroless_factorials : ℕ → Finset ℕ
  | 0 => {1}
  | n + 1 =>
    let prev_set := reachable_zeroless_factorials n
    prev_set.biUnion fun m =>
      let prod := (n + 1) * m
      {prod, remove_zeros prod}

lemma ofDigits_zero (l : List ℕ) (hl : ∀ x ∈ l, x = 0) (b : ℕ) : ofDigits b l = 0 := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    rw [ofDigits]
    simp only [Nat.cast_id]
    have hd : d = 0 := hl d (List.mem_cons_self)
    have hl_zero : ∀ x ∈ l, x = 0 := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    rw [hd, ih hl_zero]
    simp

lemma digits_has_nonzero (n : ℕ) (hn : n > 0) : ∃ x ∈ Nat.digits 10 n, x ≠ 0 := by
  by_contra h
  push_neg at h
  have h_zero : ofDigits 10 (Nat.digits 10 n) = 0 := ofDigits_zero _ h _
  have h_eq : ofDigits 10 (Nat.digits 10 n) = n := ofDigits_digits 10 n
  rw [h_eq] at h_zero
  omega

lemma ofDigits_pos (l : List ℕ) (hl : l ≠ []) (h_nz : ∀ x ∈ l, x ≠ 0) : ofDigits (10 : ℕ) l > 0 := by
  induction l with
  | nil => contradiction
  | cons d l ih =>
    rw [ofDigits]
    simp only [Nat.cast_id]
    have hd_nz : d ≠ 0 := h_nz d (List.mem_cons_self)
    have hd_pos : d > 0 := Nat.pos_of_ne_zero hd_nz
    have h_mul_nonneg : 10 * ofDigits (10 : ℕ) l ≥ 0 := Nat.zero_le _
    omega

lemma filter_not_nil {α : Type*} (p : α → Bool) (l : List α) (x : α) (h : x ∈ l) (hx : p x = true) : l.filter p ≠ [] := by
  induction l with
  | nil => contradiction
  | cons y l ih =>
    rw [List.filter_cons]
    split_ifs with hy
    · simp
    · intro h_empty
      have h_mem : x ∈ l := by
        cases h with
        | head => 
          have h_px2 : p x = false := by
            cases h_px : p x with
            | false => rfl
            | true =>
              exfalso
              exact hy h_px
          rw [hx] at h_px2
          contradiction
        | tail _ h_mem => exact h_mem
      exact ih h_mem h_empty

lemma remove_zeros_pos {n : ℕ} (hn : n > 0) : remove_zeros n > 0 := by
  rw [remove_zeros_eq_old]
  have h_has := digits_has_nonzero n hn
  rcases h_has with ⟨x, hx, hx_nz⟩
  have h_not_nil : (Nat.digits 10 n).filter (fun d => d ≠ 0) ≠ [] := by
    have hx_nz_bool : (decide (x ≠ 0)) = true := decide_eq_true hx_nz
    exact filter_not_nil (fun d => decide (d ≠ 0)) (Nat.digits 10 n) x hx hx_nz_bool
  have h_all_nz : ∀ y ∈ (Nat.digits 10 n).filter (fun d => d ≠ 0), y ≠ 0 := by
    intro y hy
    rw [List.mem_filter] at hy
    exact of_decide_eq_true hy.2
  exact ofDigits_pos _ h_not_nil h_all_nz

lemma reachable_pos (n : ℕ) : ∀ m ∈ reachable_zeroless_factorials n, m > 0 := by
  induction n with
  | zero =>
    intro m hm
    simp [reachable_zeroless_factorials] at hm
    rw [hm]
    decide
  | succ n ih =>
    intro m hm
    rw [reachable_zeroless_factorials] at hm
    simp only [mem_biUnion, mem_insert, mem_singleton] at hm
    rcases hm with ⟨m', hm', hm'2⟩
    have hm'_pos := ih m' hm'
    rcases hm'2 with rfl | rfl
    · -- m = (n + 1) * m'
      have h1 : n + 1 > 0 := by omega
      exact Nat.mul_pos h1 hm'_pos
    · -- m = remove_zeros ((n + 1) * m')
      have h1 : n + 1 > 0 := by omega
      have h2 : (n + 1) * m' > 0 := Nat.mul_pos h1 hm'_pos
      exact remove_zeros_pos h2


lemma ofDigits_ten_mod_nine (l : List ℕ) : ofDigits 10 l % 9 = l.sum % 9 := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    rw [ofDigits]
    simp only [Nat.cast_id, List.sum_cons]
    have h_mod : ofDigits 10 l = 9 * (ofDigits 10 l / 9) + (ofDigits 10 l % 9) := (Nat.div_add_mod (ofDigits 10 l) 9).symm
    have h_mod2 : l.sum = 9 * (l.sum / 9) + (l.sum % 9) := (Nat.div_add_mod (l.sum) 9).symm
    omega


lemma ofDigits_ten_mod_three (l : List ℕ) : ofDigits 10 l % 3 = l.sum % 3 := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    rw [ofDigits]
    simp only [Nat.cast_id, List.sum_cons]
    have h_mod : ofDigits 10 l = 3 * (ofDigits 10 l / 3) + (ofDigits 10 l % 3) := (Nat.div_add_mod (ofDigits 10 l) 3).symm
    have h_mod2 : l.sum = 3 * (l.sum / 3) + (l.sum % 3) := (Nat.div_add_mod (l.sum) 3).symm
    omega


lemma sum_filter_ne_zero (l : List ℕ) : (l.filter (fun d => d ≠ 0)).sum = l.sum := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    rw [List.filter_cons]
    split_ifs with hd
    · -- d ≠ 0
      simp only [List.sum_cons]
      rw [ih]
    · -- d = 0
      have hd_eq : d = 0 := by
        by_contra h
        have h2 : decide (d ≠ 0) = true := decide_eq_true h
        exact hd h2
      rw [hd_eq]
      simp only [List.sum_cons, zero_add]
      rw [ih]


lemma remove_zeros_mod_nine (X : ℕ) : remove_zeros X % 9 = X % 9 := by
  rw [remove_zeros_eq_old]
  rw [ofDigits_ten_mod_nine]
  rw [sum_filter_ne_zero]
  rw [← ofDigits_ten_mod_nine]
  rw [Nat.ofDigits_digits]

lemma remove_zeros_mod_three (X : ℕ) : remove_zeros X % 3 = X % 3 := by
  rw [remove_zeros_eq_old]
  rw [ofDigits_ten_mod_three]
  rw [sum_filter_ne_zero]
  rw [← ofDigits_ten_mod_three]
  rw [Nat.ofDigits_digits]


lemma digits_ten_pow_mul (j : ℕ) (X : ℕ) (hX : X > 0) :
    Nat.digits 10 (10^j * X) = List.replicate j 0 ++ Nat.digits 10 X := by
  exact Nat.digits_base_pow_mul (by decide) hX

lemma remove_zeros_ten_pow_mul (j : ℕ) (X : ℕ) (hX : X > 0) :
    remove_zeros (10^j * X) = remove_zeros X := by
  rw [remove_zeros_eq_old, remove_zeros_eq_old]
  rw [digits_ten_pow_mul j X hX]
  have h_filt : (List.replicate j 0 ++ Nat.digits 10 X).filter (fun d => d ≠ 0) = (Nat.digits 10 X).filter (fun d => d ≠ 0) := by
    rw [List.filter_append]
    have h_zero : (List.replicate j 0).filter (fun d => d ≠ 0) = [] := by
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [List.replicate_succ, List.filter_cons]
        simp [ih]
    rw [h_zero, List.nil_append]
  rw [h_filt]



lemma reachable_mod_three (n : ℕ) : ∀ m ∈ reachable_zeroless_factorials n, n ≥ 3 → m % 3 = 0 := by
  induction n with
  | zero =>
    intro m hm hn
    omega
  | succ n ih =>
    intro m hm hn_succ
    rw [reachable_zeroless_factorials] at hm
    simp only [mem_biUnion, mem_insert, mem_singleton] at hm
    rcases hm with ⟨m', hm', hm'2⟩
    have hm_mod_eq : m % 3 = ((n + 1) * m') % 3 := by
      rcases hm'2 with rfl | rfl
      · rfl
      · rw [remove_zeros_mod_three]
    rw [hm_mod_eq]
    have hn_cases : n ≥ 3 ∨ n = 2 := by omega
    rcases hn_cases with hn_ge | rfl
    · have hm'_mod := ih m' hm' hn_ge
      have h_div : m' = 3 * (m' / 3) := by
        have : m' % 3 = 0 := hm'_mod
        omega
      rw [h_div]
      have h_mul : (n + 1) * (3 * (m' / 3)) = 3 * ((n + 1) * (m' / 3)) := by ring
      rw [h_mul]
      omega
    · omega


lemma reachable_mod_nine (n : ℕ) : ∀ m ∈ reachable_zeroless_factorials n, n ≥ 6 → m % 9 = 0 := by
  induction n with
  | zero =>
    intro m hm hn
    omega
  | succ n ih =>
    intro m hm hn_succ
    rw [reachable_zeroless_factorials] at hm
    simp only [mem_biUnion, mem_insert, mem_singleton] at hm
    rcases hm with ⟨m', hm', hm'2⟩
    have hm_mod_eq : m % 9 = ((n + 1) * m') % 9 := by
      rcases hm'2 with rfl | rfl
      · rfl
      · rw [remove_zeros_mod_nine]
    rw [hm_mod_eq]
    have hn_cases : n ≥ 6 ∨ n = 5 := by omega
    rcases hn_cases with hn_ge | rfl
    · have hm'_mod := ih m' hm' hn_ge
      have h_div : m' = 9 * (m' / 9) := by
        have : m' % 9 = 0 := hm'_mod
        omega
      rw [h_div]
      have h_mul : (n + 1) * (9 * (m' / 9)) = 9 * ((n + 1) * (m' / 9)) := by ring
      rw [h_mul]
      omega
    · have hm'_mod3 := reachable_mod_three 5 m' hm' (by decide)
      have h_div : m' = 3 * (m' / 3) := by
        have : m' % 3 = 0 := hm'_mod3
        omega
      rw [h_div]
      have h_mul : 6 * (3 * (m' / 3)) = 9 * (2 * (m' / 3)) := by ring
      rw [h_mul]
      omega

lemma reachable_ge_nine_of_ge_six (n : ℕ) (hn : n ≥ 6) : ∀ m ∈ reachable_zeroless_factorials n, m ≥ 9 := by
  intro m hm
  have h_mod := reachable_mod_nine n m hm hn
  have h_pos := reachable_pos n m hm
  omega


lemma remove_zeros_of_lt (x : ℕ) (hx : x ≠ 0) (hlt : x < 10) : remove_zeros x = x := by
  rw [remove_zeros_eq_old]
  rw [Nat.digits_of_lt 10 x hx hlt]
  have h_filt : [x].filter (fun d => d ≠ 0) = [x] := by
    rw [List.filter_cons]
    split_ifs with h
    · rfl
    · exfalso
      have h_dec : x = 0 := by
        by_contra h2
        have h3 : decide (x ≠ 0) = true := decide_eq_true h2
        exact h h3
      exact hx h_dec
  rw [h_filt]
  rfl




lemma reachable_zero : reachable_zeroless_factorials 0 = {1} := rfl
lemma reachable_one : reachable_zeroless_factorials 1 = {1} := by decide
lemma reachable_two : reachable_zeroless_factorials 2 = {2} := by decide
lemma reachable_three : reachable_zeroless_factorials 3 = {6} := by decide
lemma reachable_four : reachable_zeroless_factorials 4 = {24} := by decide
lemma reachable_five : reachable_zeroless_factorials 5 = {12, 120} := by decide

lemma reachable_ge_n_of_le_nine (n : ℕ) (hn : n ≤ 9) : ∀ m ∈ reachable_zeroless_factorials n, m ≥ n := by
  intro m hm
  interval_cases n
  · omega
  · rw [reachable_one] at hm; simp at hm; rw [hm]
  · rw [reachable_two] at hm; simp at hm; rw [hm]
  · rw [reachable_three] at hm; simp at hm; rw [hm]; decide
  · rw [reachable_four] at hm; simp at hm; rw [hm]; decide
  · rw [reachable_five] at hm; simp at hm; rcases hm with rfl | rfl <;> omega
  · have h_ge := reachable_ge_nine_of_ge_six 6 (by omega) m hm
    omega
  · have h_ge := reachable_ge_nine_of_ge_six 7 (by omega) m hm
    omega
  · have h_ge := reachable_ge_nine_of_ge_six 8 (by omega) m hm
    omega
  · have h_ge := reachable_ge_nine_of_ge_six 9 (by omega) m hm
    omega

lemma reachable_nonempty (n : ℕ) : (reachable_zeroless_factorials n).Nonempty := by
  induction n with
  | zero => exact Finset.singleton_nonempty 1
  | succ n ih =>
    rcases ih with ⟨m, hm⟩
    let prod := (n + 1) * m
    exact ⟨prod, Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_insert_self prod _⟩⟩

noncomputable def a (n : ℕ) : ℕ :=
  (reachable_zeroless_factorials n).min' (reachable_nonempty n)

lemma a_ge_n_of_le_nine (n : ℕ) (hn : n ≤ 9) : a n ≥ n := by
  unfold a
  exact reachable_ge_n_of_le_nine n hn _ (Finset.min'_mem _ _)

lemma a_ge_nine_of_ge_six (n : ℕ) (hn : n ≥ 6) : a n ≥ 9 := by
  unfold a
  exact reachable_ge_nine_of_ge_six n hn _ (Finset.min'_mem _ _)


lemma card_filter_lt_eq_zero_iff (s : Finset ℕ) (x : ℕ) :
    (s.filter (fun y => y < x)).card = 0 ↔ ∀ y ∈ s, x ≤ y := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h y hy
    by_contra h_lt
    push_neg at h_lt
    have h_mem : y ∈ s.filter (fun y => y < x) := by
      rw [Finset.mem_filter]
      exact ⟨hy, h_lt⟩
    exact h y h_mem
  · intro h y hy
    rw [Finset.mem_filter] at hy
    have h_ge := h y hy.1
    omega


lemma remove_zeros_idemp (n : ℕ) : remove_zeros (remove_zeros n) = remove_zeros n := by
  rw [remove_zeros_eq_old (remove_zeros n)]
  have h_rem : remove_zeros n = ofDigits 10 ((Nat.digits 10 n).filter (fun d => d ≠ 0)) := remove_zeros_eq_old n
  rw [h_rem]
  set L := (Nat.digits 10 n).filter (fun d => d ≠ 0)
  have h_lt : ∀ l ∈ L, l < 10 := by
    intro l hl
    rw [List.mem_filter] at hl
    exact Nat.digits_lt_base (by decide) hl.1
  have h_nz : ∀ h : L ≠ [], L.getLast h ≠ 0 := by
    intro h
    have h_mem : L.getLast h ∈ L := List.getLast_mem h
    rw [List.mem_filter] at h_mem
    exact of_decide_eq_true h_mem.2
  have h_dig : Nat.digits 10 (ofDigits 10 L) = L := Nat.digits_ofDigits 10 (by decide) L h_lt h_nz
  rw [h_dig]
  have h_filt : L.filter (fun d => d ≠ 0) = L := by
    apply List.filter_eq_self.mpr
    intro l hl
    rw [List.mem_filter] at hl
    exact hl.2
  rw [h_filt]

lemma remove_zeros_mem (n : ℕ) : ∀ m ∈ reachable_zeroless_factorials n, remove_zeros m ∈ reachable_zeroless_factorials n := by
  induction n with
  | zero =>
    intro m hm
    rw [reachable_zeroless_factorials] at hm
    simp at hm
    rw [hm]
    unfold remove_zeros digitsNat ofDigitsNat
    decide
  | succ n ih =>
    intro m hm
    rw [reachable_zeroless_factorials] at hm
    simp only [mem_biUnion, mem_insert, mem_singleton] at hm
    rcases hm with ⟨m', hm', hm'2⟩
    rcases hm'2 with rfl | rfl
    · rw [reachable_zeroless_factorials]
      simp only [mem_biUnion, mem_insert, mem_singleton]
      use m'
      refine ⟨hm', Or.inr rfl⟩
    · rw [remove_zeros_idemp]
      rw [reachable_zeroless_factorials]
      simp only [mem_biUnion, mem_insert, mem_singleton]
      use m'
      refine ⟨hm', Or.inr rfl⟩

lemma remove_zeros_ge_a (n : ℕ) : ∀ m ∈ reachable_zeroless_factorials n, remove_zeros m ≥ a n := by
  intro m hm
  have h_mem := remove_zeros_mem n m hm
  unfold a
  exact Finset.min'_le _ (remove_zeros m) h_mem







lemma filter_length_le (L : List ℕ) : (L.filter (fun d => d ≠ 0)).length ≤ L.length := by
  induction L with
  | nil => rfl
  | cons d L' ih =>
    rw [List.filter_cons]
    by_cases hd : d = 0
    · subst hd
      have h_cond : ¬ (0 ≠ 0) := by decide
      have h_dec : (decide (0 ≠ 0)) = false := decide_eq_false h_cond
      rw [h_dec]
      rw [if_neg (by decide)]
      simp only [List.length_cons]
      omega
    · have h_cond : d ≠ 0 := hd
      have h_dec : (decide (d ≠ 0)) = true := decide_eq_true h_cond
      rw [h_dec]
      rw [if_pos (by decide)]
      simp only [List.length_cons]
      omega

lemma ofDigits_filter_le (p : ℕ → Bool) (L : List ℕ) : ofDigits 10 (L.filter p) ≤ ofDigits 10 L := by
  induction L with
  | nil => rfl
  | cons d L' ih =>
    rw [List.filter_cons]
    split_ifs with hd
    · rw [ofDigits, ofDigits]
      simp only [Nat.cast_id]
      omega
    · rw [ofDigits]
      simp only [Nat.cast_id]
      calc ofDigits 10 (List.filter p L') ≤ ofDigits 10 L' := ih
      _ ≤ d + 10 * ofDigits 10 L' := by omega

lemma ofDigits_le_filter_mul_ten_pow_precise (L : List ℕ) :
    ofDigits 10 L ≤ ofDigits 10 (L.filter (fun d => d ≠ 0)) * 10^(L.length - (L.filter (fun d => d ≠ 0)).length) := by
  induction L with
  | nil => rfl
  | cons d L' ih =>
    rw [List.filter_cons]
    by_cases hd : d = 0
    · subst hd
      have h_cond : ¬ (0 ≠ 0) := by decide
      have h_dec : (decide (0 ≠ 0)) = false := decide_eq_false h_cond
      rw [h_dec]
      rw [if_neg (by decide)]
      simp only [List.length_cons]
      rw [ofDigits]
      simp only [Nat.cast_id, zero_add]
      have h_sub : L'.length + 1 - (L'.filter (fun d => d ≠ 0)).length =
                   (L'.length - (L'.filter (fun d => d ≠ 0)).length) + 1 := by
        have := filter_length_le L'
        omega
      rw [h_sub]
      have h_pow : 10^((L'.length - (L'.filter (fun d => d ≠ 0)).length) + 1) =
                   10^(L'.length - (L'.filter (fun d => d ≠ 0)).length) * 10 := by ring
      rw [h_pow]
      have h_mul : ofDigits 10 (L'.filter (fun d => d ≠ 0)) * (10^(L'.length - (L'.filter (fun d => d ≠ 0)).length) * 10) =
                   (ofDigits 10 (L'.filter (fun d => d ≠ 0)) * 10^(L'.length - (L'.filter (fun d => d ≠ 0)).length)) * 10 := by ring
      rw [h_mul]
      omega
    · have h_cond : d ≠ 0 := hd
      have h_dec : (decide (d ≠ 0)) = true := decide_eq_true h_cond
      rw [h_dec]
      rw [if_pos (by decide)]
      simp only [List.length_cons]
      rw [ofDigits, ofDigits]
      simp only [Nat.cast_id]
      have h_sub2 : L'.length + 1 - ((L'.filter (fun d => d ≠ 0)).length + 1) =
                    L'.length - (L'.filter (fun d => d ≠ 0)).length := by
        omega
      rw [h_sub2]
      have h1 : d ≤ d * 10^(L'.length - (L'.filter (fun d => d ≠ 0)).length) := by
        have h_pos : 10^(L'.length - (L'.filter (fun d => d ≠ 0)).length) ≥ 1 := Nat.one_le_pow _ 10 (by decide)
        exact Nat.le_mul_of_pos_right d h_pos
      have h2 : 10 * ofDigits 10 L' ≤ 10 * ofDigits 10 (L'.filter (fun d => d ≠ 0)) * 10^(L'.length - (L'.filter (fun d => d ≠ 0)).length) := by
        have h_mul1 : 10 * ofDigits 10 L' ≤ 10 * (ofDigits 10 (L'.filter (fun d => d ≠ 0)) * 10^(L'.length - (L'.filter (fun d => d ≠ 0)).length)) := Nat.mul_le_mul_left 10 ih
        have h_eq_pow : 10 * (ofDigits 10 (L'.filter (fun d => d ≠ 0)) * 10^(L'.length - (L'.filter (fun d => d ≠ 0)).length)) =
                        10 * ofDigits 10 (L'.filter (fun d => d ≠ 0)) * 10^(L'.length - (L'.filter (fun d => d ≠ 0)).length) := by ring
        rw [h_eq_pow] at h_mul1
        exact h_mul1
      have h_dist : (d + 10 * ofDigits 10 (L'.filter (fun d => d ≠ 0))) * 10^(L'.length - (L'.filter (fun d => d ≠ 0)).length) =
                    d * 10^(L'.length - (L'.filter (fun d => d ≠ 0)).length) + 10 * ofDigits 10 (L'.filter (fun d => d ≠ 0)) * 10^(L'.length - (L'.filter (fun d => d ≠ 0)).length) := by ring
      rw [h_dist]
      omega

lemma ofDigits_ge_sum (L : List ℕ) : ofDigits 10 L ≥ L.sum := by
  induction L with
  | nil => rfl
  | cons d L' ih =>
    rw [ofDigits]
    simp only [Nat.cast_id, List.sum_cons]
    have h_mul : 10 * ofDigits 10 L' ≥ ofDigits 10 L' := Nat.le_mul_of_pos_left _ (by decide)
    omega

lemma ten_pow_succ_minus_one_gt (k : ℕ) (hk : k > 0) : k < 10^(k+1) - 1 := by
  induction k with
  | zero => contradiction
  | succ k ih =>
    by_cases hk_zero : k = 0
    · subst hk_zero
      decide
    · have hk_pos : k > 0 := Nat.pos_of_ne_zero hk_zero
      have h_ih := ih hk_pos
      have h_pow : 10^(k+2) = 10^(k+1) * 10 := by ring
      have h_pow_pos : 10^(k+1) > 0 := Nat.pow_pos (by decide)
      have h_sub : 10^(k+2) - 1 = (10^(k+1) - 1) * 10 + 9 := by
        omega
      omega

lemma ten_pow_sub_one_mod_ten (k : ℕ) : (10^(k+1) - 1) % 10 = 9 := by
  have h1 : 10^(k+1) = 10 * 10^k := by ring
  have h2 : 10^k = (10^k - 1) + 1 := (Nat.sub_add_cancel (Nat.pow_pos (by decide))).symm
  rw [h2] at h1
  have h3 : 10 * (10^k - 1 + 1) = 10 * (10^k - 1) + 10 := by ring
  rw [h3] at h1
  have h4 : 10^(k+1) - 1 = 10 * (10^k - 1) + 9 := by
    omega
  omega

lemma coprime_ten_pow_minus_one (k : ℕ) : Nat.Coprime (10^(k+1) - 1) 10 := by
  rw [Nat.Coprime]
  rw [Nat.gcd_comm]
  rw [Nat.gcd_rec]
  rw [ten_pow_sub_one_mod_ten]
  decide

lemma coprime_dvd_general (k : ℕ) (j : ℕ) (p : ℕ) (h : (10^(k+1) - 1) ∣ j * 10^p) : (10^(k+1) - 1) ∣ j := by
  have h_cop : Nat.Coprime (10^(k+1) - 1) (10^p) := Nat.Coprime.pow_right p (coprime_ten_pow_minus_one k)
  exact Nat.Coprime.dvd_of_dvd_mul_right h_cop h

lemma not_dvd_of_lt (k : ℕ) (hk : k > 0) : ¬ (10^(k+1) - 1) ∣ k := by
  intro h
  have h_le := Nat.le_of_dvd hk h
  have h_gt := ten_pow_succ_minus_one_gt k hk
  omega

lemma eq_mul_contradiction_general (k : ℕ) (hk : k > 0) (j : ℕ) (hj : j > 0) (hj_le : j ≤ k) (d : ℕ) (p : ℕ) :
    (10^(k+1) - 1) * d ≠ j * 10^p := by
  intro h_eq
  have h_dvd : (10^(k+1) - 1) ∣ j * 10^p := by
    use d
    exact h_eq.symm
  have h_dvd_j : (10^(k+1) - 1) ∣ j := coprime_dvd_general k j p h_dvd
  have h_gt := ten_pow_succ_minus_one_gt k hk
  have h_not : ¬ (10^(k+1) - 1) ∣ j := by
    intro h
    have h_le := Nat.le_of_dvd hj h
    omega
  exact h_not h_dvd_j

lemma a_ten_pow_ge (k : ℕ) (hk : k > 0) : a (10^k) ≥ min (10^k) (a (10^k - 1)) := by
  unfold a
  rw [ge_iff_le, Finset.le_min'_iff]
  intro m hm
  have h_pow_pos : 10^k > 0 := Nat.pow_pos (by decide)
  have h_eq : 10^k = (10^k - 1) + 1 := (Nat.sub_add_cancel h_pow_pos).symm
  have h_eq2 : (10^k - 1) + 1 = 10^k := Nat.sub_add_cancel h_pow_pos
  rw [h_eq] at hm
  rw [reachable_zeroless_factorials] at hm
  simp only [mem_biUnion, mem_insert, mem_singleton] at hm
  rcases hm with ⟨m', hm', hm'2⟩
  rw [h_eq2] at hm'2
  rcases hm'2 with rfl | rfl
  · have hm'_pos := reachable_pos (10^k - 1) m' hm'
    have : m' ≥ 1 := by omega
    have h_ge : 10^k * m' ≥ 10^k := by
      calc 10^k * m' ≥ 10^k * 1 := Nat.mul_le_mul_left _ this
      _ = 10^k := by ring
    exact le_trans (Nat.min_le_left (10^k) (a (10^k - 1))) h_ge
  · have hm'_pos := reachable_pos (10^k - 1) m' hm'
    rw [remove_zeros_ten_pow_mul k m' hm'_pos]
    have h_ge := remove_zeros_ge_a (10^k - 1) m' hm'
    exact le_trans (Nat.min_le_right (10^k) (a (10^k - 1))) h_ge

lemma a_5_ge : a 5 ≥ 12 := by
  unfold a
  rw [ge_iff_le, Finset.le_min'_iff, ← card_filter_lt_eq_zero_iff]
  decide

lemma a_15_ge : a 15 ≥ 13968 := by
  unfold a
  rw [ge_iff_le, Finset.le_min'_iff]
  decide

lemma a_20_ge : a 20 ≥ 269154 := by
  unfold a
  rw [ge_iff_le, Finset.le_min'_iff]
  decide

lemma reachable_ge_a_ten_pow (k : ℕ) (n : ℕ) (hn : n ≥ 10^k) :
    ∀ m ∈ reachable_zeroless_factorials n, m ≥ a (10^k) := by
  induction n with
  | zero =>
    intro m hm
    by_cases hk : k = 0
    · subst hk
      unfold a
      exact Finset.min'_le _ m hm
    · have : 10^k > 0 := Nat.pow_pos (by decide)
      omega
  | succ n ih =>
    intro m hm
    by_cases hn_ge : n ≥ 10^k
    · -- n ≥ 10^k, so we can use ih hn_ge
      rw [reachable_zeroless_factorials] at hm
      simp only [mem_biUnion, mem_insert, mem_singleton] at hm
      rcases hm with ⟨m', hm', hm'2⟩
      have hm'_ge := ih hn_ge m' hm'
      rcases hm'2 with rfl | rfl
      · have : m' ≥ 1 := reachable_pos n m' hm'
        calc (n + 1) * m' ≥ 1 * m' := Nat.mul_le_mul_right _ (by omega)
        _ = m' := by ring
        _ ≥ a (10^k) := hm'_ge
      · -- m = remove_zeros ((n + 1) * m')
        have h_rem_ge := remove_zeros_ge_a n m' hm'
        have h_an_ge : a n ≥ a (10^k) := by
          unfold a
          rw [ge_iff_le, Finset.le_min'_iff]
          exact ih hn_ge
        sorry
    · -- n < 10^k. Since n + 1 ≥ 10^k, we must have n + 1 = 10^k.
      have hn_eq : n + 1 = 10^k := by omega
      rw [hn_eq] at hm
      unfold a
      exact Finset.min'_le _ m hm

lemma a_ten_pow_ge_k (k : ℕ) : a (10^k) ≥ k := by
  induction k with
  | zero =>
    unfold a
    rw [ge_iff_le, Finset.le_min'_iff]
    intro m hm
    have := reachable_pos 1 m hm
    omega
  | succ k ih =>
    by_cases hk_zero : k = 0
    · subst hk_zero
      unfold a
      rw [ge_iff_le, Finset.le_min'_iff]
      intro m hm
      have := reachable_pos 10 m hm
      omega
    · have hk_pos : k > 0 := Nat.pos_of_ne_zero hk_zero
      have h_ge := a_ten_pow_ge (k+1) (by omega)
      -- h_ge : a (10^(k+1)) ≥ min (10^(k+1)) (a (10^(k+1) - 1))
      have h_min_ge : min (10^(k+1)) (a (10^(k+1) - 1)) ≥ k + 1 := by
        rw [ge_iff_le]
        rw [Nat.le_min]
        constructor
        · have := ten_pow_succ_gt_self k
          omega
        · -- We want to prove a (10^(k+1) - 1) ≥ k + 1
          -- Since 10^(k+1) - 1 ≥ 10^k, we can use reachable_ge_a_ten_pow!
          have h_ge10k : 10^(k+1) - 1 ≥ 10^k := by
            have : 10^(k+1) - 1 = 10 * 10^k - 1 := by ring
            omega
          have h_ge_a := reachable_ge_a_ten_pow k (10^(k+1) - 1) h_ge10k
          have h_a_ge : a (10^(k+1) - 1) ≥ a (10^k) := by
            unfold a
            rw [ge_iff_le, Finset.le_min'_iff]
            exact h_ge_a
          -- So a (10^(k+1) - 1) ≥ a (10^k) ≥ k.
          -- Since 10^(k+1) - 1 ≥ 6 (since k > 0), a (10^(k+1) - 1) is a multiple of 9.
          have h_mod6 : 10^(k+1) - 1 ≥ 6 := by
            have : 10^(k+1) ≥ 10 := Nat.pow_le_pow_right (by decide : 1 ≤ 10) (by omega : 1 ≤ k+1)
            omega
          have h_mod9 : a (10^(k+1) - 1) % 9 = 0 := by
            unfold a
            exact reachable_mod_nine (10^(k+1) - 1) _ (Finset.min'_mem _ _) h_mod6
          -- If a (10^(k+1) - 1) < k + 1:
          by_contra h_lt
          push_neg at h_lt
          have h_eq : a (10^(k+1) - 1) = k := by omega
          rw [h_eq] at h_mod9
          -- So k is a multiple of 9, let k = 9 * j.
          have h_div : k = 9 * (k / 9) := (Nat.div_add_mod k 9).symm.trans (by omega)
          -- Now we look at the elements of reachable_zeroless_factorials (10^(k+1) - 1).
          -- Since a (10^(k+1) - 1) = k, the minimum is k.
          -- So k ∈ reachable_zeroless_factorials (10^(k+1) - 1).
          have hk_mem : k ∈ reachable_zeroless_factorials (10^(k+1) - 1) := by
            have := Finset.min'_mem (reachable_zeroless_factorials (10^(k+1) - 1)) (reachable_nonempty (10^(k+1) - 1))
            change a (10^(k+1) - 1) ∈ reachable_zeroless_factorials (10^(k+1) - 1) at this
            rw [h_eq] at this
            exact this
          -- 10^(k+1) - 1 = (10^(k+1) - 2) + 1
          have h_eq_minus_one : 10^(k+1) - 1 = (10^(k+1) - 2) + 1 := by omega
          have h_eq_minus_two : (10^(k+1) - 2) + 1 = 10^(k+1) - 1 := by omega
          have hk_mem2 := hk_mem
          rw [h_eq_minus_one] at hk_mem2
          rw [reachable_zeroless_factorials] at hk_mem2
          simp only [mem_biUnion, mem_insert, mem_singleton] at hk_mem2
          rcases hk_mem2 with ⟨m'', hm'', hm''2⟩
          rw [h_eq_minus_two] at hm''2
          rcases hm''2 with h_prod | h_rem
          · -- k = (10^(k+1) - 1) * m''
            have hm''_pos := reachable_pos (10^(k+1) - 2) m'' hm''
            have h_ge_prod : (10^(k+1) - 1) * m'' ≥ 10^(k+1) - 1 := by
              calc (10^(k+1) - 1) * m'' ≥ (10^(k+1) - 1) * 1 := Nat.mul_le_mul_left _ hm''_pos
              _ = 10^(k+1) - 1 := by ring
            have : 10^(k+1) - 1 > k := by
              have := ten_pow_succ_minus_one_gt k hk_pos
              omega
            omega
          · -- k = remove_zeros ((10^(k+1) - 1) * m'')
            have hm''_pos := reachable_pos (10^(k+1) - 2) m'' hm''
            -- Since m'' is in reachable_zeroless_factorials (10^(k+1) - 2).
            -- Since 10^(k+1) - 2 ≥ 10^k, by reachable_ge_a_ten_pow we have m'' ≥ a (10^k) ≥ k.
            have h_ge10k_2 : 10^(k+1) - 2 ≥ 10^k := by
              rcases k with _ | k'
              · decide
              · have : 10^(k'+2) = 10 * 10^(k'+1) := by ring
                omega
            have hm''_ge_a := reachable_ge_a_ten_pow k (10^(k+1) - 2) h_ge10k_2 m'' hm''
            have hm''_ge_k : m'' ≥ k := by omega
            -- Since k is a multiple of 9, and k > 0.
            -- (10^(k+1) - 1) * m'' = k * 10^p is impossible?
            -- Wait, does remove_zeros X = k imply X = k * 10^p?
            -- Let's see: since k is a multiple of 9, and k > 0, we must have k ≥ 9.
            -- If k = 9:
            -- Then remove_zeros ((10^(k+1) - 1) * m'') = 9.
            -- So (10^(k+1) - 1) * m'' = 9 * 10^p.
            -- Which contradicts eq_mul_contradiction_general k hk_pos 9 (by decide) (by decide) m'' p!
            -- Wait, what if k > 9?
            -- Can we just do by_cases on k < 9 and k ≥ 9?
            -- If k < 9, then since k % 9 = 0 and k > 0, k = 9.
            -- What if k > 9?
            -- Actually, if we can prove k < 9 is always true for the B case we are interested in?
            -- No, B can be larger.
            -- But wait!
            -- Is there any other way?
            sorry
      omega

theorem oeis_a374265_conjecture_1_boundedness.disproof : ¬ ∃ B : ℕ, ∀ n : ℕ, a n ≤ B := by
  intro ⟨B, hB⟩
  have h_cases : B < 9 ∨ B < 18 ∨ B < 13968 ∨ B < 269154 ∨ B ≥ 269154 := by omega
  rcases h_cases with h_lt9 | h_lt18 | h_lt13968 | h_lt269154 | h_ge269154
  · have h_le := hB (B + 1)
    have h_ge_n := a_ge_n_of_le_nine (B + 1) (by omega)
    omega
  · have h_le := hB 18
    have h_ge18 : a 18 ≥ 18 := by
      unfold a
      rw [ge_iff_le, Finset.le_min'_iff]
      decide
    omega
  · have h_le := hB 15
    have h_ge13968 := a_15_ge
    omega
  · have h_le := hB 20
    have h_ge269154 := a_20_ge
    omega
  · have h_le := hB (10^(B + 1))
    have h_ge : a (10^(B + 1)) ≥ B + 1 := a_ten_pow_ge_k (B + 1)
    omega

