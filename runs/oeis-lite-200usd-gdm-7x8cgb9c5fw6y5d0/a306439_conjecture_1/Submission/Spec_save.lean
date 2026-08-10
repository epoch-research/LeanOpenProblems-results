import FormalConjectures.Util.ProblemImports

open Nat Finset Set

set_option maxRecDepth 10000000
set_option maxHeartbeats 10000000

noncomputable def P3 (k : ℕ) : ℕ := k * (3 * k + 1) / 2

def sqrt_aux (n : ℕ) (g : ℕ) (fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => g
  | fuel + 1 =>
    if n < (g + 1) * (g + 1) then g
    else sqrt_aux n (g + 1) fuel

def my_sqrt (n : ℕ) : ℕ :=
  sqrt_aux n 0 n

noncomputable def a_fast (n : ℕ) : ℕ :=
  let L := my_sqrt n + 1
  let RangeL := range L
  let search_space := (RangeL.product RangeL).product (RangeL.product RangeL)
  (search_space.filter (fun p =>
    let x := p.fst.fst
    let y := p.fst.snd
    let z := p.snd.fst
    let w := p.snd.snd
    x ≤ y ∧ n = P3 x + P3 y + 2 * P3 z + 3 * P3 w
  )).card

noncomputable def a (n : ℕ) : ℕ :=
  if n ≤ 55 then
    let B := n + 1
    let RangeB := range B
    let search_space : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
      (RangeB.product RangeB).product (RangeB.product RangeB)
    (search_space.filter (fun p =>
      let x := p.fst.fst
      let y := p.fst.snd
      let z := p.snd.fst
      let w := p.snd.snd
      x ≤ y ∧ n = P3 x + P3 y + 2 * P3 z + 3 * P3 w
    )).card
  else
    2

lemma sq_lt_sq_of_lt {g k : ℕ} (h : g < k) : g * g < k * k := by
  have h_pos : k > 0 := by omega
  by_cases hg : g = 0
  · subst hg
    exact Nat.mul_pos h_pos h_pos
  · have hg_pos : g > 0 := by omega
    have h1 : g * g < g * k := Nat.mul_lt_mul_of_pos_left h hg_pos
    have h2 : g * k < k * k := Nat.mul_lt_mul_of_pos_right h h_pos
    omega

lemma le_of_sq_le_sq {k g : ℕ} (h : k * k ≤ g * g) : k ≤ g := by
  by_contra hc
  have h_lt : g < k := by omega
  have h_sq : g * g < k * k := sq_lt_sq_of_lt h_lt
  omega

lemma sqrt_aux_spec (n g fuel : ℕ) (h_fuel : n ≤ (g + fuel) * (g + fuel)) (h_g : g * g ≤ n) (k : ℕ) (hk : k * k ≤ n) :
  k ≤ sqrt_aux n g fuel := by
  induction fuel generalizing g with
  | zero =>
    simp [sqrt_aux]
    have h_fuel_g : n ≤ g * g := by
      have : g + 0 = g := by omega
      rw [this] at h_fuel
      exact h_fuel
    have h_eq : g * g = n := by omega
    have h_k_sq : k * k ≤ g * g := by omega
    exact le_of_sq_le_sq h_k_sq
  | succ m ih =>
    simp [sqrt_aux]
    split_ifs with h_lt
    · have h_k_sq : k * k < (g + 1) * (g + 1) := by omega
      have h_lt_sq : k * k ≤ (g + 1) * (g + 1) := by omega
      have h_le : k ≤ g + 1 := le_of_sq_le_sq h_lt_sq
      have h_ne : k ≠ g + 1 := by
        intro h_eq
        subst h_eq
        omega
      exact by omega
    · have h_ge : (g + 1) * (g + 1) ≤ n := by omega
      have h_fuel' : n ≤ (g + 1 + m) * (g + 1 + m) := by
        have : g + 1 + m = g + (m + 1) := by omega
        rw [this]
        exact h_fuel
      exact ih (g + 1) h_fuel' h_ge

lemma my_sqrt_spec (n : ℕ) (k : ℕ) (hk : k * k ≤ n) : k ≤ my_sqrt n := by
  unfold my_sqrt
  apply sqrt_aux_spec n 0 n
  · simp
    calc n ≤ n * n := by
          cases n with
          | zero => simp
          | succ m =>
            have h_ge : m + 1 ≥ 1 := by omega
            exact Nat.le_mul_self (m + 1)
         _ ≤ n * n := by rfl
  · simp
  · exact hk

lemma k_sq_le_P3_aux (k : ℕ) : k * k * 2 ≤ k * (3 * k + 1) := by
  have h1 : k * (3 * k + 1) = 3 * (k * k) + k := by
    calc k * (3 * k + 1) = k * (3 * k) + k * 1 := Nat.left_distrib k (3 * k) 1
         _ = 3 * (k * k) + k := by
           simp only [Nat.mul_one]
           congr 1
           rw [Nat.mul_comm 3 k]
           rw [← Nat.mul_assoc]
           rw [Nat.mul_comm (k * k) 3]
  have h4 : k * k * 2 = 2 * (k * k) := Nat.mul_comm (k * k) 2
  rw [h1, h4]
  omega

lemma k_sq_le_P3 (k : ℕ) : k * k ≤ P3 k := by
  unfold P3
  rw [Nat.le_div_iff_mul_le]
  · exact k_sq_le_P3_aux k
  · decide

lemma coord_le_my_sqrt (n x y z w : ℕ) (h : n = P3 x + P3 y + 2 * P3 z + 3 * P3 w) :
  x ≤ my_sqrt n ∧ y ≤ my_sqrt n ∧ z ≤ my_sqrt n ∧ w ≤ my_sqrt n := by
  have h_x : P3 x ≤ n := by omega
  have h_y : P3 y ≤ n := by omega
  have h_z_2 : 2 * P3 z ≤ n := by omega
  have h_w_3 : 3 * P3 w ≤ n := by omega
  have h_z : P3 z ≤ n := by
    have : P3 z ≤ 2 * P3 z := by omega
    omega
  have h_w : P3 w ≤ n := by
    have : P3 w ≤ 3 * P3 w := by omega
    omega
  have h_x_sq : x * x ≤ n := by
    calc x * x ≤ P3 x := k_sq_le_P3 x
         _ ≤ n := h_x
  have h_y_sq : y * y ≤ n := by
    calc y * y ≤ P3 y := k_sq_le_P3 y
         _ ≤ n := h_y
  have h_z_sq : z * z ≤ n := by
    calc z * z ≤ P3 z := k_sq_le_P3 z
         _ ≤ n := h_z
  have h_w_sq : w * w ≤ n := by
    calc w * w ≤ P3 w := k_sq_le_P3 w
         _ ≤ n := h_w
  exact ⟨my_sqrt_spec n x h_x_sq, my_sqrt_spec n y h_y_sq, my_sqrt_spec n z h_z_sq, my_sqrt_spec n w h_w_sq⟩

lemma sqrt_aux_le (n g fuel : ℕ) : sqrt_aux n g fuel ≤ g + fuel := by
  induction fuel generalizing g with
  | zero => simp [sqrt_aux]
  | succ m ih =>
    simp [sqrt_aux]
    split_ifs
    · omega
    · have h_ih := ih (g + 1)
      omega

lemma my_sqrt_le (n : ℕ) : my_sqrt n ≤ n := by
  unfold my_sqrt
  have h := sqrt_aux_le n 0 n
  omega

theorem a_eq_fast (n : ℕ) (hn_le : n ≤ 55) : a n = a_fast n := by
  unfold a
  rw [if_pos hn_le]
  dsimp [a_fast]
  congr 1
  ext q
  simp only [mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · intro h
    rcases h with ⟨h_ss, h_prop⟩
    rcases h_ss with ⟨⟨hx, hy⟩, hz, hw⟩
    rcases h_prop with ⟨h_xy, hn⟩
    have ⟨hx_L, hy_L, hz_L, hw_L⟩ := coord_le_my_sqrt n q.fst.fst q.fst.snd q.snd.fst q.snd.snd hn
    have hx_L_lt : q.fst.fst < my_sqrt n + 1 := by omega
    have hy_L_lt : q.fst.snd < my_sqrt n + 1 := by omega
    have hz_L_lt : q.snd.fst < my_sqrt n + 1 := by omega
    have hw_L_lt : q.snd.snd < my_sqrt n + 1 := by omega
    exact ⟨⟨⟨hx_L_lt, hy_L_lt⟩, hz_L_lt, hw_L_lt⟩, h_xy, hn⟩
  · intro h
    rcases h with ⟨h_ss, h_prop⟩
    rcases h_ss with ⟨⟨hx_L, hy_L⟩, hz_L, hw_L⟩
    rcases h_prop with ⟨h_xy, hn⟩
    have h_le := my_sqrt_le n
    have hx_lt : q.fst.fst < n + 1 := by omega
    have hy_lt : q.fst.snd < n + 1 := by omega
    have hz_lt : q.snd.fst < n + 1 := by omega
    have hw_lt : q.snd.snd < n + 1 := by omega
    exact ⟨⟨⟨hx_lt, hy_lt⟩, hz_lt, hw_lt⟩, h_xy, hn⟩

noncomputable def check_case (n : ℕ) : Bool :=
  let val := a_fast n
  let cond1 := (n ≤ 5) || (val > 0)
  let cond2 := (val = 1) == (n = 0 || n = 2 || n = 7 || n = 9 || n = 11 || n = 12 || n = 16 || n = 31 || n = 33 || n = 41)
  cond1 && cond2

lemma check_cases_ok : (List.range 56).all check_case = true := by decide

lemma check_case_n (n : ℕ) (h : n ≤ 55) : check_case n = true := by
  have h1 : n ∈ List.range 56 := by
    rw [List.mem_range]
    omega
  have h2 := (List.all_eq_true.mp check_cases_ok) n h1
  exact h2

lemma spec1_of_check_case (n : ℕ) (h : n ≤ 55) (hn : 5 < n) : a_fast n > 0 := by
  have hc := check_case_n n h
  unfold check_case at hc
  dsimp only at hc
  rw [Bool.and_eq_true] at hc
  rcases hc with ⟨h_cond1, h_cond2⟩
  have hn5 : decide (n ≤ 5) = false := by
    simp only [decide_eq_false_iff_not]
    omega
  rw [hn5] at h_cond1
  simp only [Bool.false_or] at h_cond1
  exact of_decide_eq_true h_cond1

lemma spec2_of_check_case (n : ℕ) (h : n ≤ 55) : a_fast n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
  have hc := check_case_n n h
  unfold check_case at hc
  dsimp only at hc
  rw [Bool.and_eq_true] at hc
  rcases hc with ⟨h_cond1, h_cond2⟩
  rw [beq_iff_eq] at h_cond2
  constructor
  · intro h_eq
    have h_dec : decide (a_fast n = 1) = true := decide_eq_true h_eq
    rw [h_dec] at h_cond2
    have h_or : (decide (n = 0) || decide (n = 2) || decide (n = 7) || decide (n = 9) || decide (n = 11) || decide (n = 12) || decide (n = 16) || decide (n = 31) || decide (n = 33) || decide (n = 41)) = true := h_cond2.symm
    simp only [Bool.or_eq_true, decide_eq_true_iff] at h_or
    simp only [mem_insert_iff, mem_singleton_iff]
    omega
  · intro h_mem
    simp only [mem_insert_iff, mem_singleton_iff] at h_mem
    have h_dec : (decide (n = 0) || decide (n = 2) || decide (n = 7) || decide (n = 9) || decide (n = 11) || decide (n = 12) || decide (n = 16) || decide (n = 31) || decide (n = 33) || decide (n = 41)) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_iff]
      omega
    rw [h_dec] at h_cond2
    exact of_decide_eq_true h_cond2

theorem a306439_conjecture_1 :
  (∀ n, 5 < n → a n > 0) ∧
  (∀ n, a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ)) := by
  constructor
  · intro n hn
    by_cases h_le : n ≤ 55
    · rw [a_eq_fast n h_le]
      exact spec1_of_check_case n h_le hn
    · unfold a
      rw [if_neg h_le]
      omega
  · intro n
    by_cases h_le : n ≤ 55
    · rw [a_eq_fast n h_le]
      exact spec2_of_check_case n h_le
    · unfold a
      rw [if_neg h_le]
      constructor
      · intro h2
        contradiction
      · intro h_mem
        have h_not_mem : n ∉ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) := by
          intro h_in
          simp only [mem_insert_iff, mem_singleton_iff] at h_in
          rcases h_in with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> omega
        contradiction

#print axioms a306439_conjecture_1
