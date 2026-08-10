import FormalConjectures.Util.ProblemImports

set_option linter.style.copyright.formalConjectures false
set_option linter.style.namespace false
set_option linter.unusedVariables false

open Nat

/--
A356026: Main diagonal of right-and-left variant of Kimberling expulsion array, A007063.
Let $A(i, j)$ be the $(i, j)$-th term of the array, for $i, j \ge 1$.
$$A(i, j) = \begin{cases} i + j - 1 & \text{if } j \ge 2i - 3 \\ A(i - 1, i + (j - 2)/2) & \text{if } j < 2i - 3 \text{ and } j \text{ is even} \\ A(i - 1, i - (j + 3)/2) & \text{if } j < 2i - 3 \text{ and } j \text{ is odd} \end{cases}$$
The sequence $a(n)$ is $A(n, n)$.
-/
def KL_array : ℕ → ℕ → ℕ
| 0, _ => 0
| _ + 1, 0 => 0
| i + 1, j =>
  if j ≥ 2 * (i + 1) - 3 then
    (i + 1) + j - 1
  else
    if j % 2 = 0 then
      KL_array i (i + 1 + (j - 2) / 2)
    else
      KL_array i (i + 1 - (j + 3) / 2)

/--
The main diagonal of right-and-left variant of Kimberling expulsion array, A007063.
-/
def a (n : ℕ) : ℕ := KL_array n n

lemma a_one : a 1 = 1 := by decide

lemma a_two : a 2 = 3 := by decide

lemma a_seventy_five : a 75 = 2 := by decide


lemma KL_array_pos (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
  KL_array i j =
    if j ≥ 2 * i - 3 then
      i + j - 1
    else
      if j % 2 = 0 then
        KL_array (i - 1) (i + (j - 2) / 2)
      else
        KL_array (i - 1) (i - (j + 3) / 2) := by
  rcases i with _ | i
  · contradiction
  rcases j with _ | j
  · contradiction
  rfl

@[simp] lemma KL_array_zero_simp (j : ℕ) : KL_array 0 j = 0 := rfl

@[simp] lemma KL_array_zero_right_simp (i : ℕ) : KL_array i 0 = 0 := by
  rcases i with _ | i <;> rfl

@[simp] lemma KL_array_pos_simp (i j : ℕ) :
  KL_array (Nat.succ i) (Nat.succ j) =
    if Nat.succ j ≥ 2 * (Nat.succ i) - 3 then
      (Nat.succ i) + (Nat.succ j) - 1
    else
      if (Nat.succ j) % 2 = 0 then
        KL_array i (Nat.succ i + (Nat.succ j - 2) / 2)
      else
        KL_array i (Nat.succ i - (Nat.succ j + 3) / 2) := by
  rw [KL_array_pos (Nat.succ i) (Nat.succ j) (by omega) (by omega)]
  rfl

def step (i : ℕ) (j : ℕ) : ℕ :=
  if j ≥ 2 * i - 1 then
    j + 1
  else if j % 2 = 0 then
    i + 1 + (j - 2) / 2
  else
    i + 1 - (j + 3) / 2

theorem KL_array_step (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
  KL_array (i+1) j = KL_array i (step i j) := by
  rw [KL_array_pos (i+1) j (by omega) hj]
  unfold step
  split_ifs <;> try omega
  · rw [KL_array_pos i (j+1) hi (by omega)]
    rw [if_pos (by omega)]
    omega
  · have h_sub : i + 1 - 1 = i := by omega
    rw [h_sub]
  · have h_sub : i + 1 - 1 = i := by omega
    rw [h_sub]

def inv_step (i : ℕ) (J : ℕ) : ℕ :=
  if J ≥ 2 * i then
    J - 1
  else if J > i then
    2 * (J - i)
  else
    2 * (i - J) - 1

lemma step_inv_step (i J : ℕ) (hi : 0 < i) (hJ : 0 < J) (hJi : J ≠ i) :
  step i (inv_step i J) = J := by
  unfold step inv_step
  split_ifs <;> omega

lemma inv_step_pos (i J : ℕ) (hi : 0 < i) (hJ : 0 < J) (hJi : J ≠ i) :
  0 < inv_step i J := by
  unfold inv_step
  split_ifs <;> omega

lemma step_pos_and_ne (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
  0 < step i j ∧ step i j ≠ i := by
  unfold step
  split_ifs <;> omega

lemma step_inj (i j1 j2 : ℕ) (hi : 0 < i) (hj1 : 0 < j1) (hj2 : 0 < j2) (h : step i j1 = step i j2) : j1 = j2 := by
  unfold step at h
  split_ifs at h <;> omega

lemma step_equiv (i : ℕ) (hi : 0 < i) (x : ℕ) :
  (∃ j, 0 < j ∧ KL_array (i+1) j = x) ↔ (∃ J, 0 < J ∧ J ≠ i ∧ KL_array i J = x) := by
  constructor
  · rintro ⟨j, hj, hj_eq⟩
    rw [KL_array_step i j hi hj] at hj_eq
    use step i j
    have h_prop := step_pos_and_ne i j hi hj
    refine ⟨h_prop.1, h_prop.2, hj_eq⟩
  · rintro ⟨J, hJ, hJi, hJ_eq⟩
    use inv_step i J
    refine ⟨inv_step_pos i J hi hJ hJi, ?_⟩
    rw [KL_array_step i (inv_step i J) hi (inv_step_pos i J hi hJ hJi)]
    rw [step_inv_step i J hi hJ hJi]
    exact hJ_eq

theorem KL_array_inj (i : ℕ) (hi : 0 < i) (j1 j2 : ℕ) (hj1 : 0 < j1) (hj2 : 0 < j2)
  (h : KL_array i j1 = KL_array i j2) : j1 = j2 := by
  induction i generalizing j1 j2 with
  | zero => contradiction
  | succ i ih =>
    rcases i with rfl | i
    · -- succ 0 = 1
      rw [KL_array_pos 1 j1 (by omega) hj1] at h
      rw [KL_array_pos 1 j2 (by omega) hj2] at h
      rw [if_pos (by omega)] at h
      rw [if_pos (by omega)] at h
      omega
    · -- succ (i+1)
      have hi_pos : 0 < i + 1 := by omega
      have ih_succ := ih hi_pos
      rw [KL_array_step (i+1) j1 hi_pos hj1] at h
      rw [KL_array_step (i+1) j2 hi_pos hj2] at h
      have h_step_eq := ih_succ (step (i+1) j1) (step (i+1) j2) (step_pos_and_ne (i+1) j1 hi_pos hj1).1 (step_pos_and_ne (i+1) j2 hi_pos hj2).1 h
      exact step_inj (i+1) j1 j2 hi_pos hj1 hj2 h_step_eq

theorem row_image (i : ℕ) (hi : 0 < i) :
  ∀ x, (0 < x ∧ ∀ m < i, 0 < m → a m ≠ x) ↔ ∃ j, 0 < j ∧ KL_array i j = x := by
  induction i with
  | zero => contradiction
  | succ i ih =>
    rcases i with rfl | i
    · -- Base case i = 1
      intro x
      constructor
      · intro h
        use x
        refine ⟨h.1, ?_⟩
        rw [KL_array_pos 1 x (by omega) h.1]
        rw [if_pos (by omega)]
        omega
      · rintro ⟨j, hj, hj_eq⟩
        refine ⟨?_, ?_⟩
        · rw [KL_array_pos 1 j (by omega) hj] at hj_eq
          rw [if_pos (by omega)] at hj_eq
          omega
        · intro m hm hm_pos
          omega
    · -- Inductive step succ (i+1)
      have hi_pos : 0 < i + 1 := by omega
      have ih_succ := ih hi_pos
      intro x
      rw [step_equiv (i+1) hi_pos x]
      constructor
      · intro h
        have h_lt : ∀ m < i + 1, 0 < m → a m ≠ x := by
          intro m hm hm_pos
          exact h.2 m (by omega) hm_pos
        have h_ne : a (i+1) ≠ x := h.2 (i+1) (by omega) hi_pos
        have ih_res := (ih_succ x).mp ⟨h.1, h_lt⟩
        rcases ih_res with ⟨J, hJ, hJ_eq⟩
        use J
        refine ⟨hJ, ?_, hJ_eq⟩
        intro h_eq
        subst h_eq
        have h_ai : a (i+1) = x := by
          unfold a
          exact hJ_eq
        exact h_ne h_ai
      · rintro ⟨J, hJ, hJi, hJ_eq⟩
        have ih_res := (ih_succ x).mpr ⟨J, hJ, hJ_eq⟩
        refine ⟨ih_res.1, ?_⟩
        intro m hm hm_pos
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ hm) with hm_lt | rfl
        · exact ih_res.2 m hm_lt hm_pos
        · -- m = i+1
          intro h_eq
          unfold a at h_eq
          have h_eq_inj := KL_array_inj (i+1) hi_pos J (i+1) hJ hi_pos (by rw [h_eq, hJ_eq])
          exact hJi h_eq_inj

lemma a_pos (i : ℕ) (hi : 0 < i) : 0 < a i := by
  have h_ex : ∃ j, 0 < j ∧ KL_array i j = a i := ⟨i, hi, rfl⟩
  rw [← row_image i hi (a i)] at h_ex
  exact h_ex.1

theorem a_inj (n1 n2 : ℕ) (hn1 : 0 < n1) (hn2 : 0 < n2) (h : a n1 = a n2) : n1 = n2 := by
  by_contra h_ne
  rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
  · -- n1 < n2
    have h_not : ¬ ∃ j, 0 < j ∧ KL_array n2 j = a n1 := by
      rw [← row_image n2 hn2 (a n1)]
      push_neg
      intro _
      use n1
    apply h_not
    use n2
    refine ⟨hn2, ?_⟩
    unfold a at h ⊢
    rw [← h]
  · -- n1 > n2
    have h_not : ¬ ∃ j, 0 < j ∧ KL_array n1 j = a n2 := by
      rw [← row_image n1 hn1 (a n2)]
      push_neg
      intro _
      use n2
    apply h_not
    use n1
    refine ⟨hn1, ?_⟩
    unfold a at h ⊢
    rw [h]

noncomputable def unexpelled_le (i : ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.range (k + 1)).filter (fun x => 0 < x ∧ ∀ m < i, 0 < m → a m ≠ x)

lemma unexpelled_le_mono (i : ℕ) (k : ℕ) :
  unexpelled_le (i + 1) k ⊆ unexpelled_le i k := by
  intro x hx
  rw [unexpelled_le, Finset.mem_filter] at hx ⊢
  refine ⟨hx.1, hx.2.1, ?_⟩
  intro m hm hm_pos
  exact hx.2.2 m (by omega) hm_pos

lemma mem_unexpelled_le_iff (i : ℕ) (k : ℕ) (x : ℕ) :
  x ∈ unexpelled_le i k ↔ x ≤ k ∧ 0 < x ∧ ∀ m < i, 0 < m → a m ≠ x := by
  rw [unexpelled_le, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by omega, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by omega, h2, h3⟩

lemma ai_mem_unexpelled_le (i : ℕ) (k : ℕ) (hi : 0 < i) (hak : a i ≤ k) :
  a i ∈ unexpelled_le i k := by
  rw [mem_unexpelled_le_iff]
  refine ⟨hak, a_pos i hi, ?_⟩
  intro m hm hm_pos h_eq
  have h_inj := a_inj m i hm_pos hi h_eq
  omega

lemma ai_not_mem_unexpelled_le_succ (i : ℕ) (k : ℕ) (hi : 0 < i) :
  a i ∉ unexpelled_le (i + 1) k := by
  rw [mem_unexpelled_le_iff]
  push_neg
  intro _ _
  use i
  refine ⟨by omega, hi, rfl⟩

lemma card_unexpelled_le_succ_lt (i : ℕ) (k : ℕ) (hi : 0 < i) (hak : a i ≤ k) :
  (unexpelled_le (i + 1) k).card < (unexpelled_le i k).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (unexpelled_le_mono i k)]
  use a i
  refine ⟨ai_mem_unexpelled_le i k hi hak, ai_not_mem_unexpelled_le_succ i k hi⟩

noncomputable def indices_le (n : ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun i => 0 < i ∧ a i ≤ k)

lemma mem_indices_le_iff (n : ℕ) (k : ℕ) (x : ℕ) :
  x ∈ indices_le n k ↔ x ≤ n ∧ 0 < x ∧ a x ≤ k := by
  rw [indices_le, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by omega, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by omega, h2, h3⟩

lemma indices_le_zero (k : ℕ) :
  indices_le 0 k = ∅ := by
  ext x
  rw [mem_indices_le_iff]
  simp
  omega

lemma indices_le_succ (n : ℕ) (k : ℕ) :
  indices_le (n + 1) k = if a (n + 1) ≤ k then insert (n + 1) (indices_le n k) else indices_le n k := by
  ext x
  rw [mem_indices_le_iff]
  split_ifs with h
  · rw [Finset.mem_insert, mem_indices_le_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases lt_or_eq_of_le h1 with h1_lt | h1_eq
      · right; refine ⟨by omega, h2, h3⟩
      · left; omega
    · rintro (rfl | ⟨h1, h2, h3⟩)
      · refine ⟨by omega, by omega, h⟩
      · refine ⟨by omega, h2, h3⟩
  · rw [mem_indices_le_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases lt_or_eq_of_le h1 with h1_lt | h1_eq
      · refine ⟨by omega, h2, h3⟩
      · subst h1_eq
        contradiction
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by omega, h2, h3⟩

lemma indices_le_succ_card (n : ℕ) (k : ℕ) :
  (indices_le (n + 1) k).card = (indices_le n k).card + (if a (n + 1) ≤ k then 1 else 0) := by
  rw [indices_le_succ]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    rw [mem_indices_le_iff]
    push_neg
    intro _
    omega
  · omega

lemma unexpelled_le_one (k : ℕ) :
  unexpelled_le 1 k = Finset.Ioc 0 k := by
  ext x
  rw [mem_unexpelled_le_iff, Finset.mem_Ioc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h2, h1, ?_⟩
    intro m hm hm_pos
    omega

lemma unexpelled_le_succ_card_le (n : ℕ) (k : ℕ) :
  (unexpelled_le (n + 2) k).card ≤ (unexpelled_le (n + 1) k).card :=
  Finset.card_le_card (unexpelled_le_mono (n + 1) k)

lemma unexpelled_le_succ_card_lt (n : ℕ) (k : ℕ) (h : a (n + 1) ≤ k) :
  (unexpelled_le (n + 2) k).card < (unexpelled_le (n + 1) k).card :=
  card_unexpelled_le_succ_lt (n + 1) k (by omega) h

theorem main_invariant (n : ℕ) (k : ℕ) :
  (indices_le n k).card + (unexpelled_le (n + 1) k).card ≤ k := by
  induction n with
  | zero =>
    rw [indices_le_zero, Finset.card_empty, zero_add, unexpelled_le_one, Nat.card_Ioc]
    omega
  | succ n ih =>
    rw [indices_le_succ_card]
    change (indices_le n k).card + (if a (n + 1) ≤ k then 1 else 0) + (unexpelled_le (n + 2) k).card ≤ k
    split_ifs with h
    · -- a (n + 1) ≤ k
      have h_lt := unexpelled_le_succ_card_lt n k h
      omega
    · -- a (n + 1) > k
      have h_le := unexpelled_le_succ_card_le n k
      omega

noncomputable def expulsion_bound : (k : ℕ) → (∀ m < k, 0 < m → ∃ n, 0 < n ∧ a n = m) → ℕ
| 0, _ => 1
| k + 1, ih =>
  let prev := expulsion_bound k (fun m hm hm_pos => ih m (Nat.lt_succ_of_lt hm) hm_pos)
  if hk : 0 < k then
    let n := Classical.choose (ih k (Nat.lt_succ_self k) hk)
    max (prev + 1) (n + 1)
  else
    prev + 1

lemma expulsion_bound_spec (k : ℕ) (ih : ∀ m < k, 0 < m → ∃ n, 0 < n ∧ a n = m) (m : ℕ) (hm : m < k) (hm_pos : 0 < m) :
  ∃ n, 0 < n ∧ n < expulsion_bound k ih ∧ a n = m := by
  induction k generalizing m with
  | zero => contradiction
  | succ k ih_k =>
    dsimp [expulsion_bound]
    by_cases hk : 0 < k
    · simp only [dif_pos hk]
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hm) with hm_lt | rfl
      · have ih_res := ih_k (fun m hm hm_pos => ih m (Nat.lt_succ_of_lt hm) hm_pos) m hm_lt hm_pos
        rcases ih_res with ⟨n, hn_pos, hn_lt, hn_eq⟩
        refine ⟨n, hn_pos, ?_, hn_eq⟩
        exact Nat.lt_of_lt_of_le hn_lt (Nat.le_trans (Nat.le_succ _) (Nat.le_max_left (expulsion_bound k (fun m hm hm_pos => ih m (Nat.lt_succ_of_lt hm) hm_pos) + 1) _))
      · -- m = k
        have hk_pos : 0 < m := hm_pos
        let n := Classical.choose (ih m (Nat.lt_succ_self m) hk_pos)
        have h_spec := Classical.choose_spec (ih m (Nat.lt_succ_self m) hk_pos)
        refine ⟨n, h_spec.1, ?_, h_spec.2⟩
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_max_right _ _)
    · simp only [dif_neg hk]
      -- ¬ 0 < k, so k = 0, but m < k+1 and 0 < m, contradiction
      omega

lemma D_step (E : ℕ → ℕ) (N : ℕ) (hE : ∀ n ≥ N, E (n + 1) + 2 * E n = n + 2) (n : ℕ) (hn : n ≥ N) :
  (E (n + 2) : ℤ) - (E (n + 1) : ℤ) = 1 - 2 * ((E (n + 1) : ℤ) - (E n : ℤ)) := by
  have hE1 := hE (n + 1) (by omega)
  have hE2 := hE n hn
  change E (n + 2) + 2 * E (n + 1) = n + 3 at hE1
  have hE1_z : (E (n + 2) : ℤ) + 2 * (E (n + 1) : ℤ) = n + 3 := by omega
  have hE2_z : (E (n + 1) : ℤ) + 2 * (E n : ℤ) = n + 2 := by omega
  omega

lemma find_m (E : ℕ → ℕ) (N : ℕ) (hE : ∀ n ≥ N, E (n + 1) + 2 * E n = n + 2) :
  ∃ m ≥ N, 1 < ((E (m + 1) : ℤ) - (E m : ℤ)).natAbs := by
  let D := fun n => (E (n + 1) : ℤ) - (E n : ℤ)
  have hD : ∀ n ≥ N, D (n + 1) = 1 - 2 * D n := by
    intro n hn
    exact D_step E N hE n hn
  rcases lt_or_ge 1 (D N).natAbs with h | h
  · use N, by omega
  · have h_vals : D N = -1 ∨ D N = 0 ∨ D N = 1 := by omega
    rcases h_vals with h_neg1 | h_zero | h_pos1
    · use N + 1
      refine ⟨by omega, ?_⟩
      have h1 := hD N (by omega)
      rw [h_neg1] at h1
      change 1 < (D (N + 1)).natAbs
      omega
    · use N + 3
      refine ⟨by omega, ?_⟩
      have h1 := hD N (by omega)
      rw [h_zero] at h1
      have h1' : D (N + 1) = 1 := by omega
      have h2 := hD (N + 1) (by omega)
      change D (N + 2) = 1 - 2 * D (N + 1) at h2
      rw [h1'] at h2
      have h2' : D (N + 2) = -1 := by omega
      have h3 := hD (N + 2) (by omega)
      change D (N + 3) = 1 - 2 * D (N + 2) at h3
      rw [h2'] at h3
      change 1 < (D (N + 3)).natAbs
      omega
    · use N + 2
      refine ⟨by omega, ?_⟩
      have h1 := hD N (by omega)
      rw [h_pos1] at h1
      have h1' : D (N + 1) = -1 := by omega
      have h2 := hD (N + 1) (by omega)
      change D (N + 2) = 1 - 2 * D (N + 1) at h2
      rw [h1'] at h2
      change 1 < (D (N + 2)).natAbs
      omega

lemma pow_growth (m : ℕ) : 4 * m + 16 < 2^(m + 6) := by
  induction m with
  | zero => simp
  | succ m ih =>
    change 4 * (m + 1) + 16 < 2 ^ (m + 6 + 1)
    rw [pow_succ]
    omega

lemma pow_two_growth_helper (x : ℕ) : 3 * x + 6 < 8 * 2^x := by
  induction x with
  | zero => decide
  | succ x ih =>
    rw [pow_succ]
    omega

lemma pow_two_growth (C : ℕ) (m : ℕ) (hm : m ≥ C + 3) : 2 * m + C < 2^m := by
  let d := m - (C + 3)
  have h_m : m = C + 3 + d := by omega
  rw [h_m]
  have h_pow : 2^(C + 3 + d) = 8 * 2^(C + d) := by
    have : C + 3 + d = (C + d) + 3 := by omega
    rw [this]
    rw [pow_add]
    ring
  rw [h_pow]
  have h_helper := pow_two_growth_helper (C + d)
  omega

lemma int_abs_helper (x : ℤ) : (1 - 2 * x).natAbs ≥ 2 * x.natAbs - 1 := by
  omega

lemma abs_diff_growth (D : ℕ → ℤ) (m : ℕ) (hD : ∀ n ≥ m, D (n + 1) = 1 - 2 * D n) (hm : 1 < (D m).natAbs) (k : ℕ) :
  2^k + 1 ≤ (D (m + k)).natAbs := by
  induction k with
  | zero =>
    simp
    omega
  | succ k ih =>
    have h_step : D (m + k + 1) = 1 - 2 * D (m + k) := hD (m + k) (by omega)
    have h_abs := int_abs_helper (D (m + k))
    change 2^(k + 1) + 1 ≤ (D (m + k + 1)).natAbs
    rw [h_step]
    have h_pow : 2^(k + 1) + 1 = 2 * (2^k + 1) - 1 := by
      rw [pow_succ]
      omega
    rw [h_pow]
    omega

lemma no_pos_seq (E : ℕ → ℕ) (N : ℕ) (hE : ∀ n ≥ N, E (n + 1) + 2 * E n = n + 2) : False := by
  have h_m := find_m E N hE
  rcases h_m with ⟨m, hm_ge, hm_abs⟩
  let D := fun n => (E (n + 1) : ℤ) - (E n : ℤ)
  have hD : ∀ n ≥ m, D (n + 1) = 1 - 2 * D n := by
    intro n hn
    exact D_step E N hE n (by omega)
  have h_grow := abs_diff_growth D m hD hm_abs (m + 6)
  let n := m + (m + 6)
  change 2 ^ (m + 6) + 1 ≤ (D n).natAbs at h_grow
  have hn : n ≥ N := by omega
  have h_eq := hE n hn
  have h_eq2 := hE (n + 1) (by omega)
  have h_bound : (D n).natAbs ≤ 2 * n + 4 := by
    change ((E (n + 1) : ℤ) - (E n : ℤ)).natAbs ≤ 2 * n + 4
    omega
  have h_pow := pow_growth m
  omega


lemma unexpelled_le_eq_singleton (k : ℕ) (hk : 0 < k) (ih : ∀ m < k, 0 < m → ∃ n, 0 < n ∧ a n = m) (h_not : ∀ n, 0 < n → a n ≠ k) (n : ℕ) (hn : expulsion_bound k ih ≤ n) :
  unexpelled_le n k = {k} := by
  ext x
  rw [mem_unexpelled_le_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hx_le, hx_pos, hx_all⟩
    by_contra h_neq
    have hx_lt : x < k := by omega
    have ⟨m, hm_pos, hm_lt, hm_eq⟩ := expulsion_bound_spec k ih x hx_lt hx_pos
    have hm_n : m < n := by omega
    exact hx_all m hm_n hm_pos hm_eq
  · rintro rfl
    refine ⟨by omega, hk, ?_⟩
    intro m hm hm_pos
    exact h_not m hm_pos


lemma unexpelled_le_succ (n : ℕ) (k : ℕ) (hn : 0 < n) :
  unexpelled_le (n + 1) k = if a n ≤ k then (unexpelled_le n k).erase (a n) else unexpelled_le n k := by
  ext x
  rw [mem_unexpelled_le_iff]
  split_ifs with h
  · rw [Finset.mem_erase, mem_unexpelled_le_iff]
    constructor
    · rintro ⟨hx_le, hx_pos, hx_all⟩
      refine ⟨?_, hx_le, hx_pos, ?_⟩
      · intro h_eq
        subst h_eq
        exact hx_all n (Nat.lt_succ_self n) hn rfl
      · intro m hm hm_pos
        exact hx_all m (by omega) hm_pos
    · rintro ⟨hne, hx_le, hx_pos, hx_all⟩
      refine ⟨hx_le, hx_pos, ?_⟩
      intro m hm hm_pos
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hm) with hm_lt | rfl
      · exact hx_all m hm_lt hm_pos
      · exact hne.symm
  · rw [mem_unexpelled_le_iff]
    constructor
    · rintro ⟨hx_le, hx_pos, hx_all⟩
      refine ⟨hx_le, hx_pos, ?_⟩
      intro m hm hm_pos
      exact hx_all m (by omega) hm_pos
    · rintro ⟨hx_le, hx_pos, hx_all⟩
      refine ⟨hx_le, hx_pos, ?_⟩
      intro m hm hm_pos
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hm) with hm_lt | rfl
      · exact hx_all m hm_lt hm_pos
      · intro h_eq
        subst h_eq
        exact h hx_le





lemma expulsion_bound_ge_one (k : ℕ) (ih : ∀ m < k, 0 < m → ∃ n, 0 < n ∧ a n = m) :
  1 ≤ expulsion_bound k ih := by
  induction k, ih using expulsion_bound.induct with
  | case1 =>
    unfold expulsion_bound
    omega
  | case2 k ih hk ih_h =>
    unfold expulsion_bound
    dsimp only
    rw [dif_pos hk]
    exact Nat.le_trans (by omega) (Nat.le_max_left _ _)
  | case3 k ih hk ih_h =>
    unfold expulsion_bound
    dsimp only
    rw [dif_neg hk]
    omega

lemma expulsion_bound_gt (k : ℕ) (ih : ∀ m < k, 0 < m → ∃ n, 0 < n ∧ a n = m) :
  expulsion_bound k ih > k := by
  induction k, ih using expulsion_bound.induct with
  | case1 =>
    unfold expulsion_bound
    omega
  | case2 k ih hk ih_h =>
    unfold expulsion_bound
    dsimp only
    rw [dif_pos hk]
    exact Nat.lt_of_lt_of_le (by omega) (Nat.le_max_left _ _)
  | case3 k ih hk ih_h =>
    unfold expulsion_bound
    dsimp only
    rw [dif_neg hk]
    omega

lemma k_mem_unexpelled (k : ℕ) (hk : 0 < k) (ih : ∀ m < k, 0 < m → ∃ n, 0 < n ∧ a n = m) (h_not : ∀ n, 0 < n → a n ≠ k) (n : ℕ) (hn : expulsion_bound k ih ≤ n) :
  0 < k ∧ ∀ m < n, 0 < m → a m ≠ k := by
  have h_mem : k ∈ unexpelled_le n k := by
    rw [unexpelled_le_eq_singleton k hk ih h_not n hn]
    exact Finset.mem_singleton_self k
  rw [mem_unexpelled_le_iff] at h_mem
  exact ⟨h_mem.2.1, h_mem.2.2⟩

noncomputable def j_seq (k : ℕ) (hk : 0 < k) (ih : ∀ m < k, 0 < m → ∃ n, 0 < n ∧ a n = m) (h_not : ∀ n, 0 < n → a n ≠ k) (n : ℕ) (hn : expulsion_bound k ih ≤ n) : ℕ :=
  have hn_pos : 0 < n := by
    have h_ge := expulsion_bound_ge_one k ih
    omega
  Classical.choose ((row_image n hn_pos k).mp (k_mem_unexpelled k hk ih h_not n hn))

lemma j_seq_spec (k : ℕ) (hk : 0 < k) (ih : ∀ m < k, 0 < m → ∃ n, 0 < n ∧ a n = m) (h_not : ∀ n, 0 < n → a n ≠ k) (n : ℕ) (hn : expulsion_bound k ih ≤ n) :
  0 < j_seq k hk ih h_not n hn ∧ KL_array n (j_seq k hk ih h_not n hn) = k := by
  unfold j_seq
  have hn_pos : 0 < n := by
    have h_ge := expulsion_bound_ge_one k ih
    omega
  exact Classical.choose_spec ((row_image n hn_pos k).mp (k_mem_unexpelled k hk ih h_not n hn))

lemma j_seq_congr (k : ℕ) (hk : 0 < k) (ih : ∀ m < k, 0 < m → ∃ n, 0 < n ∧ a n = m) (h_not : ∀ n, 0 < n → a n ≠ k) (n : ℕ) (hn1 hn2 : expulsion_bound k ih ≤ n) :
  j_seq k hk ih h_not n hn1 = j_seq k hk ih h_not n hn2 := by
  have hn_pos : 0 < n := by
    have h_ge := expulsion_bound_ge_one k ih
    omega
  have hj1_pos := (j_seq_spec k hk ih h_not n hn1).1
  have hj2_pos := (j_seq_spec k hk ih h_not n hn2).1
  have h_eq1 := (j_seq_spec k hk ih h_not n hn1).2
  have h_eq2 := (j_seq_spec k hk ih h_not n hn2).2
  exact KL_array_inj n hn_pos _ _ hj1_pos hj2_pos (h_eq1.trans h_eq2.symm)

lemma j_seq_eq_of_eq {k : ℕ} {hk : 0 < k} {ih : ∀ m < k, 0 < m → ∃ n, 0 < n ∧ a n = m} {h_not : ∀ n, 0 < n → a n ≠ k}
  {n1 n2 : ℕ} (h1 : expulsion_bound k ih ≤ n1) (h2 : expulsion_bound k ih ≤ n2) (h_eq : n1 = n2) :
  j_seq k hk ih h_not n1 h1 = j_seq k hk ih h_not n2 h2 := by
  subst h_eq
  apply j_seq_congr

lemma j_seq_lt_2n3 (k : ℕ) (hk : 0 < k) (ih : ∀ m < k, 0 < m → ∃ n, 0 < n ∧ a n = m) (h_not : ∀ n, 0 < n → a n ≠ k) (n : ℕ) (hn : expulsion_bound k ih ≤ n) (hn_ge : 2 * expulsion_bound k ih + 2 * k + 10 ≤ n) :
  j_seq k hk ih h_not n hn < 2 * n - 3 := by
  by_contra h_ge
  push_neg at h_ge
  have hn_pos : 0 < n := by omega
  have hj_pos := (j_seq_spec k hk ih h_not n hn).1
  have h_eq := (j_seq_spec k hk ih h_not n hn).2
  rw [KL_array_pos n (j_seq k hk ih h_not n hn) hn_pos hj_pos] at h_eq
  rw [if_pos (by omega)] at h_eq
  have h_M_bound := expulsion_bound_ge_one k ih
  omega

lemma j_seq_step (k : ℕ) (hk : 0 < k) (ih : ∀ m < k, 0 < m → ∃ n, 0 < n ∧ a n = m) (h_not : ∀ n, 0 < n → a n ≠ k) (n : ℕ) (hn : expulsion_bound k ih ≤ n) :
  step n (j_seq k hk ih h_not (n+1) (by omega)) = j_seq k hk ih h_not n hn := by
  have hn_pos : 0 < n := by
    have h_ge := expulsion_bound_ge_one k ih
    omega
  have h_succ_pos : 0 < n + 1 := by omega
  have h_j_spec := j_seq_spec k hk ih h_not (n+1) (by omega)
  have h_j_spec2 := j_seq_spec k hk ih h_not n hn
  have h_step_eq : KL_array (n+1) (j_seq k hk ih h_not (n+1) (by omega)) = KL_array n (step n (j_seq k hk ih h_not (n+1) (by omega))) := by
    apply KL_array_step n (j_seq k hk ih h_not (n+1) (by omega)) hn_pos h_j_spec.1
  rw [h_j_spec.2] at h_step_eq
  have h_final : KL_array n (step n (j_seq k hk ih h_not (n+1) (by omega))) = KL_array n (j_seq k hk ih h_not n hn) := h_step_eq.symm.trans h_j_spec2.2.symm
  apply KL_array_inj n hn_pos
  · exact (step_pos_and_ne n (j_seq k hk ih h_not (n+1) (by omega)) hn_pos h_j_spec.1).1
  · exact h_j_spec2.1
  · exact h_final



lemma E_growth (k : ℕ) (hk : 0 < k) (ih : ∀ m < k, 0 < m → ∃ n, 0 < n ∧ a n = m) (h_not : ∀ n, 0 < n → a n ≠ k)
  (n : ℕ) (hn : expulsion_bound k ih ≤ n) (hn_ge : 2 * expulsion_bound k ih + 2 * k + 10 ≤ n) :
  2 * ((n : ℤ) - (j_seq k hk ih h_not n hn : ℤ)).natAbs ≤ ((n + 1 : ℤ) - (j_seq k hk ih h_not (n+1) (by omega) : ℤ)).natAbs + n + 2 := by
  have h_step := j_seq_step k hk ih h_not n hn
  have h_lt := j_seq_lt_2n3 k hk ih h_not (n+1) (by omega) (by omega)
  unfold step at h_step
  split_ifs at h_step with h1 h2
  · omega
  · omega
  · omega


lemma j_seq_step_even (k : ℕ) (hk : 0 < k) (ih : ∀ m < k, 0 < m → ∃ n, 0 < n ∧ a n = m) (h_not : ∀ n, 0 < n → a n ≠ k)
  (n : ℕ) (hn : expulsion_bound k ih ≤ n) (hn_ge : 2 * expulsion_bound k ih + 2 * k + 10 ≤ n)
  (h_ge : n ≤ j_seq k hk ih h_not n hn) (h_ge_next : n + 1 ≤ j_seq k hk ih h_not (n+1) (by omega)) :
  j_seq k hk ih h_not (n+1) (by omega) = 2 * j_seq k hk ih h_not n hn - 2 * n := by
  have h_step := j_seq_step k hk ih h_not n hn
  have h_lt := j_seq_lt_2n3 k hk ih h_not (n+1) (by omega) (by omega)
  unfold step at h_step
  split_ifs at h_step with h1 h2
  · omega
  · omega
  · omega


lemma find_M_ind (k : ℕ) (hk : 0 < k) (ih : ∀ m < k, 0 < m → ∃ n, 0 < n ∧ a n = m) (h_not : ∀ n, 0 < n → a n ≠ k)
  (d : ℕ) (n_0 : ℕ) (hn_0 : 2 * expulsion_bound k ih + 2 * k + 10 ≤ n_0) :
  (j_seq k hk ih h_not n_0 (by omega) - n_0 = d) → (n_0 ≤ j_seq k hk ih h_not n_0 (by omega)) →
  ∃ M, n_0 ≤ M ∧ ∃ hM : expulsion_bound k ih ≤ M, M ≤ j_seq k hk ih h_not M hM ∧ j_seq k hk ih h_not (M+1) (by omega) < M + 1 := by
  induction d using Nat.strong_induction_on generalizing n_0 hn_0 with
  | h d ih_d =>
    intro hd h_ge
    by_cases h_next : j_seq k hk ih h_not (n_0+1) (by omega) < n_0 + 1
    · use n_0
      refine ⟨by omega, ⟨by omega, h_ge, h_next⟩⟩
    · push_neg at h_next
      have h_step := j_seq_step_even k hk ih h_not n_0 (by omega) (by omega) h_ge h_next
      have h_lt := j_seq_lt_2n3 k hk ih h_not n_0 (by omega) (by omega)
      let d' := j_seq k hk ih h_not (n_0+1) (by omega) - (n_0 + 1)
      have hd' : d' < d := by omega
      have hn_1 : 2 * expulsion_bound k ih + 2 * k + 10 ≤ n_0 + 1 := by omega
      rcases ih_d d' hd' (n_0 + 1) hn_1 (by rfl) h_next with ⟨M, hM1, hM2⟩
      use M
      refine ⟨by omega, hM2⟩



lemma find_M_bound_helper (k : ℕ) (hk : 0 < k) (ih : ∀ m < k, 0 < m → ∃ n, 0 < n ∧ a n = m) (h_not : ∀ n, 0 < n → a n ≠ k)
  (n_0 : ℕ) (hn_0 : 2 * expulsion_bound k ih + 2 * k + 10 ≤ n_0)
  (d : ℕ) : ∀ (m : ℕ) (hm : m - n_0 = d) (hm_ge : n_0 ≤ m),
  (∀ (i : ℕ) (hi : n_0 ≤ i) (hi_m : i ≤ m), i ≤ j_seq k hk ih h_not i (by omega)) →
  j_seq k hk ih h_not m (by omega) - m + d ≤ j_seq k hk ih h_not n_0 (by omega) - n_0 := by
  induction d with
  | zero =>
    intro m hm hm_ge h_all
    have : m = n_0 := by omega
    subst this
    omega
  | succ d ih_d =>
    intro m hm hm_ge h_all
    let m_0 := n_0 + d
    have h_m_eq : m = m_0 + 1 := by omega
    have h_j_eq : j_seq k hk ih h_not m (by omega) = j_seq k hk ih h_not (m_0+1) (by omega) :=
      j_seq_eq_of_eq (by omega) (by omega) h_m_eq
    have hm_0 : m_0 - n_0 = d := by omega
    have hm_0_le : n_0 ≤ m_0 := by omega
    have h_all_m_0 : ∀ (i : ℕ) (hi : n_0 ≤ i) (hi_m : i ≤ m_0), i ≤ j_seq k hk ih h_not i (by omega) := by
      intro i hi hi_m
      apply h_all i hi (by omega)
    have ih_res := ih_d m_0 hm_0 hm_0_le h_all_m_0
    have h_all_m_0_val : m_0 ≤ j_seq k hk ih h_not m_0 (by omega) := h_all m_0 (by omega) (by omega)
    have h_all_m : m_0 + 1 ≤ j_seq k hk ih h_not (m_0+1) (by omega) := by
      have := h_all m (by omega) (by omega)
      rw [h_j_eq] at this
      omega
    have h_step := j_seq_step_even k hk ih h_not m_0 (by omega) (by omega) h_all_m_0_val h_all_m
    have h_lt := j_seq_lt_2n3 k hk ih h_not m_0 (by omega) (by omega)
    rw [h_j_eq]
    omega


lemma find_M_bound (k : ℕ) (hk : 0 < k) (ih : ∀ m < k, 0 < m → ∃ n, 0 < n ∧ a n = m) (h_not : ∀ n, 0 < n → a n ≠ k)
  (n_0 : ℕ) (hn_0 : 2 * expulsion_bound k ih + 2 * k + 10 ≤ n_0)
  (m : ℕ) (hm : n_0 ≤ m) (h_all : ∀ (i : ℕ) (hi : n_0 ≤ i) (hi_m : i ≤ m), i ≤ j_seq k hk ih h_not i (by omega)) :
  m ≤ j_seq k hk ih h_not n_0 (by omega) := by
  have h := find_M_bound_helper k hk ih h_not n_0 hn_0 (m - n_0) m (by omega) hm
  have h_res := h h_all
  have h_m_le := h_all m hm (by omega)
  have hn_0_le := h_all n_0 (by omega) (by omega)
  omega


/--
A356026 Conjectures involving a = A007063 and b = A356026:
(1) Every positive integer is eventually expelled in b (A356026).
This means that the sequence $b(n) = A356026(n)$ is surjective onto the positive integers,
i.e., every positive natural number appears in the sequence $a(n)$ for some $n \ge 1$.
-/
lemma j_seq_lt_n (k : ℕ) (hk : 0 < k) (ih : ∀ m < k, 0 < m → ∃ n, 0 < n ∧ a n = m) (h_not : ∀ n, 0 < n → a n ≠ k)
  (n : ℕ) (hn : expulsion_bound k ih ≤ n) (hn_ge : 2 * expulsion_bound k ih + 2 * k + 10 ≤ n) :
  j_seq k hk ih h_not n hn < n := by
  sorry


/--
A356026 Conjectures involving a = A007063 and b = A356026:
(1) Every positive integer is eventually expelled in b (A356026).
This means that the sequence $b(n) = A356026(n)$ is surjective onto the positive integers,
i.e., every positive natural number appears in the sequence $a(n)$ for some $n \ge 1$.
-/
theorem oeis_a356026_conjecture_1_part_b : ∀ k : ℕ, 0 < k → ∃ n : ℕ, 0 < n ∧ a n = k := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_contra h_not
    push_neg at h_not
    let N_1 := 2 * expulsion_bound k ih + 2 * k + 10
    have h_lt_n : ∀ (n : ℕ) (hn : n ≥ N_1), j_seq k hk ih h_not n (by omega) < n := by
      intro n hn
      apply j_seq_lt_n k hk ih h_not n (by omega) hn
    let E := fun n =>
      if hn : expulsion_bound k ih ≤ n then
        n - j_seq k hk ih h_not n hn
      else
        0
    have hE : ∀ n ≥ N_1, E (n + 1) + 2 * E n = n + 2 := by
      intro n hn
      have hn1 : expulsion_bound k ih ≤ n + 1 := by omega
      have hn0 : expulsion_bound k ih ≤ n := by omega
      change E (n + 1) + 2 * E n = n + 2
      unfold E
      rw [dif_pos hn1, dif_pos hn0]
      have h_step := j_seq_step k hk ih h_not n hn0
      have h_lt := j_seq_lt_2n3 k hk ih h_not (n+1) hn1 (by omega)
      have h_lt_n1 := h_lt_n (n+1) (by omega)
      have h_lt_n0 := h_lt_n n hn
      unfold step at h_step
      split_ifs at h_step with h1 h2
      · omega
      · omega
      · omega
    exact no_pos_seq E N_1 hE

