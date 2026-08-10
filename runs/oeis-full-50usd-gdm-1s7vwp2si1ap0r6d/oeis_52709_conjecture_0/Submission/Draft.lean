import FormalConjectures.Util.ProblemImports

def A052709 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k =>
    ((Nat.choose (2 * k) k) / (k + 1)) * (Nat.choose k (n - 1 - k))

namespace A052709_Conjecture

open List

def is_positive_list (l : List ℕ) : Prop :=
  ∀ x ∈ l, 0 < x

def covers_initial_interval (l : List ℕ) : Prop :=
  is_positive_list l ∧
  let s := l.toFinset
  match s.max with
  | some max_s => ∀ m : ℕ, 0 < m → (m ∈ s ↔ m ≤ max_s)
  | none => l.isEmpty

def has_nondecreasing_pattern_3 (l : List ℕ) : Prop :=
  ∃ (i j k : Fin l.length),
    i < j ∧ j < k ∧ l.get i ≤ l.get j ∧ l.get j ≤ l.get k

def avoids_pattern_xyz (l : List ℕ) : Prop :=
  ¬ has_nondecreasing_pattern_3 l

def sequences_counted_by_A052709 (n : ℕ) : Set (List ℕ) :=
  { l : List ℕ | l.length = n - 1 ∧ covers_initial_interval l ∧ avoids_pattern_xyz l }

end A052709_Conjecture

open A052709_Conjecture

lemma mem_seq_11 : [1, 1] ∈ sequences_counted_by_A052709 3 := by
  refine ⟨rfl, ?_, ?_⟩
  · constructor
    · intro x hx; simp at hx; subst hx; decide
    · dsimp [covers_initial_interval]
      have h_max : [1, 1].toFinset.max = some 1 := by
        rw [List.toFinset_cons, List.toFinset_cons, List.toFinset_nil]
        rw [Finset.max_insert, Finset.max_insert]
        rfl
      rw [h_max]
      intro m hm
      simp
      omega
  · intro h
    rcases h with ⟨i, j, k, hij, hjk, _, _⟩
    have : i.val < j.val := hij
    have : j.val < k.val := hjk
    have : k.val < 2 := k.isLt
    omega

lemma mem_seq_12 : [1, 2] ∈ sequences_counted_by_A052709 3 := by
  refine ⟨rfl, ?_, ?_⟩
  · constructor
    · intro x hx; simp at hx; rcases hx with rfl | rfl <;> decide
    · dsimp [covers_initial_interval]
      have h_max : [1, 2].toFinset.max = some 2 := by
        rw [List.toFinset_cons, List.toFinset_cons, List.toFinset_nil]
        rw [Finset.max_insert, Finset.max_insert]
        rfl
      rw [h_max]
      intro m hm
      simp
      omega
  · intro h
    rcases h with ⟨i, j, k, hij, hjk, _, _⟩
    have : i.val < j.val := hij
    have : j.val < k.val := hjk
    have : k.val < 2 := k.isLt
    omega

lemma mem_seq_21 : [2, 1] ∈ sequences_counted_by_A052709 3 := by
  refine ⟨rfl, ?_, ?_⟩
  · constructor
    · intro x hx; simp at hx; rcases hx with rfl | rfl <;> decide
    · dsimp [covers_initial_interval]
      have h_max : [2, 1].toFinset.max = some 2 := by
        rw [List.toFinset_cons, List.toFinset_cons, List.toFinset_nil]
        rw [Finset.max_insert, Finset.max_insert]
        rfl
      rw [h_max]
      intro m hm
      simp
      omega
  · intro h
    rcases h with ⟨i, j, k, hij, hjk, _, _⟩
    have : i.val < j.val := hij
    have : j.val < k.val := hjk
    have : k.val < 2 := k.isLt
    omega

lemma n3_cases (l : List ℕ) (h_len : l.length = 2) (h_cov : covers_initial_interval l) :
    l = [1, 1] ∨ l = [1, 2] ∨ l = [2, 1] := by
  match l with
  | [] => simp only [List.length_nil] at h_len; omega
  | [x] => simp only [List.length_singleton] at h_len; omega
  | x :: y :: tl =>
    have h_tl_nil : tl = [] := by
      have h_tl_len : tl.length = 0 := by
        have : (x :: y :: tl).length = 2 := h_len
        simp only [List.length_cons] at this
        omega
      exact List.eq_nil_of_length_eq_zero h_tl_len
    subst h_tl_nil
    -- Now l is [x, y]
    have h_pos : is_positive_list [x, y] := h_cov.1
    have h_x_pos : 0 < x := h_pos x (by simp)
    have h_y_pos : 0 < y := h_pos y (by simp)
    have h_cov_spec := h_cov.2
    dsimp [covers_initial_interval] at h_cov_spec
    -- let us get the max
    have h_max : [x, y].toFinset.max = some (max x y) := by
      have h_to_finset : [x, y].toFinset = insert x (insert y ∅ : Finset ℕ) := by
        rw [List.toFinset_cons, List.toFinset_cons, List.toFinset_nil]
      rw [h_to_finset]
      rw [Finset.max_insert, Finset.max_insert]
      rfl
    rw [h_max] at h_cov_spec
    -- h_cov_spec is: ∀ m, 0 < m → (m ∈ [x, y].toFinset ↔ m ≤ max x y)
    have h1 := h_cov_spec 1 (by decide)
    have h_1_le_max : 1 ≤ max x y := by
      have : x ≤ max x y := le_max_left x y
      omega
    have h_1_mem := h1.mpr h_1_le_max
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at h_1_mem
    -- h_1_mem : 1 = x ∨ 1 = y
    have h_max_le_2 : max x y ≤ 2 := by
      by_contra! h_gt
      have h3 := h_cov_spec 3 (by decide)
      have h_3_le_max : 3 ≤ max x y := h_gt
      have h_3_mem := h3.mpr h_3_le_max
      simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at h_3_mem
      have h2 := h_cov_spec 2 (by decide)
      have h_2_le_max : 2 ≤ max x y := by omega
      have h_2_mem := h2.mpr h_2_le_max
      simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at h_2_mem
      rcases h_1_mem with rfl | rfl
      · rcases h_2_mem with h_2_x | h_2_y
        · omega
        · rcases h_3_mem with h_3_x | h_3_y
          · omega
          · omega
      · rcases h_2_mem with h_2_x | h_2_y
        · rcases h_3_mem with h_3_x | h_3_y
          · omega
          · omega
        · omega
    have h_x_le_2 : x ≤ 2 := by
      have : x ≤ max x y := le_max_left x y
      omega
    have h_y_le_2 : y ≤ 2 := by
      have : y ≤ max x y := le_max_right x y
      omega
    rcases h_1_mem with rfl | rfl
    · -- 1 = x
      -- y must be 1 or 2
      have : y = 1 ∨ y = 2 := by omega
      rcases this with rfl | rfl
      · left; rfl
      · right; left; rfl
    · -- 1 = y
      -- x must be 1 or 2
      have : x = 1 ∨ x = 2 := by omega
      rcases this with rfl | rfl
      · left; rfl
      · right; right; rfl

def equiv3 : sequences_counted_by_A052709 3 ≃ Fin 3 where
  toFun l :=
    if l.val = [1, 1] then 0
    else if l.val = [1, 2] then 1
    else 2
  invFun i :=
    match i with
    | 0 => ⟨[1, 1], mem_seq_11⟩
    | 1 => ⟨[1, 2], mem_seq_12⟩
    | 2 => ⟨[2, 1], mem_seq_21⟩
  left_inv l := by
    have h_cases := n3_cases l.val l.property.1 l.property.2.1
    rcases h_cases with h | h | h
    · have h_eq : l.val = [1, 1] := h
      dsimp
      rw [if_pos h_eq]
      exact Subtype.ext h_eq.symm
    · have h_eq : l.val = [1, 2] := h
      dsimp
      rw [if_neg (by intro hc; simp [h_eq] at hc)]
      rw [if_pos h_eq]
      exact Subtype.ext h_eq.symm
    · have h_eq : l.val = [2, 1] := h
      dsimp
      rw [if_neg (by intro hc; simp [h_eq] at hc)]
      rw [if_neg (by intro hc; simp [h_eq] at hc)]
      exact Subtype.ext h_eq.symm
  right_inv i := by
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl

theorem n3_conjecture (n : ℕ) (h : 0 < n) [Fintype (sequences_counted_by_A052709 n)] :
    A052709 n = Fintype.card (sequences_counted_by_A052709 n) := by
  aesop

