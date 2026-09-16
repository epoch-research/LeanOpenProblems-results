import FormalConjectures.Util.ProblemImports

open Finset Nat

def bits_times_4 (n : ℕ) : Finset ℕ :=
  if h : n = 0 then ∅
  else
    let S' := (bits_times_4 (n / 2)).image (fun x => 2 * x)
    if n % 2 = 1 then insert 4 S' else S'
termination_by n

def make_set (n : ℕ) : Finset ℕ :=
  if n % 4 = 0 then bits_times_4 (n / 4)
  else if n % 4 = 1 then insert 9 (bits_times_4 ((n - 9) / 4))
  else if n % 4 = 2 then insert 18 (bits_times_4 ((n - 18) / 4))
  else insert 27 (bits_times_4 ((n - 27) / 4))

lemma bits_times_4_mod_4 (n : ℕ) : ∀ x ∈ bits_times_4 n, x % 4 = 0 := by
  induction' n using Nat.strong_induction_on with n ih
  rw [bits_times_4]
  split_ifs with h h2
  · simp
  · intro x hx
    rw [mem_insert] at hx
    rcases hx with rfl | hx
    · decide
    · rw [mem_image] at hx
      rcases hx with ⟨y, hy, rfl⟩
      have := ih (n / 2) (by omega) y hy
      omega
  · intro x hx
    rw [mem_image] at hx
    rcases hx with ⟨y, hy, rfl⟩
    have := ih (n / 2) (by omega) y hy
    omega

lemma sum_bits_times_4 (n : ℕ) : (bits_times_4 n).sum id = 4 * n := by
  induction' n using Nat.strong_induction_on with n ih
  rw [bits_times_4]
  split_ifs with h h2
  · simp [h]
  · have h_inj : Set.InjOn (fun (x : ℕ) => 2 * x) (bits_times_4 (n / 2)) := by
      intro a _ b _ hab; dsimp at hab; omega
    have h_sum : ((bits_times_4 (n / 2)).image (fun x => 2 * x)).sum id = 2 * (4 * (n / 2)) := by
      rw [sum_image h_inj]
      have : (∑ x ∈ bits_times_4 (n / 2), id (2 * x)) = ∑ x ∈ bits_times_4 (n / 2), 2 * id x := rfl
      rw [this, ← mul_sum]
      rw [ih (n/2) (by omega)]
    have h_not_mem : 4 ∉ (bits_times_4 (n / 2)).image (fun x => 2 * x) := by
      intro h_mem
      rw [mem_image] at h_mem
      rcases h_mem with ⟨y, hy, hy2⟩
      have := bits_times_4_mod_4 (n / 2) y hy
      omega
    rw [sum_insert h_not_mem]
    rw [h_sum]
    change 4 + 2 * (4 * (n / 2)) = 4 * n
    omega
  · have h_inj : Set.InjOn (fun (x : ℕ) => 2 * x) (bits_times_4 (n / 2)) := by
      intro a _ b _ hab; dsimp at hab; omega
    have h_sum : ((bits_times_4 (n / 2)).image (fun x => 2 * x)).sum id = 2 * (4 * (n / 2)) := by
      rw [sum_image h_inj]
      have : (∑ x ∈ bits_times_4 (n / 2), id (2 * x)) = ∑ x ∈ bits_times_4 (n / 2), 2 * id x := rfl
      rw [this, ← mul_sum]
      rw [ih (n/2) (by omega)]
    rw [h_sum]
    omega

lemma sum_make_set (n : ℕ) (hn : n > 23) : (make_set n).sum id = n := by
  unfold make_set
  split_ifs with h1 h2 h3
  · rw [sum_bits_times_4]
    omega
  · have h_not_mem : 9 ∉ bits_times_4 ((n - 9) / 4) := by
      intro h_mem
      have := bits_times_4_mod_4 _ 9 h_mem
      revert this
      decide
    rw [sum_insert h_not_mem, sum_bits_times_4]
    dsimp; omega
  · have h_not_mem : 18 ∉ bits_times_4 ((n - 18) / 4) := by
      intro h_mem
      have := bits_times_4_mod_4 _ 18 h_mem
      revert this
      decide
    rw [sum_insert h_not_mem, sum_bits_times_4]
    dsimp; omega
  · have h_not_mem : 27 ∉ bits_times_4 ((n - 27) / 4) := by
      intro h_mem
      have := bits_times_4_mod_4 _ 27 h_mem
      revert this
      decide
    rw [sum_insert h_not_mem, sum_bits_times_4]
    dsimp
    have h4 : n % 4 = 3 := by omega
    omega

lemma not_squarefree_9 : ¬ Squarefree 9 := by
  intro h
  have h3 : 3 * 3 ∣ 9 := by decide
  have h4 := h 3 h3
  rw [Nat.isUnit_iff] at h4
  contradiction

lemma not_squarefree_18 : ¬ Squarefree 18 := by
  intro h
  have h3 : 3 * 3 ∣ 18 := by decide
  have h4 := h 3 h3
  rw [Nat.isUnit_iff] at h4
  contradiction

lemma not_squarefree_27 : ¬ Squarefree 27 := by
  intro h
  have h3 : 3 * 3 ∣ 27 := by decide
  have h4 := h 3 h3
  rw [Nat.isUnit_iff] at h4
  contradiction

lemma not_squarefree_of_mult_4 (x : ℕ) (h1 : x % 4 = 0) : ¬ Squarefree x := by
  intro h
  have h3 : 2 * 2 ∣ x := by
    apply Dvd.intro (x / 4)
    omega
  have h4 := h 2 h3
  rw [Nat.isUnit_iff] at h4
  contradiction

lemma make_set_not_squarefree (n : ℕ) : ∀ x ∈ make_set n, ¬ Squarefree x := by
  unfold make_set
  split_ifs with h1 h2 h3
  · intro x hx
    apply not_squarefree_of_mult_4
    exact bits_times_4_mod_4 _ x hx
  · intro x hx
    rw [mem_insert] at hx
    rcases hx with rfl | hx
    · exact not_squarefree_9
    · apply not_squarefree_of_mult_4
      exact bits_times_4_mod_4 _ x hx
  · intro x hx
    rw [mem_insert] at hx
    rcases hx with rfl | hx
    · exact not_squarefree_18
    · apply not_squarefree_of_mult_4
      exact bits_times_4_mod_4 _ x hx
  · intro x hx
    rw [mem_insert] at hx
    rcases hx with rfl | hx
    · exact not_squarefree_27
    · apply not_squarefree_of_mult_4
      exact bits_times_4_mod_4 _ x hx

lemma bits_times_4_pos (n : ℕ) : ∀ x ∈ bits_times_4 n, x > 0 := by
  induction' n using Nat.strong_induction_on with n ih
  rw [bits_times_4]
  split_ifs with h h2
  · simp
  · intro x hx
    rw [mem_insert] at hx
    rcases hx with rfl | hx
    · decide
    · rw [mem_image] at hx
      rcases hx with ⟨y, hy, rfl⟩
      have := ih (n / 2) (by omega) y hy
      omega
  · intro x hx
    rw [mem_image] at hx
    rcases hx with ⟨y, hy, rfl⟩
    have := ih (n / 2) (by omega) y hy
    omega

lemma make_set_pos (n : ℕ) : ∀ x ∈ make_set n, x > 0 := by
  unfold make_set
  split_ifs with h1 h2 h3
  · exact bits_times_4_pos _
  · intro x hx
    rw [mem_insert] at hx
    rcases hx with rfl | hx
    · decide
    · exact bits_times_4_pos _ _ hx
  · intro x hx
    rw [mem_insert] at hx
    rcases hx with rfl | hx
    · decide
    · exact bits_times_4_pos _ _ hx
  · intro x hx
    rw [mem_insert] at hx
    rcases hx with rfl | hx
    · decide
    · exact bits_times_4_pos _ _ hx
lemma make_set_subset (n : ℕ) (hn : n > 23) : make_set n ⊆ range (n + 1) \ {0} := by
  intro x hx
  rw [mem_sdiff, mem_range, mem_singleton]
  constructor
  · have h_sum := sum_make_set n hn
    have h_le : id x ≤ (make_set n).sum id := single_le_sum (fun y hy => Nat.zero_le (id y)) hx
    dsimp at h_le
    rw [h_sum] at h_le
    omega
  · have := make_set_pos n x hx
    omega

lemma A256012_pos (n : ℕ) (hn : n > 23) : card (filter (fun P : Finset ℕ => P.sum id = n ∧ (∀ k ∈ P, ¬ Squarefree k)) (powerset (range (n + 1) \ {0}))) > 0 := by
  apply Finset.card_pos.mpr
  rw [filter_nonempty_iff]
  use make_set n
  constructor
  · rw [mem_powerset]
    exact make_set_subset n hn
  · constructor
    · exact sum_make_set n hn
    · exact make_set_not_squarefree n
