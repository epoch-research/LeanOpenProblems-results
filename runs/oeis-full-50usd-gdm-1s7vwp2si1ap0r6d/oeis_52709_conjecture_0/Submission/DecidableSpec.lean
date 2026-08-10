import FormalConjectures.Util.ProblemImports
import Submission.Spec

open A052709_Conjecture

-- Let us define a decidable instance for is_positive_list
instance decidable_is_positive_list (l : List ℕ) : Decidable (is_positive_list l) :=
  inferInstanceAs (Decidable (∀ x ∈ l, 0 < x))

-- Let us define a decidable instance for covers_initial_interval
lemma covers_initial_interval_iff (l : List ℕ) :
    covers_initial_interval l ↔
    is_positive_list l ∧
    let s := l.toFinset
    match s.max with
    | some max_s => ∀ m ∈ List.range (max_s + 1), 0 < m → (m ∈ s ↔ m ≤ max_s)
    | none => l.isEmpty := by
  dsimp [covers_initial_interval]
  by_cases h : is_positive_list l
  · simp [h]
    let s := l.toFinset
    rcases s.max with _ | max_s
    · rfl
    · constructor
      · intro h2 m _ h_0
        exact h2 m h_0
      · intro h2 m h_0
        by_cases hm : m ≤ max_s
        · have : m ∈ List.range (max_s + 1) := by
            rw [List.mem_range]
            omega
          exact h2 m this h_0
        · have : ¬ m ≤ max_s := hm
          constructor
          · intro h_mem
            have : m ≤ max_s := Finset.le_max h_mem
            contradiction
          · intro h_le
            contradiction
  · simp [h]

instance decidable_covers_initial_interval (l : List ℕ) : Decidable (covers_initial_interval l) :=
  decidable_of_iff _ (covers_initial_interval_iff l).symm

instance decidable_has_nondecreasing_pattern_3 (l : List ℕ) : Decidable (has_nondecreasing_pattern_3 l) :=
  inferInstance

instance decidable_avoids_pattern_xyz (l : List ℕ) : Decidable (avoids_pattern_xyz l) :=
  inferInstance

-- Now let us test if we can decide membership in sequences_counted_by_A052709 3
example : [1, 1] ∈ sequences_counted_by_A052709 3 := by decide

def boundedLists : ℕ → Finset ℕ → Finset (List ℕ)
  | 0, _ => {[]}
  | L + 1, S => S.biUnion (fun x => (boundedLists L S).map ⟨fun l => x :: l, fun l1 l2 h => by injection h⟩)

lemma mem_boundedLists (L : ℕ) (S : Finset ℕ) (l : List ℕ) :
    l ∈ boundedLists L S ↔ l.length = L ∧ ∀ x ∈ l, x ∈ S := by
  induction' L with L ih generalizing l
  · simp [boundedLists]
    rintro rfl
    simp
  · rw [boundedLists]
    simp only [Finset.mem_biUnion, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨x, hx, l', hl', rfl⟩
      rw [ih] at hl'
      rcases hl' with ⟨hl'_len, hl'_mem⟩
      simp [hl'_len, hx]
      exact hl'_mem
    · rintro ⟨h_len, h_mem⟩
      rcases l with _ | ⟨x, l'⟩
      · contradiction
      · simp only [List.length_cons, add_left_inj] at h_len
          simp only [List.forall_mem_cons] at h_mem
        refine ⟨x, h_mem.1, l', ?_, rfl⟩
        rw [ih]
        exact ⟨h_len, h_mem.2⟩

lemma le_length_of_mem (l : List ℕ) (h : covers_initial_interval l) (x : ℕ) (hx : x ∈ l) :
    x ≤ l.length := by
  have h_pos := h.1
  have h_cov := h.2
  have h_x_pos : 0 < x := h_pos x hx
  revert h_cov
  dsimp [covers_initial_interval]
  rcases h_max : l.toFinset.max with _ | max_s
  · intro h_cov
    have h_nil : l = [] := by
      rcases l with _ | ⟨y, tl⟩
      · rfl
      · dsimp at h_cov
        contradiction
    subst h_nil
    contradiction
  · intro h_cov
    have h_x_mem : x ∈ l.toFinset := List.mem_toFinset.mpr hx
    have h_x_le : x ≤ max_s := by
      have := h_cov x h_x_pos
      exact this.mp h_x_mem
    have h_max_pos : 0 < max_s := by omega
    have h_max_mem : max_s ∈ l.toFinset := by
      have := h_cov max_s h_max_pos
      exact this.mpr (le_refl max_s)
    have h_subset : Finset.Ico 1 (max_s + 1) ⊆ l.toFinset := by
      intro m hm
      rw [Finset.mem_Ico] at hm
      have h_m_pos : 0 < m := hm.1
      have h_m_le : m ≤ max_s := by omega
      have := h_cov m h_m_pos
      exact this.mpr h_m_le
    have h_card_le := Finset.card_le_card h_subset
    rw [Nat.card_Ico] at h_card_le
    have h_card_max : max_s + 1 - 1 = max_s := by omega
    rw [h_card_max] at h_card_le
    have h_len_le : l.toFinset.card ≤ l.length := List.toFinset_card_le l
    omega

def sequences_finset (n : ℕ) : Finset (List ℕ) :=
  let S := Finset.Icc 1 (n - 1)
  (boundedLists (n - 1) S).filter (fun l =>
    decide (l.length = n - 1 ∧ covers_initial_interval l ∧ avoids_pattern_xyz l)
  )

instance instFintypeSequencesCountedByA052709 (n : ℕ) : Fintype (sequences_counted_by_A052709 n) :=
  Fintype.ofFinset (sequences_finset n) (by
    intro l
    dsimp [sequences_finset, sequences_counted_by_A052709]
    simp only [Finset.mem_filter, decide_eq_true_iff]
    constructor
    · rintro ⟨_, h2, h3, h4⟩
      exact ⟨h2, h3, h4⟩
    · rintro ⟨h2, h3, h4⟩
      refine ⟨?_, h2, h3, h4⟩
      rw [mem_boundedLists]
      refine ⟨h2, ?_⟩
      intro x hx
      rw [Finset.mem_Icc]
      have h_len : l.length = n - 1 := h2
      have h_le := le_length_of_mem l h3 x hx
      rw [h_len] at h_le
      have h_pos : 0 < x := h3.1 x hx
      exact ⟨h_pos, h_le⟩
  )

#eval Fintype.card (sequences_counted_by_A052709 1)
#eval Fintype.card (sequences_counted_by_A052709 2)
#eval Fintype.card (sequences_counted_by_A052709 3)
#eval Fintype.card (sequences_counted_by_A052709 4)
#eval Fintype.card (sequences_counted_by_A052709 5)

