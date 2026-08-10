import FormalConjectures.Util.ProblemImports

open Finset Nat Set

def P_a08 (n m : ℕ) : Prop :=
  0 < m ∧ ∃ D ∈ (Nat.divisors m).powerset, D.card = n ∧ D.sum id = m

def P_a08' (n m : ℕ) : Prop :=
  0 < m ∧ ∃ D ∈ powersetCard n (Nat.divisors m), D.sum id = m

instance (n m : ℕ) : Decidable (P_a08' n m) := by
  unfold P_a08'
  infer_instance

def P_a08_dec_fast (n m : ℕ) : Prop :=
  0 < m ∧ (Nat.divisors m).card ≥ n ∧ ∃ D ∈ powersetCard n (Nat.divisors m), D.sum id = m

lemma P_a08_dec_fast_eq (n m : ℕ) :
  P_a08' n m ↔ P_a08_dec_fast n m := by
  unfold P_a08' P_a08_dec_fast
  constructor
  · rintro ⟨h1, D, hD, hsum⟩
    have hcard : (Nat.divisors m).card ≥ n := by
      rw [mem_powersetCard] at hD
      have h_le := Finset.card_le_card hD.1
      omega
    exact ⟨h1, hcard, D, hD, hsum⟩
  · rintro ⟨h1, _, D, hD, hsum⟩
    exact ⟨h1, D, hD, hsum⟩

instance (n m : ℕ) : Decidable (P_a08_dec_fast n m) := by
  unfold P_a08_dec_fast
  infer_instance

def P_a (n m : ℕ) : Prop :=
  0 < m ∧ ∃ D ∈ (Nat.divisors m).powerset, D.card = n ∧ D.sum id = m ∧ D.lcm id = m

lemma P_a_eq (n m : ℕ) :
  (0 < m ∧ ∃ D : Finset ℕ, D ⊆ Nat.divisors m ∧ D.card = n ∧ D.sum id = m ∧ D.lcm id = m) ↔ P_a n m := by
  unfold P_a
  simp only [Finset.mem_powerset]

def P_a' (n m : ℕ) : Prop :=
  0 < m ∧ ∃ D ∈ powersetCard n (Nat.divisors m), D.sum id = m ∧ D.lcm id = m

instance (n m : ℕ) : Decidable (P_a' n m) := by
  unfold P_a'
  infer_instance

set_option maxRecDepth 100000

-- k = 6, m = 24
lemma test_6_min : ∀ x ∈ Finset.range 24, ¬ P_a08_dec_fast 6 x := by decide
lemma test_6_P : P_a' 6 24 := by decide

-- k = 7, m = 48
lemma test_7_min : ∀ x ∈ Finset.range 48, ¬ P_a08_dec_fast 7 x := by decide
lemma test_7_P : P_a' 7 48 := by decide

-- k = 8, m = 60
lemma test_8_min : ∀ x ∈ Finset.range 60, ¬ P_a08_dec_fast 8 x := by decide
lemma test_8_P : P_a' 8 60 := by decide

-- k = 9, m = 84
lemma test_9_min : ∀ x ∈ Finset.range 84, ¬ P_a08_dec_fast 9 x := by decide
lemma test_9_P : P_a' 9 84 := by decide

-- k = 10, m = 120
lemma test_10_min1 : ∀ x ∈ Finset.range 30, ¬ P_a08_dec_fast 10 x := by decide
lemma test_10_min2 : ∀ x ∈ Finset.Ico 30 60, ¬ P_a08_dec_fast 10 x := by decide
lemma test_10_min3 : ∀ x ∈ Finset.Ico 60 90, ¬ P_a08_dec_fast 10 x := by decide
lemma test_10_min4 : ∀ x ∈ Finset.Ico 90 120, ¬ P_a08_dec_fast 10 x := by decide
lemma test_10_P : P_a 10 120 := by
  rw [← P_a_eq]
  refine ⟨by omega, {1, 2, 3, 4, 5, 6, 15, 20, 24, 40}, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
  · decide
  · decide
  · decide

-- k = 11, m = 120
lemma P_a08_eq_dec_fast (n m : ℕ) :
  P_a08 n m ↔ P_a08_dec_fast n m := by
  unfold P_a08 P_a08_dec_fast
  simp only [Finset.mem_powersetCard, Finset.mem_powerset]
  constructor
  · rintro ⟨h1, D, hD, hcard, hsum⟩
    refine ⟨h1, ?_, D, ⟨hD, hcard⟩, hsum⟩
    have h_le := Finset.card_le_card hD
    omega
  · rintro ⟨h1, _, D, ⟨hD, hcard⟩, hsum⟩
    exact ⟨h1, D, hD, hcard, hsum⟩

lemma test_range_11 : ∀ x ∈ Finset.range 120, (divisors x).card < 11 ∨ x = 60 ∨ x = 72 ∨ x = 84 ∨ x = 90 ∨ x = 96 ∨ x = 108 := by decide

lemma test_11_min (x : ℕ) (hx : x < 120) : ¬ P_a08 11 x := by
  rw [P_a08_eq_dec_fast]
  have h_cases : (divisors x).card < 11 ∨ x = 60 ∨ x = 72 ∨ x = 84 ∨ x = 90 ∨ x = 96 ∨ x = 108 := by
    have h_in : x ∈ Finset.range 120 := Finset.mem_range.mpr hx
    exact test_range_11 x h_in
  rcases h_cases with h_card | rfl | rfl | rfl | rfl | rfl | rfl
  · intro h
    rcases h with ⟨h_pos, _, D, hD, hsum⟩
    rw [Finset.mem_powersetCard] at hD
    have h_le := Finset.card_le_card hD.1
    omega
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

lemma test_11_P : P_a 11 120 := by
  rw [← P_a_eq]
  refine ⟨by omega, {1, 2, 3, 4, 5, 6, 8, 12, 15, 24, 40}, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
  · decide
  · decide
  · decide

-- k = 12, m = 120
/-
lemma test_12_min1 : ∀ x ∈ Finset.range 30, ¬ P_a08_dec_fast 12 x := by decide
lemma test_12_min2 : ∀ x ∈ Finset.Ico 30 60, ¬ P_a08_dec_fast 12 x := by decide
lemma test_12_min3 : ∀ x ∈ Finset.Ico 60 90, ¬ P_a08_dec_fast 12 x := by decide
lemma test_12_min4 : ∀ x ∈ Finset.Ico 90 120, ¬ P_a08_dec_fast 12 x := by decide
-/
lemma test_12_P : P_a 12 120 := by
  rw [← P_a_eq]
  refine ⟨by omega, {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 24, 30}, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
  · decide
  · decide
  · decide

-- k = 13, m = 180
/-
lemma test_13_min1 : ∀ x ∈ Finset.range 30, ¬ P_a08_dec_fast 13 x := by decide
lemma test_13_min2 : ∀ x ∈ Finset.Ico 30 60, ¬ P_a08_dec_fast 13 x := by decide
lemma test_13_min3 : ∀ x ∈ Finset.Ico 60 90, ¬ P_a08_dec_fast 13 x := by decide
lemma test_13_min4 : ∀ x ∈ Finset.Ico 90 120, ¬ P_a08_dec_fast 13 x := by decide
lemma test_13_min5 : ∀ x ∈ Finset.Ico 120 150, ¬ P_a08_dec_fast 13 x := by decide
lemma test_13_min6 : ∀ x ∈ Finset.Ico 150 180, ¬ P_a08_dec_fast 13 x := by decide
-/
lemma test_13_P : P_a 13 180 := by
  rw [← P_a_eq]
  refine ⟨by omega, {1, 2, 3, 4, 5, 6, 9, 10, 12, 18, 20, 30, 60}, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
  · decide
  · decide
  · decide

-- k = 14, m = 180
/-
lemma test_14_min1 : ∀ x ∈ Finset.range 30, ¬ P_a08_dec_fast 14 x := by decide
lemma test_14_min2 : ∀ x ∈ Finset.Ico 30 60, ¬ P_a08_dec_fast 14 x := by decide
lemma test_14_min3 : ∀ x ∈ Finset.Ico 60 90, ¬ P_a08_dec_fast 14 x := by decide
lemma test_14_min4 : ∀ x ∈ Finset.Ico 90 120, ¬ P_a08_dec_fast 14 x := by decide
-/
/-
lemma test_14_min5 : ∀ x ∈ Finset.Ico 120 150, ¬ P_a08_dec_fast 14 x := by decide
-/
/-
lemma test_14_120 : ¬ P_a08_dec_fast 14 120 := by decide
-/
/-
lemma test_14_min6 : ∀ x ∈ Finset.Ico 150 180, ¬ P_a08_dec_fast 14 x := by decide
-/
lemma test_14_P : P_a 14 180 := by
  rw [← P_a_eq]
  refine ⟨by omega, {1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 45}, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
  · decide
  · decide
  · decide

-- k = 15, m = 240
/-
lemma test_15_min1 : ∀ x ∈ Finset.range 30, ¬ P_a08_dec_fast 15 x := by decide
lemma test_15_min2 : ∀ x ∈ Finset.Ico 30 60, ¬ P_a08_dec_fast 15 x := by decide
lemma test_15_min3 : ∀ x ∈ Finset.Ico 60 90, ¬ P_a08_dec_fast 15 x := by decide
lemma test_15_min4 : ∀ x ∈ Finset.Ico 90 120, ¬ P_a08_dec_fast 15 x := by decide
lemma test_15_min5 : ∀ x ∈ Finset.Ico 120 150, ¬ P_a08_dec_fast 15 x := by decide
lemma test_15_min6 : ∀ x ∈ Finset.Ico 150 180, ¬ P_a08_dec_fast 15 x := by decide
lemma test_15_min7 : ∀ x ∈ Finset.Ico 180 210, ¬ P_a08_dec_fast 15 x := by decide
lemma test_15_min8 : ∀ x ∈ Finset.Ico 210 240, ¬ P_a08_dec_fast 15 x := by decide
-/
lemma test_15_P : P_a 15 240 := by
  rw [← P_a_eq]
  refine ⟨by omega, {1, 2, 3, 5, 6, 8, 10, 12, 15, 16, 20, 24, 30, 40, 48}, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
  · decide
  · decide
  · decide

lemma test_range_16 : ∀ x ∈ Finset.range 360, (divisors x).card < 16 ∨ x = 120 ∨ x = 168 ∨ x = 180 ∨ x = 210 ∨ x = 216 ∨ x = 240 ∨ x = 252 ∨ x = 264 ∨ x = 270 ∨ x = 280 ∨ x = 288 ∨ x = 300 ∨ x = 312 ∨ x = 330 ∨ x = 336 := by decide
