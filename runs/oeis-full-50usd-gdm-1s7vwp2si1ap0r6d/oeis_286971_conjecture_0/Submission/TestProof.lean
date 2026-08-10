import FormalConjectures.Util.ProblemImports

open Nat

-- Dummy checkN for testing
def checkN (n : ℕ) : Bool :=
  n % 2 = 0

def allTrueSeq (lo hi : ℕ) (fuel : ℕ) : Bool :=
  match fuel with
  | 0 => false
  | f + 1 =>
    if lo > hi then true
    else if checkN lo = false then false
    else allTrueSeq (lo + 1) hi f

theorem allTrueSeq_sound (fuel : ℕ) (lo hi : ℕ) (h : allTrueSeq lo hi fuel = true) (n : ℕ) (hn : n ∈ Finset.Icc lo hi) :
  checkN n = true := by
  induction fuel generalizing lo hi n with
  | zero =>
    dsimp [allTrueSeq] at h
    contradiction
  | succ f ih =>
    dsimp [allTrueSeq] at h
    rw [Finset.mem_Icc] at hn
    split_ifs at h with h1 h2
    · omega
    · by_cases h_lo : n = lo
      · cases h_check : checkN n
        · subst h_lo
          rw [h_check] at h2
          contradiction
        · rfl
      · apply ih (lo + 1) hi h n
        rw [Finset.mem_Icc]
        omega

def allTrueChunks (lo hi : ℕ) (fuel : ℕ) : Bool :=
  match fuel with
  | 0 => false
  | f + 1 =>
    if lo > hi then true
    else
      let next_lo := lo + 1000
      let chunk_hi := if next_lo - 1 < hi then next_lo - 1 else hi
      allTrueSeq lo chunk_hi 1005 && allTrueChunks next_lo hi f

theorem allTrueChunks_sound (fuel : ℕ) (lo hi : ℕ) (h : allTrueChunks lo hi fuel = true) (n : ℕ) (hn : n ∈ Finset.Icc lo hi) :
  checkN n = true := by
  induction fuel generalizing lo hi n with
  | zero =>
    dsimp [allTrueChunks] at h
    contradiction
  | succ f ih =>
    dsimp [allTrueChunks] at h
    rw [Finset.mem_Icc] at hn
    split_ifs at h with h1 h_split
    · omega
    · rw [Bool.and_eq_true] at h
      rcases h with ⟨h_seq, h_rec⟩
      by_cases h_chunk : n ≤ lo + 999
      · apply allTrueSeq_sound 1005 lo (lo + 999) h_seq n
        rw [Finset.mem_Icc]
        exact ⟨hn.1, h_chunk⟩
      · apply ih (lo + 1000) hi h_rec n
        rw [Finset.mem_Icc]
        exact ⟨by omega, hn.2⟩
    · rw [Bool.and_eq_true] at h
      rcases h with ⟨h_seq, h_rec⟩
      apply allTrueSeq_sound 1005 lo hi h_seq n
      rw [Finset.mem_Icc]
      exact hn
