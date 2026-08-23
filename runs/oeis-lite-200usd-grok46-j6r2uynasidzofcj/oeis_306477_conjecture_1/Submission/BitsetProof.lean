import FormalConjectures.Util.ProblemImports

open Nat List

set_option exponentiation.threshold 300
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

def triBits : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    let t := (k + 1) * (k + 2) / 2
    triBits k ||| (2 ^ t)

def addVals (base : ℕ) : List ℕ → ℕ
  | [] => 0
  | v :: vs => (base <<< v) ||| addVals base vs

lemma choose_two_eq_mul (w : ℕ) :
    (w + 2).choose 2 = (w + 1) * (w + 2) / 2 := by
  rw [choose_two_right (w + 2)]
  have : w + 2 - 1 = w + 1 := by omega
  rw [this, Nat.mul_comm]

lemma testBit_triBits_iff (W t : ℕ) :
    (triBits W).testBit t = true ↔ ∃ w < W, (w + 1) * (w + 2) / 2 = t := by
  induction W with
  | zero =>
    simp [triBits]
  | succ W ih =>
    simp only [triBits, testBit_or, Bool.or_eq_true, testBit_two_pow, decide_eq_true_eq, ih]
    constructor
    · rintro (⟨w, hw, rfl⟩ | h)
      · exact ⟨w, Nat.lt_succ_of_lt hw, rfl⟩
      · exact ⟨W, Nat.lt_succ_self W, h⟩
    · rintro ⟨w, hw, rfl⟩
      rw [Nat.lt_succ_iff] at hw
      rcases eq_or_lt_of_le hw with hW | hW
      · subst hW; exact Or.inr rfl
      · exact Or.inl ⟨w, hW, rfl⟩

lemma testBit_addVals_iff (base : ℕ) (vs : List ℕ) (n : ℕ) :
    (addVals base vs).testBit n = true ↔
      ∃ v ∈ vs, v ≤ n ∧ base.testBit (n - v) = true := by
  induction vs with
  | nil =>
    simp [addVals]
  | cons v vs ih =>
    simp only [addVals, testBit_or, Bool.or_eq_true, mem_cons, testBit_shiftLeft, ih]
    constructor
    · rintro (h | h)
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨v, Or.inl rfl, h.1, h.2⟩
      · rcases h with ⟨v', hv', hge, hb⟩
        exact ⟨v', Or.inr hv', hge, hb⟩
    · rintro ⟨v', hv', hge, hb⟩
      rcases hv' with rfl | hv'
      · refine Or.inl ?_
        simp [hge, hb]
      · exact Or.inr ⟨v', hv', hge, hb⟩

lemma testBit_addVals_tri_iff (W : ℕ) (qs : List ℕ) (n : ℕ) :
    (addVals (triBits W) qs).testBit n = true ↔
      ∃ q ∈ qs, ∃ w < W, q ≤ n ∧ (w + 1) * (w + 2) / 2 = n - q := by
  rw [testBit_addVals_iff]
  constructor
  · rintro ⟨q, hq, hle, hb⟩
    rcases (testBit_triBits_iff W (n - q)).1 hb with ⟨w, hw, hwq⟩
    exact ⟨q, hq, w, hw, hle, hwq⟩
  · rintro ⟨q, hq, w, hw, hle, hwq⟩
    refine ⟨q, hq, hle, ?_⟩
    exact (testBit_triBits_iff W (n - q)).2 ⟨w, hw, hwq⟩

lemma testBit_add4_iff (W : ℕ) (qs rs ss : List ℕ) (n : ℕ) :
    (addVals (addVals (addVals (triBits W) qs) rs) ss).testBit n = true ↔
      ∃ s ∈ ss, ∃ r ∈ rs, ∃ q ∈ qs, ∃ w < W,
        s + r + q ≤ n ∧ (w + 1) * (w + 2) / 2 + q + r + s = n := by
  rw [testBit_addVals_iff]
  constructor
  · intro h
    rcases h with ⟨s, hs, hles, hbit⟩
    have h2 := (testBit_addVals_iff (addVals (triBits W) qs) rs (n - s)).1 hbit
    rcases h2 with ⟨r, hr, hler, hbit2⟩
    have h3 := (testBit_addVals_tri_iff W qs (n - s - r)).1 hbit2
    rcases h3 with ⟨q, hq, w, hw, hleq, hwq⟩
    have hsum : s + r + q ≤ n := by omega
    refine ⟨s, hs, r, hr, q, hq, w, hw, hsum, ?_⟩
    omega
  · intro h
    rcases h with ⟨s, hs, r, hr, q, hq, w, hw, hle, hwq⟩
    refine ⟨s, hs, by omega, ?_⟩
    refine (testBit_addVals_iff (addVals (triBits W) qs) rs (n - s)).2 ⟨r, hr, by omega, ?_⟩
    refine (testBit_addVals_tri_iff W qs (n - s - r)).2 ⟨q, hq, w, hw, by omega, ?_⟩
    omega

example : (triBits 5).testBit 1 = true := by decide
example : (triBits 5).testBit 6 = true := by decide
