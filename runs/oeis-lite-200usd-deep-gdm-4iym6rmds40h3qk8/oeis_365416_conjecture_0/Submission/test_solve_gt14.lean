import FormalConjectures.Util.ProblemImports

open Nat

def IsCompositePrimePow (m : ℕ) : Prop :=
  ∃ (p e : ℕ), Nat.Prime p ∧ 1 < e ∧ p ^ e = m

lemma lt_pow_self (e : ℕ) : e < 2 ^ e := by
  induction e with
  | zero => decide
  | succ e ih =>
    have : e + 1 < 2 ^ e + 1 := by omega
    have : 1 ≤ 2 ^ e := Nat.one_le_pow e 2 (by decide)
    omega

def isCompositePrimePow_bool (m : ℕ) : Bool :=
  match m with
  | 0 => false
  | 1 => false
  | m =>
    let primes := (List.range m).filter (fun p => p.Prime)
    let exps := List.range m
    primes.any (fun p =>
      exps.any (fun e =>
        1 < e ∧ p ^ e = m
      )
    )

lemma isCompositePrimePow_iff_bool (m : ℕ) : IsCompositePrimePow m ↔ isCompositePrimePow_bool m = true := by
  constructor
  · rintro ⟨p, e, hp, he, hpe⟩
    have hm : m ≥ 4 := by
      calc m = p ^ e := hpe.symm
        _ ≥ 2 ^ e := Nat.pow_le_pow_left hp.two_le e
        _ ≥ 2 ^ 2 := Nat.pow_le_pow_right (by decide) he
    have hp_lt : p < m := by
      have hp_ge2 : 2 ≤ p := hp.two_le
      have : p < p * p := Nat.lt_mul_self_iff.mpr hp_ge2
      have hp_pos : 0 < p := by omega
      have : p * p ≤ p ^ e := by
        calc p * p = p ^ 2 := by ring
          _ ≤ p ^ e := Nat.pow_le_pow_right hp_pos he
      omega
    have he_lt : e < m := by
      have : e < 2 ^ e := lt_pow_self e
      have : 2 ^ e ≤ p ^ e := Nat.pow_le_pow_left hp.two_le e
      omega
    rcases m with _ | _ | m'
    · contradiction
    · contradiction
    · simp only [isCompositePrimePow_bool]
      rw [List.any_eq_true]
      use p
      constructor
      · simp only [List.mem_filter, List.mem_range, decide_eq_true_iff]
        exact ⟨hp_lt, hp⟩
      · rw [List.any_eq_true]
        use e
        constructor
        · simp only [List.mem_range]
          exact he_lt
        · simp only [decide_eq_true_iff]
          exact ⟨he, hpe⟩
  · intro h
    rcases m with _ | _ | m'
    · contradiction
    · contradiction
    · simp only [isCompositePrimePow_bool, List.any_eq_true, List.mem_filter, List.mem_range, decide_eq_true_iff] at h
      rcases h with ⟨p, ⟨hp_lt, hp⟩, e, he_lt, he, hpe⟩
      exact ⟨p, e, hp, he, hpe⟩

instance (m : ℕ) : Decidable (IsCompositePrimePow m) :=
  decidable_of_iff (isCompositePrimePow_bool m = true) (isCompositePrimePow_iff_bool m).symm

lemma oeis_365416_conjecture_0_gt_14 (k : ℕ) (hk : 14 ≤ k) :
  ¬ (IsCompositePrimePow (2 * k - 1) ∧ IsCompositePrimePow (2 * k + 1)) := by
  rintro ⟨⟨p, e, hp, he, hpe⟩, ⟨q, f, hq, hf, hqf⟩⟩
  sorry
