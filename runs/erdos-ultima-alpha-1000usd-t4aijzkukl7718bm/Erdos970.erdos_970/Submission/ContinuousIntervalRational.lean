import Submission.ContinuousIntervalEnvelope

/-! Pruned rational evaluation of the continuous interval envelope. -/
namespace Erdos970.ContinuousInterval

section Computable
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

def fastEnvelope (q : ℕ → R) : ℕ → R → R × R
  | 0, x => (max 0 x, x)
  | k + 1, x =>
      (if x ≤ (k : R) + 1 then 0 else max 0
        ((fastEnvelope q k x).1 - (fastEnvelope q k (1 + (x - 1) * q k)).2),
       (fastEnvelope q k x).2 - (fastEnvelope q k ((x + 1) * q k - 1)).1)

end Computable

theorem fastEnvelope_eq (q : ℕ → ℝ) (k : ℕ)
    (hq : ∀ i < k, 0 ≤ q i ∧ q i ≤ 1) (x : ℝ) :
    fastEnvelope q k x = envelope q k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    have he (y : ℝ) := ih (fun i hi => hq i (by omega)) y
    apply Prod.ext
    · by_cases hx : x ≤ (k : ℝ) + 1
      · have hl : (fastEnvelope q (k + 1) x).1 = 0 := by
          rw [fastEnvelope]
          simp only [hx, ↓reduceIte]
        rw [hl, lower_zero_of_le_card q (k + 1) hq x (by simpa using hx)]
      · have hx0 : 0 ≤ x := by have := Nat.cast_nonneg (α := ℝ) k; linarith
        conv_lhs => arg 1; rw [fastEnvelope]
        conv_rhs => arg 1; rw [envelope]
        simp only [if_neg hx, he, stepLower, clip, max_eq_right hx0]
    · conv_lhs => arg 1; rw [fastEnvelope]
      conv_rhs => arg 1; rw [envelope]
      simp only [he, stepUpper]

theorem fastEnvelope_congr {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (q Q : ℕ → R) (k : ℕ) (hq : ∀ i < k, q i = Q i) (x : R) :
    fastEnvelope q k x = fastEnvelope Q k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    have he (y : R) := ih (fun i hi => hq i (by omega)) y
    simp only [fastEnvelope, hq k (by omega), he]

theorem cast_fastEnvelope (q : ℕ → ℚ) (k : ℕ) (x : ℚ) :
    Prod.map (fun y : ℚ => (y : ℝ)) (fun y : ℚ => (y : ℝ)) (fastEnvelope q k x) =
      fastEnvelope (fun i => (q i : ℝ)) k (x : ℝ) := by
  induction k generalizing x with
  | zero => simp [fastEnvelope]
  | succ k ih =>
    have hl (y : ℚ) := congrArg Prod.fst (ih y)
    have hu (y : ℚ) := congrArg Prod.snd (ih y)
    simp only [Prod.map_fst, Prod.map_snd] at hl hu
    have ha : ((1 + (x - 1) * q k : ℚ) : ℝ) = 1 + ((x : ℝ) - 1) * (q k : ℝ) := by
      push_cast
      rfl
    have hb : (((x + 1) * q k - 1 : ℚ) : ℝ) = ((x : ℝ) + 1) * (q k : ℝ) - 1 := by
      push_cast
      rfl
    have hc : ((x : ℝ) ≤ (k : ℝ) + 1) ↔ x ≤ (k : ℚ) + 1 := by exact_mod_cast Iff.rfl
    conv_lhs => arg 3; rw [fastEnvelope]
    conv_rhs => rw [fastEnvelope]
    apply Prod.ext
    · dsimp only [Prod.map, Prod.fst]
      simp only [hc]
      split_ifs
      · simp
      · simp only [Rat.cast_max, Rat.cast_zero, Rat.cast_sub, hl, hu, ha]
    · dsimp only [Prod.map, Prod.snd]
      simp only [Rat.cast_sub, hu, hl, hb]

theorem real_positive_of_rational (q : ℕ → ℚ) (k m : ℕ)
    (hq : ∀ i < k, 0 ≤ q i ∧ q i ≤ 1)
    (hpos : 0 < (fastEnvelope q k (m : ℚ)).1) :
    0 < (envelope (fun i => (q i : ℝ)) k m).1 := by
  have he := congrArg Prod.fst (cast_fastEnvelope q k (m : ℚ))
  simp only [Prod.map_fst, Rat.cast_natCast] at he
  rw [fastEnvelope_eq _ k (fun i hi => by exact_mod_cast hq i hi)] at he
  rw [← he]
  exact_mod_cast hpos

#print axioms fastEnvelope_eq
#print axioms real_positive_of_rational
end Erdos970.ContinuousInterval
