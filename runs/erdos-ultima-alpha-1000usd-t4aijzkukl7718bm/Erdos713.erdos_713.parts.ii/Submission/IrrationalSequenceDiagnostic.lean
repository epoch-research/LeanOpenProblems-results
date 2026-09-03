import FormalConjecturesUtil

/-! Integrality, monotonicity, and superadditivity do not force a rational power index.
This does not identify an extremal-number sequence of a fixed graph. -/
open Filter Asymptotics
namespace Erdos713IrrationalSequenceDiagnostic

noncomputable def index : ℝ := 1 + Real.sqrt 2 / 6
noncomputable def seq (n : ℕ) : ℕ := ⌊(n : ℝ)^index⌋₊

lemma index_bounds : (6 : ℝ)/5 < index ∧ index < (5 : ℝ)/4 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  dsimp only [index]
  constructor <;> nlinarith

lemma index_irrational : Irrational index := by
  have hi := irrational_sqrt_two.div_ratCast (by norm_num : (6 : ℚ) ≠ 0)
  simpa only [Rat.cast_one,Rat.cast_ofNat] using hi.ratCast_add 1

lemma seq_monotone : Monotone seq := by
  intro a b hab
  exact Nat.floor_mono (Real.rpow_le_rpow (Nat.cast_nonneg a) (Nat.cast_le.mpr hab)
    (by have := index_bounds.1; linarith))

lemma seq_superadditive (a b : ℕ) : seq a + seq b ≤ seq (a+b) := by
  apply Nat.le_floor
  have ha := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg a) index)
  have hb := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg b) index)
  have hh := Real.add_rpow_le_rpow_add (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
    (Nat.cast_nonneg b : (0 : ℝ) ≤ b) (by have := index_bounds.1; linarith : 1 ≤ index)
  rw [Nat.cast_add,Nat.cast_add]
  dsimp only [seq]
  linarith

lemma seq_asymptotic : IsEquivalent atTop (fun n : ℕ => (seq n : ℝ))
    (fun n : ℕ => (n : ℝ)^index) := by
  have hr : 0 < index := by have := index_bounds.1; linarith
  exact isEquivalent_nat_floor.comp_tendsto
    ((tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop)

lemma exists_irrational_integer_sequence :
    ∃ r : ℝ, (6 : ℝ)/5 < r ∧ r < (5 : ℝ)/4 ∧ Irrational r ∧
      ∃ f : ℕ → ℕ, Monotone f ∧ (∀ a b, f a+f b ≤ f (a+b)) ∧
        IsEquivalent atTop (fun n : ℕ => (f n : ℝ)) (fun n : ℕ => (n : ℝ)^r) :=
  ⟨index,index_bounds.1,index_bounds.2,index_irrational,seq,seq_monotone,
    seq_superadditive,seq_asymptotic⟩

#print axioms exists_irrational_integer_sequence
end Erdos713IrrationalSequenceDiagnostic
