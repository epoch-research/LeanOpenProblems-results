import Submission.IntervalHullStep

/-!
# Soundness of exact quotient rescaling with monotone hulls

These bounds apply to the actual sequence of positive pairwise coprime moduli.
They do not transfer first-prime computations to other prime sets, and no
uniform quadratic positivity is asserted here.
-/
namespace Erdos970.IntervalRescaling.IntegerHull

/-- Bounds for every forbidden residue vector at a fixed sieve stage. -/
def Bounds (p : ℕ → ℕ) (k : ℕ) (l u : ℕ → ℝ) : Prop :=
  ∀ m r, l m ≤ (count p r k m : ℝ) ∧ (count p r k m : ℝ) ≤ u m

/-- Prefix lower and suffix upper bounds remain valid by monotonicity of
actual survivor counts in the interval length. -/
theorem Bounds.hulls {p : ℕ → ℕ} {k : ℕ} {l u : ℕ → ℝ} (h : Bounds p k l u) :
    Bounds p k (lowerHull l) (upperHull u) := by
  intro m r
  constructor
  · apply lowerHull_le
    intro n hnm
    exact (h n r).1.trans (by exact_mod_cast count_mono_length p r k hnm)
  · apply le_upperHull
    intro n hmn
    exact (show (count p r k m : ℝ) ≤ count p r k n by
      exact_mod_cast count_mono_length p r k hmn).trans (h n r).2

/-- Exact first-hit rescaling supplies the two raw bounds before closure. -/
theorem Bounds.raw_step {p : ℕ → ℕ} {k : ℕ} {l u : ℕ → ℝ} (h : Bounds p k l u)
    (hp : 0 < p k) (hprev : ∀ i < k, 0 < p i)
    (hc : ∀ i < k, (p k).Coprime (p i)) :
    Bounds p (k + 1) (rawLower (p k) l u) (rawUpper (p k) l u) := by
  intro m r
  obtain ⟨c, s, hcl, hcu, he⟩ := firstHitCount_rescale p r k m hp hprev hc
  have hl : l (m / p k) ≤ (firstHitCount p r k m : ℝ) := by
    rw [he]
    exact (h (m / p k) s).1.trans (by exact_mod_cast count_mono_length p s k hcl)
  have hu : (firstHitCount p r k m : ℝ) ≤
      u (BlockSieve.SievePolynomial.ceilQuotient m (p k)) := by
    rw [he]
    exact (show (count p s k c : ℝ) ≤
      count p s k (BlockSieve.SievePolynomial.ceilQuotient m (p k)) by
      exact_mod_cast count_mono_length p s k hcu).trans
        (h (BlockSieve.SievePolynomial.ceilQuotient m (p k)) s).2
  have hpart : (firstHitCount p r k m : ℝ) + count p r (k + 1) m = count p r k m := by
    exact_mod_cast count_succ_partition p r k m
  have hold := h m r
  dsimp [rawLower, rawUpper]
  constructor <;> linarith

/-- The closed step is sound independently of the compatibility proof. -/
theorem Bounds.closed_step {p : ℕ → ℕ} {k : ℕ} {l u : ℕ → ℝ} (h : Bounds p k l u)
    (hp : 0 < p k) (hprev : ∀ i < k, 0 < p i)
    (hc : ∀ i < k, (p k).Coprime (p i)) :
    Bounds p (k + 1) (lowerHull (rawLower (p k) l u))
      (upperHull (rawUpper (p k) l u)) := (h.raw_step hp hprev hc).hulls

/-- Start at any verified prefix and take `k` additional closed sieve steps. -/
noncomputable def closedEnvelope (p : ℕ → ℕ) (b : ℕ) (lo hi : ℕ → ℝ) :
    ℕ → (ℕ → ℝ) × (ℕ → ℝ)
  | 0 => (lo, hi)
  | k + 1 =>
    let old := closedEnvelope p b lo hi k
    (lowerHull (rawLower (p (b + k)) old.1 old.2),
      upperHull (rawUpper (p (b + k)) old.1 old.2))

/-- Every stage of the infinite-domain hull recurrence bounds actual counts. -/
theorem closedEnvelope_sound (p : ℕ → ℕ) (b : ℕ) (lo hi : ℕ → ℝ)
    (hbase : Bounds p b lo hi) (k : ℕ)
    (hp : ∀ i < b + k, 0 < p i)
    (hc : ∀ i < b + k, ∀ j < i, (p i).Coprime (p j)) :
    Bounds p (b + k) (closedEnvelope p b lo hi k).1 (closedEnvelope p b lo hi k).2 := by
  induction k with
  | zero => simpa only [Nat.add_zero, closedEnvelope] using hbase
  | succ k ih =>
    have hh := ih (fun i hi => hp i (by omega)) (fun i hi => hc i (by omega))
    have hs := hh.closed_step (hp (b + k) (by omega))
      (fun i hi => hp i (by omega)) (hc (b + k) (by omega))
    simpa only [closedEnvelope, Nat.add_assoc] using hs

/-- Compatibility and nonnegativity propagate in the same recurrence. -/
theorem closedEnvelope_compatible (p : ℕ → ℕ) (b : ℕ) (lo hi : ℕ → ℝ)
    (hbase : Compatible lo hi) (hlo : ∀ n, 0 ≤ lo n) (k : ℕ)
    (hp : ∀ i < k, 0 < p (b + i)) :
    Compatible (closedEnvelope p b lo hi k).1 (closedEnvelope p b lo hi k).2 ∧
      ∀ n, 0 ≤ (closedEnvelope p b lo hi k).1 n := by
  induction k with
  | zero => exact ⟨hbase, hlo⟩
  | succ k ih =>
    have hh := ih (fun i hi => hp i (by omega))
    exact hh.1.closed_step hh.2 (p (b + k)) (hp k (by omega))

/-- Positivity gives a survivor for the actual moduli. The quantitative
positivity premise is not eliminated by this theorem. -/
theorem survivor_of_closedEnvelope_pos (p : ℕ → ℕ) (b : ℕ) (lo hi : ℕ → ℝ)
    (hbase : Bounds p b lo hi) (k : ℕ)
    (hp : ∀ i < b + k, 0 < p i)
    (hc : ∀ i < b + k, ∀ j < i, (p i).Coprime (p j)) (m : ℕ)
    (hpos : 0 < (closedEnvelope p b lo hi k).1 m) (r : ℕ → ℕ) :
    ∃ x < m, ∀ j < b + k, ¬x ≡ r j [MOD p j] := by
  have hb := (closedEnvelope_sound p b lo hi hbase k hp hc m r).1
  have hn : 0 < count p r (b + k) m := by exact_mod_cast hpos.trans_le hb
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hn
  exact ⟨x, Finset.mem_range.mp (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

/-- The empty prefix has exact lower and upper count equal to its length. -/
lemma bounds_zero (p : ℕ → ℕ) : Bounds p 0 (fun n => (n : ℝ)) (fun n => (n : ℝ)) := by
  intro m r
  simp [count]

lemma compatible_length : Compatible (fun n : ℕ => (n : ℝ)) (fun n : ℕ => (n : ℝ)) := by
  refine ⟨by simp, by simp, fun n => Nat.cast_nonneg n, ?_, ?_⟩ <;>
    intro m n <;> simp

#print axioms closedEnvelope_sound
#print axioms closedEnvelope_compatible
#print axioms survivor_of_closedEnvelope_pos
end Erdos970.IntervalRescaling.IntegerHull
