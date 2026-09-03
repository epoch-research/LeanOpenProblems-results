import Submission.ContinuousIntervalCertificate

/-! Arbitrarily many finite lattice chord patches may be inserted after every
sieve stage. They strengthen the unpatched envelope, with a proved transfer to
arbitrary larger coprime moduli. Uniform quadratic positivity is not asserted. -/
namespace Erdos970.ContinuousInterval
open IntervalRescaling

noncomputable def chordPatches : List ℕ → (ℝ → ℝ) → (ℝ → ℝ) →
    (ℝ → ℝ) × (ℝ → ℝ)
  | [], L, U => (L, U)
  | a :: cells, L, U => chordPatches cells (patchLower L a) (patchUpper U a)

lemma Regular.chordPatches {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U) (cells : List ℕ) :
    Regular d (chordPatches cells L U).1 (chordPatches cells L U).2 := by
  induction cells generalizing L U with
  | nil => exact h
  | cons a cells ih => exact ih (h.patch a)

lemma IntervalBounds.chordPatches {d α : ℝ} {L U : ℝ → ℝ} {p : ℕ → ℕ} {k : ℕ}
    (hreg : Regular d L U) (h : IntervalBounds L U α p k) (cells : List ℕ) :
    IntervalBounds (chordPatches cells L U).1 (chordPatches cells L U).2 α p k := by
  induction cells generalizing L U with
  | nil => exact h
  | cons a cells ih => exact ih (hreg.patch a) (h.patch hreg a)

lemma chordPatches_dominates (cells : List ℕ) (L U : ℝ → ℝ) :
    Dominates (chordPatches cells L U).1 (chordPatches cells L U).2 L U := by
  induction cells generalizing L U with
  | nil => exact ⟨fun _ => le_rfl, fun _ _ => le_rfl⟩
  | cons a cells ih =>
    have hh := ih (patchLower L a) (patchUpper U a)
    exact ⟨fun x => (le_max_left _ _).trans (hh.1 x),
      fun x hx => (hh.2 x hx).trans (min_le_left _ _)⟩

noncomputable def patchedEnvelope (Q : ℕ → ℝ) (cells : ℕ → List ℕ) :
    ℕ → (ℝ → ℝ) × (ℝ → ℝ)
  | 0 => (fun x => max 0 x, fun x => x)
  | k + 1 => chordPatches (cells k)
      (stepLower (Q k) (patchedEnvelope Q cells k).1 (patchedEnvelope Q cells k).2)
      (stepUpper (Q k) (patchedEnvelope Q cells k).1 (patchedEnvelope Q cells k).2)

theorem patchedEnvelope_regular (Q : ℕ → ℝ) (cells : ℕ → List ℕ) (k : ℕ)
    (hQ : ∀ i < k, 0 ≤ Q i ∧ Q i ≤ 1) :
    Regular (density Q k) (patchedEnvelope Q cells k).1 (patchedEnvelope Q cells k).2 := by
  induction k with
  | zero => exact envelope_regular Q 0 (fun _ hi => by omega)
  | succ k ih =>
    have hh := ((ih (fun i hi => hQ i (by omega))).step (Q k)
      (hQ k (by omega)).1 (hQ k (by omega)).2).chordPatches (cells k)
    simpa only [patchedEnvelope, density, Finset.prod_range_succ] using hh

/-- Patching can never weaken the original continuous envelope. -/
theorem patchedEnvelope_dominates (Q : ℕ → ℝ) (cells : ℕ → List ℕ) (k : ℕ)
    (hQ : ∀ i < k, 0 ≤ Q i ∧ Q i ≤ 1) :
    Dominates (patchedEnvelope Q cells k).1 (patchedEnvelope Q cells k).2
      (fun x => (envelope Q k x).1) (fun x => (envelope Q k x).2) := by
  induction k with
  | zero => exact ⟨fun _ => le_rfl, fun _ _ => le_rfl⟩
  | succ k ih =>
    have hs := (ih (fun i hi => hQ i (by omega))).step (Q k)
      (hQ k (by omega)).1 (hQ k (by omega)).2
    have hp := chordPatches_dominates (cells k)
      (stepLower (Q k) (patchedEnvelope Q cells k).1 (patchedEnvelope Q cells k).2)
      (stepUpper (Q k) (patchedEnvelope Q cells k).1 (patchedEnvelope Q cells k).2)
    exact ⟨fun x => (hs.1 x).trans (hp.1 x), fun x hx => (hp.2 x hx).trans (hs.2 x hx)⟩

/-- The patched reference envelopes bound the normalized actual count. This
allows arbitrary finite choices of cells at every stage, without assuming that
the actual primes equal the reference primes. -/
theorem patchedEnvelope_normalized_bound (p : ℕ → ℕ) (Q : ℕ → ℝ)
    (cells : ℕ → List ℕ) (k : ℕ)
    (hp : ∀ i < k, 1 < p i)
    (hcop : ∀ i < k, ∀ j < i, (p i).Coprime (p j))
    (hQ : ∀ i < k, 1 / (p i : ℝ) ≤ Q i ∧ Q i ≤ 1) :
    IntervalBounds (patchedEnvelope Q cells k).1 (patchedEnvelope Q cells k).2
      (normalization p Q k) p k := by
  induction k with
  | zero => intro m r; simp [patchedEnvelope, normalization, count]
  | succ k ih =>
    have hpp : ∀ i < k, 1 < p i := fun i hi => hp i (by omega)
    have hcc : ∀ i < k, ∀ j < i, (p i).Coprime (p j) := fun i hi => hcop i (by omega)
    have hQQ : ∀ i < k, 1 / (p i : ℝ) ≤ Q i ∧ Q i ≤ 1 := fun i hi => hQ i (by omega)
    have hQR : ∀ i < k, 0 ≤ Q i ∧ Q i ≤ 1 := fun i hi =>
      ⟨(by positivity : 0 ≤ 1 / (p i : ℝ)).trans (hQQ i hi).1, (hQQ i hi).2⟩
    have hreg := patchedEnvelope_regular Q cells k hQR
    have hs := IntervalBounds.step hreg (ih hpp hcc hQQ)
      (normalization_nonneg p Q k hpp hQQ)
      (fun i hi => (hpp i hi).le.trans_lt' (by norm_num)) (hp k (by omega))
      (hcop k (by omega)) (Q k) (hQ k (by omega)).1 (hQ k (by omega)).2
    have hQk0 : 0 ≤ Q k :=
      (by positivity : 0 ≤ 1 / (p k : ℝ)).trans (hQ k (by omega)).1
    have hh := hs.chordPatches (hreg.step (Q k) hQk0 (hQ k (by omega)).2) (cells k)
    simpa only [patchedEnvelope, normalization_succ] using hh

theorem survivor_of_positive_patchedEnvelope (p : ℕ → ℕ) (Q : ℕ → ℝ)
    (cells : ℕ → List ℕ) (k : ℕ)
    (hp : ∀ i < k, 1 < p i)
    (hcop : ∀ i < k, ∀ j < i, (p i).Coprime (p j))
    (hQ : ∀ i < k, 1 / (p i : ℝ) ≤ Q i ∧ Q i ≤ 1)
    (m : ℕ) (hpos : 0 < (patchedEnvelope Q cells k).1 m) (r : ℕ → ℕ) :
    ∃ x < m, ∀ i < k, ¬x ≡ r i [MOD p i] := by
  have hh := hpos.trans_le (patchedEnvelope_normalized_bound p Q cells k hp hcop hQ m r).1
  have hcount : 0 < count p r k m := by
    by_contra hn
    have hz : count p r k m = 0 := by omega
    simp [hz] at hh
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hcount
  exact ⟨x, Finset.mem_range.mp (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

#print axioms patchedEnvelope_regular
#print axioms patchedEnvelope_dominates
#print axioms patchedEnvelope_normalized_bound
#print axioms survivor_of_positive_patchedEnvelope
end Erdos970.ContinuousInterval
