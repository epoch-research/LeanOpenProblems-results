import Submission.ContinuousIntervalQuantum
import Submission.ContinuousIntervalPatched

/-! Integer-threshold refinements can be inserted after every sieve stage,
optionally following lattice chord patches. The triggering hypotheses are
checked explicitly, and the whole recursion retains the normalized transfer.
No uniform quadratic positivity is asserted. -/
namespace Erdos970.ContinuousInterval
open IntervalRescaling

noncomputable def quantumRefine (d : ℝ) (g : ℕ) (L : ℝ → ℝ) : ℝ → ℝ :=
  if 0 < d ∧ 0 < g ∧ L ((g - 1 : ℕ) : ℝ) = 0 ∧ 0 < L g then
    quantumPatch d g (quantumSlope L g) (quantumIntercept L g) L
  else L

lemma Regular.quantumRefine {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U) (g : ℕ) :
    Regular d (quantumRefine d g L) U := by
  unfold ContinuousInterval.quantumRefine
  split_ifs with hh
  · exact h.quantumPatch g _ _ hh.1 hh.2.1 (h.quantumSlope_bounds g).1
      (h.quantumSlope_bounds g).2 (h.quantumIntercept_nonpos g hh.2.1 hh.2.2.1)
  · exact h

lemma IntervalBounds.quantumRefine {d α : ℝ} {L U : ℝ → ℝ}
    {p : ℕ → ℕ} {k : ℕ} (hr : Regular d L U) (h : IntervalBounds L U α p k)
    (hda : d ≤ α) (g : ℕ) : IntervalBounds (quantumRefine d g L) U α p k := by
  unfold ContinuousInterval.quantumRefine
  split_ifs with hh
  · exact (quantum_cell_certificate hr h g hh.1 hda hh.2.1 hh.2.2.1 hh.2.2.2).2
  · exact h

lemma quantumRefine_dominates (d : ℝ) (g : ℕ) (L U : ℝ → ℝ) :
    Dominates (quantumRefine d g L) U L U := by
  constructor
  · intro x
    unfold ContinuousInterval.quantumRefine
    split_ifs
    · exact le_max_left _ _
    · exact le_rfl
  · intro x hx
    exact le_rfl

noncomputable def quantumEnvelope (Q : ℕ → ℝ) (cells : ℕ → List ℕ) (trigger : ℕ → ℕ) :
    ℕ → (ℝ → ℝ) × (ℝ → ℝ)
  | 0 => (fun x => max 0 x, fun x => x)
  | k + 1 =>
      let E := quantumEnvelope Q cells trigger k
      let F := chordPatches (cells k) (stepLower (Q k) E.1 E.2) (stepUpper (Q k) E.1 E.2)
      (quantumRefine (density Q (k + 1)) (trigger k) F.1, F.2)

theorem quantumEnvelope_regular (Q : ℕ → ℝ) (cells : ℕ → List ℕ) (trigger : ℕ → ℕ)
    (k : ℕ) (hQ : ∀ i < k, 0 ≤ Q i ∧ Q i ≤ 1) :
    Regular (density Q k) (quantumEnvelope Q cells trigger k).1
      (quantumEnvelope Q cells trigger k).2 := by
  induction k with
  | zero => exact envelope_regular Q 0 (fun i hi => by omega)
  | succ k ih =>
    have hs := (ih (fun i hi => hQ i (by omega))).step (Q k)
      (hQ k (by omega)).1 (hQ k (by omega)).2
    have hp := hs.chordPatches (cells k)
    have hd : density Q k * (1 - Q k) = density Q (k + 1) := by
      simp only [density, Finset.prod_range_succ]
    rw [hd] at hp
    exact hp.quantumRefine (trigger k)

/-- Neither kind of refinement can weaken the original unpatched envelopes. -/
theorem quantumEnvelope_dominates (Q : ℕ → ℝ) (cells : ℕ → List ℕ) (trigger : ℕ → ℕ)
    (k : ℕ) (hQ : ∀ i < k, 0 ≤ Q i ∧ Q i ≤ 1) :
    Dominates (quantumEnvelope Q cells trigger k).1 (quantumEnvelope Q cells trigger k).2
      (fun x => (envelope Q k x).1) (fun x => (envelope Q k x).2) := by
  induction k with
  | zero => exact ⟨fun _ => le_rfl, fun _ _ => le_rfl⟩
  | succ k ih =>
    have hs := (ih (fun i hi => hQ i (by omega))).step (Q k)
      (hQ k (by omega)).1 (hQ k (by omega)).2
    let E := quantumEnvelope Q cells trigger k
    let A := stepLower (Q k) E.1 E.2
    let B := stepUpper (Q k) E.1 E.2
    have hp := chordPatches_dominates (cells k) A B
    have hq := quantumRefine_dominates (density Q (k + 1)) (trigger k)
      (chordPatches (cells k) A B).1 (chordPatches (cells k) A B).2
    exact ⟨fun x => ((hs.1 x).trans (hp.1 x)).trans (hq.1 x),
      fun x hx => ((hq.2 x hx).trans (hp.2 x hx)).trans (hs.2 x hx)⟩

/-- The stronger recursion still bounds every actual normalized survivor count
for arbitrary larger pairwise coprime moduli. -/
theorem quantumEnvelope_normalized_bound (p : ℕ → ℕ) (Q : ℕ → ℝ)
    (cells : ℕ → List ℕ) (trigger : ℕ → ℕ) (k : ℕ)
    (hp : ∀ i < k, 1 < p i)
    (hcop : ∀ i < k, ∀ j < i, (p i).Coprime (p j))
    (hQ : ∀ i < k, 1 / (p i : ℝ) ≤ Q i ∧ Q i ≤ 1) :
    IntervalBounds (quantumEnvelope Q cells trigger k).1
      (quantumEnvelope Q cells trigger k).2 (normalization p Q k) p k := by
  induction k with
  | zero => intro m r; simp [quantumEnvelope, normalization, count]
  | succ k ih =>
    have hpp : ∀ i < k, 1 < p i := fun i hi => hp i (by omega)
    have hcc : ∀ i < k, ∀ j < i, (p i).Coprime (p j) := fun i hi => hcop i (by omega)
    have hQQ : ∀ i < k, 1 / (p i : ℝ) ≤ Q i ∧ Q i ≤ 1 := fun i hi => hQ i (by omega)
    have hQR : ∀ i < k, 0 ≤ Q i ∧ Q i ≤ 1 := fun i hi =>
      ⟨(by positivity : 0 ≤ 1 / (p i : ℝ)).trans (hQQ i hi).1, (hQQ i hi).2⟩
    have hqk : 0 ≤ Q k := (by positivity : 0 ≤ 1 / (p k : ℝ)).trans (hQ k (by omega)).1
    have hreg := quantumEnvelope_regular Q cells trigger k hQR
    have hs := IntervalBounds.step hreg (ih hpp hcc hQQ)
      (normalization_nonneg p Q k hpp hQQ)
      (fun i hi => by have := hpp i hi; omega) (hp k (by omega))
      (hcop k (by omega)) (Q k) (hQ k (by omega)).1 (hQ k (by omega)).2
    have hstep := hreg.step (Q k) hqk (hQ k (by omega)).2
    have hpatch := hs.chordPatches hstep (cells k)
    have hpatchreg := hstep.chordPatches (cells k)
    have hd : density Q k * (1 - Q k) = density Q (k + 1) := by
      simp only [density, Finset.prod_range_succ]
    rw [hd] at hpatchreg
    rw [← normalization_succ] at hpatch
    exact hpatch.quantumRefine hpatchreg (density_le_normalization p Q (k + 1) hp hQ)
      (trigger k)

theorem survivor_of_positive_quantumEnvelope (p : ℕ → ℕ) (Q : ℕ → ℝ)
    (cells : ℕ → List ℕ) (trigger : ℕ → ℕ) (k : ℕ)
    (hp : ∀ i < k, 1 < p i)
    (hcop : ∀ i < k, ∀ j < i, (p i).Coprime (p j))
    (hQ : ∀ i < k, 1 / (p i : ℝ) ≤ Q i ∧ Q i ≤ 1)
    (m : ℕ) (hpos : 0 < (quantumEnvelope Q cells trigger k).1 m) (r : ℕ → ℕ) :
    ∃ x < m, ∀ j < k, ¬x ≡ r j [MOD p j] := by
  have hh := hpos.trans_le (quantumEnvelope_normalized_bound p Q cells trigger k hp hcop hQ m r).1
  have hcount : 0 < count p r k m := by
    by_contra hn
    have hz : count p r k m = 0 := by omega
    simp [hz] at hh
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hcount
  exact ⟨x, Finset.mem_range.mp (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

#print axioms quantumEnvelope_dominates
#print axioms quantumEnvelope_regular
#print axioms quantumEnvelope_normalized_bound
#print axioms survivor_of_positive_quantumEnvelope
end Erdos970.ContinuousInterval
