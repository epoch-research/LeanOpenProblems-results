import Submission.ContinuousIntervalPatched

/-! Transfer of a verified fixed-prefix seed through larger tail moduli.
The seed bounds are explicit hypotheses; no uniform quadratic positivity is
asserted. A separate forcing theorem can adjoin missing prefix primes. -/
namespace Erdos970.ContinuousInterval
open IntervalRescaling

noncomputable def seedRun (Q : ℕ → ℝ) (cells : ℕ → List ℕ) (b : ℕ)
    (L U : ℝ → ℝ) : ℕ → (ℝ → ℝ) × (ℝ → ℝ)
  | 0 => (L, U)
  | t + 1 => chordPatches (cells (b + t))
      (stepLower (Q (b + t)) (seedRun Q cells b L U t).1 (seedRun Q cells b L U t).2)
      (stepUpper (Q (b + t)) (seedRun Q cells b L U t).1 (seedRun Q cells b L U t).2)

noncomputable def seedDensity (d : ℝ) (Q : ℕ → ℝ) (b : ℕ) : ℕ → ℝ
  | 0 => d
  | t + 1 => seedDensity d Q b t * (1 - Q (b + t))

noncomputable def seedScale (p : ℕ → ℕ) (Q : ℕ → ℝ) (b : ℕ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => seedScale p Q b t * (1 - boost (1 / (p (b + t) : ℝ)) (Q (b + t)))

theorem seedRun_regular {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U)
    (Q : ℕ → ℝ) (cells : ℕ → List ℕ) (b t : ℕ)
    (hQ : ∀ i < t, 0 ≤ Q (b + i) ∧ Q (b + i) ≤ 1) :
    Regular (seedDensity d Q b t) (seedRun Q cells b L U t).1 (seedRun Q cells b L U t).2 := by
  induction t with
  | zero => exact h
  | succ t ih =>
    exact ((ih (fun i hi => hQ i (by omega))).step (Q (b + t))
      (hQ t (by omega)).1 (hQ t (by omega)).2).chordPatches (cells (b + t))

theorem seedScale_nonneg (p : ℕ → ℕ) (Q : ℕ → ℝ) (b t : ℕ)
    (hp : ∀ i < t, 1 < p (b + i))
    (hQ : ∀ i < t, 1 / (p (b + i) : ℝ) ≤ Q (b + i) ∧ Q (b + i) ≤ 1) :
    0 ≤ seedScale p Q b t := by
  induction t with
  | zero => norm_num [seedScale]
  | succ t ih =>
    have hpR : (1 : ℝ) < p (b + t) := by exact_mod_cast hp t (by omega)
    have hq : 1 / (p (b + t) : ℝ) < 1 := (div_lt_one (by linarith)).mpr hpR
    exact mul_nonneg (ih (fun i hi => hp i (by omega)) (fun i hi => hQ i (by omega)))
      (sub_nonneg.mpr (boost_bounds _ _ hq (hQ t (by omega)).1 (hQ t (by omega)).2).2)

/-- A seed for the actual prefix transfers through arbitrary larger coprime
moduli in the tail. The seed itself is not replaced by fictitious small primes. -/
theorem seedRun_normalized_bound {d : ℝ} {L U : ℝ → ℝ}
    (p : ℕ → ℕ) (Q : ℕ → ℝ) (cells : ℕ → List ℕ) (b t : ℕ)
    (hr : Regular d L U) (hs : IntervalBounds L U 1 p b)
    (hp : ∀ i < b + t, 1 < p i)
    (hc : ∀ i < b + t, ∀ j < i, (p i).Coprime (p j))
    (hQ : ∀ i < t, 1 / (p (b + i) : ℝ) ≤ Q (b + i) ∧ Q (b + i) ≤ 1) :
    IntervalBounds (seedRun Q cells b L U t).1 (seedRun Q cells b L U t).2
      (seedScale p Q b t) p (b + t) := by
  induction t with
  | zero => simpa only [seedRun, seedScale, Nat.add_zero] using hs
  | succ t ih =>
    have hpp : ∀ i < b + t, 1 < p i := fun i hi => hp i (by omega)
    have hcc : ∀ i < b + t, ∀ j < i, (p i).Coprime (p j) := fun i hi => hc i (by omega)
    have hQQ : ∀ i < t, 1 / (p (b + i) : ℝ) ≤ Q (b + i) ∧ Q (b + i) ≤ 1 :=
      fun i hi => hQ i (by omega)
    have hQR : ∀ i < t, 0 ≤ Q (b + i) ∧ Q (b + i) ≤ 1 := fun i hi =>
      ⟨(by positivity : 0 ≤ 1 / (p (b + i) : ℝ)).trans (hQQ i hi).1, (hQQ i hi).2⟩
    have hreg := seedRun_regular hr Q cells b t hQR
    have hnorm := seedScale_nonneg p Q b t (fun i hi => hpp (b + i) (by omega)) hQQ
    have hstep := IntervalBounds.step hreg (ih hpp hcc hQQ) hnorm
      (fun i hi => by have := hpp i hi; omega) (hp (b + t) (by omega))
      (hc (b + t) (by omega)) (Q (b + t)) (hQ t (by omega)).1 (hQ t (by omega)).2
    have hq0 : 0 ≤ Q (b + t) :=
      (by positivity : 0 ≤ 1 / (p (b + t) : ℝ)).trans (hQ t (by omega)).1
    have hh := hstep.chordPatches (hreg.step (Q (b + t)) hq0 (hQ t (by omega)).2)
      (cells (b + t))
    simpa only [seedRun, seedScale, Nat.add_assoc] using hh

theorem survivor_of_positive_seedRun {d : ℝ} {L U : ℝ → ℝ}
    (p : ℕ → ℕ) (Q : ℕ → ℝ) (cells : ℕ → List ℕ) (b t : ℕ)
    (hr : Regular d L U) (hs : IntervalBounds L U 1 p b)
    (hp : ∀ i < b + t, 1 < p i)
    (hc : ∀ i < b + t, ∀ j < i, (p i).Coprime (p j))
    (hQ : ∀ i < t, 1 / (p (b + i) : ℝ) ≤ Q (b + i) ∧ Q (b + i) ≤ 1)
    (m : ℕ) (hpos : 0 < (seedRun Q cells b L U t).1 m) (r : ℕ → ℕ) :
    ∃ x < m, ∀ i < b + t, ¬x ≡ r i [MOD p i] := by
  have hh := hpos.trans_le (seedRun_normalized_bound p Q cells b t hr hs hp hc hQ m r).1
  have hcount : 0 < count p r (b + t) m := by
    by_contra hn
    have hz : count p r (b + t) m = 0 := by omega
    simp [hz] at hh
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hcount
  exact ⟨x, Finset.mem_range.mp (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

#print axioms seedRun_normalized_bound
#print axioms survivor_of_positive_seedRun
end Erdos970.ContinuousInterval
