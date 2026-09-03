import Submission.BinaryMinplusCertificates
import Submission.BinaryWeightedControl

/-! Exact embedding of weighted binary DFAs into the minimum-path framework.
The embedded control has an insufficient rate; no finiteness is asserted. -/
namespace Erdos406BinaryMinplusDeterministic
open Erdos406Tropical (Automaton Run)
open Erdos406GroupedCertificate
open Erdos406AffinePotential (weightFrom)

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def ofDFA (D : DFA ℕ σ) (w : σ → ℕ → ℝ) : Automaton σ where
  next s d := {D.step s d}
  nonempty _ _ := Finset.singleton_nonempty _
  weight s d _ := w s d
  start := D.start

lemma dfa_run (D : DFA ℕ σ) (w : σ → ℕ → ℝ) (L : List ℕ) (s : σ) :
    Run (ofDFA D w) s L (D.evalFrom s L) (weightFrom D w s L) := by
  induction L generalizing s with
  | nil => exact Run.nil s
  | cons d L ih =>
    exact Run.cons (by simp [ofDFA]) (ih (D.step s d))

lemma valueFrom_eq (D : DFA ℕ σ) (w : σ → ℕ → ℝ) (L : List ℕ) (s : σ) :
    Erdos406Minplus.valueFrom (ofDFA D w) s L = weightFrom D w s L := by
  induction L generalizing s with
  | nil => rfl
  | cons d L ih =>
    change ({D.step s d} : Finset σ).inf' (Finset.singleton_nonempty _)
      (fun t => w s d + Erdos406Minplus.valueFrom (ofDFA D w) t L) =
        w s d + weightFrom D w (D.step s d) L
    rw [Finset.inf'_singleton, ih]

lemma value_eq (D : DFA ℕ σ) (w : σ → ℕ → ℝ) (n : ℕ) :
    Erdos406BinaryMinplus.value (ofDFA D w) n =
      Erdos406BinaryWeighted.weightNat D w n :=
  valueFrom_eq D w _ D.start

noncomputable def construction (C : Erdos406BinaryWeighted.Construction σ) :
    Erdos406BinaryMinplus.Construction (ofDFA C.D C.w) where
  R := C.R
  H := C.P
  seed c hc := by
    refine ⟨evalNat 2 C.D c, Erdos406BinaryWeighted.weightNat C.D C.w c,
      dfa_run C.D C.w _ C.D.start, C.relation_start c hc, C.upper_start c hc⟩
  step s t c d e cp hc hd he hcp hid hr sp hs := by
    have hsp : sp = C.D.step s d := by simpa [ofDFA] using hs
    subst sp
    exact ⟨C.D.step t e, by simp [ofDFA],
      C.relation_step s t c d e cp hc hd he hcp hid hr,
      C.upper_step s t c d e cp hc hd he hcp hid hr⟩
  finish s t c hc hr := C.upper_finish s t c hc hr

noncomputable def powerBound {D : DFA ℕ σ} {w : σ → ℕ → ℝ}
    (P : Erdos406BinaryWeighted.PowerBound D w) :
    Erdos406BinaryMinplus.PowerBound (ofDFA D w) where
  a := P.a
  B := P.B
  G := P.G
  J := P.J
  start s hs := by
    have he : s = D.step D.start 1 := by simpa [ofDFA] using hs
    simpa only [he] using P.start
  step s t hs ht := by
    have he : t = D.step s 0 := by simpa [ofDFA] using ht
    simpa only [he] using P.step s hs
  lower_step s t hs ht := by
    have he : t = D.step s 0 := by simpa [ofDFA] using ht
    simpa only [he] using P.lower_step s hs
  lower_end s t hs ht := by
    have he : s = D.step D.start 1 := by simpa [ofDFA] using hs
    simpa only [he] using P.lower_end t ht

noncomputable def control := ofDFA Erdos406BinaryWeightedControl.D
  Erdos406BinaryWeightedControl.w

noncomputable def controlConstruction : Erdos406BinaryMinplus.Construction control :=
  construction Erdos406BinaryWeightedControl.construction

noncomputable def controlPowerBound : Erdos406BinaryMinplus.PowerBound control :=
  powerBound Erdos406BinaryWeightedControl.powerBound

/-- The sparse singleton-edge control uses a proper subset of the states
for its power-zero-tail invariant. -/
lemma control_reachable_set_proper :
    controlPowerBound.G 1 ∧ ¬ controlPowerBound.G 4 := by
  change Erdos406BinaryWeightedControl.G 1 ∧ ¬ Erdos406BinaryWeightedControl.G 4
  decide +kernel

theorem control_construction_bound (n d : ℕ) (hd : d < 2) :
    Erdos406BinaryMinplus.value control (3*n+d) ≤
      Erdos406BinaryMinplus.value control n + 1 :=
  controlConstruction.construction_bound n d hd

theorem control_power_bound (k : ℕ) :
    (5/8 : ℝ)*k ≤ Erdos406BinaryMinplus.value control (2^k) := by
  have h := controlPowerBound.power_lower k
  change (5/8 : ℝ)*k-0 ≤ _ at h
  simpa using h

theorem control_not_supercritical : ¬ Real.log 2 < (5/8 : ℝ)*Real.log 3 :=
  Erdos406BinaryWeightedControl.control_not_supercritical

#print axioms value_eq
#print axioms construction
#print axioms powerBound
#print axioms control_construction_bound
#print axioms control_power_bound
#print axioms control_reachable_set_proper
end Erdos406BinaryMinplusDeterministic
