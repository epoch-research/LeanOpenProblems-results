import Submission.Resilience

/-!
Interface and boundary checks for the conditional resilience bridge.
No instance of R2 is assumed globally or supplied by a conjectural declaration.
-/

open SimpleGraph Erdos548.Resilience

/- Check the import environment, not just the text of the proof. -/
run_cmd do
  let env ← Lean.getEnv
  for n in [`Erdos548.erdos_548, `Erdos548.erdos_548.disproof] do
    if env.contains n then
      throwError "Forbidden conjectural declaration present: {n}"
  Lean.logInfo "Verified: neither conjectural declaration from Spec is in the environment."

universe u

section BoundaryChecks

variable {V : Type u}

-- The natural parameter subtraction is valid at its endpoint k = 2.
example [Finite V] (G : SimpleGraph V) (F : Set (Sym2 V)) (hF : F ⊆ G.edgeSet) :
    D 0 (G.deleteEdges F) = D 2 G + 2 * ((Nat.card V : ℚ) - (F.ncard : ℚ)) := by
  simpa using D_deleteEdges 2 (by decide) G F hF

-- At the FULL budget n, excess is preserved, not merely nonnegative.
example [Finite V] (k : ℕ) (hk : 2 ≤ k) (G : SimpleGraph V)
    (F : Set (Sym2 V)) (hF : F ⊆ G.edgeSet) (hb : F.ncard = Nat.card V) :
    D (k - 2) (G.deleteEdges F) = D k G := by
  simpa only [hb, sub_self, mul_zero, add_zero] using D_deleteEdges k hk G F hF

-- Zero deletions are included in the budget.
example [Finite V] (k : ℕ) (hk : 2 ≤ k) (G : SimpleGraph V) :
    D (k - 2) G = D k G + 2 * (Nat.card V : ℚ) := by
  simpa using D_deleteEdges k hk G ∅ (Set.empty_subset _)

-- Rational k - 1 is negative at k = 0; it is NOT natural truncated subtraction.
example : D 0 (⊥ : SimpleGraph (Fin 1)) = 1 := by norm_num [D]

-- Empty hosts have no positive excess at any parameter.
example (k : ℕ) : D k (⊥ : SimpleGraph (Fin 0)) = 0 := by simp [D]

-- Criticality supplies every original R2 side condition and the host order bound.
example [Fintype V] (k : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : Erdos548.Critical.IsInducedCritical k G) :
    G.Connected ∧ ⌈(k : ℚ) / 2⌉₊ ≤ G.minDegree ∧ k ≤ G.maxDegree ∧
      k + 1 ≤ Nat.card V :=
  ⟨connected_of_inducedCritical hc, hc.minDegree_ge_ceil, hc.maxDegree_ge,
    card_ge_of_excess_pos k G hc.positive⟩

end BoundaryChecks

-- The elementary k = 2 theorem has no R2 parameter and needs no extra order assumption.
example (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : (n : ℚ) / 2 < (G.edgeSet.ncard : ℚ))
    (T : SimpleGraph (Fin 3)) (hT : T.IsTree) : Nonempty (T.Copy G) := by
  have hp : 0 < Erdos548.Critical.excess 2 G := by
    unfold Erdos548.Critical.excess
    simp only [Nat.card_fin]
    norm_num
    linarith
  exact strictAt_two G hp T hT

-- Direct finite-label interface: the smaller-host order bound is DERIVED.
-- The damaged graph is not assumed connected, critical, or to retain a degree bound.
example {n k : ℕ} (hk : 2 ≤ k) (ih : StrictAt.{0} (k - 2))
    (G : SimpleGraph (Fin n))
    (hG : ((k : ℚ) - 1) / 2 * n < (G.edgeSet.ncard : ℚ))
    (F : Set (Sym2 (Fin n))) (hF : F ⊆ G.edgeSet) (hb : F.ncard ≤ n) :
    (k - 2) + 1 ≤ n ∧ TreeUniversal (k - 2) (G.deleteEdges F) := by
  have hp : 0 < Erdos548.Critical.excess k G := by
    simpa only [Erdos548.Critical.excess, Nat.card_fin] using sub_pos.mpr hG
  have hb' : F.ncard ≤ Nat.card (Fin n) := by simpa using hb
  exact ⟨by simpa using card_ge_after_deletion k hk G hp F hF hb',
    robustUniversal_of_strictAt k hk ih G hp F hF hb'⟩

-- R2 is precisely the original degree/connectivity candidate: no density hypothesis.
example (hR2 : UniformR2.{u}) {V : Type u} [Fintype V] (k : ℕ) (hk : 3 ≤ k)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hmin : ⌈(k : ℚ) / 2⌉₊ ≤ G.minDegree) (hmax : k ≤ G.maxDegree)
    (hrob : RobustUniversal (k - 2) G) : TreeUniversal k G :=
  hR2 k hk G hconn hmin hmax hrob

-- Check ordinary Copy, not induced containment, against the exact original target.
example (hR2 : UniformR2.{0}) (n k : ℕ) (hn : k + 1 ≤ n)
    (G : SimpleGraph (Fin n))
    (hG : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ))
    (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree) : Nonempty (T.Copy G) :=
  erdos_548_of_uniformR2 hR2 n k hn G hG T hT

-- Even the weaker critical-host assumption yields the +1 statement.
example (hR2 : UniformCriticalR2.{0}) : Erdos548.Auxiliary.PlusOneStatement :=
  Erdos548.Auxiliary.plusOneStatement_of_strictThresholdStatement
    (strictThresholdStatement_of_uniformCriticalR2 hR2)
