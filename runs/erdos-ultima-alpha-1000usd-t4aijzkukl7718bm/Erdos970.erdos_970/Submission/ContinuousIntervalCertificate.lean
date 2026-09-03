import Submission.ContinuousIntervalTransfer
import Submission.ContinuousIntervalChord

/-! A one-stage Jensen transfer for arbitrary regular interval certificates.
Chord replacements preserve the integer-length certificate exactly. -/
namespace Erdos970.ContinuousInterval
open IntervalRescaling BlockSieve.SievePolynomial

def IntervalBounds (L U : ℝ → ℝ) (α : ℝ) (p : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ (m : ℕ) (r : ℕ → ℕ), L m ≤ α * (count p r k m : ℝ) ∧
    α * (count p r k m : ℝ) ≤ U m

lemma IntervalBounds.patch {L U : ℝ → ℝ} {d α : ℝ} {p : ℕ → ℕ} {k : ℕ}
    (hreg : Regular d L U) (h : IntervalBounds L U α p k) (a : ℕ) :
    IntervalBounds (patchLower L a) (patchUpper U a) α p k := by
  intro m r
  rw [patchLower_nat hreg, patchUpper_nat hreg]
  exact h m r

/-- The one-stage argument only requires regularity and bounds at natural
lengths. In particular, lattice chord patches are valid between stages. -/
theorem IntervalBounds.step {L U : ℝ → ℝ} {d α : ℝ} {p : ℕ → ℕ} {k : ℕ}
    (hreg : Regular d L U) (h : IntervalBounds L U α p k) (hα : 0 ≤ α)
    (hp : ∀ i < k, 0 < p i) (hpk : 1 < p k)
    (hcop : ∀ j < k, (p k).Coprime (p j))
    (Q : ℝ) (hQlo : 1 / (p k : ℝ) ≤ Q) (hQhi : Q ≤ 1) :
    IntervalBounds (stepLower Q L U) (stepUpper Q L U)
      (α * (1 - boost (1 / (p k : ℝ)) Q)) p (k + 1) := by
  intro m r
  have hprev := h m r
  have hpR : (1 : ℝ) < p k := by exact_mod_cast hpk
  have hq : 1 / (p k : ℝ) < 1 := (div_lt_one (by linarith)).mpr hpR
  let a := boost (1 / (p k : ℝ)) Q
  have ha := boost_bounds _ _ hq hQlo hQhi
  change 0 ≤ a ∧ a ≤ 1 at ha
  have hb : 0 ≤ 1 - a := sub_nonneg.mpr ha.2
  obtain ⟨c, s, hcl, hcu, he⟩ := firstHitCount_rescale p r k m (by omega) hp hcop
  have hchild := h c s
  let v := a * (m : ℝ) + (1 - a) * (c : ℝ)
  have hv : 0 ≤ v := add_nonneg (mul_nonneg ha.1 (Nat.cast_nonneg m))
    (mul_nonneg hb (Nat.cast_nonneg c))
  have hsand := mixture_sandwich (m : ℝ) c (1 / (p k : ℝ)) Q a ha.2
    (boost_identity _ _ hq) (quotient_sandwich_sharp m (p k) c (by omega) hcl hcu)
  have hJlo := hreg.lower_convex.2 (Set.mem_univ (m : ℝ)) (Set.mem_univ (c : ℝ)) ha.1 hb
    (show a + (1 - a) = 1 by ring)
  have hJhi := hreg.upper_concave.2
    (show (m : ℝ) ∈ Set.Ici 0 from (Nat.cast_nonneg m : (0 : ℝ) ≤ m))
    (show (c : ℝ) ∈ Set.Ici 0 from (Nat.cast_nonneg c : (0 : ℝ) ≤ c)) ha.1 hb
    (show a + (1 - a) = 1 by ring)
  simp only [smul_eq_mul] at hJlo hJhi
  have hlow : L (((m : ℝ) + 1) * Q - 1) ≤
      a * (α * (count p r k m : ℝ)) + (1 - a) * (α * (count p s k c : ℝ)) := by
    calc
      _ ≤ L v := hreg.lower_mono hsand.1
      _ ≤ a * L m + (1 - a) * L c := hJlo
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hprev.1 ha.1)
        (mul_le_mul_of_nonneg_left hchild.1 hb)
  have hhigh : a * (α * (count p r k m : ℝ)) + (1 - a) * (α * (count p s k c : ℝ)) ≤
      U (1 + ((m : ℝ) - 1) * Q) := by
    calc
      _ ≤ a * U m + (1 - a) * U c := add_le_add (mul_le_mul_of_nonneg_left hprev.2 ha.1)
        (mul_le_mul_of_nonneg_left hchild.2 hb)
      _ ≤ U v := hJhi
      _ ≤ _ := hreg.upper_mono hv (hv.trans hsand.2) hsand.2
  have hpart : (count p r (k + 1) m : ℝ) + count p s k c = count p r k m := by
    have hh := count_succ_partition p r k m
    rw [he] at hh
    exact_mod_cast (show count p r (k + 1) m + count p s k c = count p r k m by omega)
  have hnonneg : 0 ≤ (α * (1 - a)) * (count p r (k + 1) m : ℝ) :=
    mul_nonneg (mul_nonneg hα hb) (Nat.cast_nonneg _)
  have hscaled : (α * (1 - a)) * (count p r (k + 1) m : ℝ) =
      α * (count p r k m : ℝ) -
      (a * (α * (count p r k m : ℝ)) + (1 - a) * (α * (count p s k c : ℝ))) := by
    nlinarith [congrArg (fun x : ℝ => α * (1 - a) * x) hpart]
  constructor
  · change clip (fun x => L x - U (1 + (x - 1) * Q)) m ≤ _
    rw [clip, max_eq_right (Nat.cast_nonneg m)]
    apply max_le hnonneg
    change L m - U (1 + ((m : ℝ) - 1) * Q) ≤ (α * (1 - a)) * _
    rw [hscaled]
    linarith [hprev.1]
  · change (α * (1 - a)) * (count p r (k + 1) m : ℝ) ≤ U m - L (((m : ℝ) + 1) * Q - 1)
    rw [hscaled]
    linarith [hprev.2]

#print axioms IntervalBounds.step
end Erdos970.ContinuousInterval
