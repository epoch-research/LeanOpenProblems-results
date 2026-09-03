import Submission.CoreFilteredDeletion
import Submission.SelbergSharpUpper

/-! Upper-sieve estimates for the core-filtered deletion budget. Each residue
row is rescaled separately. There is no assertion of independence between
rows and no suppression of the summed upper-sieve remainders. -/
namespace Erdos970.GapAverages
open Finset Real

lemma intervalCount_le_sharp_log (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime)
    (m R : ℕ) (hR : 0 < R) (hfull : ∀ a, a.Prime → a ≤ R → a ∈ Q)
    (r : Phase Q) : intervalCount Q m r ≤
      (m : ℝ) / log (R + 1) + (exp 2 * R / log (R + 1)) ^ 2 := by
  classical
  have hh := FiniteSelberg.prime_survivors_le_sharp_log
    (fun q : Q => q.val) (fun q => hQ q.val q.property) Subtype.val_injective
    (phaseResidues Q r) m R hR (fun a ha haR => ⟨⟨a, hfull a ha haR⟩, rfl⟩)
  rw [← CoverFibers.phaseSurvivors_card]
  convert hh using 1
  congr 2
  ext x
  simp only [CoverFibers.phaseSurvivors, mem_filter, Nat.ModEq, phaseResidues_mem,
    Nat.mod_eq_of_lt (r _).isLt]

/-- Uniform upper bound on one row, with its exact rounded length. -/
theorem rowCount_le_sharp_log (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime)
    (m p R : ℕ) (hp : 0 < p) (hc : ∀ q ∈ Q, p.Coprime q)
    (hR : 0 < R) (hfull : ∀ a, a.Prime → a ≤ R → a ∈ Q)
    (a : Fin p) (r : Phase Q) : rowCount Q m p a r ≤
      (residueHits m p a : ℝ) / log (R + 1) + (exp 2 * R / log (R + 1)) ^ 2 := by
  rw [rowCount_eq_progression Q m p hp]
  let e := affinePhaseEquiv Q hQ a.val p hc
  have he : e (e.symm r) = r := e.apply_symm_apply r
  have hh := progressionCount_affine Q hQ a.val p
    (IntervalRescaling.progressionLength m p a.val hp) hc (e.symm r)
  change progressionCount Q a.val p _ (e (e.symm r)) = _ at hh
  rw [he] at hh
  rw [hh, progressionLength_eq_residueHits m p hp a]
  exact intervalCount_le_sharp_log Q hQ _ R hR hfull (e.symm r)

/-- A convenient slightly enlarged row bound, with no phase-dependent length. -/
theorem rowCount_le_sharp_log_real (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime)
    (m p R : ℕ) (hp : 0 < p) (hc : ∀ q ∈ Q, p.Coprime q)
    (hR : 0 < R) (hfull : ∀ a, a.Prime → a ≤ R → a ∈ Q)
    (a : Fin p) (r : Phase Q) : rowCount Q m p a r ≤
      ((m : ℝ) / p + 1) / log (R + 1) + (exp 2 * R / log (R + 1)) ^ 2 := by
  apply (rowCount_le_sharp_log Q hQ m p R hp hc hR hfull a r).trans
  apply add_le_add _ le_rfl
  exact div_le_div_of_nonneg_right (residueHits_le_real m p hp a)
    (log_nonneg (by exact_mod_cast Nat.le_add_left 1 R))

/-- Sum all core-filtered row bounds, allowing a different cutoff on each row.
In particular every upper-sieve error is retained in the sum. -/
theorem filteredDeletionBudget_le_sharp_rows (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (R : P → ℕ)
    (hR : ∀ p : P, p.val ∉ Q → 0 < R p)
    (hfull : ∀ p : P, p.val ∉ Q → ∀ a, a.Prime → a ≤ R p → a ∈ Q)
    (r : Phase P) : filteredDeletionBudget P Q hQP m r ≤
      ∑ p : P, if p.val ∈ Q then 0 else
        ((m : ℝ) / p.val + 1) / log (R p + 1) +
          (exp 2 * R p / log (R p + 1)) ^ 2 := by
  classical
  unfold filteredDeletionBudget
  apply sum_le_sum
  intro p hp
  by_cases hpQ : p.val ∈ Q
  · simp only [hpQ, if_true, le_refl]
  · simp only [hpQ, if_false]
    have hc : ∀ q ∈ Q, p.val.Coprime q := by
      intro q hq
      apply (Nat.coprime_primes (hP p.val p.property) (hP q (hQP hq))).mpr
      intro he
      exact hpQ (he.symm ▸ hq)
    exact rowCount_le_sharp_log_real Q (fun q hq => hP q (hQP hq)) m p.val (R p)
      (hP p.val p.property).pos hc (hR p hpQ) (hfull p hpQ) (r p) (corePhase P Q hQP r)

/-- Cover exclusion with a core-filtered, rather than raw, deletion budget. -/
theorem exponent_le_retained_log_of_filtered_cover (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (B b : ℝ)
    (htail : lowCountFraction P m B ≤ exp (-b))
    (r : Phase P) (hr : intervalCount P m r = 0)
    (hB : filteredDeletionBudget P Q hQP m r ≤ B) :
    b ≤ ∑ p ∈ Q, log (p : ℝ) := by
  have hpos : 0 < ∏ p ∈ Q, (p : ℝ)⁻¹ := prod_pos
    (fun p hp => inv_pos.mpr (by exact_mod_cast (hP p (hQP hp)).pos))
  have hh := log_le_log hpos
    ((reciprocal_le_lowCountFraction_filtered P Q hQP hP m B r hr hB).trans htail)
  rw [prod_inv_distrib, log_inv, log_prod
    (fun p hp => by exact_mod_cast (hP p (hQP hp)).ne_zero), log_exp] at hh
  linarith only [hh]

/-- Fully explicit sufficient inequality combining Selberg rows and a low-count
tail. The inequality on the row sum is not claimed to hold unconditionally. -/
theorem survivor_of_sharp_rows_low_tail (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (R : P → ℕ)
    (hR : ∀ p : P, p.val ∉ Q → 0 < R p)
    (hfull : ∀ p : P, p.val ∉ Q → ∀ a, a.Prime → a ≤ R p → a ∈ Q)
    (B b : ℝ)
    (hrows : (∑ p : P, if p.val ∈ Q then 0 else
      ((m : ℝ) / p.val + 1) / log (R p + 1) +
        (exp 2 * R p / log (R p + 1)) ^ 2) ≤ B)
    (htail : lowCountFraction P m B ≤ exp (-b))
    (hb : (∑ p ∈ Q, log (p : ℝ)) < b) (r : ℕ → ℕ) :
    ∃ x < m, ∀ p ∈ P, ¬x ≡ r p [MOD p] := by
  classical
  by_contra hbad
  push_neg at hbad
  let s : Phase P := fun p => ⟨r p.val % p.val, Nat.mod_lt _ (hP p.val p.property).pos⟩
  have hs : intervalCount P m s = 0 := by
    apply count_zero_of_cover
    intro x hx
    obtain ⟨p, hp, hxp⟩ := hbad x hx
    exact ⟨⟨p, hp⟩, hxp⟩
  exact hb.not_ge (exponent_le_retained_log_of_filtered_cover P Q hQP hP m B b
    htail s hs ((filteredDeletionBudget_le_sharp_rows P Q hQP hP m R hR hfull s).trans hrows))

#print axioms rowCount_le_sharp_log
#print axioms filteredDeletionBudget_le_sharp_rows
#print axioms survivor_of_sharp_rows_low_tail
end Erdos970.GapAverages
