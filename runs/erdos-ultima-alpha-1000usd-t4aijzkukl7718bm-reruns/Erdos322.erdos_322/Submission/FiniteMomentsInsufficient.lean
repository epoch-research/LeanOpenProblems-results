import Submission.Spec

/-! A counterexample to a proposed finite-moment bootstrap, not to Erdős 322. -/
namespace Erdos322Research.FiniteMoments

open Erdos322.MomentReduction

/-- Spikes of size `t` at the perfect `d`th powers `t^d`. -/
def sparsePowers (d n : ℕ) : ℕ :=
  if (d.nthRoot n)^d = n then d.nthRoot n else 0

lemma sparsePowers_at_power {d : ℕ} (hd : d ≠ 0) (t : ℕ) :
    sparsePowers d (t^d) = t := by
  simp [sparsePowers, Nat.nthRoot_pow hd]

/-- All moments of order less than `d` have a linear summatory bound. -/
theorem low_moments_linear (d q N : ℕ) (hd : d ≠ 0)
    (hq : 1 ≤ q) (hqd : q+1 ≤ d) (hN : 1 ≤ N) :
    countMoment (sparsePowers d) q N ≤ N := by
  classical
  let S := (Finset.Icc 1 N).filter (fun n ↦ (d.nthRoot n)^d = n)
  have hroot : 1 ≤ d.nthRoot N := (Nat.le_nthRoot_iff hd).mpr (by simpa using hN)
  have hmem (n : ℕ) (hn : n ∈ S) : d.nthRoot n ∈ Finset.Icc 1 (d.nthRoot N) := by
    obtain ⟨hn, he⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    apply Finset.mem_Icc.mpr
    constructor
    · exact (Nat.le_nthRoot_iff hd).mpr (by simpa using hn1)
    · exact (Nat.le_nthRoot_iff hd).mpr (by omega)
  have hcard : S.card ≤ d.nthRoot N := by
    have hc := Finset.card_le_card_of_injOn (fun n ↦ d.nthRoot n)
      (s := S) (t := Finset.Icc 1 (d.nthRoot N)) hmem
      (by
        intro a ha b hb he
        have ha' := (Finset.mem_filter.mp (show a ∈ (Finset.Icc 1 N).filter
          (fun n ↦ (d.nthRoot n)^d = n) from ha)).2
        have hb' := (Finset.mem_filter.mp (show b ∈ (Finset.Icc 1 N).filter
          (fun n ↦ (d.nthRoot n)^d = n) from hb)).2
        change d.nthRoot a = d.nthRoot b at he
        rw [← ha', ← hb', he])
    simpa using hc
  have hs : countMoment (sparsePowers d) q N = ∑ n ∈ S, (d.nthRoot n : ℝ)^q := by
    unfold countMoment
    simp only [S, Finset.sum_filter, sparsePowers]
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs <;> simp [show q ≠ 0 by omega]
  rw [hs]
  calc
    ∑ n ∈ S, (d.nthRoot n : ℝ)^q ≤ ∑ _n ∈ S, (d.nthRoot N : ℝ)^q := by
      apply Finset.sum_le_sum
      intro n hn
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast (Finset.mem_Icc.mp (hmem n hn)).2) q
    _ = (S.card : ℝ) * (d.nthRoot N : ℝ)^q := by simp
    _ ≤ (d.nthRoot N : ℝ) * (d.nthRoot N : ℝ)^q := by gcongr
    _ = ((d.nthRoot N)^(q+1) : ℕ) := by push_cast; ring
    _ ≤ ((d.nthRoot N)^d : ℕ) := by
      exact_mod_cast Nat.pow_le_pow_right hroot hqd
    _ ≤ N := by exact_mod_cast Nat.pow_nthRoot_le (Or.inl hd)

/-- Despite all these low-moment bounds, the sequence is not subpolynomial. -/
theorem sparsePowers_not_subpolynomial (d : ℕ) (hd : d ≠ 0) :
    ¬ Subpolynomial (sparsePowers d) := by
  intro h
  have hm := (subpolynomial_iff_quadratic_moments _).mp h
  obtain ⟨C, hC, hbound⟩ := hm (2*d+1) (by omega)
  obtain ⟨t, ht⟩ := exists_nat_gt (max C 1)
  have htC : C < (t : ℝ) := (le_max_left C 1).trans_lt ht
  have htR : (1 : ℝ) < t := (le_max_right C 1).trans_lt ht
  have htN : 1 ≤ t := by exact_mod_cast htR.le
  have hN : 1 ≤ t^d := one_le_pow₀ htN
  have hb := hbound (t^d) hN
  have hs : ((t : ℝ)^(2*d+1)) ≤ countMoment (sparsePowers d) (2*d+1) (t^d) := by
    simpa only [sparsePowers_at_power hd] using
      single_le_countMoment (sparsePowers d) (2*d+1) (t^d) hN
  have hb' : (t : ℝ)^(2*d) * t ≤ C * (t : ℝ)^(2*d) := by
    have hh := hs.trans hb
    push_cast at hh
    convert hh using 1; ring
  have hp : (0 : ℝ) < (t : ℝ)^(2*d) := pow_pos (by linarith) _
  have hle : (t : ℝ) ≤ C := by
    nlinarith [hb']
  exact htC.not_ge hle

/-- No fixed finite list of even linear moment bounds suffices for the
subpolynomial conclusion used to negate the original conjecture. -/
theorem finite_moments_do_not_suffice (Q : ℕ) :
    ∃ r : ℕ → ℕ,
      (∀ q : ℕ, 1 ≤ q → q ≤ Q → ∀ N : ℕ, 1 ≤ N → countMoment r q N ≤ N) ∧
      ¬ Subpolynomial r := by
  refine ⟨sparsePowers (Q+2), ?_, sparsePowers_not_subpolynomial _ (by omega)⟩
  intro q hq hqQ N hN
  exact low_moments_linear _ _ _ (by omega) hq (by omega) hN

end Erdos322Research.FiniteMoments
