import Submission.PolynomialBoostError

/-! Packing bounds admit a quantitative, rather than exact, marginal transfer.
The final survivor theorem is conditional on an explicit robust main-term inequality. -/
namespace Erdos970.FiniteSelberg

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def boostProbability (q q' : ι → ℝ) (i : ι) : ℝ :=
  (q' i - q i) / (1 - q i)

theorem boostProbability_bounds (q q' : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i < 1 ∧ q i ≤ q' i ∧ q' i ≤ 1) (i : ι) :
    0 ≤ boostProbability q q' i ∧ boostProbability q q' i ≤ q' i := by
  have hd : 0 < 1 - q i := sub_pos.mpr (hq i).2.1
  constructor
  · exact div_nonneg (sub_nonneg.mpr (hq i).2.2.1) hd.le
  · apply (div_le_iff₀ hd).mpr
    have hh : 0 ≤ q i * (1 - q' i) :=
      mul_nonneg (hq i).1 (sub_nonneg.mpr (hq i).2.2.2)
    nlinarith

theorem boostProbability_identity (q q' : ι → ℝ)
    (hq : ∀ i, q i < 1) (i : ι) :
    boostProbability q q' i + (1 - boostProbability q q' i) * q i = q' i := by
  have hd : 1 - q i ≠ 0 := (sub_pos.mpr (hq i)).ne'
  unfold boostProbability
  field_simp
  ring

/-- A nonnegative packing polynomial has a controlled upper bound after passing to
larger reference marginals. This does not claim exact preservation of its old bound. -/
theorem dominating_polynomial_upper {α : Type*} (A : Finset α)
    (c : α → ℝ) (S : α → Finset ι) (B : Finset ι)
    (hS : ∀ t ∈ A, S t ⊆ B) (q q' : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i < 1 ∧ q i ≤ q' i ∧ q' i ≤ 1)
    (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ Finset.range m, hitMonomial T (ω j)) -
        (m : ℝ) * ∏ i ∈ T, q i| ≤ 1)
    (cap : ℝ)
    (hcap : (∑ j ∈ Finset.range m, ∑ t ∈ A, c t * hitMonomial (S t) (ω j)) ≤ cap)
    (hnonneg : ∀ v : ι → Bool, 0 ≤ ∑ t ∈ A, c t * hitMonomial (S t) v) :
    (∑ j ∈ Finset.range m, average (boostProbability q q') (fun η =>
      ∑ t ∈ A, c t * hitMonomial (S t) (fun i => ω j i || η i))) ≤
        cap + (m : ℝ) * average q' (fun v => ∑ t ∈ A, c t * hitMonomial (S t) v) +
          2 * (∑ t ∈ A, |c t|) * ∑ i ∈ B, q' i := by
  have ha (i : ι) : 0 ≤ boostProbability q q' i ∧ boostProbability q q' i ≤ 1 :=
    ⟨(boostProbability_bounds q q' hq i).1,
      (boostProbability_bounds q q' hq i).2.trans (hq i).2.2.2⟩
  have he := polynomial_boost_remainder_change A c S B hS
    (boostProbability q q') q ha m ω herr
  simp_rw [boostProbability_identity q q' (fun i => (hq i).2.1)] at he
  have hcost : 0 ≤ ∑ t ∈ A, |c t| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hsum : (∑ i ∈ B, boostProbability q q' i) ≤ ∑ i ∈ B, q' i :=
    Finset.sum_le_sum (fun i hi => (boostProbability_bounds q q' hq i).2)
  have herror := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2 * ∑ t ∈ A, |c t|)
  have hmean : 0 ≤ average q (fun v => ∑ t ∈ A, c t * hitMonomial (S t) v) :=
    average_nonneg q (fun i => ⟨(hq i).1, (hq i).2.1.le⟩) _ hnonneg
  have hmmean := mul_nonneg (Nat.cast_nonneg m) hmean
  have he' := (abs_le.mp he).2
  linarith

/-- Reference polynomials may use packing corrections provided their main term
also pays for the explicit marginal-transfer error. No uniform existence of such
certificates is asserted here. -/
theorem survivor_from_dominating_packing_polynomials {α β κ : Type*}
    (A : Finset α) (c : α → ℝ) (S : α → Finset ι)
    (K : Finset κ) (D : κ → Finset β) (d : κ → β → ℝ)
    (T : κ → β → Finset ι) (B : κ → Finset ι) (w cap : κ → ℝ)
    (hD : ∀ u ∈ K, ∀ t ∈ D u, T u t ⊆ B u)
    (hw : ∀ u ∈ K, 0 ≤ w u)
    (q q' : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i < 1 ∧ q i ≤ q' i ∧ q' i ≤ 1)
    (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ U : Finset ι,
      |(∑ j ∈ Finset.range m, hitMonomial U (ω j)) -
        (m : ℝ) * ∏ i ∈ U, q i| ≤ 1)
    (hcap : ∀ u ∈ K, (∑ j ∈ Finset.range m,
      ∑ t ∈ D u, d u t * hitMonomial (T u t) (ω j)) ≤ cap u)
    (hpack : ∀ u ∈ K, ∀ v : ι → Bool,
      0 ≤ ∑ t ∈ D u, d u t * hitMonomial (T u t) v)
    (hpoint : ∀ v : ι → Bool, v ≠ (fun _ => false) →
      (∑ t ∈ A, c t * hitMonomial (S t) v) ≤
        ∑ u ∈ K, w u * ∑ t ∈ D u, d u t * hitMonomial (T u t) v)
    (hmain : (∑ t ∈ A, |c t|) + ∑ u ∈ K, w u *
      (cap u + (m : ℝ) * average q'
        (fun v => ∑ t ∈ D u, d u t * hitMonomial (T u t) v) +
        2 * (∑ t ∈ D u, |d u t|) * ∑ i ∈ B u, q' i) <
      (m : ℝ) * average q' (fun v => ∑ t ∈ A, c t * hitMonomial (S t) v)) :
    ∃ j < m, ∀ i, ω j i = false := by
  classical
  let a := boostProbability q q'
  have ha (i : ι) : 0 ≤ a i ∧ a i ≤ 1 :=
    ⟨(boostProbability_bounds q q' hq i).1,
      (boostProbability_bounds q q' hq i).2.trans (hq i).2.2.2⟩
  have hprob (i : ι) : a i + (1 - a i) * q i = q' i :=
    boostProbability_identity q q' (fun i => (hq i).2.1) i
  let F (v : ι → Bool) := ∑ t ∈ A, c t * hitMonomial (S t) v
  let G (u : κ) (v : ι → Bool) := ∑ t ∈ D u, d u t * hitMonomial (T u t) v
  let budget (u : κ) := cap u + (m : ℝ) * average q' (G u) +
    2 * (∑ t ∈ D u, |d u t|) * ∑ i ∈ B u, q' i
  have hupper (u : κ) (hu : u ∈ K) :
      (∑ j ∈ Finset.range m, average a (fun η => G u (fun i => ω j i || η i))) ≤
        budget u :=
    dominating_polynomial_upper (D u) (d u) (T u) (B u) (hD u hu)
      q q' hq m ω herr (cap u) (hcap u hu) (hpack u hu)
  have hbase := boosted_polynomial_interval_error A c S a q ha m ω herr
  simp_rw [hprob] at hbase
  by_contra hbad
  push_neg at hbad
  have hp (j : ℕ) (hj : j < m) (η : ι → Bool) :
      F (fun i => ω j i || η i) ≤ ∑ u ∈ K, w u * G u (fun i => ω j i || η i) := by
    apply hpoint
    intro heq
    obtain ⟨i, hi⟩ := hbad j hj
    have hh := congrFun heq i
    cases hω : ω j i
    · exact hi hω
    · simp [hω] at hh
  have hpointsum : (∑ j ∈ Finset.range m, average a (fun η => F (fun i => ω j i || η i))) ≤
      ∑ j ∈ Finset.range m, ∑ u ∈ K, w u *
        average a (fun η => G u (fun i => ω j i || η i)) := by
    apply Finset.sum_le_sum
    intro j hj
    have hh := average_mono a ha _ _ (hp j (Finset.mem_range.mp hj))
    simpa only [average_sum, average_mul_const] using hh
  have hbudget : (∑ j ∈ Finset.range m, ∑ u ∈ K, w u *
      average a (fun η => G u (fun i => ω j i || η i))) ≤ ∑ u ∈ K, w u * budget u := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro u hu
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hupper u hu) (hw u hu)
  have hle := hpointsum.trans hbudget
  change |(∑ j ∈ Finset.range m, average a (fun η => F (fun i => ω j i || η i))) -
    (m : ℝ) * average q' F| ≤ ∑ t ∈ A, |c t| at hbase
  change (∑ t ∈ A, |c t|) + ∑ u ∈ K, w u * budget u < (m : ℝ) * average q' F at hmain
  have hh := (abs_le.mp hbase).1
  linarith

#print axioms dominating_polynomial_upper
#print axioms survivor_from_dominating_packing_polynomials

end Erdos970.FiniteSelberg
