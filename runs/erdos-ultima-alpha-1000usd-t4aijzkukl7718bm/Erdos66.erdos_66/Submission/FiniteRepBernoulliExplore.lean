import Submission.BernoulliConcentrationExplore
import Submission.IntegerBlockExplore

/-! Representation counts as disjoint Bernoulli monomials. -/
namespace Erdos66FiniteRepBernoulli
open AdditiveCombinatorics Erdos66FiniteBernoulli Erdos66BernoulliConcentration
open scoped Classical
set_option maxHeartbeats 800000

noncomputable def selected (L : ℕ) (ω : Fin (L + 1) → Bool) : Set ℕ :=
  {n | ∃ i : Fin (L + 1), i.val = n ∧ ω i = true}

lemma selected_finite (L : ℕ) (ω : Fin (L + 1) → Bool) : (selected L ω).Finite := by
  apply Set.Finite.subset (Set.finite_range (fun i : Fin (L + 1) ↦ i.val))
  rintro n ⟨i, rfl, hi⟩
  exact ⟨i, rfl⟩

lemma mem_selected (L : ℕ) (ω : Fin (L + 1) → Bool) (i : Fin (L + 1)) :
    i.val ∈ selected L ω ↔ ω i = true := by
  constructor
  · rintro ⟨j, hj, hω⟩
    have he : j = i := Fin.ext hj
    simpa only [he] using hω
  · intro hi; exact ⟨i, rfl, hi⟩

noncomputable def pairs (L q : ℕ) : Finset (Fin (L + 1) × Fin (L + 1)) :=
  Finset.univ.filter (fun a ↦ a.1.val + a.2.val = q)

noncomputable def halfPairs (L q : ℕ) : Finset (Fin (L + 1) × Fin (L + 1)) :=
  (pairs L q).filter (fun a ↦ a.1 ≤ a.2)

noncomputable def pairCoords {L : ℕ} (a : Fin (L + 1) × Fin (L + 1)) : Finset (Fin (L + 1)) :=
  {a.1, a.2}

noncomputable def pairWeight {L : ℕ} (a : Fin (L + 1) × Fin (L + 1)) : ℝ :=
  if a.1 = a.2 then 1 else 2

lemma mem_pairs {L q : ℕ} {a : Fin (L + 1) × Fin (L + 1)} :
    a ∈ pairs L q ↔ a.1.val + a.2.val = q := by simp [pairs]

lemma mem_halfPairs {L q : ℕ} {a : Fin (L + 1) × Fin (L + 1)} :
    a ∈ halfPairs L q ↔ a.1.val + a.2.val = q ∧ a.1 ≤ a.2 := by
  simp [halfPairs, mem_pairs]

lemma pairCoords_disjoint (L q : ℕ) :
    (halfPairs L q : Set (Fin (L + 1) × Fin (L + 1))).Pairwise
      (fun a b ↦ Disjoint (pairCoords a) (pairCoords b)) := by
  intro a ha b hb hab
  have ha' := mem_halfPairs.mp ha
  have hb' := mem_halfPairs.mp hb
  apply Finset.disjoint_left.mpr
  intro i hia hib
  simp only [pairCoords, Finset.mem_insert, Finset.mem_singleton] at hia hib
  have hneq : a.1.val ≠ b.1.val ∨ a.2.val ≠ b.2.val := by
    by_contra hn
    push_neg at hn
    exact hab (Prod.ext (Fin.ext hn.1) (Fin.ext hn.2))
  have hle₁ : a.1.val ≤ a.2.val := ha'.2
  have hle₂ : b.1.val ≤ b.2.val := hb'.2
  rcases hia with hia | hia <;> rcases hib with hib | hib <;>
    have he := congrArg Fin.val (hia.symm.trans hib) <;> omega

lemma pairWeight_bounds {L : ℕ} (a : Fin (L + 1) × Fin (L + 1)) :
    0 ≤ pairWeight a ∧ pairWeight a ≤ 2 := by
  unfold pairWeight
  split_ifs <;> norm_num

lemma symmetric_sum (L q : ℕ) (f : (Fin (L + 1) × Fin (L + 1)) → ℝ)
    (hf : ∀ a, f a.swap = f a) :
    (∑ a ∈ pairs L q, f a) = ∑ a ∈ halfPairs L q, pairWeight a * f a := by
  have hswap : (∑ a ∈ (pairs L q).filter (fun a ↦ ¬ a.1 ≤ a.2), f a) =
      ∑ a ∈ (pairs L q).filter (fun a ↦ a.1 < a.2), f a := by
    apply Finset.sum_equiv (Equiv.prodComm _ _)
    · intro a
      simp only [Finset.mem_filter, mem_pairs, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
      constructor
      · rintro ⟨h, hlt⟩
        exact ⟨by omega, lt_of_not_ge hlt⟩
      · rintro ⟨h, hlt⟩
        exact ⟨by omega, not_le_of_gt hlt⟩
    · intro a ha
      exact (hf a).symm
  have hsplit := Finset.sum_filter_add_sum_filter_not (pairs L q) (fun a ↦ a.1 ≤ a.2) f
  rw [hswap] at hsplit
  rw [← hsplit]
  change (∑ a ∈ halfPairs L q, f a) + _ = _
  have hstrict : (pairs L q).filter (fun a ↦ a.1 < a.2) =
      (halfPairs L q).filter (fun a ↦ a.1 ≠ a.2) := by
    ext a
    simp only [Finset.mem_filter, halfPairs]
    constructor
    · rintro ⟨ha, hlt⟩
      exact ⟨⟨ha, hlt.le⟩, ne_of_lt hlt⟩
    · rintro ⟨⟨ha, hle⟩, hne⟩
      exact ⟨ha, lt_of_le_of_ne hle hne⟩
  rw [hstrict, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases he : a.1 = a.2 <;> simp [pairWeight, he] <;> ring

lemma bit_mul_self (v : Bool) : bit v * bit v = bit v := by cases v <;> norm_num [bit]

lemma pair_monomial {L : ℕ} (a : Fin (L + 1) × Fin (L + 1)) (ω : Fin (L + 1) → Bool) :
    monomial (pairCoords a) ω = bit (ω a.1) * bit (ω a.2) := by
  by_cases he : a.1 = a.2
  · simp [monomial, pairCoords, he, bit_mul_self]
  · simp [monomial, pairCoords, he]

lemma selected_rep (L q : ℕ) (ω : Fin (L + 1) → Bool) :
    (sumRep (selected L ω) q : ℝ) =
      ∑ a ∈ halfPairs L q, pairWeight a * monomial (pairCoords a) ω := by
  have hfull : sumRep (selected L ω) q =
      ((pairs L q).filter (fun a ↦ ω a.1 = true ∧ ω a.2 = true)).card := by
    rw [sumRep_def]
    apply Finset.card_bij (fun a ha ↦
      (⟨a.1, by have hh := (Finset.mem_filter.mp ha).2.1; rcases hh with ⟨i, hi, hω⟩; omega⟩,
       ⟨a.2, by have hh := (Finset.mem_filter.mp ha).2.2; rcases hh with ⟨i, hi, hω⟩; omega⟩))
    · intro a ha
      have hh := Finset.mem_filter.mp ha
      simp only [Finset.mem_filter, mem_pairs]
      refine ⟨Finset.mem_antidiagonal.mp hh.1, ?_, ?_⟩
      · exact (mem_selected L ω _).mp hh.2.1
      · exact (mem_selected L ω _).mp hh.2.2
    · intro a ha b hb he
      have h₁ := congrArg (fun p : Fin (L + 1) × Fin (L + 1) ↦ p.1.val) he
      have h₂ := congrArg (fun p : Fin (L + 1) × Fin (L + 1) ↦ p.2.val) he
      exact Prod.ext h₁ h₂
    · intro a ha
      obtain ⟨hsum, h₁, h₂⟩ := (Finset.mem_filter.mp ha)
      refine ⟨(a.1.val, a.2.val), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr (mem_pairs.mp hsum),
          (mem_selected L ω a.1).mpr h₁, (mem_selected L ω a.2).mpr h₂⟩
      · rfl
  rw [hfull]
  have hcast : (((pairs L q).filter (fun a ↦ ω a.1 = true ∧ ω a.2 = true)).card : ℝ) =
      ∑ a ∈ pairs L q, bit (ω a.1) * bit (ω a.2) := by
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro a ha
    cases h₁ : ω a.1 <;> cases h₂ : ω a.2 <;> norm_num [bit, h₁, h₂]
  rw [hcast, symmetric_sum L q _ (fun a ↦ mul_comm _ _)]
  simp_rw [pair_monomial]

noncomputable def repMean (L q : ℕ) (p : Fin (L + 1) → ℝ) : ℝ :=
  ∑ a ∈ halfPairs L q, pairWeight a * ∏ i ∈ pairCoords a, p i

lemma rep_mgf (L q : ℕ) (p : Fin (L + 1) → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (t : ℝ) (ht : |t| ≤ 1 / 2) :
    expect p (fun ω ↦ Real.exp (t * ((sumRep (selected L ω) q : ℝ) - repMean L q p))) ≤
      Real.exp (2 * t ^ 2 * repMean L q p) := by
  simp_rw [selected_rep]
  exact centered_mgf_bound p hp (halfPairs L q) pairCoords (pairCoords_disjoint L q)
    pairWeight (fun a _ ↦ pairWeight_bounds a) t ht

noncomputable def diagCorrection (L q : ℕ) (p : Fin (L + 1) → ℝ) : ℝ :=
  ∑ a ∈ (halfPairs L q).filter (fun a ↦ a.1 = a.2), (p a.1 - p a.1 ^ 2)

lemma mean_decomposition (L q : ℕ) (p : Fin (L + 1) → ℝ) :
    repMean L q p = (∑ a ∈ pairs L q, p a.1 * p a.2) + diagCorrection L q p := by
  rw [repMean, symmetric_sum L q _ (fun a ↦ mul_comm _ _), diagCorrection,
    Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases he : a.1 = a.2
  · simp [pairWeight, pairCoords, he]
    ring
  · simp [pairWeight, pairCoords, he]

lemma diagCorrection_bounds (L q : ℕ) (p : Fin (L + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    0 ≤ diagCorrection L q p ∧ diagCorrection L q p ≤ 1 := by
  have hterm (i : Fin (L + 1)) : 0 ≤ p i - p i ^ 2 ∧ p i - p i ^ 2 ≤ 1 := by
    have hh := mul_nonneg (hp i).1 (sub_nonneg.mpr (hp i).2)
    constructor <;> nlinarith [(hp i).2, sq_nonneg (p i)]
  have hc : ((halfPairs L q).filter (fun a ↦ a.1 = a.2)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha, hae⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb, hbe⟩ := Finset.mem_filter.mp hb
    have ha := (mem_halfPairs.mp ha).1
    have hb := (mem_halfPairs.mp hb).1
    have ha' := congrArg Fin.val hae
    have hb' := congrArg Fin.val hbe
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  constructor
  · exact Finset.sum_nonneg (fun a ha ↦ (hterm a.1).1)
  · have hh := Finset.sum_le_sum (s := (halfPairs L q).filter (fun a ↦ a.1 = a.2))
      (fun a ha ↦ (hterm a.1).2)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hh
    exact hh.trans (by exact_mod_cast hc)

lemma pairs_sum_range (L q : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ a ∈ pairs L q, f a.1.val a.2.val) =
      ∑ k ∈ Finset.range (q + 1), if k ≤ L ∧ q - k ≤ L then f k (q - k) else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun a ha ↦ a.1.val)
  · intro a ha
    have hh := mem_pairs.mp ha
    simp only [Finset.mem_filter, Finset.mem_range]
    have h₁ := a.1.isLt
    have h₂ := a.2.isLt
    omega
  · intro a ha b hb he
    have ha' := mem_pairs.mp ha
    have hb' := mem_pairs.mp hb
    exact Prod.ext (Fin.ext he) (Fin.ext (by omega))
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    refine ⟨(⟨k, by omega⟩, ⟨q - k, by omega⟩), mem_pairs.mpr (by dsimp; omega), rfl⟩
  · intro a ha
    have hh := mem_pairs.mp ha
    have he : q - a.1.val = a.2.val := by omega
    simp only [he]

/-- The finite union-bound criterion applied directly to representation
functions of one finite set of natural numbers. -/
theorem exists_simultaneous_rep_bound (L Q : ℕ) (p : Fin (L + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (V ε : ℝ)
    (hV : 0 < V) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hm : ∀ q ≤ Q, repMean L q p ≤ V)
    (hsmall : 2 * (Q + 1 : ℝ) * Real.exp (-ε ^ 2 * V / 8) < 1) :
    ∃ D : Set ℕ, D.Finite ∧ (∀ n ∈ D, n ≤ L) ∧
      ∀ q ≤ Q, |(sumRep D q : ℝ) - repMean L q p| < ε * V := by
  have hsmall' : 2 * ((Finset.range (Q + 1)).card : ℝ) * Real.exp (-ε ^ 2 * V / 8) < 1 := by
    simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using hsmall
  obtain ⟨ω, hω⟩ := exists_simultaneous_bound p hp (Finset.range (Q + 1))
    (fun q ω ↦ (sumRep (selected L ω) q : ℝ)) (fun q ↦ repMean L q p) V ε hV hε hε1
    (fun q hq ↦ hm q (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hq))
    (fun q _ t ht ↦ rep_mgf L q p hp t ht) hsmall'
  refine ⟨selected L ω, selected_finite L ω, ?_, ?_⟩
  · rintro n ⟨i, rfl, hi⟩
    exact Nat.le_of_lt_succ i.isLt
  · intro q hq
    exact hω q (Finset.mem_range.mpr (by omega))

end Erdos66FiniteRepBernoulli
