import Submission.PartialFiberSelection
import Submission.WeightedHypergraph

/-!
Vertex-independent selection, with a separate probability for each partial
residue fiber. The resulting cost is the exact common-difference overlap cost,
weighted by the square of each of the two fiber probabilities. No favorable
asymptotic family of square fibers is assumed to exist.
-/
namespace Erdos773.WeightedPartialFibers
open Finset MatchedResidueLifting PartialResidueFibers PartialFiberSelection
set_option maxHeartbeats 2000000

/-- Extend fiber probabilities to values. Under pair matching the fibers are
disjoint, so at most one summand is nonzero. -/
noncomputable def valueWeight (R : Finset ℕ) (V : ℕ → Finset ℕ)
    (p : ℕ → ℝ) (a : ℕ) : ℝ := ∑ r ∈ R, if a ∈ V r then p r else 0

lemma valueWeight_nonneg {R : Finset ℕ} {V : ℕ → Finset ℕ} {p : ℕ → ℝ}
    (hp : ∀ r ∈ R, 0 ≤ p r) (a : ℕ) : 0 ≤ valueWeight R V p a := by
  apply sum_nonneg
  intro r hr
  split <;> [exact hp r hr; exact le_refl 0]

lemma valueWeight_eq {q : ℕ} {R : Finset ℕ} {V : ℕ → Finset ℕ}
    (hM : PairMatching q R)
    (hres : ∀ r ∈ R, ∀ a ∈ V r, a%q=r^2%q)
    (p : ℕ → ℝ) {r a : ℕ} (hr : r ∈ R) (ha : a ∈ V r) :
    valueWeight R V p a=p r := by
  unfold valueWeight
  rw [sum_eq_single r]
  · simp [ha]
  · intro s hs hsr
    have hn : a ∉ V s := fun has =>
      disjoint_left.mp (fibers_disjoint hM hres hr hs hsr.symm) ha has
    simp [hn]
  · exact fun hn => (hn hr).elim

lemma keySupport_product {q : ℕ} {R : Finset ℕ} {V : ℕ → Finset ℕ}
    (hM : PairMatching q R)
    (hres : ∀ r ∈ R, ∀ a ∈ V r, a%q=r^2%q)
    (p : ℕ → ℝ) {k : Σ _ : ℕ × ℕ, ℕ} (hk : k ∈ crossKeys R V) :
    (∏ a ∈ keySupport V k, valueWeight R V p a)=p k.1.1^2*p k.1.2^2 := by
  obtain ⟨hkR,hkD⟩ := mem_sigma.mp hk
  obtain ⟨hkR,hrs⟩ := mem_filter.mp hkR
  obtain ⟨hr,hs⟩ := mem_product.mp hkR
  obtain ⟨hDr,hDs⟩ := mem_inter.mp hkD
  obtain ⟨ha,hb,hab,_⟩ := diffRep_spec hDr
  obtain ⟨hc,hd,hcd,_⟩ := diffRep_spec hDs
  have hdis := disjoint_left.mp (fibers_disjoint hM hres hr hs (ne_of_lt hrs))
  have hac : (diffRep (V k.1.1) k.2).1 ≠ (diffRep (V k.1.2) k.2).1 := by
    intro he; exact hdis ha (he ▸ hc)
  have had : (diffRep (V k.1.1) k.2).1 ≠ (diffRep (V k.1.2) k.2).2 := by
    intro he; exact hdis ha (he ▸ hd)
  have hbc : (diffRep (V k.1.1) k.2).2 ≠ (diffRep (V k.1.2) k.2).1 := by
    intro he; exact hdis hb (he ▸ hc)
  have hbd : (diffRep (V k.1.1) k.2).2 ≠ (diffRep (V k.1.2) k.2).2 := by
    intro he; exact hdis hb (he ▸ hd)
  simp only [keySupport, prod_insert, mem_insert, mem_singleton, ne_of_lt hab,
    ne_of_lt hcd, hac, had, hbc, hbd, or_self, not_false_eq_true, prod_singleton,
    valueWeight_eq hM hres p hr ha, valueWeight_eq hM hres p hr hb,
    valueWeight_eq hM hres p hs hc, valueWeight_eq hM hres p hs hd]
  ring

lemma weighted_obstruction_cost {q : ℕ} {R : Finset ℕ} {V : ℕ → Finset ℕ}
    (hM : PairMatching q R)
    (hres : ∀ r ∈ R, ∀ a ∈ V r, a%q=r^2%q)
    (hV : ∀ r ∈ R, IsSidon (V r : Set ℕ))
    (p : ℕ → ℝ) (hp : ∀ r ∈ R, 0 ≤ p r) :
    (∑ e ∈ sidonObstructions (R.biUnion V), ∏ a ∈ e, valueWeight R V p a.val) ≤
      ∑ k ∈ crossKeys R V, p k.1.1^2*p k.1.2^2 := by
  classical
  let U := R.biUnion V
  let E := (sidonObstructions U).image (fun e : Finset U => e.image Subtype.val)
  have hE : E ⊆ (crossKeys R V).image (keySupport V) := by
    intro S hS
    obtain ⟨e,he,rfl⟩ := mem_image.mp hS
    obtain ⟨_,a,c,b,d,rfl,he,hnt⟩ := mem_filter.mp he
    have hn : ¬((a.val=c.val ∧ b.val=d.val) ∨ (a.val=d.val ∧ b.val=c.val)) := by
      simpa only [Subtype.ext_iff] using hnt
    obtain ⟨k,hk,hK⟩ := collision_key hM hres hV
      a.property b.property c.property d.property he hn
    apply mem_image.mpr
    refine ⟨k,hk,?_⟩
    rw [hK]
    ext x
    simp [or_left_comm]
  have hnn (S : Finset ℕ) : 0 ≤ ∏ a ∈ S, valueWeight R V p a :=
    prod_nonneg (fun a _ => valueWeight_nonneg hp a)
  calc
    _ = ∑ S ∈ E, ∏ a ∈ S, valueWeight R V p a := by
      rw [sum_image (Finset.image_injective Subtype.val_injective).injOn]
      apply sum_congr rfl
      intro e he
      exact (prod_image Subtype.val_injective.injOn).symm
    _ ≤ ∑ S ∈ (crossKeys R V).image (keySupport V),
        ∏ a ∈ S, valueWeight R V p a :=
      sum_le_sum_of_subset_of_nonneg hE (fun S _ _ => hnn S)
    _ ≤ ∑ k ∈ crossKeys R V, ∏ a ∈ keySupport V k, valueWeight R V p a :=
      sum_image_le_of_nonneg (fun S _ => hnn S)
    _ = _ := sum_congr rfl (fun k hk => keySupport_product hM hres p hk)

/-- Nonuniform selection from the actual value union. Every key is counted
once, and every support probability has two distinct factors from each fiber. -/
theorem alteration (q : ℕ) (R : Finset ℕ) (V : ℕ → Finset ℕ)
    (hM : PairMatching q R)
    (hres : ∀ r ∈ R, ∀ a ∈ V r, a%q=r^2%q)
    (hV : ∀ r ∈ R, IsSidon (V r : Set ℕ))
    (p : ℕ → ℝ) (hp : ∀ r ∈ R, 0 ≤ p r) (hp1 : ∀ r ∈ R, p r ≤ 1) :
    (∑ r ∈ R, p r*(V r).card) - (∑ k ∈ crossKeys R V, p k.1.1^2*p k.1.2^2) ≤
      (maxSidonSubsetCard (R.biUnion V) : ℝ) := by
  classical
  have hw1 : ∀ a ∈ R.biUnion V, valueWeight R V p a ≤ 1 := by
    intro a ha
    obtain ⟨r,hr,ha⟩ := mem_biUnion.mp ha
    rw [valueWeight_eq hM hres p hr ha]
    exact hp1 r hr
  have hsum : (∑ a ∈ R.biUnion V, valueWeight R V p a) =
      ∑ r ∈ R, p r*(V r).card := by
    rw [sum_biUnion (fun r hr s hs hne => fibers_disjoint hM hres hr hs hne)]
    apply sum_congr rfl
    intro r hr
    calc
      _ = ∑ _a ∈ V r, p r := sum_congr rfl (fun a ha => valueWeight_eq hM hres p hr ha)
      _ = _ := by simp [mul_comm]
  have hh := WeightedSelection.sidon_alteration_bound (R.biUnion V) (valueWeight R V p)
    (fun a _ => valueWeight_nonneg hp a) hw1
  have hc := weighted_obstruction_cost hM hres hV p hp
  rw [hsum] at hh
  linarith

/-- The same bound written as a sum over unordered pairs of fiber labels. -/
theorem overlap_alteration (q : ℕ) (R : Finset ℕ) (V : ℕ → Finset ℕ)
    (hM : PairMatching q R)
    (hres : ∀ r ∈ R, ∀ a ∈ V r, a%q=r^2%q)
    (hV : ∀ r ∈ R, IsSidon (V r : Set ℕ))
    (p : ℕ → ℝ) (hp : ∀ r ∈ R, 0 ≤ p r) (hp1 : ∀ r ∈ R, p r ≤ 1) :
    (∑ r ∈ R, p r*(V r).card) -
      (∑ rs ∈ (R ×ˢ R).filter (fun rs => rs.1 < rs.2),
        p rs.1^2*p rs.2^2*(positiveDiffs (V rs.1) ∩ positiveDiffs (V rs.2)).card) ≤
      (maxSidonSubsetCard (R.biUnion V) : ℝ) := by
  have hh := alteration q R V hM hres hV p hp hp1
  simpa [crossKeys, sum_sigma, mul_comm] using hh

/-- Specialization to actual squares with arbitrary partial index sets. -/
theorem partial_square_alteration (q : ℕ) (R : Finset ℕ) (B : ℕ → Finset ℕ)
    (hq : 0 < q) (hM : PairMatching q R)
    (hB : ∀ r ∈ R, IsSidon (fiberValues q r (B r) : Set ℕ))
    (p : ℕ → ℝ) (hp : ∀ r ∈ R, 0 ≤ p r) (hp1 : ∀ r ∈ R, p r ≤ 1) :
    (∑ r ∈ R, p r*(B r).card) -
      (∑ rs ∈ (R ×ˢ R).filter (fun rs => rs.1 < rs.2),
        p rs.1^2*p rs.2^2*
          (positiveDiffs (fiberValues q rs.1 (B rs.1)) ∩
            positiveDiffs (fiberValues q rs.2 (B rs.2))).card) ≤
      (maxSidonSubsetCard (R.biUnion (fun r => fiberValues q r (B r))) : ℝ) := by
  have hc (r : ℕ) : (fiberValues q r (B r)).card=(B r).card := by
    apply card_image_of_injective
    intro a b he
    have hh := Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) he
    nlinarith
  have hh := overlap_alteration q R (fun r => fiberValues q r (B r)) hM
    (fun r _ _ ha => fiberValues_residue q r (B r) ha) hB p hp hp1
  simpa only [hc] using hh

/-- Labels whose individual probability is at least t. -/
noncomputable def threshold (R : Finset ℕ) (p : ℕ → ℝ) (t : ℝ) : Finset ℕ :=
  R.filter (fun r => t ≤ p r)

/-- Discarding low-probability fibers loses at most t times the original
vertex count from the weighted mass. This statement needs no arithmetic. -/
theorem threshold_mass (R : Finset ℕ) (m : ℕ → ℕ) (p : ℕ → ℝ)
    (hp1 : ∀ r ∈ R, p r ≤ 1) (t : ℝ) (ht : 0 ≤ t) :
    (∑ r ∈ R, p r*m r) - t*(∑ r ∈ R, m r : ℕ) ≤
      (∑ r ∈ threshold R p t, m r : ℕ) := by
  classical
  have hh : (∑ r ∈ R, p r*m r) ≤
      ∑ r ∈ R, ((if t ≤ p r then (m r : ℝ) else 0) + t*m r) := by
    apply sum_le_sum
    intro r hr
    split_ifs with htr
    · have hp := mul_le_mul_of_nonneg_right (hp1 r hr) (Nat.cast_nonneg (m r) : (0:ℝ) ≤ m r)
      have ht' : 0 ≤ t*m r := mul_nonneg ht (Nat.cast_nonneg (m r))
      linarith
    · have hp := mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge htr))
        (Nat.cast_nonneg (m r) : (0:ℝ) ≤ m r)
      simpa only [zero_add] using hp
  rw [sum_add_distrib, ← sum_filter, ← mul_sum] at hh
  simp only [threshold, Nat.cast_sum] at *
  linarith

lemma crossKeys_mono {R S : Finset ℕ} (hRS : R ⊆ S) (V : ℕ → Finset ℕ) :
    crossKeys R V ⊆ crossKeys S V := by
  intro k hk
  obtain ⟨hr,hD⟩ := mem_sigma.mp hk
  obtain ⟨hr,hrs⟩ := mem_filter.mp hr
  obtain ⟨hr,hs⟩ := mem_product.mp hr
  exact mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hRS hr,hRS hs⟩,hrs⟩,hD⟩

/-- Unweighted overlap count after thresholding. Division by t^4 gives the
cost bound when t is positive. -/
theorem threshold_cost (R : Finset ℕ) (V : ℕ → Finset ℕ) (p : ℕ → ℝ)
    (t : ℝ) (ht : 0 ≤ t) :
    t^4*(crossKeys (threshold R p t) V).card ≤
      ∑ k ∈ crossKeys R V, p k.1.1^2*p k.1.2^2 := by
  classical
  calc
    _ = ∑ _k ∈ crossKeys (threshold R p t) V, t^4 := by simp [mul_comm]
    _ ≤ ∑ k ∈ crossKeys (threshold R p t) V, p k.1.1^2*p k.1.2^2 := by
      apply sum_le_sum
      intro k hk
      obtain ⟨hr,_⟩ := mem_sigma.mp hk
      obtain ⟨hr,_⟩ := mem_filter.mp hr
      obtain ⟨hr,hs⟩ := mem_product.mp hr
      have htr := (mem_filter.mp hr).2
      have hts := (mem_filter.mp hs).2
      have hpr := pow_le_pow_left₀ ht htr 2
      have hps := pow_le_pow_left₀ ht hts 2
      calc
        t^4 = t^2*t^2 := by ring
        _ ≤ p k.1.1^2*p k.1.2^2 := mul_le_mul hpr hps (sq_nonneg t) (sq_nonneg _)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg
      (crossKeys_mono (filter_subset _ _) V) (fun k _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

#print axioms overlap_alteration
#print axioms partial_square_alteration
#print axioms threshold_mass
#print axioms threshold_cost
end Erdos773.WeightedPartialFibers
