import Submission.PartialResidueFibers
import Submission.Hypergraph
import Submission.APFreeExtraction

/-!
Selection from individually Sidon partial residue fibers. The cost is the
number of shared positive differences between different fibers, not the
stronger short-product condition for full fibers. The needed near-linear
family with sufficiently small overlap cost has NOT been constructed.
-/
namespace Erdos773.PartialFiberSelection
open Finset MatchedResidueLifting PartialResidueFibers
set_option maxHeartbeats 2000000

noncomputable def diffRep (A : Finset ℕ) (D : ℕ) : ℕ × ℕ :=
  if h : D ∈ positiveDiffs A then Classical.choose (mem_image.mp h) else (0,0)

lemma diffRep_spec {A : Finset ℕ} {D : ℕ} (hD : D ∈ positiveDiffs A) :
    (diffRep A D).1 ∈ A ∧ (diffRep A D).2 ∈ A ∧
    (diffRep A D).1 < (diffRep A D).2 ∧
    (diffRep A D).2-(diffRep A D).1=D := by
  rw [diffRep, dif_pos hD]
  have hh := Classical.choose_spec (mem_image.mp hD)
  obtain ⟨hp,he⟩ := hh
  obtain ⟨hp,hlt⟩ := mem_filter.mp hp
  obtain ⟨ha,hb⟩ := mem_product.mp hp
  exact ⟨ha,hb,hlt,he⟩

lemma diffRep_eq {A : Finset ℕ} (hA : IsSidon (A : Set ℕ))
    {a b D : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hab : a < b) (he : b-a=D) :
    diffRep A D=(a,b) := by
  have hh := diffRep_spec (mem_positiveDiffs.mpr ⟨a,ha,b,hb,hab,he⟩)
  have h := endpoints_unique hA hh.1 hh.2.1 ha hb hh.2.2.1 hab (hh.2.2.2.trans he.symm)
  exact Prod.ext h.1 h.2

/-- Each unordered pair of distinct residue labels is counted once. -/
def crossKeys (R : Finset ℕ) (V : ℕ → Finset ℕ) : Finset (Σ _ : ℕ × ℕ, ℕ) :=
  ((R ×ˢ R).filter (fun rs => rs.1 < rs.2)).sigma
    (fun rs => positiveDiffs (V rs.1) ∩ positiveDiffs (V rs.2))

noncomputable def keySupport (V : ℕ → Finset ℕ) (k : Σ _ : ℕ × ℕ, ℕ) : Finset ℕ :=
  {(diffRep (V k.1.1) k.2).1, (diffRep (V k.1.1) k.2).2,
    (diffRep (V k.1.2) k.2).1, (diffRep (V k.1.2) k.2).2}

lemma crossKeys_card (R : Finset ℕ) (V : ℕ → Finset ℕ) :
    (crossKeys R V).card =
      ∑ rs ∈ (R ×ˢ R).filter (fun rs => rs.1 < rs.2), (positiveDiffs (V rs.1) ∩ positiveDiffs (V rs.2)).card := by
  simp [crossKeys]

private lemma oriented_key {R : Finset ℕ} {V : ℕ → Finset ℕ} {r s D : ℕ}
    (hr : r ∈ R) (hs : s ∈ R) (hrs : r ≠ s)
    (hD : D ∈ positiveDiffs (V r) ∩ positiveDiffs (V s)) :
    ∃ k ∈ crossKeys R V, keySupport V k=keySupport V ⟨(r,s),D⟩ := by
  rcases lt_or_gt_of_ne hrs with hrs | hsr
  · exact ⟨⟨(r,s),D⟩,mem_sigma.mpr
      ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hr,hs⟩,hrs⟩,hD⟩,rfl⟩
  · refine ⟨⟨(s,r),D⟩,mem_sigma.mpr
      ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hs,hr⟩,hsr⟩,
        mem_inter.mpr ⟨(mem_inter.mp hD).2,(mem_inter.mp hD).1⟩⟩,?_⟩
    ext x
    simp [keySupport,or_comm,or_left_comm,or_assoc]

private lemma aligned_support {V : ℕ → Finset ℕ} {r s a b c d : ℕ}
    (hr : IsSidon (V r : Set ℕ)) (hs : IsSidon (V s : Set ℕ))
    (ha : a ∈ V r) (hb : b ∈ V s) (hc : c ∈ V r) (hd : d ∈ V s)
    (he : a+b=c+d) (hac : a ≠ c) :
    ∃ D ∈ positiveDiffs (V r) ∩ positiveDiffs (V s),
      keySupport V ⟨(r,s),D⟩ = {a,b,c,d} := by
  rcases lt_or_gt_of_ne hac with hac | hca
  · have hdb : d < b := by omega
    refine ⟨c-a,mem_inter.mpr ⟨mem_positiveDiffs.mpr ⟨a,ha,c,hc,hac,rfl⟩,
      mem_positiveDiffs.mpr ⟨d,hd,b,hb,hdb,by omega⟩⟩,?_⟩
    have hrp := diffRep_eq hr ha hc hac rfl
    have hsp := diffRep_eq hs hd hb hdb (show b-d=c-a by omega)
    ext x
    simp [keySupport,hrp,hsp,or_comm,or_left_comm]
  · have hbd : b < d := by omega
    refine ⟨a-c,mem_inter.mpr ⟨mem_positiveDiffs.mpr ⟨c,hc,a,ha,hca,rfl⟩,
      mem_positiveDiffs.mpr ⟨b,hb,d,hd,hbd,by omega⟩⟩,?_⟩
    have hrp := diffRep_eq hr hc ha hca rfl
    have hsp := diffRep_eq hs hb hd hbd (show d-b=a-c by omega)
    ext x
    simp [keySupport,hrp,hsp,or_left_comm]

lemma collision_key {q : ℕ} {R : Finset ℕ} {V : ℕ → Finset ℕ}
    (hM : PairMatching q R)
    (hres : ∀ r ∈ R, ∀ a ∈ V r, a%q=r^2%q)
    (hV : ∀ r ∈ R, IsSidon (V r : Set ℕ))
    {a b c d : ℕ} (ha : a ∈ R.biUnion V) (hb : b ∈ R.biUnion V)
    (hc : c ∈ R.biUnion V) (hd : d ∈ R.biUnion V)
    (he : a+b=c+d) (hnt : ¬((a=c ∧ b=d) ∨ (a=d ∧ b=c))) :
    ∃ k ∈ crossKeys R V, keySupport V k={a,b,c,d} := by
  obtain ⟨r,hr,ha⟩ := mem_biUnion.mp ha
  obtain ⟨s,hs,hb⟩ := mem_biUnion.mp hb
  obtain ⟨t,ht,hc⟩ := mem_biUnion.mp hc
  obtain ⟨u,hu,hd⟩ := mem_biUnion.mp hd
  rcases matched_labels hM hres hr hs ht hu ha hb hc hd he with ⟨hrt,hsu⟩ | ⟨hru,hst⟩
  · subst t; subst u
    have hrs : r ≠ s := by
      intro h; subst s
      exact hnt (hV r hr a ha c hc b hb d hd he)
    have hac : a ≠ c := by intro h; apply hnt; omega
    obtain ⟨D,hD,hE⟩ := aligned_support (hV r hr) (hV s hs) ha hb hc hd he hac
    obtain ⟨k,hk,hkE⟩ := oriented_key hr hs hrs hD
    exact ⟨k,hk,hkE.trans hE⟩
  · subst u; subst t
    have hrs : r ≠ s := by
      intro h; subst s
      exact hnt (hV r hr a ha c hc b hb d hd he)
    have had : a ≠ d := by intro h; apply hnt; omega
    obtain ⟨D,hD,hE⟩ := aligned_support (hV r hr) (hV s hs) ha hb hd hc (by omega) had
    obtain ⟨k,hk,hkE⟩ := oriented_key hr hs hrs hD
    refine ⟨k,hk,?_⟩
    rw [hkE,hE]
    ext x
    simp [or_comm]

/-- Every actual obstruction is represented by a common positive difference
of two selected fibers. Endpoint uniqueness makes the key determine its support. -/
theorem obstruction_card_bound (q : ℕ) (R : Finset ℕ) (V : ℕ → Finset ℕ)
    (hM : PairMatching q R)
    (hres : ∀ r ∈ R, ∀ a ∈ V r, a%q=r^2%q)
    (hV : ∀ r ∈ R, IsSidon (V r : Set ℕ)) :
    (sidonObstructions (R.biUnion V)).card ≤ (crossKeys R V).card := by
  classical
  let U := R.biUnion V
  apply le_trans _ (card_image_le (f := keySupport V) (s := crossKeys R V))
  apply card_le_card_of_injOn (fun e : Finset U => e.image Subtype.val)
  · intro e he
    obtain ⟨_,a,c,b,d,rfl,he,hnt⟩ := mem_filter.mp he
    have hn : ¬((a.val=c.val ∧ b.val=d.val) ∨ (a.val=d.val ∧ b.val=c.val)) := by
      simpa only [Subtype.ext_iff] using hnt
    obtain ⟨k,hk,hE⟩ := collision_key hM hres hV a.property b.property c.property d.property he hn
    apply mem_image.mpr
    refine ⟨k,hk,?_⟩
    rw [hE]
    ext x
    simp [or_left_comm]
  · exact (Finset.image_injective Subtype.val_injective).injOn

private lemma obstruction_card_four {A : Finset ℕ} (hAP : ThreeAPFree (A : Set ℕ))
    {e : Finset A} (he : e ∈ sidonObstructions A) : e.card=4 := by
  classical
  obtain ⟨_,a,c,b,d,rfl,he,hnt⟩ := mem_filter.mp he
  have hn : ¬((a.val=c.val ∧ b.val=d.val) ∨ (a.val=d.val ∧ b.val=c.val)) := by
    simpa only [Subtype.ext_iff] using hnt
  have hd := APFreeExtraction.four_distinct_of_collision hAP
    a.property b.property c.property d.property he hn
  have hab : a ≠ b := fun h => hd.1 (congrArg Subtype.val h)
  have hac : a ≠ c := fun h => hd.2.1 (congrArg Subtype.val h)
  have had : a ≠ d := fun h => hd.2.2.1 (congrArg Subtype.val h)
  have hbc : b ≠ c := fun h => hd.2.2.2.1 (congrArg Subtype.val h)
  have hbd : b ≠ d := fun h => hd.2.2.2.2.1 (congrArg Subtype.val h)
  have hcd : c ≠ d := fun h => hd.2.2.2.2.2 (congrArg Subtype.val h)
  simp [hab,hac,had,hbc.symm,hbd,hcd]

/-- Factor-free alteration on a union of individually Sidon partial fibers.
Three-entry obstructions are absent by modular pair matching. -/
theorem alteration (q : ℕ) (R : Finset ℕ) (V : ℕ → Finset ℕ)
    (hM : PairMatching q R)
    (hres : ∀ r ∈ R, ∀ a ∈ V r, a%q=r^2%q)
    (hV : ∀ r ∈ R, IsSidon (V r : Set ℕ))
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    p*(R.biUnion V).card-p^4*(crossKeys R V).card ≤
      (maxSidonSubsetCard (R.biUnion V) : ℝ) := by
  classical
  have hAP := union_threeAPFree q R V hM hres hV
  have hc := obstruction_card_bound q R V hM hres hV
  have hsum : (∑ e ∈ sidonObstructions (R.biUnion V), p^e.card) =
      p^4*(sidonObstructions (R.biUnion V)).card := by
    calc
      _ = ∑ _e ∈ sidonObstructions (R.biUnion V), p^4 := by
        apply sum_congr rfl
        intro e he
        rw [obstruction_card_four hAP he]
      _ = _ := by simp [mul_comm]
  have hh := sidon_alteration_bound (R.biUnion V) p hp hp1
  rw [hsum] at hh
  have hcR : ((sidonObstructions (R.biUnion V)).card : ℝ) ≤ (crossKeys R V).card := by
    exact_mod_cast hc
  have hcost := mul_le_mul_of_nonneg_left hcR (pow_nonneg hp 4)
  linarith

/-- Specialization to actual square values, with exact partial-fiber cardinality. -/
theorem partial_square_alteration (q : ℕ) (R : Finset ℕ) (B : ℕ → Finset ℕ)
    (hq : 0 < q) (hM : PairMatching q R)
    (hB : ∀ r ∈ R, IsSidon (fiberValues q r (B r) : Set ℕ))
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    p*(∑ r ∈ R, (B r).card : ℕ)-p^4*(crossKeys R (fun r => fiberValues q r (B r))).card ≤
      (maxSidonSubsetCard (R.biUnion (fun r => fiberValues q r (B r))) : ℝ) := by
  have hh := alteration q R (fun r => fiberValues q r (B r)) hM
    (fun r _ _ ha => fiberValues_residue q r (B r) ha) hB p hp hp1
  rw [partial_card q R B hq hM] at hh
  exact hh

#print axioms obstruction_card_bound
#print axioms alteration
#print axioms partial_square_alteration
end Erdos773.PartialFiberSelection
