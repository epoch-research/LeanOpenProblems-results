import Submission.NaturalSidonExtractionExplore
import Submission.ReflectionRoundingPatchExplore

/-! Exact finite template amplification with no low-digit carry. A symmetric
Sidon packet amplifies an entire representation profile, not just one target.
This file controls self-counts; mixed counts with an old set are separate. -/
namespace Erdos66TemplatePacket
open AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66NaturalSidonExtraction
  Erdos66ReflectionRoundingPatch
open scoped Classical
set_option maxHeartbeats 1500000

noncomputable def tensor (M : ℕ) (P S : Finset ℕ) : Finset ℕ :=
  (P×ˢS).image (fun ax ↦ ax.1*M+ax.2)

lemma encode_unique (M : ℕ) (hM : 0 < M) (a b x y : ℕ)
    (hx : x < M) (hy : y < M) (he : a*M+x=b*M+y) : a=b ∧ x=y := by
  have hh := congrArg (fun n ↦ n % M) he
  simp only [Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] at hh
  refine ⟨?_,hh⟩
  exact Nat.eq_of_mul_eq_mul_right hM (by omega)

lemma tensor_card (M : ℕ) (hM : 0 < M) (P S : Finset ℕ)
    (hS : ∀ x∈S, x < M) : (tensor M P S).card=P.card*S.card := by
  unfold tensor
  rw [Finset.card_image_of_injOn]
  · exact Finset.card_product _ _
  · intro ax hax by' hby he
    have hx := (Finset.mem_product.mp hax).2
    have hy := (Finset.mem_product.mp hby).2
    have hh := encode_unique M hM ax.1 by'.1 ax.2 by'.2 (hS _ hx) (hS _ hy) he
    exact Prod.ext hh.1 hh.2

/-- Exact digit factorization. The hypothesis on low sums rules out carries. -/
theorem tensor_rep (M : ℕ) (hM : 0 < M) (P S : Finset ℕ)
    (hS : ∀ x∈S, x < M) (hSS : ∀ x∈S, ∀ y∈S, x+y < M)
    (q t : ℕ) (ht : t < M) :
    sumRep (tensor M P S : Set ℕ) (q*M+t)=sumRep (P : Set ℕ) q*sumRep (S : Set ℕ) t := by
  rw [←pairs_self,←pairs_self,←pairs_self]
  unfold pairs
  rw [←Finset.card_product]
  symm
  apply Finset.card_bij (fun abxy _ ↦ (abxy.1.1*M+abxy.2.1,abxy.1.2*M+abxy.2.2))
  · intro v hv
    obtain ⟨hab,hxy⟩ := Finset.mem_product.mp hv
    obtain ⟨hab,habq⟩ := Finset.mem_filter.mp hab
    obtain ⟨hxy,hxyt⟩ := Finset.mem_filter.mp hxy
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
    · exact Finset.mem_image.mpr ⟨(v.1.1,v.2.1),Finset.mem_product.mpr ⟨ha,hx⟩,rfl⟩
    · exact Finset.mem_image.mpr ⟨(v.1.2,v.2.2),Finset.mem_product.mpr ⟨hb,hy⟩,rfl⟩
    · dsimp
      nlinarith
  · intro v hv w hw he
    have hvxy := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hv).2).1
    have hwxy := Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_product.mp hw).2).1
    have he₁ := congrArg Prod.fst he
    have he₂ := congrArg Prod.snd he
    have ha := encode_unique M hM _ _ _ _ (hS _ hvxy.1) (hS _ hwxy.1) he₁
    have hb := encode_unique M hM _ _ _ _ (hS _ hvxy.2) (hS _ hwxy.2) he₂
    exact Prod.ext (Prod.ext ha.1 hb.1) (Prod.ext ha.2 hb.2)
  · intro ab hab
    obtain ⟨hab,he⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    obtain ⟨ax,hax,haxe⟩ := Finset.mem_image.mp ha
    obtain ⟨by',hby,hbye⟩ := Finset.mem_image.mp hb
    obtain ⟨haP,hxS⟩ := Finset.mem_product.mp hax
    obtain ⟨hbP,hyS⟩ := Finset.mem_product.mp hby
    have hsum : (ax.1+by'.1)*M+(ax.2+by'.2)=q*M+t := by
      nlinarith
    have hh := encode_unique M hM _ _ _ _ (hSS _ hxS _ hyS) ht hsum
    refine ⟨((ax.1,by'.1),(ax.2,by'.2)),Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haP,hbP⟩,hh.1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hxS,hyS⟩,hh.2⟩
    · exact Prod.ext haxe hbye

lemma natReflect_mixed_off {F : Finset ℕ} (hF : NatSidon F) (T n : ℕ)
    (hT : ∀ a∈F, a ≤ T) (hn : n ≠ T) : pairs F (natReflect T F) n ≤ 1 := by
  rw [pairs_eq_filter,Finset.card_le_one]
  intro a ha b hb
  obtain ⟨haF,han,haR⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbF,hbn,hbR⟩ := Finset.mem_filter.mp hb
  obtain ⟨a',ha',ha'e⟩ := Finset.mem_image.mp haR
  obtain ⟨b',hb',hb'e⟩ := Finset.mem_image.mp hbR
  have haT := hT a' ha'
  have hbT := hT b' hb'
  have hh := hF a haF b' hb' b hbF a' ha' (by omega)
  rcases hh with hh | hh <;> omega

/-- A polynomially bounded coarse packet with one large count and bounded
counts everywhere else. This is obtained from a Sidon subset of a range. -/
theorem exists_coarse_packet (m : ℕ) :
    ∃ P : Finset ℕ, P.card=2*m ∧ (∀ a∈P, a ≤ 2*(m^4+1)) ∧
      sumRep (P : Set ℕ) (2*(m^4+1))=2*m ∧
      ∀ q : ℕ, q ≠ 2*(m^4+1) → sumRep (P : Set ℕ) q ≤ 6 := by
  obtain ⟨F,hFsub,hFc,hF⟩ := exists_natSidon_subset (Finset.range (m^4+1)) m (by simp)
  let T := 2*(m^4+1)
  have hhalf (a : ℕ) (ha : a∈F) : 2*a < T := by
    have hh := Finset.mem_range.mp (hFsub ha)
    dsimp [T]
    omega
  have hT (a : ℕ) (ha : a∈F) : a ≤ T := by have hh := hhalf a ha; omega
  have hR (a : ℕ) (ha : a∈natReflect T F) : a ≤ T := by
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    exact Nat.sub_le _ _
  have hdis : Disjoint F (natReflect T F) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hb
    have ha' := hhalf a ha
    have hb' := hhalf b hb
    omega
  have hcard : (natReflect T F).card=F.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb he
    have haT := hT a ha
    have hbT := hT b hb
    change T-a=T-b at he
    omega
  have hzeroF : pairs F F T=0 := by
    rw [pairs,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
    intro ab hab he
    have ha := hhalf ab.1 (Finset.mem_product.mp hab).1
    have hb := hhalf ab.2 (Finset.mem_product.mp hab).2
    omega
  have hzeroR : pairs (natReflect T F) (natReflect T F) T=0 := by
    rw [pairs,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
    intro ab hab he
    obtain ⟨a,ha,hae⟩ := Finset.mem_image.mp (Finset.mem_product.mp hab).1
    obtain ⟨b,hb,hbe⟩ := Finset.mem_image.mp (Finset.mem_product.mp hab).2
    have ha' := hhalf a ha
    have hb' := hhalf b hb
    omega
  refine ⟨F∪natReflect T F,?_,?_,?_,?_⟩
  · rw [Finset.card_union_of_disjoint hdis,hcard,hFc]
    omega
  · intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hT a ha
    · exact hR a ha
  · rw [←pairs_self,pairs_union_self _ _ _ hdis,hzeroF,hzeroR,natReflect_mixed F T hT,hFc]
    omega
  · intro q hq
    rw [sumRep_union_self _ _ _ hdis]
    have h₁ := natSidon_rep_le_two hF q
    have h₂ := natReflect_mixed_off hF T q hT hq
    have h₃ := natSidon_rep_le_two (natReflect_sidon hF T hT) q
    omega

/-- One finite pattern is amplified on a whole coarse block. Away from that
block, every self-count is at most six times the original template bound. -/
theorem exists_amplified_template (W : ℕ) (hW : 0 < W) (S : Finset ℕ)
    (hS : ∀ x∈S, x < W) (m U : ℕ) (hU : ∀ n, sumRep (S : Set ℕ) n ≤ U) :
    ∃ D : Finset ℕ, D.card=2*m*S.card ∧
      (∀ a∈D, a < (2*(m^4+1)+1)*(2*W)) ∧
      (∀ t < 2*W, sumRep (D : Set ℕ) ((2*(m^4+1))*(2*W)+t)=2*m*sumRep (S : Set ℕ) t) ∧
      ∀ n : ℕ, n/(2*W) ≠ 2*(m^4+1) → sumRep (D : Set ℕ) n ≤ 6*U := by
  obtain ⟨P,hPc,hPb,hPcenter,hPoff⟩ := exists_coarse_packet m
  have hM : 0 < 2*W := by omega
  have hS' : ∀ x∈S, x < 2*W := fun x hx ↦ (hS x hx).trans_le (by omega)
  have hSS : ∀ x∈S, ∀ y∈S, x+y < 2*W := by intro x hx y hy; have := hS x hx; have := hS y hy; omega
  refine ⟨tensor (2*W) P S,?_,?_,?_,?_⟩
  · rw [tensor_card (2*W) hM P S hS',hPc]
  · intro a ha
    obtain ⟨ax,hax,rfl⟩ := Finset.mem_image.mp ha
    have hp := hPb ax.1 (Finset.mem_product.mp hax).1
    have hs := hS ax.2 (Finset.mem_product.mp hax).2
    have hh := Nat.mul_le_mul_right (2*W) hp
    nlinarith
  · intro t ht
    rw [tensor_rep (2*W) hM P S hS' hSS _ t ht,hPcenter]
  · intro n hn
    have he := Nat.div_add_mod' n (2*W)
    rw [←he,tensor_rep (2*W) hM P S hS' hSS _ _ (Nat.mod_lt _ hM)]
    exact Nat.mul_le_mul (hPoff _ hn) (hU _)

end Erdos66TemplatePacket
