import Submission.MatchedResidueLifting

/-!
Exact compatibility for arbitrary partial residue fibers. Unlike full-fiber
short-product injectivity, the condition here only concerns differences that
are actually present in the selected sets. No near-linear selection theorem
is asserted.
-/
namespace Erdos773.PartialResidueFibers
open Finset MatchedResidueLifting
set_option maxHeartbeats 1000000

/-- Positive differences present in a set of values. -/
def positiveDiffs (A : Finset ℕ) : Finset ℕ :=
  ((A ×ˢ A).filter (fun ab => ab.1 < ab.2)).image (fun ab => ab.2-ab.1)

lemma mem_positiveDiffs {A : Finset ℕ} {D : ℕ} :
    D ∈ positiveDiffs A ↔ ∃ a ∈ A, ∃ b ∈ A, a < b ∧ b-a=D := by
  simp only [positiveDiffs, mem_image, mem_filter, mem_product, Prod.exists]
  aesop

lemma positive_of_mem_positiveDiffs {A : Finset ℕ} {D : ℕ}
    (hD : D ∈ positiveDiffs A) : 0 < D := by
  obtain ⟨a,ha,b,hb,hab,rfl⟩ := mem_positiveDiffs.mp hD
  omega

lemma differences_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    positiveDiffs A ⊆ positiveDiffs B := by
  intro D hD
  obtain ⟨a,ha,b,hb,hab,he⟩ := mem_positiveDiffs.mp hD
  exact mem_positiveDiffs.mpr ⟨a,hAB ha,b,hAB hb,hab,he⟩

/-- Positive differences in a Sidon set have unique increasing endpoints. -/
lemma endpoints_unique {A : Finset ℕ} (hA : IsSidon (A : Set ℕ))
    {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a < b) (hcd : c < d) (he : b-a=d-c) : a=c ∧ b=d := by
  rcases hA a ha c hc d hd b hb (by omega) with h | h <;> omega

/-- Only differences realized on the selected fibers must be separated. -/
def Compatible (R : Finset ℕ) (V : ℕ → Finset ℕ) : Prop :=
  ∀ r ∈ R, ∀ s ∈ R, r ≠ s → Disjoint (positiveDiffs (V r)) (positiveDiffs (V s))

lemma label_injective {q : ℕ} {R : Finset ℕ} (hM : PairMatching q R)
    {r s : ℕ} (hr : r ∈ R) (hs : s ∈ R) (he : r^2%q=s^2%q) : r=s := by
  have hh : r^2+r^2 ≡ s^2+s^2 [MOD q] := by
    simp only [Nat.ModEq, Nat.add_mod, Nat.mod_mod, he]
  rcases hM r hr r hr s hs s hs hh with h | h <;> exact h.1

lemma fibers_disjoint {q : ℕ} {R : Finset ℕ} {V : ℕ → Finset ℕ}
    (hM : PairMatching q R)
    (hres : ∀ r ∈ R, ∀ a ∈ V r, a%q=r^2%q)
    {r s : ℕ} (hr : r ∈ R) (hs : s ∈ R) (hne : r ≠ s) :
    Disjoint (V r) (V s) := by
  apply disjoint_left.mpr
  intro a har has
  exact hne (label_injective hM hr hs ((hres r hr a har).symm.trans (hres s hs a has)))

lemma matched_labels {q : ℕ} {R : Finset ℕ} {V : ℕ → Finset ℕ}
    (hM : PairMatching q R)
    (hres : ∀ r ∈ R, ∀ a ∈ V r, a%q=r^2%q)
    {r s t u a b c d : ℕ} (hr : r ∈ R) (hs : s ∈ R) (ht : t ∈ R) (hu : u ∈ R)
    (ha : a ∈ V r) (hb : b ∈ V s) (hc : c ∈ V t) (hd : d ∈ V u)
    (he : a+b=c+d) : (r=t ∧ s=u) ∨ (r=u ∧ s=t) := by
  apply hM r hr s hs t ht u hu
  have hh := congrArg (fun n : ℕ => n%q) he
  simpa only [Nat.ModEq, Nat.add_mod, Nat.mod_mod, hres r hr a ha, hres s hs b hb,
    hres t ht c hc, hres u hu d hd] using hh

private lemma identify_aligned {R : Finset ℕ} {V : ℕ → Finset ℕ}
    (hV : ∀ r ∈ R, IsSidon (V r : Set ℕ)) (hC : Compatible R V)
    {r s a b c d : ℕ} (hr : r ∈ R) (hs : s ∈ R)
    (ha : a ∈ V r) (hb : b ∈ V s) (hc : c ∈ V r) (hd : d ∈ V s)
    (he : a+b=c+d) : (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  by_cases hrs : r=s
  · subst s
    exact hV r hr a ha c hc b hb d hd he
  have hdis := disjoint_left.mp (hC r hr s hs hrs)
  rcases lt_trichotomy a c with hac | hac | hca
  · have hdb : d < b := by omega
    exact (hdis (mem_positiveDiffs.mpr ⟨a,ha,c,hc,hac,rfl⟩)
      (mem_positiveDiffs.mpr ⟨d,hd,b,hb,hdb,by omega⟩)).elim
  · exact Or.inl ⟨hac,by omega⟩
  · have hbd : b < d := by omega
    exact (hdis (mem_positiveDiffs.mpr ⟨c,hc,a,ha,hca,rfl⟩)
      (mem_positiveDiffs.mpr ⟨b,hb,d,hd,hbd,by omega⟩)).elim

/-- Exact union criterion under modular pair matching. Fibers can be arbitrary
finite subsets; no index interval, size, or short-product condition is assumed. -/
theorem sidon_iff_compatible (q : ℕ) (R : Finset ℕ) (V : ℕ → Finset ℕ)
    (hM : PairMatching q R)
    (hres : ∀ r ∈ R, ∀ a ∈ V r, a%q=r^2%q) :
    IsSidon ((R.biUnion V : Finset ℕ) : Set ℕ) ↔
      (∀ r ∈ R, IsSidon (V r : Set ℕ)) ∧ Compatible R V := by
  constructor
  · intro hS
    have hsub (r : ℕ) (hr : r ∈ R) : V r ⊆ R.biUnion V := by
      intro a ha
      exact mem_biUnion.mpr ⟨r,hr,ha⟩
    refine ⟨fun r hr => Set.IsSidon.subset hS (hsub r hr), ?_⟩
    intro r hr s hs hrs
    apply disjoint_left.mpr
    intro D hDr hDs
    obtain ⟨a,ha,b,hb,hab,heab⟩ := mem_positiveDiffs.mp hDr
    obtain ⟨c,hc,d,hd,hcd,hecd⟩ := mem_positiveDiffs.mp hDs
    have hadis := disjoint_left.mp (fibers_disjoint hM hres hr hs hrs)
    rcases hS a (hsub r hr ha) c (hsub s hs hc) d (hsub s hs hd)
      b (hsub r hr hb) (by omega) with h | h
    · exact hadis ha (h.1 ▸ hc)
    · omega
  · rintro ⟨hV,hC⟩ a ha c hc b hb d hd he
    obtain ⟨r,hr,ha⟩ := mem_biUnion.mp ha
    obtain ⟨s,hs,hb⟩ := mem_biUnion.mp hb
    obtain ⟨t,ht,hc⟩ := mem_biUnion.mp hc
    obtain ⟨u,hu,hd⟩ := mem_biUnion.mp hd
    rcases matched_labels hM hres hr hs ht hu ha hb hc hd he with ⟨hrt,hsu⟩ | ⟨hru,hst⟩
    · subst t; subst u
      exact identify_aligned hV hC hr hs ha hb hc hd he
    · subst u; subst t
      rcases identify_aligned hV hC hr hs ha hb hd hc (by omega) with h | h
      · exact Or.inr h
      · exact Or.inl h

/-- Square values from arbitrary selected indices in one affine fiber. -/
def fiberValues (q r : ℕ) (B : Finset ℕ) : Finset ℕ :=
  B.image (fun k => (q*k+r)^2)

lemma fiberValues_residue (q r : ℕ) (B : Finset ℕ) {a : ℕ}
    (ha : a ∈ fiberValues q r B) : a%q=r^2%q := by
  obtain ⟨k,hk,rfl⟩ := mem_image.mp ha
  simp [Nat.add_mod, Nat.pow_mod]

/-- Specialized exact criterion for partial affine-square fibers. -/
theorem partial_square_iff (q : ℕ) (R : Finset ℕ) (B : ℕ → Finset ℕ)
    (hM : PairMatching q R) :
    IsSidon ((R.biUnion (fun r => fiberValues q r (B r)) : Finset ℕ) : Set ℕ) ↔
      (∀ r ∈ R, IsSidon (fiberValues q r (B r) : Set ℕ)) ∧
        Compatible R (fun r => fiberValues q r (B r)) :=
  sidon_iff_compatible q R _ hM (fun r _ _ ha => fiberValues_residue q r (B r) ha)

/-- There are no cross-fiber three-term arithmetic progressions. -/
theorem union_threeAPFree (q : ℕ) (R : Finset ℕ) (V : ℕ → Finset ℕ)
    (hM : PairMatching q R)
    (hres : ∀ r ∈ R, ∀ a ∈ V r, a%q=r^2%q)
    (hV : ∀ r ∈ R, IsSidon (V r : Set ℕ)) :
    ThreeAPFree ((R.biUnion V : Finset ℕ) : Set ℕ) := by
  intro a ha b hb c hc he
  obtain ⟨r,hr,ha⟩ := mem_biUnion.mp ha
  obtain ⟨s,hs,hb⟩ := mem_biUnion.mp hb
  obtain ⟨t,ht,hc⟩ := mem_biUnion.mp hc
  have hh : r=s ∧ t=s := by
    rcases matched_labels hM hres hr ht hs hs ha hc hb hb he with h | h <;> exact h
  obtain ⟨hrs,hts⟩ := hh
  subst r; subst t
  rcases hV s hs a ha b hb c hc b hb he with h | h <;> exact h.1

/-- Actual cardinality of the partial square-value union, without overlap loss. -/
theorem partial_card (q : ℕ) (R : Finset ℕ) (B : ℕ → Finset ℕ)
    (hq : 0 < q) (hM : PairMatching q R) :
    (R.biUnion (fun r => fiberValues q r (B r))).card = ∑ r ∈ R, (B r).card := by
  rw [card_biUnion]
  · apply sum_congr rfl
    intro r hr
    apply card_image_of_injective
    intro a b he
    have hh := Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) he
    nlinarith
  · intro r hr s hs hne
    exact fibers_disjoint hM (fun r _ _ ha => fiberValues_residue q r (B r) ha) hr hs hne

lemma two_element_sidon (x y : ℕ) : IsSidon ({x,y} : Set ℕ) := by
  intro a ha c hc b hb d hd he
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hc hb hd
  rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hb with rfl | rfl <;> rcases hd with rfl | rfl <;> omega

lemma positiveDiffs_pair {a b : ℕ} (hab : a < b) :
    positiveDiffs {a,b}={b-a} := by
  ext D
  simp only [mem_positiveDiffs, mem_insert, mem_singleton]
  constructor
  · rintro ⟨x,hx,y,hy,hxy,he⟩
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> omega
  · intro hD
    exact ⟨a,Or.inl rfl,b,Or.inr rfl,hab,hD.symm⟩

lemma positiveDiffs_fiber_pair (q r H : ℕ) (hq : 0 < q) (hH : 0 < H) :
    positiveDiffs (fiberValues q r {0,H})={q*H*(q*H+2*r)} := by
  have hp : 0 < q*H := Nat.mul_pos hq hH
  have hab : r^2 < (q*H+r)^2 :=
    Nat.pow_lt_pow_left (by omega : r < q*H+r) (by decide : (2 : ℕ) ≠ 0)
  have hv : fiberValues q r {0,H}={r^2,(q*H+r)^2} := by simp [fiberValues]
  rw [hv,positiveDiffs_pair hab]
  congr 1
  have he : (q*H+r)^2=r^2+q*H*(q*H+2*r) := by ring
  omega

/-- An unbounded family of sparse two-fiber examples. The index H can be
arbitrarily larger than q: full-fiber length bounds do not apply to it. -/
theorem sparse_two_fiber_example (q H : ℕ) (hq : 9 ≤ q) (hH : 0 < H) :
    IsSidon (({1,2} : Finset ℕ).biUnion
      (fun r => fiberValues q r {0,H}) : Set ℕ) := by
  have hq0 : 0 < q := by omega
  have hm2 : 2%q=2 := Nat.mod_eq_of_lt (by omega)
  have hm5 : 5%q=5 := Nat.mod_eq_of_lt (by omega)
  have hm8 : 8%q=8 := Nat.mod_eq_of_lt (by omega)
  have hM : PairMatching q {1,2} := by
    intro r hr s hs t ht u hu he
    simp only [mem_insert,mem_singleton] at hr hs ht hu
    rcases hr with rfl | rfl <;> rcases hs with rfl | rfl <;>
      rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;>
      simp_all [Nat.ModEq]
  apply (partial_square_iff q {1,2} (fun _ => {0,H}) hM).mpr
  constructor
  · intro r hr
    simpa [fiberValues] using two_element_sidon (r^2) ((q*H+r)^2)
  · intro r hr s hs hrs
    simp only [mem_insert,mem_singleton] at hr hs
    rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
    · exact (hrs rfl).elim
    · rw [positiveDiffs_fiber_pair q 1 H hq0 hH,positiveDiffs_fiber_pair q 2 H hq0 hH]
      simp only [disjoint_singleton]
      have hp : 0 < q*H := Nat.mul_pos hq0 hH
      nlinarith
    · rw [positiveDiffs_fiber_pair q 2 H hq0 hH,positiveDiffs_fiber_pair q 1 H hq0 hH]
      simp only [disjoint_singleton]
      have hp : 0 < q*H := Nat.mul_pos hq0 hH
      nlinarith
    · exact (hrs rfl).elim

/-- Taking H=q*t in the preceding example makes the two selected gap products
coincide modulo q. Their ACTUAL positive differences nevertheless stay distinct. -/
theorem short_product_alias (q t : ℕ) :
    (2*1*(q*t))%q=(2*2*(q*t))%q := by
  simp [Nat.mul_mod]

#print axioms sparse_two_fiber_example
#print axioms short_product_alias
#print axioms sidon_iff_compatible
#print axioms partial_square_iff
#print axioms union_threeAPFree
#print axioms partial_card
end Erdos773.PartialResidueFibers
