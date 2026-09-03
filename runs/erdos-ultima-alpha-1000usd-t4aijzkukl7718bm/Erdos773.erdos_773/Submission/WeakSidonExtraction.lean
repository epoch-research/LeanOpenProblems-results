import Submission.Hypergraph

/-!
A set with no four-distinct-entry additive collision contains a Sidon subset
of at least one quarter of its size. Thus weak Sidon upper bounds follow,
up to a constant, from ordinary Sidon upper bounds.
-/
namespace Erdos773.WeakSidonExtraction
open Finset
set_option maxHeartbeats 1000000

/-- Equal pair sums may be nontrivial only when one pair repeats its entry. -/
def WeakSidon (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a + b = c + d →
    a = b ∨ c = d ∨ (a = c ∧ b = d) ∨ (a = d ∧ b = c)

private def apTriples (A : Finset ℕ) : Finset (A × A × A) :=
  univ.filter (fun t => t.1.val < t.2.1.val ∧ t.2.1.val < t.2.2.val ∧
    t.1.val + t.2.2.val = t.2.1.val + t.2.1.val)

private def tripleSupport {A : Finset ℕ} (t : A × A × A) : Finset A :=
  {t.1, t.2.1, t.2.2}

private def apSupports (A : Finset ℕ) : Finset (Finset A) :=
  (apTriples A).image tripleSupport

private lemma middle_injective {A : Finset ℕ} (hA : WeakSidon (A : Set ℕ)) :
    Set.InjOn (fun t : A × A × A => t.2.1) (apTriples A : Set (A × A × A)) := by
  intro t ht s hs he
  obtain ⟨_, ht1, ht2, ht3⟩ := mem_filter.mp ht
  obtain ⟨_, hs1, hs2, hs3⟩ := mem_filter.mp hs
  have he' : t.2.1.val = s.2.1.val := congrArg Subtype.val he
  have heq : t.1.val + t.2.2.val = s.1.val + s.2.2.val := by omega
  have hh := hA _ t.1.property _ t.2.2.property _ s.1.property _ s.2.2.property heq
  rcases hh with hh | hh | ⟨ha,hc⟩ | ⟨ha,hc⟩
  · omega
  · omega
  · exact Prod.ext (Subtype.ext ha) (Prod.ext he (Subtype.ext hc))
  · omega

private lemma apSupports_card {A : Finset ℕ} (hA : WeakSidon (A : Set ℕ)) :
    (apSupports A).card ≤ A.card := by
  have hh : (apTriples A).card ≤ (univ : Finset A).card :=
    card_le_card_of_injOn (fun t : A × A × A => t.2.1) (fun _ _ => mem_univ _) (middle_injective hA)
  exact card_image_le.trans (by simpa using hh)

private lemma apSupports_size {A : Finset ℕ} {e : Finset A} (he : e ∈ apSupports A) :
    e.card = 3 := by
  obtain ⟨t, ht, rfl⟩ := mem_image.mp he
  obtain ⟨_, ht1, ht2, ht3⟩ := mem_filter.mp ht
  have h12 : t.1 ≠ t.2.1 := by intro h; have := congrArg Subtype.val h; omega
  have h13 : t.1 ≠ t.2.2 := by intro h; have := congrArg Subtype.val h; omega
  have h23 : t.2.1 ≠ t.2.2 := by intro h; have := congrArg Subtype.val h; omega
  simp [tripleSupport, h12, h13, h23]

private lemma ap_free_of_avoids {A : Finset ℕ} {B : Finset A}
    (hB : ∀ e ∈ apSupports A, ¬e ⊆ B) :
    ThreeAPFree ((B.image Subtype.val : Finset ℕ) : Set ℕ) := by
  intro a ha b hb c hc he
  obtain ⟨a', ha', hea⟩ := mem_image.mp ha
  obtain ⟨b', hb', heb⟩ := mem_image.mp hb
  obtain ⟨c', hc', hec⟩ := mem_image.mp hc
  rw [← hea, ← heb, ← hec] at he
  rw [← hea, ← heb]
  have havoid (a b c : A) (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
      (hab : a.val < b.val) (hbc : b.val < c.val) (he : a.val + c.val = b.val + b.val) : False := by
    apply hB (tripleSupport (a,b,c))
    · apply mem_image.mpr
      exact ⟨(a,b,c), mem_filter.mpr ⟨mem_univ _, hab, hbc, he⟩, rfl⟩
    · intro x hx
      simp only [tripleSupport, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · exact havoid a' b' c' ha' hb' hc' h (by omega) he
  · exact havoid c' b' a' hc' hb' ha' (by omega) h (by omega)

private lemma sidon_of_weak_ap_free {A : Set ℕ} (hA : WeakSidon A) (hAP : ThreeAPFree A) :
    IsSidon A := by
  intro a ha c hc b hb d hd he
  rcases hA a ha b hb c hc d hd he with hab | hcd | he | he
  · have hca := hAP hc ha hd (by omega)
    exact Or.inl ⟨hca.symm, by omega⟩
  · have hac := hAP ha hc hb (by omega)
    exact Or.inl ⟨hac, by omega⟩
  · exact Or.inl he
  · exact Or.inr he

/-- A constant-fraction extraction from weak Sidon sets; repeated-middle-root
progressions are included and removed in the proof. -/
theorem extract (A : Finset ℕ) (hA : WeakSidon (A : Set ℕ)) :
    ∃ C ⊆ A, IsSidon (C : Set ℕ) ∧ (A.card : ℝ) / 4 ≤ C.card := by
  have hn : ∀ e ∈ apSupports A, e.Nonempty := by
    intro e he
    exact card_pos.mp (by rw [apSupports_size he]; omega)
  obtain ⟨B, hB, hc⟩ := alteration_bound (apSupports A) hn (1/2) (by norm_num) (by norm_num)
  let C := B.image Subtype.val
  have hC : C ⊆ A := by
    intro c hc
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hc
    exact b.property
  have hw : WeakSidon (C : Set ℕ) := by
    intro a ha b hb c hc d hd he
    exact hA a (hC ha) b (hC hb) c (hC hc) d (hC hd) he
  have hcost : (∑ e ∈ apSupports A, (1/2 : ℝ) ^ e.card) ≤ A.card / 8 := by
    calc
      _ = ∑ _e ∈ apSupports A, (1/8 : ℝ) := by
        apply sum_congr rfl
        intro e he
        rw [apSupports_size he]
        norm_num
      _ = (apSupports A).card / 8 := by simp; ring
      _ ≤ _ := by exact_mod_cast (div_le_div_of_nonneg_right
        (show ((apSupports A).card : ℝ) ≤ A.card by exact_mod_cast apSupports_card hA)
        (by norm_num : (0 : ℝ) ≤ 8))
  refine ⟨C, hC, sidon_of_weak_ap_free hw (ap_free_of_avoids hB), ?_⟩
  have he : C.card = B.card := card_image_of_injective B Subtype.val_injective
  rw [he]
  simp only [Fintype.card_coe] at hc
  have hAc : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  linarith

/-- Weak Sidon subsets obey the ordinary maximum-cardinality bound with factor four. -/
theorem card_le_four_max {A S : Finset ℕ} (hAS : A ⊆ S) (hA : WeakSidon (A : Set ℕ)) :
    (A.card : ℝ) ≤ 4 * (Finset.maxSidonSubsetCard S : ℝ) := by
  obtain ⟨C, hC, hsidon, hcard⟩ := extract A hA
  have hh : C.card ≤ Finset.maxSidonSubsetCard S :=
    le_sup (mem_filter.mpr ⟨mem_powerset.mpr (hC.trans hAS), hsidon⟩)
  have hh' : (C.card : ℝ) ≤ Finset.maxSidonSubsetCard S := by exact_mod_cast hh
  linarith

#print axioms extract
#print axioms card_le_four_max
end Erdos773.WeakSidonExtraction
