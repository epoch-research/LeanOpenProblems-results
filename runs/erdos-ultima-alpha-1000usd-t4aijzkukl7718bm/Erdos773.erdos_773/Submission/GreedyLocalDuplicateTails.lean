import Submission.GreedyCodegreeDrift
import Submission.GreedyOverlapError

/-!
Uniform-prefix local duplicate tails without linearity. Distinct original
edges are retained as pattern indices, including repeated witness supports.
These are estimates for the stopped process, not a running-time theorem.
-/
namespace Erdos773.GreedyLocalDuplicateTails
open Finset GreedyHypergraphState GreedyCommonNeighbors GreedyWitnessPacking
open StoppedGreedyMoments GreedyConfigurationTails FourUniformRegularization
open HypergraphDegreeTrim HypergraphLinearization
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [DecidableEq α]

/-- Two different edges sharing the designated vertex u and another vertex v. -/
def patterns (H : Finset (Finset α)) (u : α) : Finset (Pattern α) :=
  (extensions H (H.filter (fun e => u ∈ e)) u (fun e => e.erase u)).filter
    (fun x => x.1 ≠ x.2.2)

lemma mem_patterns {H : Finset (Finset α)} {u v : α} {e f : Finset α} :
    (e,v,f) ∈ patterns H u ↔
      e ∈ H ∧ f ∈ H ∧ u ∈ e ∧ u ∈ f ∧ v ∈ e ∧ v ∈ f ∧ v ≠ u ∧ e ≠ f := by
  simp only [patterns,mem_filter,mem_extensions,mem_erase]
  tauto

lemma pattern_swap {H : Finset (Finset α)} {u v : α} {e f : Finset α}
    (h : (e,v,f) ∈ patterns H u) : (f,v,e) ∈ patterns H u := by
  simp only [mem_patterns] at *
  tauto

lemma patterns_card_le {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4) (u : α) (D K : ℕ) (hD : degree H u ≤ D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K) :
    (patterns H u).card ≤ 3*D*K := by
  have hs (e : Finset α) (he : e ∈ H.filter (fun e => u ∈ e)) : (e.erase u).card ≤ 3 := by
    obtain ⟨he,hu⟩ := mem_filter.mp he
    rw [card_erase_of_mem hu,h4 e he]
  have hn (e : Finset α) (_he : e ∈ H.filter (fun e => u ∈ e))
      (v : α) (hv : v ∈ e.erase u) : u ≠ v := (mem_erase.mp hv).1.symm
  calc
    _ ≤ (extensions H (H.filter (fun e => u ∈ e)) u (fun e => e.erase u)).card := card_filter_le _ _
    _ ≤ (H.filter (fun e => u ∈ e)).card*3*K := extensions_card_le H _ u _ 3 K hs hn hK
    _ ≤ D*3*K := Nat.mul_le_mul_right K (Nat.mul_le_mul_right 3 hD)
    _ = _ := by ring

def witness (x : Pattern α) : Finset α := GreedyOverlapError.witness (x.1,x.2.2)

lemma pattern_overlap {H : Finset (Finset α)} {u : α} {x : Pattern α}
    (hx : x ∈ patterns H u) : (x.1,x.2.2) ∈ overlaps H := by
  rcases x with ⟨e,v,f⟩
  obtain ⟨he,hf,hue,huf,hve,hvf,hvu,hef⟩ := mem_patterns.mp hx
  have hs : ({u,v}:Finset α) ⊆ e ∩ f := by
    simp only [insert_subset_iff,singleton_subset_iff,mem_inter]
    exact ⟨⟨hue,huf⟩,hve,hvf⟩
  have hc := card_le_card hs
  have hp : ({u,v}:Finset α).card = 2 := by simp [hvu.symm]
  rw [hp] at hc
  exact mem_filter.mpr ⟨mem_product.mpr ⟨he,hf⟩,hef,hc⟩

lemma witness_card {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    {u : α} {x : Pattern α} (hx : x ∈ patterns H u) : (witness x).card = 4 :=
  GreedyOverlapError.witness_card h4 h2 (pattern_overlap hx)

lemma first_role_incidence {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4) (u a : α) (K : ℕ)
    (hK : ∀ b c : α, b ≠ c → pairDegree H b c ≤ K) :
    ((patterns H u).filter (fun x => a ∈ x.1 \ x.2.2)).card ≤ 2*K^2 := by
  by_cases hau : a = u
  · subst a
    have he : (patterns H u).filter (fun x => u ∈ x.1 \ x.2.2) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro ⟨e,v,f⟩ hx
      obtain ⟨hx,ha⟩ := mem_filter.mp hx
      exact (mem_sdiff.mp ha).2 (mem_patterns.mp hx).2.2.2.1
    rw [he]
    exact Nat.zero_le _
  have hsub : (patterns H u).filter (fun x => a ∈ x.1 \ x.2.2) ⊆
      extensions H (H.filter (fun e => u ∈ e ∧ a ∈ e)) u (fun e => e \ {u,a}) := by
    rintro ⟨e,v,f⟩ hx
    obtain ⟨hx,ha⟩ := mem_filter.mp hx
    obtain ⟨he,hf,hue,huf,hve,hvf,hvu,_⟩ := mem_patterns.mp hx
    obtain ⟨ha,haf⟩ := mem_sdiff.mp ha
    have hva : v ≠ a := fun h => haf (h ▸ hvf)
    exact mem_extensions.mpr ⟨mem_filter.mpr ⟨he,hue,ha⟩,
      mem_sdiff.mpr ⟨hve,by simpa only [mem_insert,mem_singleton,not_or] using And.intro hvu hva⟩,
      hf,huf,hvf⟩
  have hs (e : Finset α) (he : e ∈ H.filter (fun e => u ∈ e ∧ a ∈ e)) :
      (e \ {u,a}).card ≤ 2 := by
    obtain ⟨he,hu,ha⟩ := mem_filter.mp he
    have hp : ({u,a}:Finset α) ⊆ e := by simp [insert_subset_iff,hu,ha]
    rw [card_sdiff_of_subset hp,h4 e he]
    simp [(Ne.symm hau)]
  have hn (e : Finset α) (_he : e ∈ H.filter (fun e => u ∈ e ∧ a ∈ e))
      (v : α) (hv : v ∈ e \ {u,a}) : u ≠ v := by
    intro huv
    exact (mem_sdiff.mp hv).2 (by simp [huv])
  calc
    _ ≤ (extensions H (H.filter (fun e => u ∈ e ∧ a ∈ e)) u (fun e => e \ {u,a})).card := card_le_card hsub
    _ ≤ (H.filter (fun e => u ∈ e ∧ a ∈ e)).card*2*K :=
      extensions_card_le H _ u _ 2 K hs hn hK
    _ ≤ K*2*K := Nat.mul_le_mul_right K (Nat.mul_le_mul_right 2 (hK u a (Ne.symm hau)))
    _ = _ := by ring

lemma second_role_incidence {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4) (u a : α) (K : ℕ)
    (hK : ∀ b c : α, b ≠ c → pairDegree H b c ≤ K) :
    ((patterns H u).filter (fun x => a ∈ x.2.2 \ x.1)).card ≤ 2*K^2 := by
  have hc : ((patterns H u).filter (fun x => a ∈ x.2.2 \ x.1)).card ≤
      ((patterns H u).filter (fun x => a ∈ x.1 \ x.2.2)).card := by
    apply card_le_card_of_injOn (fun x => (x.2.2,x.2.1,x.1))
    · rintro ⟨e,v,f⟩ hx
      obtain ⟨hx,ha⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨pattern_swap hx,ha⟩
    · rintro ⟨e,v,f⟩ hx ⟨e',v',f'⟩ hy heq
      simp only [Prod.mk.injEq] at heq ⊢
      tauto
  exact hc.trans (first_role_incidence h4 u a K hK)

lemma witness_incidence {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4) (u a : α) (K : ℕ)
    (hK : ∀ b c : α, b ≠ c → pairDegree H b c ≤ K) :
    ((patterns H u).filter (fun x => a ∈ witness x)).card ≤ 4*K^2 := by
  have he : (patterns H u).filter (fun x => a ∈ witness x) =
      ((patterns H u).filter (fun x => a ∈ x.1 \ x.2.2)) ∪
      ((patterns H u).filter (fun x => a ∈ x.2.2 \ x.1)) := by
    ext x
    simp only [witness,GreedyOverlapError.witness,mem_filter,mem_union]
    tauto
  rw [he]
  have hc := card_union_le
    ((patterns H u).filter (fun x => a ∈ x.1 \ x.2.2))
    ((patterns H u).filter (fun x => a ∈ x.2.2 \ x.1))
  have h1 := first_role_incidence h4 u a K hK
  have h2 := second_role_incidence h4 u a K hK
  omega

variable [Fintype α]

def cost (H : Finset (Finset α)) (u : α) (I : Finset α) : ℕ :=
  ((patterns H u).filter (fun x => witness x ⊆ I)).card

omit [Fintype α] in
lemma cost_mono (H : Finset (Finset α)) (u : α) {I J : Finset α} (hIJ : I ⊆ J) :
    cost H u I ≤ cost H u J := by
  apply card_le_card
  intro x hx
  obtain ⟨hx,hxi⟩ := mem_filter.mp hx
  exact mem_filter.mpr ⟨hx,hxi.trans hIJ⟩

/-- Duplicate excess at u is covered by the indexed local witnesses. -/
theorem excess_bound (H : Finset (Finset α)) (I : Finset α) (u : α) :
    duplicateExcess H I u ≤ cost H u I := by
  apply (GreedyOverlapError.excess_at_vertex_bound H I u).trans
  have hs : (((overlaps H).filter (fun ef => GreedyOverlapError.witness ef ⊆ I)).filter
      (fun ef => u ∈ ef.1 ∩ ef.2)) ⊆
      (((patterns H u).filter (fun x => witness x ⊆ I)).image (fun x => (x.1,x.2.2))) := by
    rintro ⟨e,f⟩ hef
    obtain ⟨hef,hu⟩ := mem_filter.mp hef
    obtain ⟨hef,hwi⟩ := mem_filter.mp hef
    obtain ⟨hef,hne,hcard⟩ := mem_filter.mp hef
    obtain ⟨he,hf⟩ := mem_product.mp hef
    have hvpos : 0 < ((e ∩ f).erase u).card := by
      rw [card_erase_of_mem hu]
      omega
    obtain ⟨v,hv⟩ := card_pos.mp hvpos
    obtain ⟨hvu,hv⟩ := mem_erase.mp hv
    obtain ⟨hue,huf⟩ := mem_inter.mp hu
    obtain ⟨hve,hvf⟩ := mem_inter.mp hv
    refine mem_image.mpr ⟨(e,v,f),mem_filter.mpr ⟨?_,hwi⟩,rfl⟩
    exact mem_patterns.mpr ⟨he,hf,hue,huf,hve,hvf,hvu,hne⟩
  exact (card_le_card hs).trans card_image_le

def prefixBad (H : Finset (Finset α)) (u : α) (B : ℕ) (I : Finset α) : Prop :=
  ∃ J ⊆ I, B < duplicateExcess H J u

/-- All selected subsets are controlled, so in particular every prefix of
    each realizing stopped-greedy path is controlled. -/
theorem prefix_duplicate_tail {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (u : α) (D K : ℕ) (hD : degree H u ≤ D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (L : ℕ) (hL : 0 < L) (n : ℕ) (hn : n ≤ L) (k : ℕ) :
    expectation H L n (event (prefixBad H u (16*K^2*k))) ≤
      ((3*D*K).choose (k+1):ℝ)*((n:ℝ)/L)^(4*(k+1)) := by
  have hdom (I : Finset α) : event (prefixBad H u (16*K^2*k)) I ≤
      event (fun I => 4*(4*K^2)*k < cost H u I) I := by
    classical
    by_cases hb : prefixBad H u (16*K^2*k) I
    · have hlt : 4*(4*K^2)*k < cost H u I := by
        obtain ⟨J,hJI,hb⟩ := hb
        have hh := hb.trans_le ((excess_bound H J u).trans (cost_mono H u hJI))
        convert hh using 1; ring
      simp only [event,if_pos hb,if_pos hlt,le_refl]
    · simpa only [event,if_neg hb] using event_nonneg
        (fun I => 4*(4*K^2)*k < cost H u I) I
  have hs (x : Pattern α) (hx : x ∈ patterns H u) := witness_card h4 h2 hx
  calc
    _ ≤ expectation H L n (event (fun I => 4*(4*K^2)*k < cost H u I)) :=
      expectation_mono H L n hdom
    _ ≤ ((patterns H u).card.choose (k+1):ℝ)*((n:ℝ)/L)^(4*(k+1)) :=
      packing_tail H L hL n hn (patterns H u) witness 4 (4*K^2) 4 k
        (fun x hx => card_pos.mp (by rw [hs x hx]; decide))
        (fun x hx => (hs x hx).le) (fun x hx => (hs x hx).ge)
        (fun a => witness_incidence h4 u a K hK)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.choose_le_choose (k+1) (patterns_card_le h4 u D K hD hK)

theorem prefix_duplicate_exponential_tail {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (u : α) (D K : ℕ) (hD : degree H u ≤ D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (L : ℕ) (hL : 0 < L) (n : ℕ) (hn : n ≤ L) (k : ℕ) :
    expectation H L n (event (prefixBad H u (16*K^2*k))) ≤
      (9*D*K*((n:ℝ)/L)^4/(k+1))^(k+1) := by
  have hh := (prefix_duplicate_tail h4 h2 u D K hD hK L hL n hn k).trans
    (choose_mul_pow_le (3*D*K) (k+1) 4 (by omega) ((n:ℝ)/L) (by positivity))
  convert hh using 1; push_cast; ring

#print axioms patterns_card_le
#print axioms witness_card
#print axioms first_role_incidence
#print axioms second_role_incidence
#print axioms witness_incidence
#print axioms excess_bound
#print axioms prefix_duplicate_tail
#print axioms prefix_duplicate_exponential_tail
end
end Erdos773.GreedyLocalDuplicateTails
