import Submission.BalancedOrientation
import Submission.UniformEvenMean

/-! Agreement and disagreement of two balanced orientations give complementary
even restrictions. This does not assert a uniform cycle-count comparison. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.OrientationComparison
open BalancedOrientation CountCritical CycleNumberSubmodularity
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {A B : V → V → ℕ}
set_option maxHeartbeats 1000000

lemma reverse_equality (hA : IsBalanced G A) (hB : IsBalanced G B) (x y : V) :
    A x y = B x y ↔ A y x = B y x := by
  have ha := hA.1 x y
  have hb := hB.1 x y
  omega

def disagreement (hA : IsBalanced G A) (hB : IsBalanced G B) : SimpleGraph V where
  Adj x y := A x y ≠ B x y
  symm := by intro x y h he; exact h ((reverse_equality hA hB x y).mpr he)
  loopless := by
    intro x h
    have ha := hA.1 x x
    have hb := hB.1 x x
    simp only [G.loopless x,if_false] at ha hb
    omega

lemma disagreement_le (hA : IsBalanced G A) (hB : IsBalanced G B) : disagreement hA hB ≤ G := by
  intro x y h
  by_contra hg
  have ha := hA.1 x y
  have hb := hB.1 x y
  simp only [hg,if_false] at ha hb
  change A x y ≠ B x y at h
  omega

lemma difference_balance (hA : IsBalanced G A) (hB : IsBalanced G B) (x : V) :
    (∑ y, (A x y - B x y)) = ∑ y, (A y x - B y x) := by
  have hpair (y : V) : A x y + (A y x-B y x) = B x y + (A x y-B x y) := by
    have ha := hA.1 x y
    have hb := hB.1 x y
    omega
  have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset V)) rfl (fun y _ => hpair y)
  simp only [Finset.sum_add_distrib] at hs
  have heq : (∑ y, A x y) = ∑ y, B x y := by
    have ha := row_twice_degree hA x
    have hb := row_twice_degree hB x
    omega
  omega

lemma disagreement_balanced (hA : IsBalanced G A) (hB : IsBalanced G B) :
    IsBalanced (disagreement hA hB) (fun x y => A x y-B x y) := by
  refine ⟨?_,difference_balance hA hB⟩
  intro x y
  have ha := hA.1 x y
  have hb := hB.1 x y
  simp only [disagreement]
  by_cases hxy : G.Adj x y <;> by_cases heq : A x y = B x y
  all_goals simp [hxy,heq] at ha hb ⊢
  all_goals omega

lemma disagreement_even (hA : IsBalanced G A) (hB : IsBalanced G B) :
    ∀ x, Even ((disagreement hA hB).degree x) := by
  intro x
  have hh := row_twice_degree (disagreement_balanced hA hB) x
  exact ⟨∑ y, (A x y-B x y),by omega⟩

lemma agreement_even (hA : IsBalanced G A) (hB : IsBalanced G B) :
    ∀ x, Even ((G \ disagreement hA hB).degree x) := by
  have heG : ∀ x, Even (G.degree x) := by
    intro x
    have hh := row_twice_degree hA x
    exact ⟨∑ y, A x y,by omega⟩
  intro x
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
    even_sdiff_of_even (disagreement_le hA hB) heG (disagreement_even hA hB) x

lemma disagreement_eq_bot_iff (hA : IsBalanced G A) (hB : IsBalanced G B) :
    disagreement hA hB = ⊥ ↔ A = B := by
  constructor
  · intro h
    funext x y
    by_contra hh
    have ha : (disagreement hA hB).Adj x y := hh
    rw [h] at ha
    exact ha
  · intro h
    ext x y
    simp [disagreement,h]

lemma disagreement_eq_graph_iff (hA : IsBalanced G A) (hB : IsBalanced G B) :
    disagreement hA hB = G ↔ A = fun x y => B y x := by
  constructor
  · intro h
    funext x y
    have ha := hA.1 x y
    have hb := hB.1 x y
    by_cases hxy : G.Adj x y
    · have hn : A x y ≠ B x y := by
        change (disagreement hA hB).Adj x y
        rwa [h]
      simp only [hxy,if_true] at ha hb
      omega
    · simp only [hxy,if_false] at ha hb
      omega
  · intro h
    apply le_antisymm (disagreement_le hA hB)
    intro x y hxy
    have hb := hB.1 x y
    simp only [hxy,if_true] at hb
    change A x y ≠ B x y
    have heq : A x y = B y x := congrFun (congrFun h x) y
    omega

lemma critical_comparison {k : ℕ} (hG : IsCountCritical k G)
    (hA : IsBalanced G A) (hB : IsBalanced G B)
    (hne : A ≠ B) (hrev : A ≠ fun x y => B y x) :
    let H := disagreement hA hB
    cycleNumber H < k ∧ cycleNumber (G \ H) < k ∧
      k ≤ cycleNumber H + cycleNumber (G \ H) := by
  dsimp only
  have hHG := disagreement_le hA hB
  have hHbot : disagreement hA hB ≠ ⊥ := (disagreement_eq_bot_iff hA hB).not.mpr hne
  have hHne : disagreement hA hB ≠ G := (disagreement_eq_graph_iff hA hB).not.mpr hrev
  have hRne : G \ disagreement hA hB ≠ G := by
    intro h
    obtain ⟨x,y,hxy⟩ := ne_bot_iff_exists_adj.mp hHbot
    have hr : (G \ disagreement hA hB).Adj x y := h.symm ▸ hHG hxy
    exact hr.2 hxy
  have hRe : ∀ v, Even ((G \ disagreement hA hB).degree v) := agreement_even hA hB
  refine ⟨hG.2.2 _ hHG hHne (disagreement_even hA hB),
    hG.2.2 _ sdiff_le hRne (fun v => ?_),?_⟩
  · simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hRe v
  have hm : disagreement hA hB ∈ CycleEnvelope.evenSubgraphs G :=
    CycleEnvelope.mem_evenSubgraphs.mpr ⟨hHG,disagreement_even hA hB⟩
  have hh := UniformEvenMean.number_le_complement_sum G hG.1 (disagreement hA hB) hm
  rwa [hG.2.1] at hh

end Erdos184.OrientationComparison
