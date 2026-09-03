import Submission.SquareSumRepresentations
import Submission.CollisionBounds

/-!
Subpower pair codegrees for four-distinct-root square-sum collisions.
The result concerns local hypergraph counts. It is not a near-linear
Sidon extraction theorem.
-/
namespace Erdos773.SquareCollisionCodegrees
open Finset Filter
set_option maxHeartbeats 1000000

/-- Unordered four-root supports, counted once each. -/
noncomputable def edges (A : Finset ℕ) : Finset (Finset ℕ) := by
  classical
  exact A.powerset.filter (fun e => e.card = 4 ∧ ∃ a b c d : ℕ,
    e = {a,b,c,d} ∧ a^2+b^2=c^2+d^2)

/-- Edges containing both prescribed roots. -/
noncomputable def pairEdges (A : Finset ℕ) (a b : ℕ) : Finset (Finset ℕ) :=
  (edges A).filter (fun e => a ∈ e ∧ b ∈ e)

lemma relabel {e : Finset ℕ} {a b : ℕ} (hab : a ≠ b)
    (ha : a ∈ e) (hb : b ∈ e)
    (he : ∃ u v w x : ℕ, e = {u,v,w,x} ∧ u^2+v^2=w^2+x^2) :
    ∃ c ∈ e, ∃ d ∈ e, e = {a,b,c,d} ∧
      (a^2+b^2=c^2+d^2 ∨ a^2+c^2=b^2+d^2 ∨ a^2+d^2=b^2+c^2) := by
  obtain ⟨u,v,w,x,rfl,he⟩ := he
  simp only [mem_insert, mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl
  all_goals try exact (hab rfl).elim
  all_goals
    first
    | exact ⟨u, by simp, v, by simp, by ext z; simp only [mem_insert, mem_singleton]; try tauto, by omega⟩
    | exact ⟨u, by simp, w, by simp, by ext z; simp only [mem_insert, mem_singleton]; try tauto, by omega⟩
    | exact ⟨u, by simp, x, by simp, by ext z; simp only [mem_insert, mem_singleton]; try tauto, by omega⟩
    | exact ⟨v, by simp, w, by simp, by ext z; simp only [mem_insert, mem_singleton]; try tauto, by omega⟩
    | exact ⟨v, by simp, x, by simp, by ext z; simp only [mem_insert, mem_singleton]; try tauto, by omega⟩
    | exact ⟨w, by simp, x, by simp, by ext z; simp only [mem_insert, mem_singleton]; try tauto, by omega⟩

lemma pairEdges_cover {N a b : ℕ} (hab : a < b) :
    pairEdges (Icc 1 N) a b ⊆
      (SquareSumRepresentations.reps N (a^2+b^2)).image (fun p => ({a,b,p.1,p.2} : Finset ℕ)) ∪
      (squareDifferenceReps N (b^2-a^2)).image (fun p => ({a,b,p.1,p.2} : Finset ℕ)) := by
  classical
  intro e he
  obtain ⟨he,ha,hb⟩ := mem_filter.mp he
  obtain ⟨heA,hcard,heq⟩ := mem_filter.mp he
  have heA' := mem_powerset.mp heA
  obtain ⟨c,hc,d,hd,he,hcase⟩ := relabel hab.ne ha hb heq
  have hcN := heA' hc
  have hdN := heA' hd
  rcases hcase with hs | hs | hs
  · apply mem_union_left
    exact mem_image.mpr ⟨(c,d), mem_filter.mpr ⟨mem_product.mpr ⟨hcN,hdN⟩,hs.symm⟩,he.symm⟩
  · apply mem_union_right
    have hcd : d < c := by nlinarith
    refine mem_image.mpr ⟨(d,c), mem_filter.mpr ⟨mem_product.mpr ⟨hdN,hcN⟩,hcd,?_⟩,?_⟩
    · change c^2 = d^2 + (b^2-a^2)
      have hh : a^2 ≤ b^2 := Nat.pow_le_pow_left hab.le 2
      have ht := Nat.sub_add_cancel hh
      omega
    · rw [he]
      ext z
      simp only [mem_insert, mem_singleton]
      tauto
  · apply mem_union_right
    have hcd : c < d := by nlinarith
    refine mem_image.mpr ⟨(c,d), mem_filter.mpr ⟨mem_product.mpr ⟨hcN,hdN⟩,hcd,?_⟩,he.symm⟩
    change d^2 = c^2 + (b^2-a^2)
    have hh : a^2 ≤ b^2 := Nat.pow_le_pow_left hab.le 2
    have ht := Nat.sub_add_cancel hh
    omega

/-- Each pair has only two kinds of completions: a fixed sum or a fixed
positive difference. The complement's order incurs no additional factor. -/
theorem pairEdges_card_bound {N a b : ℕ} (hab : a < b) :
    (pairEdges (Icc 1 N) a b).card ≤
      (SquareSumRepresentations.reps N (a^2+b^2)).card +
      (squareDifferenceReps N (b^2-a^2)).card := by
  classical
  exact (card_le_card (pairEdges_cover hab)).trans
    ((card_union_le _ _).trans (Nat.add_le_add (card_image_le) (card_image_le)))

/-- Uniform subpower pair codegrees at root height N. -/
theorem pair_codegree_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∀ N a b : ℕ, 1 ≤ a → a < b → b ≤ N →
      ((pairEdges (Icc 1 N) a b).card : ℝ) ≤ C * (N : ℝ)^δ := by
  obtain ⟨C,hC,hc⟩ := SquareSumRepresentations.reps_height_subpower δ hδ
  obtain ⟨D,hD,hd⟩ := squareDifferenceReps_subpower (δ/2) (by linarith)
  refine ⟨C+D,by positivity,fun N a b ha hab hb => ?_⟩
  have haN : a ≤ N := hab.le.trans hb
  have hb2 := Nat.pow_le_pow_left hb 2
  have ha2 := Nat.pow_le_pow_left haN 2
  have hsum : 0 < a^2+b^2 := by positivity
  have hsumN : a^2+b^2 ≤ 2*N^2 := by omega
  have hdiff : 0 < b^2-a^2 := Nat.sub_pos_of_lt (by nlinarith)
  have hdiffN : b^2-a^2 ≤ N^2 := (Nat.sub_le _ _).trans hb2
  have h1 := hc N _ hsum hsumN
  have h2 := hd N _ hdiff hdiffN
  rw [show 2*(δ/2)=δ by ring] at h2
  have h3 : ((pairEdges (Icc 1 N) a b).card : ℝ) ≤
      (SquareSumRepresentations.reps N (a^2+b^2)).card +
      (squareDifferenceReps N (b^2-a^2)).card := by
    exact_mod_cast pairEdges_card_bound hab
  nlinarith only [h1,h2,h3]

lemma edges_mono {A B : Finset ℕ} (hAB : A ⊆ B) : edges A ⊆ edges B := by
  classical
  intro e he
  obtain ⟨heA,h4,hs⟩ := mem_filter.mp he
  exact mem_filter.mpr ⟨mem_powerset.mpr ((mem_powerset.mp heA).trans hAB),h4,hs⟩

lemma pairEdges_mono {A B : Finset ℕ} (hAB : A ⊆ B) (a b : ℕ) :
    pairEdges A a b ⊆ pairEdges B a b := by
  classical
  intro e he
  obtain ⟨he,ha,hb⟩ := mem_filter.mp he
  exact mem_filter.mpr ⟨edges_mono hAB he,ha,hb⟩

lemma pairEdges_comm (A : Finset ℕ) (a b : ℕ) : pairEdges A a b = pairEdges A b a := by
  classical
  ext e
  simp [pairEdges,and_comm]

/-- Coefficient-free, unordered, eventually uniform codegree bound. -/
theorem eventually_pair_codegree_bound (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N, a ≠ b →
      ((pairEdges (Icc 1 N) a b).card : ℝ) ≤ (N : ℝ)^δ := by
  obtain ⟨C,hC,hb⟩ := pair_codegree_subpower (δ/2) (by linarith)
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^(δ/2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < δ/2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop C,eventually_ge_atTop 1] with N hlarge hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hord (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) (hbN : b ≤ N) :
      ((pairEdges (Icc 1 N) a b).card : ℝ) ≤ (N : ℝ)^δ := by
    calc
      _ ≤ C*(N : ℝ)^(δ/2) := hb N a b ha hab hbN
      _ ≤ (N : ℝ)^(δ/2)*(N : ℝ)^(δ/2) :=
        mul_le_mul_of_nonneg_right hlarge (by positivity)
      _ = _ := by rw [← Real.rpow_add hN0]; congr 1; ring
  intro a ha b hb hab
  rcases lt_or_gt_of_ne hab with hh | hh
  · exact hord a b (mem_Icc.mp ha).1 hh (mem_Icc.mp hb).2
  · rw [pairEdges_comm]
    exact hord b a (mem_Icc.mp hb).1 hh (mem_Icc.mp ha).2

#print axioms pairEdges_card_bound
#print axioms pair_codegree_subpower
#print axioms eventually_pair_codegree_bound
end Erdos773.SquareCollisionCodegrees
