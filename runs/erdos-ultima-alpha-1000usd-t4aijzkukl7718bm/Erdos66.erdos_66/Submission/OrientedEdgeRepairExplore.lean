import Submission.PartitionCurveRepairExplore
import Submission.DisjointPaletteAssemblyExplore

/-! A repair palette: each unordered label pair gets one positive point
in its first label and its negative in the second label. -/
namespace Erdos66OrientedEdgeRepair
open Erdos66OriginRepair Erdos66ParabolaRepair Erdos66PartitionCurveRepair
open scoped Classical
set_option maxHeartbeats 2000000

abbrev Edge (h : ℕ) := {e : Fin h × Fin h // e.1<e.2}

noncomputable def leftEdges (h : ℕ) (i : Fin h) : Finset (Edge h) :=
  Finset.univ.filter (fun e ↦ e.val.1=i)

noncomputable def rightEdges (h : ℕ) (i : Fin h) : Finset (Edge h) :=
  Finset.univ.filter (fun e ↦ e.val.2=i)

lemma mem_leftEdges {h : ℕ} (i : Fin h) (e : Edge h) :
    e∈leftEdges h i ↔ e.val.1=i := by simp [leftEdges]

lemma mem_rightEdges {h : ℕ} (i : Fin h) (e : Edge h) :
    e∈rightEdges h i ↔ e.val.2=i := by simp [rightEdges]

lemma left_right_card {h : ℕ} (i j : Fin h) :
    ((leftEdges h i) ∩ (rightEdges h j)).card=if i<j then 1 else 0 := by
  by_cases hij : i<j
  · have he : (leftEdges h i) ∩ (rightEdges h j)={⟨(i,j),hij⟩} := by
      ext e
      simp only [Finset.mem_inter,mem_leftEdges,mem_rightEdges,Finset.mem_singleton]
      constructor
      · rintro ⟨h₁,h₂⟩; apply Subtype.ext; exact Prod.ext h₁ h₂
      · rintro rfl; exact ⟨rfl,rfl⟩
    simp [he,hij]
  · have he : (leftEdges h i) ∩ (rightEdges h j)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨h₁,h₂⟩ := Finset.mem_inter.mp he
      have h₁ := (mem_leftEdges i e).mp h₁
      have h₂ := (mem_rightEdges j e).mp h₂
      exact hij (by simpa only [h₁,h₂] using e.property)
    simp [he,hij]

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

noncomputable def edgeRepair (h : ℕ) (f : Edge h → G) (i : Fin h) : Finset G :=
  pointRepair f (leftEdges h i) (rightEdges h i)

lemma mem_edgeRepair {h : ℕ} (f : Edge h → G) (i : Fin h) (z : G) :
    z∈edgeRepair h f i ↔
      (∃ e : Edge h, e.val.1=i ∧ f e=z) ∨ (∃ e : Edge h, e.val.2=i ∧ -(f e)=z) := by
  simp only [edgeRepair,pointRepair,Finset.mem_union,Finset.mem_image,mem_leftEdges,mem_rightEdges]
  constructor
  · rintro (⟨e,he,hz⟩ | ⟨v,⟨e,he,rfl⟩,hz⟩)
    · exact Or.inl ⟨e,he,hz⟩
    · exact Or.inr ⟨e,he,hz⟩
  · rintro (⟨e,he,hz⟩ | ⟨e,he,hz⟩)
    · exact Or.inl ⟨e,he,hz⟩
    · exact Or.inr ⟨f e,⟨e,he,rfl⟩,hz⟩

lemma edgeRepair_pairwise {h : ℕ} (f : Edge h → G) (hf : Function.Injective f)
    (hopp : ∀ e d, f e≠-(f d)) :
    Pairwise (fun i j : Fin h ↦ Disjoint (edgeRepair h f i) (edgeRepair h f j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  rw [mem_edgeRepair] at hz hz'
  rcases hz with ⟨e,he,hze⟩ | ⟨e,he,hze⟩ <;>
    rcases hz' with ⟨d,hd,hzd⟩ | ⟨d,hd,hzd⟩
  · have heq := hf (hze.trans hzd.symm)
    exact hij (he.symm.trans (heq ▸ hd))
  · exact hopp e d (hze.trans hzd.symm)
  · exact hopp d e (hzd.trans hze.symm)
  · have heq := hf (neg_injective (hze.trans hzd.symm))
    exact hij (he.symm.trans (heq ▸ hd))

lemma edgeRepair_origin {h : ℕ} (f : Edge h → G) (hf : Function.Injective f)
    (hopp : ∀ e d, f e≠-(f d)) (i j : Fin h) :
    pairCount (edgeRepair h f i) (edgeRepair h f j) 0=if i=j then 0 else 1 := by
  unfold edgeRepair
  rw [pointRepair_origin f hf hopp,left_right_card,Finset.inter_comm,rightEdges]
  change (if i<j then 1 else 0)+((leftEdges h j)∩(rightEdges h i)).card=_
  rw [left_right_card]
  rcases lt_trichotomy i j with he | he | he
  · simp [he,ne_of_lt he,not_lt_of_ge (le_of_lt he)]
  · simp [he]
  · simp [he,(ne_of_lt he).symm,not_lt_of_ge (le_of_lt he)]

lemma edgeRepair_disjoint_base {h : ℕ} (A : Finset G) (f : Edge h → G)
    (hpos : ∀ e, f e∉A) (hneg : ∀ e, -(f e)∉A) (i : Fin h) :
    Disjoint A (edgeRepair h f i) := pointRepair_disjoint_base A f hpos hneg _ _

section CurveEmbedding
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma edge_card_le (h : ℕ) : Fintype.card (Edge h)≤h^2 := by
  have he := Fintype.card_subtype_le (fun e : Fin h × Fin h ↦ e.1<e.2)
  simpa only [Fintype.card_prod,Fintype.card_fin,pow_two] using he

/-- A field with more than h^2 elements has room for the entire repair
palette on one auxiliary curve. No choice of coarse sets is involved. -/
theorem exists_edge_curve_embedding (h : ℕ) (hh : h^2<Fintype.card F)
    (hF : ringChar F≠2) (w : F) (hw : w≠0) :
    ∃ f : Edge h → F×F, Function.Injective f ∧
      (∀ e, (f e).1≠0) ∧ (∀ e, f e∈curve w) ∧ (∀ e d, f e≠-(f d)) := by
  classical
  obtain ⟨f,hf,hf0,hfc⟩ := partition_curve_embedding (fun _ : Edge h ↦ ()) (fun _ : Unit ↦ w)
    (fun i j _ ↦ Subsingleton.elim i j) (fun _ ↦ hw) (by
      intro i
      cases i
      simpa using (edge_card_le h).trans_lt hh)
  refine ⟨f,hf,hf0,hfc,?_⟩
  apply curve_images_no_opposites (fun _ : Edge h ↦ ()) (fun _ : Unit ↦ w) (fun _ ↦ hw)
    (fun _ _ ↦ ?_) f hf0 hfc
  have htwo : (2:F)≠0 := Ring.two_ne_zero hF
  simpa only [two_mul] using mul_ne_zero htwo hw

end CurveEmbedding
end Erdos66OrientedEdgeRepair
