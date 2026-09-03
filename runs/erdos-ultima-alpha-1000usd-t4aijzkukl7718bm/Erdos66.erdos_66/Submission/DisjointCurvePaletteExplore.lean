import Submission.PaletteL1RepairExplore

/-! Converting parameter curves into disjoint palettes, uniformly in all
later coarse colors. An edge-indexed repair retains all off-diagonal
origin counts, at a total L1 cost O(h). -/
namespace Erdos66DisjointCurvePalette
open Erdos66OriginRepair Erdos66ParabolaRepair Erdos66AsymmetricRepair
  Erdos66PartitionCurveRepair Erdos66DisjointPaletteAssembly Erdos66OrientedEdgeRepair
  Erdos66PaletteL1Repair
open scoped Classical
set_option maxHeartbeats 2600000

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def erasedCurve (u : F) : Finset (F×F) := (curve u).erase 0

lemma erasedCurve_zero (u : F) : (0:F×F)∉erasedCurve u := Finset.notMem_erase _ _

lemma curve_eq_erased (u : F) : curve u=erasedCurve u∪{0} := by
  have h0 : (0:F×F)∈curve u := by rw [mem_curve]; simp
  rw [Finset.union_singleton,erasedCurve,Finset.insert_erase h0]

lemma erasedCurve_pairwise {h : ℕ} (u : Fin h → F) (hu : Function.Injective u)
    (hu0 : ∀ i, u i≠0) : Pairwise (fun i j ↦ Disjoint (erasedCurve (u i)) (erasedCurve (u j))) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  exact (Finset.mem_erase.mp hz).1 (curve_intersection (hu0 i) (hu0 j)
    (fun he ↦ hij (hu he)) (Finset.mem_erase.mp hz).2 (Finset.mem_erase.mp hz').2)

lemma erasedCurve_origin (u v : F) (hu : u≠0) (hv : v≠0) (huv : u+v≠0) :
    pairCount (erasedCurve u) (erasedCurve v) 0=0 := by
  rw [pairCount,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
  intro z hz hz'
  have hn : -z∈curve v := by simpa only [zero_sub] using (Finset.mem_erase.mp hz').2
  have hneg : z∈curve (-v) := by simpa only [neg_neg] using neg_mem_curve v hn
  exact (Finset.mem_erase.mp hz).1 (curve_intersection hu (neg_ne_zero.mpr hv)
    (fun he ↦ huv (by rw [he,neg_add_cancel])) (Finset.mem_erase.mp hz).2 hneg)

lemma curve_origin (u v : F) (hu : u≠0) (hv : v≠0) (huv : u+v≠0) :
    pairCount (curve u) (curve v) 0=1 := by
  rw [curve_eq_erased u,curve_eq_erased v,pairCount_add_zero _ _ (erasedCurve_zero u) (erasedCurve_zero v)]
  rw [erasedCurve_origin u v hu hv huv]
  simp [erasedCurve_zero]

noncomputable def repairedPalette (h : ℕ) (u : Fin h → F) (f : Edge h → F×F)
    (i : Fin h) : Finset (F×F) := erasedCurve (u i)∪edgeRepair h f i

lemma repairedPalette_pairwise {h : ℕ} (u : Fin h → F) (hu : Function.Injective u)
    (hu0 : ∀ i, u i≠0) (f : Edge h → F×F) (hf : Function.Injective f)
    (hopp : ∀ e d, f e≠-(f d))
    (hpos : ∀ i e, f e∉curve (u i)) (hneg : ∀ i e, -(f e)∉curve (u i)) :
    Pairwise (fun i j ↦ Disjoint (repairedPalette h u f i) (repairedPalette h u f j)) := by
  have hD (i j : Fin h) : Disjoint (erasedCurve (u i)) (edgeRepair h f j) :=
    (edgeRepair_disjoint_base (curve (u i)) f (hpos i) (hneg i) j).mono_left (Finset.erase_subset _ _)
  intro i j hij
  exact Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_right.mpr
    ⟨erasedCurve_pairwise u hu hu0 hij,hD i j⟩,
    Finset.disjoint_union_right.mpr ⟨(hD j i).symm,edgeRepair_pairwise f hf hopp hij⟩⟩

lemma repairedPalette_origin {h : ℕ} (u : Fin h → F)
    (hu0 : ∀ i, u i≠0) (huopp : ∀ i j, u i+u j≠0)
    (f : Edge h → F×F) (hf : Function.Injective f) (hopp : ∀ e d, f e≠-(f d))
    (hpos : ∀ i e, f e∉curve (u i)) (hneg : ∀ i e, -(f e)∉curve (u i)) (i j : Fin h) :
    pairCount (repairedPalette h u f i) (repairedPalette h u f j) 0=if i=j then 0 else 1 := by
  have hD (i j : Fin h) : Disjoint (erasedCurve (u i)) (edgeRepair h f j) :=
    (edgeRepair_disjoint_base (curve (u i)) f (hpos i) (hneg i) j).mono_left (Finset.erase_subset _ _)
  have hM (i j : Fin h) : pairCount (edgeRepair h f i) (erasedCurve (u j)) 0=0 := by
    apply Nat.eq_zero_of_le_zero
    have he := pairCount_mono (Finset.Subset.refl (edgeRepair h f i)) (Finset.erase_subset 0 (curve (u j))) 0
    have hz := pointRepair_base_origin (curve (u j)) f (hpos j) (hneg j) (leftEdges h i) (rightEdges h i)
    exact he.trans (by rw [show edgeRepair h f i=pointRepair f (leftEdges h i) (rightEdges h i) from rfl,hz])
  unfold repairedPalette
  rw [pairCount_union_mixed _ _ _ _ _ (hD i i) (hD j j),
    erasedCurve_origin _ _ (hu0 i) (hu0 j) (huopp i j),hM, pairCount_comm (erasedCurve (u i)),hM,
    edgeRepair_origin f hf hopp]
  omega

lemma repairedPalette_sum_nonzero {h : ℕ} (u : Fin h → F) (hu : Function.Injective u)
    (hu0 : ∀ i, u i≠0) (f : Edge h → F×F) (hf : Function.Injective f)
    (hopp : ∀ e d, f e≠-(f d)) (hpos : ∀ i e, f e∉curve (u i)) (hneg : ∀ i e, -(f e)∉curve (u i))
    (hF : ringChar F≠2) (w : F) (hw : w≠0) (hfc : ∀ e, f e∈curve w)
    (z : F×F) (hz : z≠0) :
    (∑ i : Fin h, ∑ j : Fin h, (pairCount (repairedPalette h u f i) (repairedPalette h u f j) z:ℝ)) ≤
      (∑ i : Fin h, ∑ j : Fin h, (pairCount (erasedCurve (u i)) (erasedCurve (u j)) z:ℝ))+
        8*(h:ℝ)+8 := by
  let U := Finset.univ.image u
  let E := Finset.univ.biUnion (fun i ↦ erasedCurve (u i))
  let D := Finset.univ.biUnion (edgeRepair h f)
  have hU : ∀ v∈U, v≠0 := by
    intro v hv; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv; exact hu0 i
  have hUc : U.card=h := by simp [U,Finset.card_image_of_injective _ hu]
  have hE : E⊆parabolaSet U := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := Finset.mem_biUnion.mp hx
    rw [parabolaSet_eq_biUnion]
    exact Finset.mem_biUnion.mpr ⟨u i,Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩,
      (Finset.mem_erase.mp hxi).2⟩
  have hD : D⊆parabolaSet ({w,-w}:Finset F) := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := Finset.mem_biUnion.mp hx
    rw [mem_edgeRepair] at hxi
    rcases hxi with ⟨e,he,rfl⟩ | ⟨e,he,rfl⟩
    · rw [parabolaSet_eq_biUnion]
      exact Finset.mem_biUnion.mpr ⟨w,by simp,hfc e⟩
    · rw [parabolaSet_eq_biUnion]
      exact Finset.mem_biUnion.mpr ⟨-w,by simp,neg_mem_curve w (hfc e)⟩
  have hED : Disjoint E D := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨i,hi,hxi⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨j,hj,hxj⟩ := Finset.mem_biUnion.mp hx'
    exact Finset.disjoint_left.mp (edgeRepair_disjoint_base (curve (u i)) f (hpos i) (hneg i) j)
      (Finset.mem_erase.mp hxi).2 hxj
  have hW : ∀ v∈({w,-w}:Finset F), v≠0 := by
    intro v hv; simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hw
    · exact neg_ne_zero.mpr hw
  have hWc : ({w,-w}:Finset F).card=2 := by simp [parameter_ne_neg hF hw]
  have hM := (pairCount_mono hD hE z).trans (parabolaSet_pairCount_le hF {w,-w} U hW hU z hz)
  have hS := (pairCount_mono hD hD z).trans (parabolaSet_pairCount_le hF {w,-w} {w,-w} hW hW z hz)
  rw [hWc,hUc] at hM
  rw [hWc] at hS
  have hcount : pairCount (E∪D) (E∪D) z ≤ pairCount E E z+8*h+8 := by
    rw [pairCount_union_self _ _ _ hED]; omega
  have hP : Finset.univ.biUnion (repairedPalette h u f)=E∪D := by
    unfold repairedPalette; exact Finset.biUnion_union
  have hPs := pairCount_biUnion_self Finset.univ (repairedPalette h u f)
    (fun _ _ _ _ hij ↦ repairedPalette_pairwise u hu hu0 f hf hopp hpos hneg hij) z
  have hEs := pairCount_biUnion_self Finset.univ (fun i ↦ erasedCurve (u i))
    (fun _ _ _ _ hij ↦ erasedCurve_pairwise u hu hu0 hij) z
  rw [hP] at hPs
  change pairCount E E z=_ at hEs
  rw [hPs,hEs] at hcount
  exact_mod_cast hcount

/-- A disjoint fine palette approximates the full parameter-count matrix
in L1, including the exceptional fine origin. The palette is fixed before
any coarse sets or colors. -/
theorem exists_disjoint_curve_palette (h : ℕ) (hh : h^2<Fintype.card F)
    (hroom : 2*h+1<Fintype.card F) (hF : ringChar F≠2)
    (u : Fin h → F) (hu : Function.Injective u) (hu0 : ∀ i, u i≠0)
    (huopp : ∀ i j, u i+u j≠0) :
    ∃ P : Fin h → Finset (F×F), Pairwise (fun i j ↦ Disjoint (P i) (P j)) ∧
      ∀ z : F×F, (∑ i : Fin h, ∑ j : Fin h,
        |(pairCount (P i) (P j) z:ℝ)-pairCount (curve (u i)) (curve (u j)) z|)≤10*(h:ℝ)+8 := by
  let U := Finset.univ.image u
  have hUc : U.card=h := by simp [U,Finset.card_image_of_injective _ hu]
  obtain ⟨w,hw,hwU,hnwU⟩ := exists_unused_parameter U (by rw [hUc]; exact hroom)
  obtain ⟨f,hf,hf0,hfc,hopp⟩ := exists_edge_curve_embedding h hh hF w hw
  have hpos (i : Fin h) (e : Edge h) : f e∉curve (u i) := by
    intro he
    have hne : w≠u i := fun heq ↦ hwU (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,heq.symm⟩)
    exact hf0 e (congrArg Prod.fst (curve_intersection hw (hu0 i) hne (hfc e) he))
  have hneg (i : Fin h) (e : Edge h) : -(f e)∉curve (u i) := by
    intro he
    have hne : -w≠u i := fun heq ↦ hnwU (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,heq.symm⟩)
    have hz := curve_intersection (neg_ne_zero.mpr hw) (hu0 i) hne (neg_mem_curve w (hfc e)) he
    have heq : -(f e).1=0 := congrArg Prod.fst hz
    exact hf0 e (neg_eq_zero.mp heq)
  refine ⟨repairedPalette h u f,repairedPalette_pairwise u hu hu0 f hf hopp hpos hneg,fun z ↦ ?_⟩
  by_cases hz : z=0
  · subst z
    rw [palette_L1_origin _ _ (fun i j ↦ curve_origin _ _ (hu0 i) (hu0 j) (huopp i j))
      (repairedPalette_origin u hu0 huopp f hf hopp hpos hneg),Fintype.card_fin]
    have hh0 : (0:ℝ)≤h := Nat.cast_nonneg h
    linarith
  · have he := palette_L1_nonzero (fun i ↦ curve (u i)) (fun i ↦ erasedCurve (u i))
      (repairedPalette h u f) (erasedCurve_pairwise u hu hu0) (fun i ↦ erasedCurve_zero (u i))
      (fun i ↦ curve_eq_erased (u i)) (fun _ ↦ Finset.subset_union_left) (8*(h:ℝ)+8) z hz
      (by simpa only [add_assoc] using repairedPalette_sum_nonzero u hu hu0 f hf hopp hpos hneg hF w hw hfc z hz)
    rw [Fintype.card_fin] at he
    linarith

end Erdos66DisjointCurvePalette
