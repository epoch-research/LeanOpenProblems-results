import FormalConjecturesUtil
import Submission.CycleBundleCertificate

/-! Four alternating twin classes on C9 give a C8-free family with
quartically many labelled C9 copies, all through a fixed vertex.
This diagnoses cycle-count and overlap arguments, NOT Erdős 713. -/
open SimpleGraph Finset
namespace Erdos713C9BundleDiagnostic
open Erdos713CycleBundleCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

abbrev Vertex (m : ℕ) := Σ i : Fin 9, Fin (if i.val % 2 = 0 then 1 else m)

def graph (m : ℕ) : SimpleGraph (Vertex m) where
  Adj x y := (cycleGraph 9).Adj x.fst y.fst
  symm _ _ h := h.symm
  loopless x := (cycleGraph 9).loopless x.fst

lemma same_hub {m : ℕ} (x y : Vertex m) (hx : x.fst.val % 2 = 0)
    (hxy : x.fst = y.fst) : x = y := by
  obtain ⟨i,a⟩ := x
  obtain ⟨j,b⟩ := y
  dsimp only at hxy hx
  subst j
  have hab : a = b := by
    apply Fin.ext
    have ha := a.isLt
    have hb := b.isLt
    simp only [if_pos hx] at ha hb
    omega
  subst b
  rfl

/-- The eight-step certificate forces two equal singleton-fibre vertices
in any putative C8 copy. No numerical sampling is used. -/
theorem free_eight (m : ℕ) : (cycleGraph 8).Free (graph m) := by
  rintro ⟨f⟩
  let g : Fin 8 → Fin 9 := fun i => (f i).fst
  have hStep (i : Fin 8) : (cycleGraph 9).Adj (g i) (g (i+1)) := by
    exact f.toHom.map_rel' (by
      rw [cycleGraph_adj]
      exact Or.inr (by abel))
  obtain ⟨i,j,hij,hi,heq⟩ := repeated_hub_of_hom g hStep
  have hh : f i = f j := same_hub (f i) (f j) hi heq
  exact (ne_of_lt hij) (f.injective hh)

def pick {m : ℕ} (a : Fin 4 → Fin m) (i : Fin 9) : Vertex m := by
  refine ⟨i,?_⟩
  by_cases h : i.val % 2 = 0
  · exact ⟨0,by simp [h]⟩
  · have hi : i.val / 2 < 4 := by have := i.isLt; omega
    exact ⟨(a ⟨i.val/2,hi⟩).val,by simp [h]⟩

@[simp] lemma pick_fst {m : ℕ} (a : Fin 4 → Fin m) (i : Fin 9) : (pick a i).fst = i := rfl

def cycleCopy {m : ℕ} (a : Fin 4 → Fin m) : (cycleGraph 9).Copy (graph m) where
  toHom := ⟨pick a,fun h => h⟩
  injective' _ _ h := congrArg Sigma.fst h

lemma cycleCopy_injective (m : ℕ) : Function.Injective (cycleCopy (m := m)) := by
  intro a b hab
  funext i
  apply Fin.ext
  fin_cases i
  · have hh := congrArg (fun f : (cycleGraph 9).Copy (graph m) => (f 1).snd.val) hab
    simpa [cycleCopy,pick] using hh
  · have hh := congrArg (fun f : (cycleGraph 9).Copy (graph m) => (f 3).snd.val) hab
    simpa [cycleCopy,pick] using hh
  · have hh := congrArg (fun f : (cycleGraph 9).Copy (graph m) => (f 5).snd.val) hab
    simpa [cycleCopy,pick] using hh
  · have hh := congrArg (fun f : (cycleGraph 9).Copy (graph m) => (f 7).snd.val) hab
    simpa [cycleCopy,pick] using hh

lemma card_vertex (m : ℕ) : Fintype.card (Vertex m) = 4*m+5 := by
  simp only [Vertex,Fintype.card_sigma,Fintype.card_fin]
  norm_num [Fin.sum_univ_succ]
  omega

lemma labelled_count_lower {A V W : Type*} [Fintype A] [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : A → H.Copy G) (hf : Function.Injective f) :
    Fintype.card A ≤ G.labelledCopyCount H := by
  classical
  exact Fintype.card_le_of_injective f hf

/-- Different four-tuples give distinct labelled copies. -/
theorem many_nine_cycles (m : ℕ) : m^4 ≤ (graph m).labelledCopyCount (cycleGraph 9) := by
  have hh := labelled_count_lower (graph m) (cycleGraph 9)
    (cycleCopy (m := m)) (cycleCopy_injective m)
  simpa only [Fintype.card_fun,Fintype.card_fin] using hh

lemma subgraph_family_injective (m : ℕ) :
    Function.Injective (fun a : Fin 4 → Fin m => (cycleCopy a).toSubgraph) := by
  intro a b hab
  have hR : Set.range (pick a) = Set.range (pick b) := by
    simpa [Copy.toSubgraph,Subgraph.map_verts,cycleCopy] using congrArg Subgraph.verts hab
  apply cycleCopy_injective m
  apply DFunLike.ext
  intro i
  have hi : pick a i ∈ Set.range (pick b) := hR ▸ Set.mem_range_self i
  obtain ⟨j,hj⟩ := hi
  have hji : j = i := congrArg Sigma.fst hj
  subst j
  exact hj.symm

lemma unlabelled_count_lower {A V W : Type*} [Fintype A] [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : A → H.Copy G)
    (hf : Function.Injective (fun a => (f a).toSubgraph)) :
    Fintype.card A ≤ G.copyCount H := by
  classical
  rw [copyCount_eq_card_image_copyToSubgraph]
  have he : (univ.image (fun a : A => (f a).toSubgraph)).card = Fintype.card A := by
    simpa only [card_univ] using card_image_of_injective univ hf
  rw [← he]
  apply card_le_card
  intro K hK
  obtain ⟨a,_,rfl⟩ := mem_image.mp hK
  exact mem_image.mpr ⟨f a,mem_univ _,rfl⟩

/-- The quartic lower bound holds for actual unlabelled cycle subgraphs,
not merely for multiple labellings of the same cycle. -/
theorem many_unlabelled_nine_cycles (m : ℕ) : m^4 ≤ (graph m).copyCount (cycleGraph 9) := by
  have hh := unlabelled_count_lower (graph m) (cycleGraph 9)
    (cycleCopy (m := m)) (subgraph_family_injective m)
  simpa only [Fintype.card_fun,Fintype.card_fin] using hh

def hub (m : ℕ) : Vertex m := ⟨0,⟨0,by simp⟩⟩

lemma projected_ne_zero {m : ℕ} (x : Vertex m) (hx : x ≠ hub m) : x.fst ≠ 0 := by
  intro h
  exact hx (same_hub x (hub m) (by rw [h]; decide) h)

lemma adj_parity : ∀ i j : Fin 9, (cycleGraph 9).Adj i j → i ≠ 0 → j ≠ 0 →
    i.val % 2 ≠ j.val % 2 := by
  simp only [cycleGraph_adj]
  decide

lemma without_hub_bipartite (m : ℕ) : ((graph m).induce {hub m}ᶜ).IsBipartite := by
  refine ⟨Coloring.mk (fun x => (⟨x.val.fst.val % 2,Nat.mod_lt _ (by decide)⟩ : Fin 2)) ?_⟩
  intro x y hxy hcol
  apply adj_parity x.val.fst y.val.fst hxy
    (projected_ne_zero x.val x.property) (projected_ne_zero y.val y.property)
  exact congrArg Fin.val hcol

lemma nine_not_bipartite : ¬ (cycleGraph 9).IsBipartite := by
  intro h
  have hadj (i : Fin 9) : (cycleGraph 9).Adj i (i+1) := by
    rw [cycleGraph_adj]
    exact Or.inr (by abel)
  let p : (cycleGraph 9).Walk 0 0 :=
    Walk.cons (hadj 0) (Walk.cons (hadj 1) (Walk.cons (hadj 2)
      (Walk.cons (hadj 3) (Walk.cons (hadj 4) (Walk.cons (hadj 5)
        (Walk.cons (hadj 6) (Walk.cons (hadj 7) (Walk.cons (hadj 8) Walk.nil))))))))
  have hh := (two_colorable_iff_forall_loop_even.mp h) 0 p
  have hl : p.length = 9 := rfl
  rw [hl] at hh
  exact (by decide : ¬ Even (9 : ℕ)) hh

/-- All C9 copies share one hub, despite the quartic number of copies.
No exactness or large minimum-degree assertion is made for this family. -/
theorem every_copy_hits_hub (m : ℕ) (f : (cycleGraph 9).Copy (graph m)) :
    ∃ i, f i = hub m := by
  by_contra hh
  push_neg at hh
  have hom : cycleGraph 9 →g (graph m).induce {hub m}ᶜ :=
    ⟨fun i => ⟨f i,hh i⟩,fun {_ _} h => f.toHom.map_rel' h⟩
  exact nine_not_bipartite ((without_hub_bipartite m).of_hom hom)

def secondHub (m : ℕ) : Vertex m := ⟨2,⟨0,by norm_num⟩⟩

lemma thin_degree {m : ℕ} (x : Vertex m) (hx : x.fst = 1) :
    Nat.card ((graph m).neighborSet x) = 2 := by
  classical
  have hAdj : ∀ j : Fin 9, (cycleGraph 9).Adj 1 j ↔ j = 0 ∨ j = 2 := by
    simp only [cycleGraph_adj]
    decide
  have hN : (graph m).neighborSet x = {hub m,secondHub m} := by
    ext y
    change (cycleGraph 9).Adj x.fst y.fst ↔ y = hub m ∨ y = secondHub m
    rw [hx,hAdj]
    constructor
    · rintro (hy | hy)
      · exact Or.inl (same_hub y (hub m) (by rw [hy]; decide) hy)
      · exact Or.inr (same_hub y (secondHub m) (by rw [hy]; decide) hy)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hne : hub m ≠ secondHub m := by
    intro hh
    have hp := congrArg Sigma.fst hh
    exact (by decide : (0 : Fin 9) ≠ 2) hp
  rw [hN]
  simp [Nat.card_eq_fintype_card,hne]

/-- These diagnostic hosts fail every minimum-degree target above two. -/
theorem has_degree_two {m : ℕ} (hm : 0 < m) :
    ∃ x : Vertex m, Nat.card ((graph m).neighborSet x) = 2 := by
  let x : Vertex m := ⟨1,⟨0,by simpa using hm⟩⟩
  exact ⟨x,thin_degree x rfl⟩

lemma quartic_dominates {C : ℝ} (hC : 0 < C) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ 1 ≤ m ∧ C*(4*(m : ℝ)+5)^3 < (m : ℝ)^4 := by
  obtain ⟨m,hm⟩ := exists_nat_gt (max (N : ℝ) (max 1 (729*C)))
  have hNm : (N : ℝ) < m := (le_max_left _ _).trans_lt hm
  have hm1 : (1 : ℝ) < m := ((le_max_left (1 : ℝ) (729*C)).trans (le_max_right _ _)).trans_lt hm
  have hmC : 729*C < m := ((le_max_right (1 : ℝ) (729*C)).trans (le_max_right _ _)).trans_lt hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hbase : 4*(m : ℝ)+5 ≤ 9*m := by linarith
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 4*(m : ℝ)+5) hbase 3
  have hpowC := mul_le_mul_of_nonneg_left hpow hC.le
  have hlast := mul_lt_mul_of_pos_right hmC (pow_pos hm0 3)
  refine ⟨m,?_,?_,?_⟩
  · exact_mod_cast hNm.le
  · exact_mod_cast hm1.le
  · nlinarith only [hpowC,hlast]

/-- There is no uniform cubic upper bound for C9 subgraph counts in
arbitrary C8-free graphs, even if all the C9 copies hit one vertex. -/
theorem counterexamples_to_cubic_bound {C : ℝ} (hC : 0 < C) (N : ℕ) :
    ∃ m : ℕ, N ≤ Fintype.card (Vertex m) ∧ (cycleGraph 8).Free (graph m) ∧
      C*(Fintype.card (Vertex m) : ℝ)^3 < ((graph m).copyCount (cycleGraph 9) : ℝ) ∧
      ∀ f : (cycleGraph 9).Copy (graph m), ∃ i, f i = hub m := by
  obtain ⟨m,hN,_,hLarge⟩ := quartic_dominates hC N
  have hCount : (m : ℝ)^4 ≤ ((graph m).copyCount (cycleGraph 9) : ℝ) := by
    exact_mod_cast many_unlabelled_nine_cycles m
  refine ⟨m,?_,free_eight m,?_,every_copy_hits_hub m⟩
  · rw [card_vertex]
    omega
  · rw [card_vertex]
    push_cast
    exact hLarge.trans_le hCount

/-- This negates only an auxiliary counting assertion, not the original
rationality conjecture. The family has no claimed extremality. -/
theorem no_uniform_cubic_bound :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      (cycleGraph 8).Free G →
      (G.copyCount (cycleGraph 9) : ℝ) ≤ C*(Fintype.card V : ℝ)^3 := by
  rintro ⟨C,hC,hBound⟩
  obtain ⟨m,_,hf,hLarge,_⟩ := counterexamples_to_cubic_bound hC 0
  exact (not_lt_of_ge (hBound (Vertex m) (graph m) hf)) hLarge

#print axioms no_uniform_cubic_bound
#print axioms has_degree_two
#print axioms free_eight
#print axioms many_nine_cycles
#print axioms many_unlabelled_nine_cycles
#print axioms every_copy_hits_hub
end Erdos713C9BundleDiagnostic
