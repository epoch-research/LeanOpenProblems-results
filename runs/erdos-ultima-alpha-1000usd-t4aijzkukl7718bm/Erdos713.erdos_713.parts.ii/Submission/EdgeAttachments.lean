import FormalConjecturesUtil
import Submission.CompactExactUnionAudit

/-! Fresh copies attached along existing edges. The base pattern must admit
self-copies aligning its distinguished edge with any oriented edge. This is
an explicit hypothesis, not an assertion about arbitrary bipartite graphs. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713EdgeAttachments
open Erdos713EdgeBlockers Erdos713Rate Erdos713RootPower

abbrev Interior {A : Type*} (x y : A) := {z : A // z ≠ x ∧ z ≠ y}

/-- Paste F along u-v, retaining all other vertices of F as fresh vertices. -/
def paste {A W : Type*} (F : SimpleGraph A) (x y : A) (H : SimpleGraph W)
    (u v : W) : SimpleGraph (W ⊕ Interior x y) where
  Adj
    | .inl a, .inl b => H.Adj a b
    | .inl a, .inr b => (a = u ∧ F.Adj x b.val) ∨ (a = v ∧ F.Adj y b.val)
    | .inr a, .inl b => (b = u ∧ F.Adj x a.val) ∨ (b = v ∧ F.Adj y a.val)
    | .inr a, .inr b => F.Adj a.val b.val
  symm := by
    rintro (a | a) (b | b) h
    · exact h.symm
    · exact h
    · exact h
    · exact h.symm
  loopless := by
    rintro (a | a) h
    · exact H.loopless a h
    · exact F.loopless a.val h

def oldCopy {A W : Type*} (F : SimpleGraph A) (x y : A) (H : SimpleGraph W) (u v : W) :
    H.Copy (paste F x y H u v) := ⟨⟨Sum.inl,fun h => h⟩,Sum.inl_injective⟩

noncomputable def petalMap {A W : Type*} (x y : A) (u v : W) (z : A) : W ⊕ Interior x y := by
  classical
  exact if hx : z = x then .inl u else if hy : z = y then .inl v else .inr ⟨z,hx,hy⟩

lemma petalMap_injective {A W : Type*} {x y : A} {u v : W} (huv : u ≠ v) :
    Function.Injective (petalMap x y u v) := by
  classical
  intro a b hab
  by_cases hax : a = x <;> by_cases hay : a = y <;>
    by_cases hbx : b = x <;> by_cases hby : b = y <;>
    simp_all [petalMap]

noncomputable def petalCopy {A W : Type*} (F : SimpleGraph A) {x y : A} (hxy : F.Adj x y)
    (H : SimpleGraph W) {u v : W} (huv : H.Adj u v) : F.Copy (paste F x y H u v) := by
  classical
  refine ⟨⟨petalMap x y u v,?_⟩,petalMap_injective huv.ne⟩
  intro a b hab
  by_cases hax : a = x <;> by_cases hay : a = y <;>
    by_cases hbx : b = x <;> by_cases hby : b = y <;>
    simp_all [petalMap,paste,huv.symm]
  all_goals first | exact Or.inl hab.symm | exact Or.inr hab.symm

/-- The alignment assumption keeps orientation; undirected edge transitivity
alone is not silently substituted for this condition. -/
def Alignable {A : Type*} (F : SimpleGraph A) (x y : A) : Prop :=
  ∀ a b, F.Adj a b → ∃ e : F.Copy F, e x = a ∧ e y = b

lemma aligned_extension {A V : Type*} {F : SimpleGraph A} {x y : A}
    (hAlign : Alignable F x y) {G : SimpleGraph V} {k : ℕ}
    (hExt : Extensible F G k) {u v : V} (huv : G.Adj u v)
    (B : Finset V) (hc : B.card ≤ k) (hu : u ∉ B) (hv : v ∉ B) :
    ∃ f : F.Copy G, f x = u ∧ f y = v ∧ ∀ a, f a ∉ B := by
  obtain ⟨f,⟨a,b,hab,he⟩,hB⟩ := hExt s(u,v) huv B hc (by
    intro w hw
    rcases Sym2.mem_iff.mp hw with rfl | rfl
    · exact hu
    · exact hv)
  rcases Sym2.eq_iff.mp he with ⟨hfu,hfv⟩ | ⟨hfv,hfu⟩
  · obtain ⟨e,hex,hey⟩ := hAlign a b hab
    refine ⟨f.comp e,?_,?_,fun z => hB (e z)⟩
    · change f (e x) = u
      rwa [hex]
    · change f (e y) = v
      rwa [hey]
  · obtain ⟨e,hex,hey⟩ := hAlign b a hab.symm
    refine ⟨f.comp e,?_,?_,fun z => hB (e z)⟩
    · change f (e x) = u
      rwa [hex]
    · change f (e y) = v
      rwa [hey]

noncomputable def extendCopy {A W V : Type*} {F : SimpleGraph A} {x y : A}
    {H : SimpleGraph W} {G : SimpleGraph V} (f : H.Copy G) (u v : W)
    (g : F.Copy G) (hx : g x = f u) (hy : g y = f v)
    (hAvoid : ∀ a : Interior x y, ∀ w, g a.val ≠ f w) :
    (paste F x y H u v).Copy G := by
  refine ⟨⟨Sum.elim f (fun a => g a.val),?_⟩,?_⟩
  · rintro (a | a) (b | b) hab
    · exact f.toHom.map_adj hab
    · rcases hab with ⟨rfl,hb⟩ | ⟨rfl,hb⟩
      · change G.Adj (f a) (g b.val)
        rw [← hx]
        exact g.toHom.map_adj hb
      · change G.Adj (f a) (g b.val)
        rw [← hy]
        exact g.toHom.map_adj hb
    · rcases hab with ⟨rfl,ha⟩ | ⟨rfl,ha⟩
      · change G.Adj (g a.val) (f b)
        rw [← hx]
        exact (g.toHom.map_adj ha).symm
      · change G.Adj (g a.val) (f b)
        rw [← hy]
        exact (g.toHom.map_adj ha).symm
    · exact g.toHom.map_adj hab
  · rintro (a | a) (b | b) hab
    · exact congrArg Sum.inl (f.injective hab)
    · exact (hAvoid b a hab.symm).elim
    · exact (hAvoid a b hab).elim
    · exact congrArg Sum.inr (Subtype.ext (g.injective hab))

lemma paste_connected {A W : Type*} {F : SimpleGraph A} {x y : A} (hxy : F.Adj x y)
    (hF : F.Connected) {H : SimpleGraph W} (hH : H.Connected) {u v : W} (huv : H.Adj u v) :
    (paste F x y H u v).Connected := by
  classical
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨.inl u,?_⟩
  rintro (w | w)
  · exact (hH u w).map (oldCopy F x y H u v).toHom
  · have hp := (hF x w.val).map (petalCopy F hxy H huv).toHom
    change (paste F x y H u v).Reachable (petalMap x y u v x)
      (petalMap x y u v w.val) at hp
    simpa only [petalMap,dif_pos rfl,dif_neg w.prop.1,dif_neg w.prop.2] using hp

/-- The distinguished edge stays fixed as fresh copies are attached. -/
inductive Built {A : Type} (F : SimpleGraph A) (x y : A) :
    {W : Type} → SimpleGraph W → W → W → Prop
  | base : Built F x y F x y
  | step {W : Type} [Fintype W] {H : SimpleGraph W} {a b : W}
      (h : Built F x y H a b) (u v : W) (huv : H.Adj u v) :
      Built F x y (paste F x y H u v) (.inl a) (.inl b)

lemma Built.adj {A W : Type} {F : SimpleGraph A} {x y : A} (hxy : F.Adj x y)
    {H : SimpleGraph W} {a b : W} (h : Built F x y H a b) : H.Adj a b := by
  induction h with
  | base => exact hxy
  | step h u v huv ih => exact ih

lemma Built.connected {A W : Type} {F : SimpleGraph A} {x y : A} (hxy : F.Adj x y)
    (hF : F.Connected) {H : SimpleGraph W} {a b : W} (h : Built F x y H a b) : H.Connected := by
  induction h with
  | base => exact hF
  | step h u v huv ih => exact paste_connected hxy hF ih huv

lemma Built.contains {A W : Type} {F : SimpleGraph A} {x y : A}
    {H : SimpleGraph W} {a b : W} (h : Built F x y H a b) : F ⊑ H := by
  induction h with
  | base => exact .refl _
  | @step W _ H a b h u v huv ih => exact ih.trans ⟨oldCopy F x y H u v⟩

#print axioms petalCopy
#print axioms extendCopy
#print axioms Built.connected
end Erdos713EdgeAttachments

namespace Erdos713EdgeAttachments
open Erdos713EdgeBlockers Erdos713Rate Erdos713RootPower

lemma Built.finite {A W : Type} [Finite A] {F : SimpleGraph A} {x y : A}
    {H : SimpleGraph W} {a b : W} (h : Built F x y H a b) : Finite W := by
  induction h with
  | base => infer_instance
  | step h u v huv ih => infer_instance

/-- Every old vertex image is retained in each attachment. The avoidance
condition concerns the entire fresh copy, not only a local support. -/
lemma Built.aligned_embedding {A W : Type} [Fintype A] {F : SimpleGraph A} {x y : A}
    (hAlign : Alignable F x y) {H : SimpleGraph W} {a b : W} (h : Built F x y H a b)
    {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hExt : Extensible F G k) (hk : Nat.card W ≤ k) {p q : V} (hpq : G.Adj p q) :
    ∃ f : H.Copy G, f a = p ∧ f b = q := by
  classical
  induction h with
  | base =>
    obtain ⟨f,hx,hy,_⟩ := aligned_extension hAlign hExt hpq ∅ (by simp) (by simp) (by simp)
    exact ⟨f,hx,hy⟩
  | @step W _ H a b h u v huv ih =>
    have hkOld : Nat.card W ≤ k := by
      have hle : Nat.card W ≤ Nat.card (W ⊕ Interior x y) :=
        Nat.card_le_card_of_injective (f := fun z : W => (Sum.inl z : W ⊕ Interior x y))
          Sum.inl_injective
      exact hle.trans hk
    obtain ⟨f,hfa,hfb⟩ := ih hkOld
    let U : Finset V := univ.image f
    let B : Finset V := U \ {f u,f v}
    have hc : B.card ≤ k := (card_le_card sdiff_subset).trans
      (card_image_le.trans (by simpa only [card_univ,Fintype.card_eq_nat_card] using hkOld))
    obtain ⟨g,hgx,hgy,hAvoid⟩ := aligned_extension hAlign hExt (f.toHom.map_adj huv)
      B hc (by simp [B]) (by simp [B])
    have hNew (z : Interior x y) (w : W) : g z.val ≠ f w := by
      intro he
      have hmem : g z.val ∈ U := he.symm ▸ mem_image_of_mem f (mem_univ w)
      have hxu : g z.val ≠ f u := fun hh => z.prop.1 (g.injective (hh.trans hgx.symm))
      have hyv : g z.val ≠ f v := fun hh => z.prop.2 (g.injective (hh.trans hgy.symm))
      exact hAvoid z.val (mem_sdiff.mpr ⟨hmem,by
        simpa only [mem_insert,mem_singleton,not_or] using And.intro hxu hyv⟩)
    exact ⟨extendCopy f u v g hgx hgy hNew,hfa,hfb⟩

lemma Built.root_edge_bound {A W : Type} [Fintype A] {F : SimpleGraph A} {x y : A}
    (hxy : F.Adj x y) (hNoIso : ∀ z, ∃ w, F.Adj z w) (hAlign : Alignable F x y)
    {H : SimpleGraph W} {a b : W} (h : Built F x y H a b)
    {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Set V)
    (hB : G.IsBipartiteWith S Sᶜ) (hroot : ∀ f : H.Copy G, f a ∉ S) :
    Nat.card G.edgeSet ≤ 2^(2*Nat.card W+2)*extremalNumber (Fintype.card V) F := by
  by_contra hn
  obtain ⟨K,hKG,hne,hExt⟩ := exists_extensible_core F G hNoIso ⟨x,y,hxy⟩ (Nat.lt_of_not_ge hn)
  obtain ⟨u,v,huv⟩ := ne_bot_iff_exists_adj.mp hne
  have hbad {u v : V} (huv : K.Adj u v) (hu : u ∈ S) : False := by
    obtain ⟨f,hfa,hfb⟩ := h.aligned_embedding hAlign hExt le_rfl huv
    let g : H.Copy G := (Copy.ofLE K G hKG).comp f
    apply hroot g
    change f a ∈ S
    rwa [hfa]
  rcases hB.mem_of_adj (hKG huv) with hh | hh
  · exact hbad huv hh.1
  · exact hbad huv.symm hh.2

lemma global_extremal_bound_of_upper {A : Type*} (F : SimpleGraph A) {r : ℝ}
    (hr : 0 ≤ r)
    (hU : (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^r)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (extremalNumber n F : ℝ) ≤ C*(n : ℝ)^r := by
  classical
  obtain ⟨C,hC,hbound⟩ := global_free_bound_of_upper F hr hU
  refine ⟨C,hC,?_⟩
  intro n
  rw [← Fintype.card_fin n,extremalNumber_le_iff_of_nonneg _ (by positivity)]
  intro G _ hG
  simpa only [edgeFinset_card,Fintype.card_eq_nat_card,Nat.card_fin] using hbound n G hG

lemma Built.root_bound_base {A W : Type} [Fintype A] {F : SimpleGraph A} {x y : A}
    (hxy : F.Adj x y) (hNoIso : ∀ z, ∃ w, F.Adj z w) (hAlign : Alignable F x y)
    {H : SimpleGraph W} {a b : W} (h : Built F x y H a b) {r : ℝ} (hr : 0 ≤ r)
    (hU : (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^r)) :
    RootPowerBound H a r := by
  obtain ⟨C,hC,hbound⟩ := global_extremal_bound_of_upper F hr hU
  let L : ℕ := 2^(2*Nat.card W+2)
  refine ⟨(L : ℝ)*C,by positivity,?_⟩
  intro n G S hB hroot
  have hb := h.root_edge_bound hxy hNoIso hAlign G S hB hroot
  simp only [Fintype.card_fin] at hb
  have hb' : (Nat.card G.edgeSet : ℝ) ≤ (L : ℝ)*(extremalNumber n F : ℝ) := by
    exact_mod_cast hb
  exact hb'.trans (by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbound n) (Nat.cast_nonneg L))

lemma Built.root_bound {A W : Type} [Fintype A] {F : SimpleGraph A} {x y : A}
    (hxy : F.Adj x y) (hF : F.Connected) (hNoIso : ∀ z, ∃ w, F.Adj z w)
    (hAlign : Alignable F x y) {H : SimpleGraph W} {a b : W} (h : Built F x y H a b)
    {r : ℝ} (hr : 0 ≤ r)
    (hU : (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^r))
    (z : W) : RootPowerBound H z r :=
  (h.root_bound_base hxy hNoIso hAlign hr hU).of_reachable ((h.connected hxy hF) a z)

lemma Built.upper {A W : Type} [Fintype A] {F : SimpleGraph A} {x y : A}
    (hxy : F.Adj x y) (hNoIso : ∀ z, ∃ w, F.Adj z w) (hAlign : Alignable F x y)
    {H : SimpleGraph W} {a b : W} (h : Built F x y H a b) {r : ℝ} (hr : 0 ≤ r)
    (hU : (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^r)) :
    (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^r) :=
  (h.root_bound_base hxy hNoIso hAlign hr hU).upper

lemma rate_of_containment {A W : Type} [Fintype A] {F : SimpleGraph A} {x y : A}
    (hxy : F.Adj x y) (hNoIso : ∀ z, ∃ w, F.Adj z w) (hAlign : Alignable F x y)
    {H : SimpleGraph W} {a b : W} (h : Built F x y H a b) {r : ℝ} (hR : HasRate F r)
    {T : Type*} {J : SimpleGraph T} (hlo : F ⊑ J) (hhi : J ⊑ H) : HasRate J r := by
  refine ⟨hR.one_le,(extremal_mono_bigO hhi).trans
    (h.upper hxy hNoIso hAlign (by linarith [hR.one_le]) hR.upper),?_⟩
  intro s hs hJ
  exact hR.lower s hs ((extremal_mono_bigO hlo).trans hJ)

lemma rooted_rate_of_containment {A W : Type} [Fintype A] {F : SimpleGraph A} {x y : A}
    (hxy : F.Adj x y) (hF : F.Connected) (hNoIso : ∀ z, ∃ w, F.Adj z w)
    (hAlign : Alignable F x y) {H : SimpleGraph W} {a b : W} (h : Built F x y H a b)
    {r : ℚ} (hR : HasRate F (r : ℝ)) {T : Type*} {J : SimpleGraph T}
    (hlo : F ⊑ J) (hhi : J ⊑ H) : Erdos713ActualBlocks.RootedRate J := by
  obtain ⟨f⟩ := hhi
  refine ⟨r,rate_of_containment hxy hNoIso hAlign h hR hlo ⟨f⟩,?_⟩
  intro z
  exact (h.root_bound hxy hF hNoIso hAlign (by linarith [hR.one_le]) hR.upper (f z)).of_copy f z

#print axioms Built.aligned_embedding
#print axioms Built.root_edge_bound
#print axioms Built.root_bound
#print axioms rate_of_containment
#print axioms rooted_rate_of_containment
end Erdos713EdgeAttachments

namespace Erdos713EdgeAttachments
open Erdos713Rate Erdos713RootPower

lemma cycle_alignable (n : ℕ) : Alignable (cycleGraph (n+2)) (0 : Fin (n+2)) 1 := by
  intro a b hab
  rcases cycleGraph_adj.mp hab with hab | hab
  · let e : cycleGraph (n+2) ≃g cycleGraph (n+2) :=
      ⟨Equiv.subLeft a,by
        intro u v
        change (cycleGraph (n+2)).Adj (a-u) (a-v) ↔ (cycleGraph (n+2)).Adj u v
        have h₁ : (a-u)-(a-v) = v-u := by abel
        have h₂ : (a-v)-(a-u) = u-v := by abel
        simp only [cycleGraph_adj,h₁,h₂,or_comm]⟩
    refine ⟨e.toCopy,?_,?_⟩
    · change a - 0 = a
      simp
    · change a - 1 = b
      have hh : a = 1+b := sub_eq_iff_eq_add.mp hab
      rw [hh]
      abel
  · let e : cycleGraph (n+2) ≃g cycleGraph (n+2) :=
      ⟨Equiv.addRight a,by intro u v; exact circulantGraph_adj_translate⟩
    refine ⟨e.toCopy,?_,?_⟩
    · change 0 + a = a
      simp
    · change 1+a = b
      exact (sub_eq_iff_eq_add.mp hab).symm

lemma cycle_base_adj (n : ℕ) : (cycleGraph (n+2)).Adj (0 : Fin (n+2)) 1 := by
  rw [cycleGraph_adj]
  exact Or.inr (by simp)

lemma cycle_no_isolates (n : ℕ) (z : Fin (n+2)) : ∃ w, (cycleGraph (n+2)).Adj z w := by
  refine ⟨z+1,?_⟩
  rw [cycleGraph_adj]
  exact Or.inr (by simp)

/-- The lower-containment hypothesis is essential: a subgraph of a cycle
attachment construction need not have the base cycle's exponent. -/
def Sandwich {A : Type} (F : SimpleGraph A) (x y : A) {T : Type*} (J : SimpleGraph T) : Prop :=
  ∃ (W : Type) (H : SimpleGraph W) (a b : W), Built F x y H a b ∧ F ⊑ J ∧ J ⊑ H

lemma Sandwich.rate {A : Type} [Fintype A] {F : SimpleGraph A} {x y : A}
    (hxy : F.Adj x y) (hNoIso : ∀ z, ∃ w, F.Adj z w) (hAlign : Alignable F x y)
    {r : ℝ} (hR : HasRate F r) {T : Type*} {J : SimpleGraph T} (h : Sandwich F x y J) :
    HasRate J r := by
  obtain ⟨W,H,a,b,hB,hlo,hhi⟩ := h
  exact rate_of_containment hxy hNoIso hAlign hB hR hlo hhi

lemma Sandwich.rooted_rate {A : Type} [Fintype A] {F : SimpleGraph A} {x y : A}
    (hxy : F.Adj x y) (hF : F.Connected) (hNoIso : ∀ z, ∃ w, F.Adj z w)
    (hAlign : Alignable F x y) {r : ℚ} (hR : HasRate F (r : ℝ))
    {T : Type*} {J : SimpleGraph T} (h : Sandwich F x y J) :
    Erdos713ActualBlocks.RootedRate J := by
  obtain ⟨W,H,a,b,hB,hlo,hhi⟩ := h
  exact rooted_rate_of_containment hxy hF hNoIso hAlign hB hR hlo hhi

lemma Sandwich.rational {A : Type} [Fintype A] {F : SimpleGraph A} {x y : A}
    (hxy : F.Adj x y) (hNoIso : ∀ z, ∃ w, F.Adj z w) (hAlign : Alignable F x y)
    {r : ℚ} (hR : HasRate F (r : ℝ)) {T : Type*} {J : SimpleGraph T} (hJ : Sandwich F x y J)
    {α c : ℝ} (hα : 1 ≤ α) (hc : c ≠ 0)
    (h : (fun n : ℕ => (extremalNumber n J : ℝ)) ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) :
    α ∈ Set.range ((↑) : ℚ → ℝ) := by
  exact ⟨r,(hJ.rate hxy hNoIso hAlign hR).unique (rate_of_asymptotic hα hc h)⟩

lemma cycle_sandwich_rooted_rate {n : ℕ} {r : ℚ}
    (hR : HasRate (cycleGraph (n+2)) (r : ℝ)) {T : Type*} {J : SimpleGraph T}
    (hJ : Sandwich (cycleGraph (n+2)) 0 1 J) : Erdos713ActualBlocks.RootedRate J :=
  hJ.rooted_rate (cycle_base_adj n) (cycleGraph_connected (n := n+1))
    (cycle_no_isolates n) (cycle_alignable n) hR

lemma hexagon_sandwich_rate {T : Type*} {J : SimpleGraph T}
    (hJ : Sandwich Erdos713C6.C6 0 1 J) : HasRate J ((4 : ℝ)/3) :=
  hJ.rate (cycle_base_adj 4) (cycle_no_isolates 4) (cycle_alignable 4)
    (Erdos713Rate.c6_rate (.refl _) (.refl _))

lemma hexagon_sandwich_rooted_rate {T : Type*} {J : SimpleGraph T}
    (hJ : Sandwich Erdos713C6.C6 0 1 J) : Erdos713ActualBlocks.RootedRate J :=
  cycle_sandwich_rooted_rate (r := 4/3)
    (by simpa using Erdos713Rate.c6_rate (.refl Erdos713C6.C6) (.refl _)) hJ

lemma decagon_sandwich_rate {T : Type*} {J : SimpleGraph T}
    (hJ : Sandwich Erdos713C10.C10 0 1 J) : HasRate J ((6 : ℝ)/5) :=
  hJ.rate (cycle_base_adj 8) (cycle_no_isolates 8) (cycle_alignable 8) Erdos713C10.rate

lemma decagon_sandwich_rooted_rate {T : Type*} {J : SimpleGraph T}
    (hJ : Sandwich Erdos713C10.C10 0 1 J) : Erdos713ActualBlocks.RootedRate J :=
  cycle_sandwich_rooted_rate (r := 6/5) (by simpa using Erdos713C10.rate) hJ

/-- Mixed actual blocks can use either new cycle-attachment family or any
previously proved piece. This invokes actual block decomposition. -/
lemma block_rates_of_cycle_attachment_blocks {W : Type*} [Fintype W] (G : SimpleGraph W)
    (h : ∀ S : Set W, Erdos713Blocks.IsBlock G S →
      3 ≤ Nat.card S →
        Erdos713CycleAssembly.Piece (G.induce S) ∨
        Sandwich Erdos713C6.C6 0 1 (G.induce S) ∨
        Sandwich Erdos713C10.C10 0 1 (G.induce S)) : Erdos713ActualBlocks.BlockRates G := by
  classical
  intro S hS hCyc
  rcases h S hS hCyc with hOld | hHex | hDec
  · haveI : Nonempty S := hS.connected.nonempty
    exact hOld.rooted_rate (hS.noCut.min_degree hS.connected
      (by simpa only [Fintype.card_eq_nat_card] using hCyc))
  · exact hexagon_sandwich_rooted_rate hHex
  · exact decagon_sandwich_rooted_rate hDec

#print axioms cycle_alignable
#print axioms hexagon_sandwich_rooted_rate
#print axioms decagon_sandwich_rooted_rate
#print axioms block_rates_of_cycle_attachment_blocks
end Erdos713EdgeAttachments

namespace Erdos713EdgeAttachments
open Erdos713EdgeBlockers

lemma paste_isBipartite {A W : Type*} {F : SimpleGraph A} {x y : A} (hxy : F.Adj x y)
    (hF : F.IsBipartite) {H : SimpleGraph W} (hH : H.IsBipartite)
    {u v : W} (huv : H.Adj u v) : (paste F x y H u v).IsBipartite := by
  obtain ⟨χF⟩ := hF
  obtain ⟨χH⟩ := hH
  let ε : Fin 2 := χH u - χF x
  let ψ : F.Coloring (Fin 2) := Coloring.mk (fun z => χF z + ε) (by
    intro a b hab he
    exact χF.valid hab (add_right_cancel he))
  have hx : ψ x = χH u := by change χF x + (χH u - χF x) = χH u; abel
  have hy : ψ y = χH v := by
    have h₁ := ψ.valid hxy
    have h₂ := χH.valid huv
    rw [hx] at h₁
    omega
  let χ : W ⊕ Interior x y → Fin 2 := Sum.elim χH (fun z => ψ z.val)
  refine ⟨Coloring.mk χ ?_⟩
  rintro (a | a) (b | b) hab
  · exact χH.valid hab
  · change χH a ≠ ψ b.val
    rcases hab with ⟨rfl,hb⟩ | ⟨rfl,hb⟩
    · rw [← hx]; exact ψ.valid hb
    · rw [← hy]; exact ψ.valid hb
  · change ψ a.val ≠ χH b
    rcases hab with ⟨rfl,ha⟩ | ⟨rfl,ha⟩
    · rw [← hx]; exact (ψ.valid ha).symm
    · rw [← hy]; exact (ψ.valid ha).symm
  · exact ψ.valid hab

lemma Built.isBipartite {A W : Type} {F : SimpleGraph A} {x y : A}
    (hxy : F.Adj x y) (hF : F.IsBipartite)
    {H : SimpleGraph W} {a b : W} (h : Built F x y H a b) : H.IsBipartite := by
  induction h with
  | base => exact hF
  | step h u v huv ih => exact paste_isBipartite hxy hF ih huv

lemma Built.free_edge_bound {A W : Type} [Fintype A] {F : SimpleGraph A} {x y : A}
    (hxy : F.Adj x y) (hNoIso : ∀ z, ∃ w, F.Adj z w) (hAlign : Alignable F x y)
    {H : SimpleGraph W} {a b : W} (h : Built F x y H a b)
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hFree : H.Free G) :
    Nat.card G.edgeSet ≤ 2^(2*Nat.card W+2)*extremalNumber (Fintype.card V) F := by
  by_contra hn
  obtain ⟨K,hKG,hne,hExt⟩ := exists_extensible_core F G hNoIso ⟨x,y,hxy⟩ (Nat.lt_of_not_ge hn)
  obtain ⟨u,v,huv⟩ := ne_bot_iff_exists_adj.mp hne
  obtain ⟨f,_,_⟩ := h.aligned_embedding hAlign hExt le_rfl huv
  exact hFree ((show H ⊑ K from ⟨f⟩).mono_right hKG)

lemma Built.extremal_bound {A W : Type} [Fintype A] {F : SimpleGraph A} {x y : A}
    (hxy : F.Adj x y) (hNoIso : ∀ z, ∃ w, F.Adj z w) (hAlign : Alignable F x y)
    {H : SimpleGraph W} {a b : W} (h : Built F x y H a b) (n : ℕ) :
    extremalNumber n H ≤ 2^(2*Nat.card W+2)*extremalNumber n F := by
  classical
  rw [← Fintype.card_fin n,extremalNumber_le_iff]
  intro G _ hG
  simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using h.free_edge_bound hxy hNoIso hAlign G hG

#print axioms Built.isBipartite
#print axioms Built.extremal_bound
end Erdos713EdgeAttachments
