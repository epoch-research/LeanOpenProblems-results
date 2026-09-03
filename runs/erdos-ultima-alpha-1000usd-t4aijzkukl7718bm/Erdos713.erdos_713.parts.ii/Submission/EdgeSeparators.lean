import FormalConjecturesUtil
import Submission.CompactRootedEdgesAudit

/-! Decomposition at separators consisting of the endpoints of an edge. -/
open SimpleGraph Filter Asymptotics Finset
namespace Erdos713EdgeSeparators
open Erdos713Blocks Erdos713RootPower Erdos713RootBlocks Erdos713Rate
open Erdos713EdgeAttachments
universe u

/-- Removing the endpoints of an edge leaves a preconnected graph.
As with NoCut, empty deletions are permitted. -/
def NoEdgeCut {W : Type*} (G : SimpleGraph W) : Prop :=
  ∀ x y, G.Adj x y → (G.induce ({x,y}ᶜ : Set W)).Preconnected

lemma NoEdgeCut.of_iso {A W : Type*} {F : SimpleGraph A} {G : SimpleGraph W}
    (e : G ≃g F) (h : NoEdgeCut F) : NoEdgeCut G := by
  intro x y hxy
  let f : (F.induce ({e x,e y}ᶜ : Set A)) →g (G.induce ({x,y}ᶜ : Set W)) :=
    { toFun := fun z => ⟨e.symm z.val,by
        intro hz
        have he : z.val = e x ∨ z.val = e y := by
          rcases Set.mem_insert_iff.mp hz with hz | hz
          · exact Or.inl (by simpa using congrArg e hz)
          · exact Or.inr (by simpa using congrArg e hz)
        exact z.prop (by simpa using he)⟩
      map_rel' := fun h => e.symm.toHom.map_adj h }
  apply (h (e x) (e y) (e.toHom.map_adj hxy)).map f
  intro z
  refine ⟨⟨e z.val,?_⟩,?_⟩
  · intro hz
    apply z.prop
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,EquivLike.apply_eq_iff_eq] using hz
  · exact Subtype.ext (e.symm_apply_apply z.val)

/-- Vertices in S away from x,y have no neighbors outside S. -/
structure EdgeLobe {W : Type*} (G : SimpleGraph W) (S : Set W) (x y : W) : Prop where
  left_mem : x ∈ S
  right_mem : y ∈ S
  edge : G.Adj x y
  closed : ∀ a ∈ S, a ≠ x → a ≠ y → ∀ b, G.Adj a b → b ∈ S

lemma EdgeLobe.connected {W : Type*} {G : SimpleGraph W} {S : Set W} {x y : W}
    (h : EdgeLobe G S x y) (hG : G.Connected) : (G.induce S).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨x,h.left_mem⟩,?_⟩
  let R : Set W := {v | ∀ hv : v ∈ S,
    (G.induce S).Reachable ⟨x,h.left_mem⟩ ⟨v,hv⟩}
  have hR : ∀ a ∈ R, ∀ b, G.Adj a b → b ∈ R := by
    intro a ha b hab hb
    by_cases haS : a ∈ S
    · exact (ha haS).trans (show (G.induce S).Adj ⟨a,haS⟩ ⟨b,hb⟩ from hab).reachable
    by_cases hbx : b = x
    · subst b; exact .rfl
    by_cases hby : b = y
    · subst b; exact (show (G.induce S).Adj ⟨x,h.left_mem⟩ ⟨y,hb⟩ from h.edge).reachable
    · exact (haS (h.closed b hb hbx hby a hab.symm)).elim
  rintro ⟨v,hv⟩
  exact mem_of_reachable_closed hR (u := x) (by intro _; exact .rfl) (hG x v) hv

lemma EdgeLobe.complement {W : Type*} {G : SimpleGraph W} {S : Set W} {x y : W}
    (h : EdgeLobe G S x y) : EdgeLobe G (insert x (insert y Sᶜ)) x y := by
  refine ⟨by simp,by simp,h.edge,?_⟩
  intro a ha hax hay b hab
  have haS : a ∉ S := by simpa only [Set.mem_insert_iff,hax,hay,false_or] using ha
  by_cases hbx : b = x
  · simp [hbx]
  by_cases hby : b = y
  · simp [hby]
  have hbS : b ∉ S := fun hbS => haS (h.closed b hbS hbx hby a hab.symm)
  simp [hbS]

lemma edge_cut_lobe {W : Type*} {G : SimpleGraph W} {x y : W} (hxy : G.Adj x y)
    (hCut : ¬ (G.induce ({x,y}ᶜ : Set W)).Preconnected) :
    ∃ S : Set W, EdgeLobe G S x y ∧ (∃ a ∈ S, a ≠ x ∧ a ≠ y) ∧ S ≠ Set.univ := by
  classical
  obtain ⟨a,b,hab⟩ := not_forall.mp hCut |>.imp (fun a ha => not_forall.mp ha)
  let U : Set W := {z | ∃ hz : z ∉ ({x,y} : Set W),
    (G.induce ({x,y}ᶜ : Set W)).Reachable a ⟨z,hz⟩}
  let S := insert x (insert y U)
  have hax : a.val ≠ x := fun he => a.prop (by simp [he])
  have hay : a.val ≠ y := fun he => a.prop (by simp [he])
  have hbx : b.val ≠ x := fun he => b.prop (by simp [he])
  have hby : b.val ≠ y := fun he => b.prop (by simp [he])
  have hbU : b.val ∉ U := by rintro ⟨_,hh⟩; exact hab hh
  refine ⟨S,⟨by simp [S],by simp [S],hxy,?_⟩,
    ⟨a.val,by exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨a.prop,.rfl⟩),hax,hay⟩,?_⟩
  · intro z hz hzx hzy w hzw
    have hzU : z ∈ U := by simpa only [S,Set.mem_insert_iff,hzx,hzy,false_or] using hz
    by_cases hw : w ∈ ({x,y} : Set W)
    · rcases Set.mem_insert_iff.mp hw with hw | hw <;> simp_all [S]
    · obtain ⟨hz,ha⟩ := hzU
      exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        ⟨hw,ha.trans (show (G.induce ({x,y}ᶜ : Set W)).Adj ⟨z,hz⟩ ⟨w,hw⟩ from hzw).reachable⟩)
  · intro hS
    have hbS : b.val ∈ S := hS.symm ▸ Set.mem_univ b.val
    simp only [S,Set.mem_insert_iff,hbx,hby,false_or] at hbS
    exact hbU hbS

/-- The original graph embeds in the edge paste of the two induced sides.
The closure condition forbids edges between their disjoint interiors. -/
noncomputable def EdgeLobe.toPaste {W : Type*} {G : SimpleGraph W} {S : Set W} {x y : W}
    (h : EdgeLobe G S x y) :
    G.Copy (paste (G.induce S) ⟨x,h.left_mem⟩ ⟨y,h.right_mem⟩
      (G.induce (insert x (insert y Sᶜ))) ⟨x,by simp⟩ ⟨y,by simp⟩) := by
  classical
  let T := insert x (insert y Sᶜ)
  let xS : S := ⟨x,h.left_mem⟩
  let yS : S := ⟨y,h.right_mem⟩
  have hS {w : W} (hw : w ∉ T) : w ∈ S := by
    by_contra hn
    exact hw (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hn))
  have hx {w : W} (hw : w ∉ T) : w ≠ x := by intro he; exact hw (by simp [T,he])
  have hy {w : W} (hw : w ∉ T) : w ≠ y := by intro he; exact hw (by simp [T,he])
  let interior (w : W) (hw : w ∉ T) : Interior xS yS :=
    ⟨⟨w,hS hw⟩,fun he => hx hw (congrArg Subtype.val he),fun he => hy hw (congrArg Subtype.val he)⟩
  let f : W → T ⊕ Interior xS yS := fun w =>
    if hw : w ∈ T then .inl ⟨w,hw⟩ else .inr (interior w hw)
  have hroot {a b : W} (ha : a ∈ T) (hb : b ∉ T) (hab : G.Adj a b) : a = x ∨ a = y := by
    have haS := h.closed b (hS hb) (hx hb) (hy hb) a hab.symm
    rcases Set.mem_insert_iff.mp ha with ha | ha
    · exact Or.inl ha
    · rcases Set.mem_insert_iff.mp ha with ha | ha
      · exact Or.inr ha
      · exact (ha haS).elim
  refine ⟨⟨f,?_⟩,?_⟩
  · intro a b hab
    by_cases ha : a ∈ T <;> by_cases hb : b ∈ T
    · simpa only [f,dif_pos ha,dif_pos hb,paste] using hab
    · simp only [f,dif_pos ha,dif_neg hb,paste]
      rcases hroot ha hb hab with rfl | rfl
      · exact Or.inl ⟨rfl,hab⟩
      · exact Or.inr ⟨rfl,hab⟩
    · simp only [f,dif_neg ha,dif_pos hb,paste]
      rcases hroot hb ha hab.symm with rfl | rfl
      · exact Or.inl ⟨rfl,hab.symm⟩
      · exact Or.inr ⟨rfl,hab.symm⟩
    · simpa only [f,dif_neg ha,dif_neg hb,paste] using hab
  · have hf : Function.LeftInverse
        (Sum.elim (fun w : T => w.val) (fun w : Interior xS yS => w.val.val)) f := by
      intro w
      by_cases hw : w ∈ T <;> simp [f,hw,interior]
    exact hf.injective

lemma EdgeLobe.root_bound {W : Type*} [Fintype W] {G : SimpleGraph W}
    {S : Set W} {x y : W} (h : EdgeLobe G S x y) (hG : G.Connected) {r : ℝ}
    (hS : ∀ z, RootPowerBound (G.induce S) z r)
    (hT : ∀ z, RootPowerBound (G.induce (insert x (insert y Sᶜ))) z r) :
    ∀ z, RootPowerBound G z r := by
  classical
  let xS : S := ⟨x,h.left_mem⟩
  let yS : S := ⟨y,h.right_mem⟩
  let T := insert x (insert y Sᶜ)
  let xT : T := ⟨x,by simp [T]⟩
  let yT : T := ⟨y,by simp [T]⟩
  have hxyS : (G.induce S).Adj xS yS := h.edge
  have hxyT : (G.induce T).Adj xT yT := h.edge
  have hSC := h.connected hG
  have hTC := h.complement.connected hG
  letI : Nontrivial S := ⟨⟨xS,yS,hxyS.ne⟩⟩
  have hR := Erdos713RootedEdges.root_bound hxyS hSC.preconnected.exists_adj_of_nontrivial
    hxyT (hS xS) (hT xT)
  have hC := paste_connected hxyS hSC hTC hxyT
  intro z
  exact (hR.of_reachable (hC _ (h.toPaste z))).of_copy h.toPaste z

/-- An induced terminal piece for deletion of clique separators of size one
or two. This is not an assertion of three-vertex-connectivity. -/
structure IsAtom {W : Type*} (G : SimpleGraph W) : Prop where
  connected : G.Connected
  noCut : NoCut G
  noEdgeCut : NoEdgeCut G

lemma IsAtom.of_iso {A W : Type*} {F : SimpleGraph A} {G : SimpleGraph W}
    (e : G ≃g F) (h : IsAtom F) : IsAtom G :=
  ⟨h.connected.map e.symm.toHom e.symm.toEquiv.surjective,
    h.noCut.map e.symm.toHom e.symm.bijective,h.noEdgeCut.of_iso e⟩

/-- Bounds are requested only for terminal induced pieces of order at least
three. Edges and singletons are handled by the baseline exponent one. -/
def AtomUpper {W : Type*} (G : SimpleGraph W) (r : ℝ) : Prop :=
  ∀ S : Set W, IsAtom (G.induce S) → 3 ≤ Nat.card S →
    ∀ x, RootPowerBound (G.induce S) x r

lemma AtomUpper.induce {W : Type*} [Fintype W] {G : SimpleGraph W} {r : ℝ}
    (h : AtomUpper G r) (T : Set W) : AtomUpper (G.induce T) r := by
  classical
  intro U hU hc y
  let e := induceImageIso G T U
  have hc' : 3 ≤ Nat.card ↥(Subtype.val '' U) := by
    rw [← Nat.card_congr e.toEquiv]
    exact hc
  exact (h _ (hU.of_iso e.symm) hc' (e y)).of_copy e.toCopy y

/-- A finite connected graph's rooted upper bound is determined by its
induced pieces with no cut vertex and no adjacent two-vertex separator. -/
lemma root_bound_of_atoms {W : Type u} [Fintype W] (G : SimpleGraph W)
    (hG : G.Connected) {r : ℝ} (hr : 1 ≤ r) (h : AtomUpper G r) :
    ∀ z, RootPowerBound G z r := by
  classical
  suffices hh : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] (G : SimpleGraph W),
      Fintype.card W = n → G.Connected → AtomUpper G r → ∀ z, RootPowerBound G z r from
    hh _ W G rfl hG h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ G hc hG h z
    by_cases hsmall : Nat.card W ≤ 2
    · exact (root_bound_small G hsmall z).mono hr
    have hthree : 3 ≤ Nat.card W := by omega
    by_cases hNC : NoCut G
    · by_cases hNE : NoEdgeCut G
      · have hU := h Set.univ ((show IsAtom G from ⟨hG,hNC,hNE⟩).of_iso (induceUnivIso G))
          (by simpa using hthree)
        exact (hU ((induceUnivIso G).symm z)).of_copy (induceUnivIso G).symm.toCopy z
      · change ¬ ∀ x y, G.Adj x y → (G.induce ({x,y}ᶜ : Set W)).Preconnected at hNE
        push_neg at hNE
        obtain ⟨x,y,hxy,hcut⟩ := hNE
        obtain ⟨S,hS,hOther,hProper⟩ := edge_cut_lobe hxy hcut
        obtain ⟨w,hw⟩ := (Set.ne_univ_iff_exists_notMem S).mp hProper
        have hScard : Fintype.card S < n := (Fintype.card_subtype_lt hw).trans_eq hc
        let T := insert x (insert y Sᶜ)
        have hTcard : Fintype.card T < n := by
          obtain ⟨v,hv,hvx,hvy⟩ := hOther
          have hn : v ∉ T := by simp [T,hvx,hvy,hv]
          exact (Fintype.card_subtype_lt hn).trans_eq hc
        have hSRoot := ih _ hScard S (G.induce S) rfl (hS.connected hG) (h.induce S)
        have hTRoot := ih _ hTcard T (G.induce T) rfl (hS.complement.connected hG) (h.induce T)
        exact hS.root_bound hG hSRoot hTRoot z
    · haveI : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp
        (by simpa only [Fintype.card_eq_nat_card] using (show 1 < Nat.card W by omega))
      obtain ⟨x⟩ := hG.nonempty
      obtain ⟨y,hxy⟩ := hG.preconnected.exists_adj_of_nontrivial x
      obtain ⟨S,x,hL,hSNC⟩ := exists_minimal_lobe (G := G)
        ⟨Set.univ,x,Set.mem_univ x,⟨y,Set.mem_univ y,hxy.ne.symm⟩,by simp⟩
      have hProper : S ≠ Set.univ := by
        intro hS
        subst S
        exact hNC (hSNC.map (induceUnivIso G).toHom (induceUnivIso G).bijective)
      obtain ⟨w,hw⟩ := (Set.ne_univ_iff_exists_notMem S).mp hProper
      have hScard : Fintype.card S < n := (Fintype.card_subtype_lt hw).trans_eq hc
      let T : Set W := insert x Sᶜ
      have hT := hL.complement hProper
      have hTcard : Fintype.card T < n := by
        obtain ⟨v,hv,hvx⟩ := hL.other
        have hn : v ∉ T := by simp [T,hvx,hv]
        exact (Fintype.card_subtype_lt hn).trans_eq hc
      have hSC := hL.connected hG
      have hTC := hT.connected hG
      have hSRoot := ih _ hScard S (G.induce S) rfl hSC (h.induce S)
      have hTRoot := ih _ hTcard T (G.induce T) rfl hTC (h.induce T)
      have hR := (hSRoot ⟨x,hL.root_mem⟩).wedge (hTRoot ⟨x,hT.root_mem⟩) hr (Erdos713RootBlocks.Lobe.no_isolates hL hG)
      let e := lobeWedgeIso hL
      have hC := Erdos713Gluing.wedge_connected hSC hTC ⟨x,hL.root_mem⟩ ⟨x,hT.root_mem⟩
      exact (hR.of_reachable (hC _ (e.symm z))).of_copy e.symm.toCopy z

lemma atomUpper_of_root_bound {W : Type*} [Fintype W] (G : SimpleGraph W)
    (hG : G.Connected) {r : ℝ} {z : W} (h : RootPowerBound G z r) : AtomUpper G r := by
  intro S hS hc y
  exact (h.of_reachable (hG z y.val)).of_copy (Copy.induce G S) y

lemma root_bound_iff_atoms {W : Type*} [Fintype W] (G : SimpleGraph W)
    (hG : G.Connected) {r : ℝ} (hr : 1 ≤ r) (z : W) :
    RootPowerBound G z r ↔ AtomUpper G r :=
  ⟨atomUpper_of_root_bound G hG,fun h => root_bound_of_atoms G hG hr h z⟩

/-- Finite extraction requires only a rooted lower threshold. The selected
piece need not have any rooted upper bound at r. -/
lemma exists_atom_root_lower {W : Type*} [Fintype W] (G : SimpleGraph W)
    (hG : G.Connected) {x : W} {r : ℝ} (hr : 1 < r) (hR : RootLower G x r) :
    ∃ S : Set W, IsAtom (G.induce S) ∧ 3 ≤ Nat.card S ∧
      ∀ y, RootLower (G.induce S) y r := by
  classical
  by_contra hn
  push_neg at hn
  have hEach (S : Set W) : ∃ a : ℝ, 1 ≤ a ∧ a < r ∧
      (IsAtom (G.induce S) → 3 ≤ Nat.card S → ∀ y, RootPowerBound (G.induce S) y a) := by
    by_cases hS : IsAtom (G.induce S) ∧ 3 ≤ Nat.card S
    · obtain ⟨y,hy⟩ := hn S hS.1 hS.2
      change ¬ ∀ a : ℝ, 1 ≤ a → RootPowerBound (G.induce S) y a → r ≤ a at hy
      push_neg at hy
      obtain ⟨a,ha,hroot,har⟩ := hy
      exact ⟨a,ha,har,fun _ _ z => hroot.of_reachable (hS.1.connected y z)⟩
    · exact ⟨1,le_rfl,hr,fun hAtom hc => (hS ⟨hAtom,hc⟩).elim⟩
  choose a ha har hEach using hEach
  obtain ⟨S₀,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Set W)) a
    ⟨∅,Finset.mem_univ _⟩
  have hBound : AtomUpper G (a S₀) := by
    intro S hS hc y
    exact (hEach S hS hc y).mono (hmax S (Finset.mem_univ _))
  exact (not_lt_of_ge (hR (a S₀) (ha S₀)
    (root_bound_of_atoms G hG (ha S₀) hBound x))) (har S₀)

lemma exists_atom_root_rate {W : Type*} [Fintype W] (G : SimpleGraph W)
    (hG : G.Connected) {x : W} {r : ℝ} (hr : 1 < r) (hR : HasRootRate G x r) :
    ∃ S : Set W, IsAtom (G.induce S) ∧ 3 ≤ Nat.card S ∧
      ∀ y, HasRootRate (G.induce S) y r := by
  obtain ⟨S,hS,hc,hLower⟩ := exists_atom_root_lower G hG hr hR.lower
  exact ⟨S,hS,hc,fun y => ⟨hr.le,
    atomUpper_of_root_bound G hG hR.upper S hS hc y,hLower y⟩⟩

/-- The ordinary upper bound passes to the SAME induced piece. Its attained
ordinary threshold is either r or strictly smaller; only a rooted lower
threshold is retained in the second branch. -/
lemma atom_rate_or_gap {W : Type*} [Fintype W] (G : SimpleGraph W)
    (hG : G.Connected) {x : W} {r : ℝ} (hr : 1 < r) (hR : RootLower G x r)
    (hU : (fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^r)) :
    ∃ S : Set W, IsAtom (G.induce S) ∧ 3 ≤ Nat.card S ∧
      (∀ y, RootLower (G.induce S) y r) ∧
      (HasRate (G.induce S) r ∨ ∃ a : ℝ, 1 ≤ a ∧ a < r ∧
        (fun n : ℕ => (extremalNumber n (G.induce S) : ℝ)) =O[atTop]
          (fun n : ℕ => (n : ℝ)^a)) := by
  classical
  obtain ⟨S,hS,hc,hLower⟩ := exists_atom_root_lower G hG hr hR
  refine ⟨S,hS,hc,hLower,?_⟩
  by_cases hRate : HasRate (G.induce S) r
  · exact Or.inl hRate
  · right
    have hupper := (extremal_mono_bigO ⟨Copy.induce G S⟩).trans hU
    have hNoLower : ¬ ∀ a : ℝ, 1 ≤ a →
        ((fun n : ℕ => (extremalNumber n (G.induce S) : ℝ)) =O[atTop]
          (fun n : ℕ => (n : ℝ)^a)) → r ≤ a :=
      fun hh => hRate ⟨hr.le,hupper,hh⟩
    push_neg at hNoLower
    obtain ⟨a,ha,hu,har⟩ := hNoLower
    exact ⟨a,ha,har,hu⟩

/-- At an irrational threshold, the SAME atom has no small-shore rooted-rate
certificate. No exact asymptotic is asserted for this induced graph. -/
lemma remaining_atom_with_rate_or_gap {W : Type*} [Fintype W] (G : SimpleGraph W)
    (hG : G.Connected) (hB : G.IsBipartite) {x : W} {r : ℝ}
    (hr : 1 < r) (hR : RootLower G x r)
    (hU : (fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^r))
    (hIrr : r ∉ Set.range ((↑) : ℚ → ℝ)) :
    ∃ S : Set W, IsAtom (G.induce S) ∧ (G.induce S).IsBipartite ∧ 8 ≤ Nat.card S ∧
      (∀ v, 2 ≤ Nat.card ((G.induce S).neighborSet v)) ∧
      (∀ A : Set S, (G.induce S).IsBipartiteWith A Aᶜ → 4 ≤ Nat.card A) ∧
      ¬ G.induce S ⊑ Erdos713C10.C10 ∧
      ¬ Erdos713ActualBlocks.RootedRate (G.induce S) ∧
      (∀ y, RootLower (G.induce S) y r) ∧
      (HasRate (G.induce S) r ∨ ∃ a : ℝ, 1 ≤ a ∧ a < r ∧
        (fun n : ℕ => (extremalNumber n (G.induce S) : ℝ)) =O[atTop]
          (fun n : ℕ => (n : ℝ)^a)) := by
  classical
  obtain ⟨S,hS,hc,hLower,hAlt⟩ := atom_rate_or_gap G hG hr hR hU
  haveI : Nonempty S := hS.connected.nonempty
  have hd := hS.noCut.min_degree hS.connected (by
    simpa only [Fintype.card_eq_nat_card] using hc)
  have hu := (extremal_mono_bigO ⟨Copy.induce G S⟩).trans hU
  have hNoRoot : ¬ Erdos713ActualBlocks.RootedRate (G.induce S) := by
    rintro ⟨q,hq,hRoot⟩
    let z : S := Classical.arbitrary S
    exact hIrr ⟨q,le_antisymm (hq.lower r hr.le hu) (hLower z q hq.one_le (hRoot z))⟩
  have hPiece : ¬ Erdos713CycleAssembly.Piece (G.induce S) :=
    fun hp => hNoRoot (hp.rooted_rate hd)
  have hSmall : ¬ ∃ A : Set S, (G.induce S).IsBipartiteWith A Aᶜ ∧ Nat.card A ≤ 3 :=
    fun hh => hPiece (Or.inl hh)
  push_neg at hSmall
  have hSB : (G.induce S).IsBipartite := Colorable.of_hom (Copy.induce G S).toHom hB
  have hc' : 8 ≤ Nat.card S := by
    by_contra hc'
    obtain ⟨A,hA,hcard⟩ := Erdos713ThreeSide.small_bipartition_of_card_le_seven (G.induce S) hSB
      (by simpa only [Fintype.card_eq_nat_card] using (show Nat.card S ≤ 7 by omega))
    exact (not_lt_of_ge hcard) (hSmall A hA)
  exact ⟨S,hS,hSB,hc',hd,fun A hA => hSmall A hA,
    fun hh => hPiece (Or.inr hh),hNoRoot,hLower,hAlt⟩

/-- Matching rational ordinary/rooted data are requested only for atoms. -/
def AtomRates {W : Type*} (G : SimpleGraph W) : Prop :=
  ∀ S : Set W, IsAtom (G.induce S) → 3 ≤ Nat.card S →
    Erdos713ActualBlocks.RootedRate (G.induce S)

lemma rooted_rate_of_atoms {W : Type*} [Fintype W] (G : SimpleGraph W)
    (hG : G.Connected) (hAtoms : AtomRates G) : Erdos713ActualBlocks.RootedRate G := by
  classical
  have hEach (S : Set W) : ∃ q : ℚ, 1 ≤ (q : ℝ) ∧
      ((IsAtom (G.induce S) ∧ 3 ≤ Nat.card S) →
        HasRate (G.induce S) (q : ℝ) ∧ ∀ y, RootPowerBound (G.induce S) y (q : ℝ)) ∧
      (¬ (IsAtom (G.induce S) ∧ 3 ≤ Nat.card S) → q = 1) := by
    by_cases hS : IsAtom (G.induce S) ∧ 3 ≤ Nat.card S
    · obtain ⟨q,hq,hRoots⟩ := hAtoms S hS.1 hS.2
      exact ⟨q,hq.one_le,fun _ => ⟨hq,hRoots⟩,fun hn => (hn hS).elim⟩
    · exact ⟨1,by norm_num,fun hh => (hS hh).elim,fun _ => rfl⟩
  choose q hOne hRates hDefault using hEach
  obtain ⟨S₀,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Set W)) q
    ⟨∅,Finset.mem_univ _⟩
  have hBound : AtomUpper G (q S₀ : ℝ) := by
    intro S hS hc y
    exact ((hRates S ⟨hS,hc⟩).2 y).mono (by exact_mod_cast hmax S (Finset.mem_univ _))
  have hRoots := root_bound_of_atoms G hG (hOne S₀) hBound
  obtain ⟨x⟩ := hG.nonempty
  refine ⟨q S₀,⟨hOne S₀,(hRoots x).upper,?_⟩,hRoots⟩
  intro a ha hu
  by_cases hS : IsAtom (G.induce S₀) ∧ 3 ≤ Nat.card S₀
  · exact (hRates S₀ hS).1.lower a ha ((extremal_mono_bigO ⟨Copy.induce G S₀⟩).trans hu)
  · simpa only [hDefault S₀ hS,Rat.cast_one] using ha

lemma AtomRates.induce {W : Type*} [Fintype W] {G : SimpleGraph W}
    (h : AtomRates G) (T : Set W) : AtomRates (G.induce T) := by
  classical
  intro U hU hc
  let e := induceImageIso G T U
  have hc' : 3 ≤ Nat.card ↥(Subtype.val '' U) := by
    rw [← Nat.card_congr e.toEquiv]
    exact hc
  exact (h _ (hU.of_iso e.symm) hc').of_iso e

lemma block_rates_of_atoms {W : Type*} [Fintype W] (G : SimpleGraph W)
    (h : AtomRates G) : Erdos713ActualBlocks.BlockRates G := by
  classical
  intro S hS hc
  exact rooted_rate_of_atoms (G.induce S) hS.connected (h.induce S)

lemma rational_of_atoms {W : Type*} [Fintype W] (G : SimpleGraph W)
    (h : AtomRates G) {α c : ℝ} (hα : 1 ≤ α) (hc : c ≠ 0)
    (hAsymptotic : IsEquivalent atTop (fun n : ℕ => (extremalNumber n G : ℝ))
      (fun n : ℕ => c*(n : ℝ)^α)) : α ∈ Set.range ((↑) : ℚ → ℝ) :=
  Erdos713ActualBlocks.rational_of_blocks G (block_rates_of_atoms G h) hα hc hAsymptotic

#print axioms NoEdgeCut.of_iso
#print axioms EdgeLobe.connected
#print axioms edge_cut_lobe
#print axioms EdgeLobe.toPaste
#print axioms EdgeLobe.root_bound
#print axioms root_bound_iff_atoms
#print axioms exists_atom_root_rate
#print axioms remaining_atom_with_rate_or_gap
#print axioms rooted_rate_of_atoms
#print axioms rational_of_atoms
end Erdos713EdgeSeparators
