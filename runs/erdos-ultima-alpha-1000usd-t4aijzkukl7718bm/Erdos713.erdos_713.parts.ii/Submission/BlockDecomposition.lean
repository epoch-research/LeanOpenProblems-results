import FormalConjecturesUtil

/-! Finite end-piece decomposition for connected graphs. These graph-theoretic
lemmas do not assert rationality of arbitrary extremal exponents. -/
open SimpleGraph
namespace Erdos713Blocks
universe u
variable {V : Type u} {G : SimpleGraph V}

/-- Deleting any vertex leaves a preconnected graph. Single vertices and edges
are permitted by this convention; no nonempty deletion is required. -/
def NoCut (G : SimpleGraph V) : Prop := ∀ x : V, (G.induce {x}ᶜ).Preconnected

lemma NoCut.map {W : Type*} {H : SimpleGraph W} (h : NoCut G)
    (f : G →g H) (hf : Function.Bijective f) : NoCut H := by
  intro y
  obtain ⟨x,rfl⟩ := hf.2 y
  let g : (G.induce {x}ᶜ) →g (H.induce {f x}ᶜ) :=
    { toFun := fun v => ⟨f v.val,fun he => v.prop (hf.1 he)⟩
      map_rel' := fun hvw => f.map_adj hvw }
  apply (h x).map g
  rintro ⟨v,hv⟩
  obtain ⟨w,hw⟩ := hf.2 v
  have hwx : w ≠ x := by intro he; exact hv (hw.symm.trans (congrArg f he))
  exact ⟨⟨w,hwx⟩,Subtype.ext hw⟩


/-- A maximal nonempty induced connected subgraph with no cut vertex.
This convention includes bridge edges and isolated singleton blocks. -/
structure IsBlock (G : SimpleGraph V) (S : Set V) : Prop where
  connected : (G.induce S).Connected
  noCut : NoCut (G.induce S)
  maximal : ∀ T : Set V, S ⊆ T → (G.induce T).Connected → NoCut (G.induce T) → T = S

lemma exists_block_superset [Fintype V] (S : Set V)
    (hS : (G.induce S).Connected) (hNC : NoCut (G.induce S)) :
    ∃ T : Set V, S ⊆ T ∧ IsBlock G T := by
  classical
  let P : Finset (Set V) := Finset.univ.filter
    (fun T => S ⊆ T ∧ (G.induce T).Connected ∧ NoCut (G.induce T))
  have hSP : S ∈ P := by simp [P,hS,hNC]
  obtain ⟨T,hT,hmax⟩ := P.exists_max_image (fun T => Nat.card T) ⟨S,hSP⟩
  obtain ⟨hST,hConn,hNoCut⟩ := (Finset.mem_filter.mp hT).2
  refine ⟨T,hST,hConn,hNoCut,?_⟩
  intro U hTU hU hUNC
  have hUP : U ∈ P := by simp [P,hST.trans hTU,hU,hUNC]
  have hc := hmax U hUP
  by_contra he
  have hlt := Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨hTU,Ne.symm he⟩)
  simp only [Nat.card_coe_set_eq] at hc
  omega

/-- All vertices of S except its root have no neighbours outside S. -/
structure Lobe (G : SimpleGraph V) (S : Set V) (x : V) : Prop where
  root_mem : x ∈ S
  other : ∃ u ∈ S, u ≠ x
  closed : ∀ u ∈ S, u ≠ x → ∀ v, G.Adj u v → v ∈ S

lemma mem_of_reachable_closed {S : Set V}
    (hS : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S)
    {u v : V} (hu : u ∈ S) (h : G.Reachable u v) : v ∈ S := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | cons hadj p ih => exact ih (hS _ hu _ hadj)

lemma Lobe.connected {S : Set V} {x : V} (h : Lobe G S x) (hG : G.Connected) :
    (G.induce S).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨x,h.root_mem⟩,?_⟩
  let R : Set V := {v | ∀ hv : v ∈ S, (G.induce S).Reachable ⟨x,h.root_mem⟩ ⟨v,hv⟩}
  have hR : ∀ u ∈ R, ∀ v, G.Adj u v → v ∈ R := by
    intro u hu v huv hv
    by_cases huS : u ∈ S
    · exact (hu huS).trans (show (G.induce S).Adj ⟨u,huS⟩ ⟨v,hv⟩ from huv).reachable
    by_cases he : v = x
    · subst v; exact .rfl
    · exact (huS (h.closed v hv he u huv.symm)).elim
  rintro ⟨v,hv⟩
  exact mem_of_reachable_closed hR (u := x) (by intro _; exact .rfl) (hG x v) hv

/-- A disconnected vertex deletion has a nonempty closed part avoiding any
prescribed vertex, and leaves another vertex outside the part and the cut. -/
lemma cut_piece (x w : V) (hw : ¬ (G.induce {w}ᶜ).Preconnected) :
    ∃ U : Set V, U.Nonempty ∧ w ∉ U ∧ x ∉ U ∧
      (∃ b, b ≠ w ∧ b ∉ U) ∧
      ∀ a ∈ U, ∀ b, G.Adj a b → b = w ∨ b ∈ U := by
  classical
  have hpair : ∃ a b : ↥({w}ᶜ : Set V),
      ¬ (G.induce {w}ᶜ).Reachable a b ∧
      ∀ hx : x ≠ w, ¬ (G.induce {w}ᶜ).Reachable a ⟨x,hx⟩ := by
    by_cases hx : x = w
    · obtain ⟨a,b,hab⟩ := not_forall.mp hw |>.imp (fun a ha => not_forall.mp ha)
      exact ⟨a,b,hab,fun hx' => (hx' hx).elim⟩
    · have ha : ∃ a, ¬ (G.induce {w}ᶜ).Reachable a ⟨x,hx⟩ := by
        by_contra hh
        push_neg at hh
        exact hw (fun a b => (hh a).trans (hh b).symm)
      obtain ⟨a,ha⟩ := ha
      exact ⟨a,⟨x,hx⟩,ha,fun _ => ha⟩
  obtain ⟨a,b,hab,hax⟩ := hpair
  let U : Set V := {v | ∃ hv : v ≠ w, (G.induce {w}ᶜ).Reachable a ⟨v,hv⟩}
  refine ⟨U,⟨a.val,a.prop,.rfl⟩,?_,?_,⟨b.val,b.prop,?_⟩,?_⟩
  · rintro ⟨hh,_⟩; exact hh rfl
  · rintro ⟨hx,h⟩; exact hax hx h
  · rintro ⟨_,h⟩; exact hab h
  · intro v hv z hvz
    by_cases hz : z = w
    · exact Or.inl hz
    · obtain ⟨hv,ha⟩ := hv
      exact Or.inr ⟨hz,ha.trans (show (G.induce {w}ᶜ).Adj ⟨v,hv⟩ ⟨z,hz⟩ from hvz).reachable⟩

lemma lobe_refine_of_cut {S : Set V} {x : V} (h : Lobe G S x)
    (w : S) (hw : ¬ ((G.induce S).induce {w}ᶜ).Preconnected) :
    ∃ T : Set V, T ⊂ S ∧ Lobe G T w.val := by
  classical
  obtain ⟨U,⟨a,ha⟩,hwU,hxU,⟨b,hbw,hbU⟩,hU⟩ :=
    cut_piece (G := G.induce S) ⟨x,h.root_mem⟩ w hw
  let T : Set V := Subtype.val '' (insert w U)
  have hTS : T ⊆ S := by rintro v ⟨v,hv,rfl⟩; exact v.prop
  have hbT : b.val ∉ T := by
    rintro ⟨z,hz,he⟩
    have hzb : z = b := Subtype.ext he
    subst z
    exact (Set.mem_insert_iff.mp hz).elim hbw hbU
  refine ⟨T,Set.ssubset_iff_subset_ne.mpr ⟨hTS,?_⟩,?_,?_,?_⟩
  · intro he; exact hbT (he.symm ▸ b.prop)
  · exact ⟨w,Set.mem_insert _ _,rfl⟩
  · refine ⟨a.val,⟨a,Set.mem_insert_of_mem _ ha,rfl⟩,?_⟩
    intro he; exact hwU (Subtype.ext he ▸ ha)
  · intro z hz hzw v hzv
    obtain ⟨z,hz,rfl⟩ := hz
    have hzU : z ∈ U := (Set.mem_insert_iff.mp hz).resolve_left
      (fun he => hzw (congrArg Subtype.val he))
    have hzx : z.val ≠ x := by
      intro he
      have hz : z = (⟨x,h.root_mem⟩ : S) := Subtype.ext he
      exact hxU (hz ▸ hzU)
    have hvS : v ∈ S := h.closed z.val z.prop hzx v hzv
    rcases hU z hzU ⟨v,hvS⟩ hzv with he | he
    · exact ⟨⟨v,hvS⟩,Set.mem_insert_iff.mpr (Or.inl he),rfl⟩
    · exact ⟨⟨v,hvS⟩,Set.mem_insert_of_mem _ he,rfl⟩

lemma exists_minimal_lobe [Fintype V] (h : ∃ S x, Lobe G S x) :
    ∃ S x, Lobe G S x ∧ NoCut (G.induce S) := by
  classical
  have hk : ∃ k : ℕ, ∃ S x, Lobe G S x ∧ Fintype.card S = k := by
    obtain ⟨S,x,h⟩ := h
    exact ⟨_,S,x,h,rfl⟩
  obtain ⟨S,x,hS,hcard⟩ := Nat.find_spec hk
  refine ⟨S,x,hS,?_⟩
  intro w
  by_contra hw
  obtain ⟨T,hTS,hT⟩ := lobe_refine_of_cut hS w hw
  have hlt : Fintype.card T < Fintype.card S := by
    let f : T → S := fun z => ⟨z.val,hTS.le z.prop⟩
    apply Fintype.card_lt_of_injective_not_surjective f
    · intro a b he
      have hv : a.val = b.val := congrArg (fun q : S => q.val) he
      exact Subtype.ext hv
    · intro hf
      apply hTS.ne
      apply Set.Subset.antisymm hTS.le
      intro v hv
      obtain ⟨z,hz⟩ := hf ⟨v,hv⟩
      have he : z.val = v := congrArg (fun q : S => q.val) hz
      exact he ▸ z.prop
  have hle := Nat.find_min' hk (show ∃ S x, Lobe G S x ∧ Fintype.card S = Fintype.card T from
    ⟨T,w.val,hT,rfl⟩)
  omega


lemma Lobe.complement {S : Set V} {x : V} (h : Lobe G S x) (hS : S ≠ Set.univ) :
    Lobe G (insert x Sᶜ) x := by
  classical
  refine ⟨Set.mem_insert _ _,?_,?_⟩
  · obtain ⟨v,hv⟩ := not_forall.mp (fun hh => hS (Set.eq_univ_of_forall hh))
    exact ⟨v,Or.inr hv,fun he => hv (he.symm ▸ h.root_mem)⟩
  · intro u hu hux v huv
    have huS : u ∉ S := (Set.mem_insert_iff.mp hu).resolve_left hux
    by_cases hvS : v ∈ S
    · by_cases hvx : v = x
      · exact Or.inl hvx
      · exact (huS (h.closed v hvS hvx u huv.symm)).elim
    · exact Or.inr hvS

lemma Lobe.root_adj {S : Set V} {x : V} (h : Lobe G S x) (hG : G.Connected) :
    ∃ v : S, (G.induce S).Adj ⟨x,h.root_mem⟩ v := by
  obtain ⟨v,hv,hvx⟩ := h.other
  apply (G.induce S).mem_support.mp
  apply mem_support_of_reachable (v := (⟨v,hv⟩ : S))
    (fun he => hvx (congrArg Subtype.val he).symm)
  exact h.connected hG _ _

lemma Lobe.card_ge_three [Fintype V] {S : Set V} {x : V} (h : Lobe G S x)
    (hd : ∀ v, 2 ≤ Nat.card (G.neighborSet v)) : 3 ≤ Nat.card S := by
  classical
  obtain ⟨v,hv,hvx⟩ := h.other
  let f : G.neighborSet v ↪ (G.induce S).neighborSet ⟨v,hv⟩ :=
    ⟨fun w => ⟨⟨w.val,h.closed v hv hvx w.val w.prop⟩,w.prop⟩,by
      intro a b he
      exact Subtype.ext (congrArg (fun q : (G.induce S).neighborSet ⟨v,hv⟩ => q.val.val) he)⟩
  have hle := Fintype.card_le_of_embedding f
  have hlt := (G.induce S).degree_lt_card_verts ⟨v,hv⟩
  have hvd := hd v
  rw [Nat.card_eq_fintype_card]
  simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] at hvd hle
  omega

lemma NoCut.min_degree [Fintype V] (h : NoCut G) (hG : G.Connected)
    (hcard : 3 ≤ Fintype.card V) : ∀ v, 2 ≤ Nat.card (G.neighborSet v) := by
  classical
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  intro v
  have hpos := hG.preconnected.degree_pos_of_nontrivial v
  simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
  by_contra hv
  have hv1 : G.degree v = 1 := by omega
  obtain ⟨w,hvw,hw⟩ := degree_eq_one_iff_existsUnique_adj.mp hv1
  have hpair : ({v,w} : Finset V).card ≤ 2 := by
    simpa using List.toFinset_card_le ([v,w] : List V)
  obtain ⟨z,_,hz⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({v,w} : Finset V)) (t := Finset.univ) (by
      simpa only [Finset.card_univ] using hpair.trans_lt (show 2 < Fintype.card V by omega))
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hz
  let a : ↥({w}ᶜ : Set V) := ⟨v,hvw.ne⟩
  let b : ↥({w}ᶜ : Set V) := ⟨z,hz.2⟩
  have hclosed : ∀ p ∈ ({a} : Set ↥({w}ᶜ : Set V)), ∀ q,
      (G.induce {w}ᶜ).Adj p q → q ∈ ({a} : Set ↥({w}ᶜ : Set V)) := by
    intro p hp q hpq
    have he : p = a := Set.mem_singleton_iff.mp hp
    subst p
    exact (q.prop (hw q.val hpq)).elim
  have hb := mem_of_reachable_closed hclosed (u := a) (Set.mem_singleton a) (h w a b)
  exact hz.1 (congrArg Subtype.val (Set.mem_singleton_iff.mp hb))

lemma exists_end_piece [Fintype V] (hG : G.Connected)
    (hd : ∀ v, 2 ≤ Nat.card (G.neighborSet v)) :
    ∃ S x, Lobe G S x ∧ (G.induce S).Connected ∧ NoCut (G.induce S) ∧
      ∀ v, 2 ≤ Nat.card ((G.induce S).neighborSet v) := by
  classical
  obtain ⟨x⟩ := hG.nonempty
  obtain ⟨y,hxy⟩ : ∃ y, G.Adj x y := by
    apply (G.degree_pos_iff_exists_adj x).mp
    have hx := hd x
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using (show 0 < Nat.card (G.neighborSet x) by omega)
  obtain ⟨S,w,hS,hNC⟩ := exists_minimal_lobe (G := G)
    ⟨Set.univ,x,Set.mem_univ x,⟨y,Set.mem_univ y,hxy.ne.symm⟩,by simp⟩
  exact ⟨S,w,hS,hS.connected hG,hNC,hNC.min_degree (hS.connected hG) (by simpa only [Fintype.card_eq_nat_card] using hS.card_ge_three hd)⟩

#print axioms exists_end_piece
end Erdos713Blocks
