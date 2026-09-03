import Submission.IndexedCycles

/-! Strong three-cycle contact rings cannot occur in an even rigid graph. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.TriangleContacts
open RigidSwitching CycleSegments
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma intersection_eq_pair (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    {a b x : V} (c : G.Walk a a) (d : G.Walk b b) (hc : c.IsCycle) (hd : d.IsCycle)
    (hdis : c.edges.Disjoint d.edges) (hxc : x ∈ c.support) (hxd : x ∈ d.support) :
    ∃ y, ∀ z, (z ∈ c.support ∧ z ∈ d.support) ↔ z = x ∨ z = y := by
  by_cases hh : ∃ y, y ∈ c.support ∧ y ∈ d.support ∧ y ≠ x
  · obtain ⟨y,hyc,hyd,hyx⟩ := hh
    refine ⟨y,fun z => ⟨?_,?_⟩⟩
    · rintro ⟨hzc,hzd⟩
      by_contra hn
      push_neg at hn
      exact rigid_no_three_common_vertices hrig heven c d hc hd hdis hyx.symm hn.1.symm hn.2.symm
        hxc hyc hzc hxd hyd hzd
    · rintro (rfl | rfl)
      · exact ⟨hxc,hxd⟩
      · exact ⟨hyc,hyd⟩
  · refine ⟨x,fun z => ⟨?_,?_⟩⟩
    · intro hz
      by_cases he : z = x
      · exact Or.inl he
      · exact (hh ⟨z,hz.1,hz.2,he⟩).elim
    · rintro (rfl | rfl) <;> exact ⟨hxc,hxd⟩

lemma common_vertex_impossible (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    {a b c₀ u v x y : V} (c : G.Walk a a) (d : G.Walk b b) (t : G.Walk c₀ c₀)
    (hc : c.IsCycle) (hd : d.IsCycle) (ht : t.IsCycle)
    (hcd : c.edges.Disjoint d.edges) (hct : c.edges.Disjoint t.edges) (hdt : d.edges.Disjoint t.edges)
    (huc : u ∈ c.support) (hud : u ∈ d.support) (hut : u ∈ t.support)
    (hvc : v ∈ c.support) (hvd : v ∈ d.support) (hvt : v ∉ t.support)
    (hxc : x ∈ c.support) (hxt : x ∈ t.support) (hxd : x ∉ d.support)
    (hyd : y ∈ d.support) (hyt : y ∈ t.support) (hyc : y ∉ c.support) : False := by
  have huv : u ≠ v := fun he => hvt (he ▸ hut)
  have hinter (z) (hzc : z ∈ c.support) (hzd : z ∈ d.support) : z = u ∨ z = v := by
    by_contra hn
    push_neg at hn
    exact rigid_no_three_common_vertices hrig heven c d hc hd hcd huv hn.1.symm hn.2.symm
      huc hvc hzc hud hvd hzd
  have ec (e) : e ∈ (c.rotate huc).edges ↔ e ∈ c.edges := (c.rotate_edges huc).mem_iff
  have ed (e) : e ∈ (d.rotate hud).edges ↔ e ∈ d.edges := (d.rotate_edges hud).mem_iff
  obtain ⟨r,s,hr,hs,hrs,hcover,hxr,hyr⟩ := two_cycle_switch_through
    (c.rotate huc) (d.rotate hud) (hc.rotate huc) (hd.rotate hud) huv
    ((c.mem_support_rotate_iff huc).mpr hvc) ((d.mem_support_rotate_iff hud).mpr hvd)
    (disjoint_mono hcd (fun e => (ec e).mp) (fun e => (ed e).mp))
    (fun z hz hz' => hinter z ((c.mem_support_rotate_iff huc).mp hz) ((d.mem_support_rotate_iff hud).mp hz'))
    ((c.mem_support_rotate_iff huc).mpr hxc) ((d.mem_support_rotate_iff hud).mpr hyd)
  have hrt : r.edges.Disjoint t.edges := by
    apply List.disjoint_left.mpr
    intro e her het
    rcases (hcover e).mp (Or.inl her) with he | he
    · exact List.disjoint_left.mp hct ((ec e).mp he) het
    · exact List.disjoint_left.mp hdt ((ed e).mp he) het
  exact rigid_no_three_common_vertices hrig heven r t hr ht hrt
    (fun h : u = x => hxd (h ▸ hud)) (fun h : u = y => hyc (h ▸ huc))
    (fun h : x = y => hxd (h.symm ▸ hyd)) r.start_mem_support hxr hyr hut hxt hyt

abbrev first : Fin 3 → Fin 3 := ![0,0,1]
abbrev second : Fin 3 → Fin 3 := ![1,2,2]
abbrev missing : Fin 3 → Fin 3 := ![2,1,0]

lemma point_incidence (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k))
    (p : Fin 3 → Fin 2 → V)
    (hp : ∀ g x, (x ∈ (C (first g)).support ∧ x ∈ (C (second g)).support) ↔ x = p g 0 ∨ x = p g 1)
    (hnt : ∀ x, ¬ (x ∈ (C 0).support ∧ x ∈ (C 1).support ∧ x ∈ (C 2).support)) :
    ∀ g i k, p g i ∈ (C k).support ↔ k ≠ missing g := by
  intro g i k
  have hb := (hp g (p g i)).mpr (by fin_cases i <;> simp)
  have hn : p g i ∉ (C (missing g)).support := by
    intro hm
    apply hnt (p g i)
    fin_cases g
    · exact ⟨hb.1,hb.2,hm⟩
    · exact ⟨hb.1,hm,hb.2⟩
    · exact ⟨hm,hb.1,hb.2⟩
  constructor
  · intro hk he
    exact hn (he ▸ hk)
  · intro hk
    have hh : ∀ g k, k ≠ missing g → k = first g ∨ k = second g := by decide
    rcases hh g k hk with rfl | rfl
    · exact hb.1
    · exact hb.2

lemma point_meet (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k))
    (p : Fin 3 → Fin 2 → V)
    (hp : ∀ g x, (x ∈ (C (first g)).support ∧ x ∈ (C (second g)).support) ↔ x = p g 0 ∨ x = p g 1) :
    ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ g i, p g i = x := by
  intro k l hkl x hx hy
  have hcase : ∀ k l, k ≠ l → ∃ g, (k = first g ∧ l = second g) ∨ (l = first g ∧ k = second g) := by decide
  obtain ⟨g,hg⟩ := hcase k l hkl
  have hi : x = p g 0 ∨ x = p g 1 := by
    apply (hp g x).mp
    rcases hg with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨hx,hy⟩
    · exact ⟨hy,hx⟩
  exact hi.elim (fun h => ⟨g,0,h.symm⟩) (fun h => ⟨g,1,h.symm⟩)

lemma point_ne_of_group_ne (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k))
    (p : Fin 3 → Fin 2 → V)
    (hi : ∀ g i k, p g i ∈ (C k).support ↔ k ≠ missing g)
    {g h : Fin 3} {i j : Fin 2} (hgh : g ≠ h) : p g i ≠ p h j := by
  intro he
  have hinj : Function.Injective missing := by decide
  have hg := (hi g i (missing h)).mpr (fun h => hgh (hinj h).symm)
  rw [he] at hg
  exact (hi h j (missing h)).mp hg rfl

#print axioms common_vertex_impossible
end Erdos184Work.TriangleContacts
