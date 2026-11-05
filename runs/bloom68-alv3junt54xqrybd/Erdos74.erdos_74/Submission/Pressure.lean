import Submission.Clusters
import Submission.Phase

/-!
# Own-cost pressure or localized binary phase repair

The repair invariant used here is the shared, weaker pointwise-neighborhood
invariant: every color change is within `rho (cost G b)` of some original
bad-edge endpoint.  A recursive repair of cost `t` has at most `2*t` such
centers.  Expanding each projected interval by eight levels bounds the number
of forbidden starts for a clean nine-level band by `2*t*(2*rho t+9)`.
The shared padding is strictly larger than this bound plus eight.

All balls are extended-distance balls.  Natural distances are used only for
vertices of such a ball, with their finiteness explicitly proved.
-/

namespace E74

open SimpleGraph
open scoped BigOperators

universe u v
variable {V : Type u}

namespace PressureProof

/-- Endpoint membership for a finite set of unordered pairs. -/
theorem mem_ends (F : Finset (Sym2 V)) (x : V) :
    x ∈ ends F ↔ ∃ e ∈ F, x ∈ e := by
  classical
  simp [ends]

/-- There are at most two endpoints per unordered pair. -/
theorem card_ends_le (F : Finset (Sym2 V)) : (ends F).card ≤ 2 * F.card := by
  classical
  calc
    (ends F).card ≤ ∑ e ∈ F, e.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ F, 2 := Finset.sum_le_sum fun e _ => by
      rw [Sym2.card_toFinset]
      split_ifs <;> omega
    _ = 2 * F.card := by simp [Nat.mul_comm]

/-- A clean run of nine levels, obtained by counting forbidden run starts.
This does not require the levels to be inhabited. -/
theorem exists_clean_nine {ι : Type*} (D : Finset ι) (level : ι → ℕ)
    (r I R : ℕ) (hwidth : I + D.card * (2 * r + 9) + 9 ≤ R) :
    ∃ a : ℕ, I + 1 ≤ a ∧ a + 8 ≤ R ∧
      ∀ z ∈ D, ∀ j : ℕ, a ≤ j → j ≤ a + 8 →
        ¬ (j ≤ level z + r ∧ level z ≤ j + r) := by
  classical
  let bad : Finset ℕ := D.biUnion fun z => Finset.Icc (level z - (r + 8)) (level z + r)
  have hb : bad.card ≤ D.card * (2 * r + 9) := by
    calc
      bad.card ≤ ∑ z ∈ D, (Finset.Icc (level z - (r + 8)) (level z + r)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ D, (2 * r + 9) := by
        apply Finset.sum_le_sum
        intro z hz
        rw [Nat.card_Icc]
        omega
      _ = D.card * (2 * r + 9) := by simp
  have hcard : bad.card < (Finset.Icc (I + 1) (R - 8)).card := by
    rw [Nat.card_Icc]
    omega
  have hex : ∃ a ∈ Finset.Icc (I + 1) (R - 8), a ∉ bad := by
    by_contra h
    have hsub : Finset.Icc (I + 1) (R - 8) ⊆ bad := by
      intro a ha
      by_contra hab
      exact h ⟨a, ha, hab⟩
    have hc := Finset.card_le_card hsub
    omega
  obtain ⟨a, ha, hab⟩ := hex
  have har := Finset.mem_Icc.mp ha
  refine ⟨a, har.1, by omega, ?_⟩
  intro z hz j haj hja hj
  apply hab
  apply Finset.mem_biUnion.mpr
  refine ⟨z, hz, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩ <;> omega

/-- Extended-distance bounded by a natural radius gives an actual short walk. -/
theorem short_walk_of_edist {G : SimpleGraph V} {x y : V} {r : ℕ}
    (h : G.edist x y ≤ (r : ℕ∞)) : ∃ p : G.Walk x y, p.length ≤ r := by
  have hn : G.edist x y ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top r) h
  obtain ⟨p, hp⟩ := G.exists_walk_of_edist_ne_top hn
  exact ⟨p, ENat.coe_le_coe.mp (hp ▸ h)⟩

/-- Graph homomorphisms do not increase extended distance. -/
theorem edist_map_le {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (x y : V) : H.edist (f x) (f y) ≤ G.edist x y := by
  by_cases h : G.edist x y = ⊤
  · simp [h]
  obtain ⟨p, hp⟩ := G.exists_walk_of_edist_ne_top h
  calc
    H.edist (f x) (f y) ≤ ((p.map f).length : ℕ∞) := (p.map f).edist_le
    _ = (p.length : ℕ∞) := by rw [Walk.length_map]
    _ = G.edist x y := hp

/-- Inside an extended-distance ball, the natural radial level is genuine. -/
theorem coe_dist_eq_edist_of_mem_ball (G : SimpleGraph V) (z : V) (R : ℕ)
    (x : ball G z R) : (G.dist z x.val : ℕ∞) = G.edist z x.val := by
  exact ENat.coe_toNat (ne_top_of_le_ne_top (ENat.coe_ne_top R) x.property)

/-- The radial level of a ball vertex is bounded by its radius. -/
theorem dist_le_of_mem_ball (G : SimpleGraph V) (z : V) (R : ℕ)
    (x : ball G z R) : G.dist z x.val ≤ R := by
  exact ENat.toNat_le_of_le_coe x.property

/-- Radial levels change by at most one on an edge. -/
theorem level_lipschitz (G : SimpleGraph V) (z : V) (B : Set V)
    {x y : B} (hxy : (G.induce B).Adj x y) :
    G.dist z x.val ≤ G.dist z y.val + 1 ∧
      G.dist z y.val ≤ G.dist z x.val + 1 := by
  have h₁ := (show G.Adj x.val y.val from hxy).diff_dist_adj (u := z)
  have h₂ := (show G.Adj y.val x.val from hxy.symm).diff_dist_adj (u := z)
  omega

/-- A short intrinsic path in a ball projects into a short radial interval. -/
theorem radial_projection (G : SimpleGraph V) (z : V) (R : ℕ)
    {x y : ball G z R} {r : ℕ}
    (hxy : (G.induce (ball G z R)).edist x y ≤ (r : ℕ∞)) :
    G.dist z x.val ≤ G.dist z y.val + r ∧
      G.dist z y.val ≤ G.dist z x.val + r := by
  have hxy' : G.edist x.val y.val ≤ (r : ℕ∞) :=
    (edist_map_le (Embedding.induce (ball G z R)).toHom x y).trans hxy
  have hyx' : G.edist y.val x.val ≤ (r : ℕ∞) := by
    rw [G.edist_comm]
    exact hxy'
  have hx := coe_dist_eq_edist_of_mem_ball G z R x
  have hy := coe_dist_eq_edist_of_mem_ball G z R y
  constructor
  · apply ENat.coe_le_coe.mp
    rw [ENat.coe_add, hx, hy]
    exact G.edist_triangle.trans (add_le_add (le_refl (G.edist z y.val)) hyx')
  · apply ENat.coe_le_coe.mp
    rw [ENat.coe_add, hx, hy]
    exact G.edist_triangle.trans (add_le_add (le_refl (G.edist z x.val)) hxy')

/-- An edge leaving an induced ball meets its exact outer radial level. -/
theorem frontier_level (G : SimpleGraph V) (z : V) (R : ℕ)
    (x : ball G z R) {y : V} (hxy : G.Adj x.val y) (hy : y ∉ ball G z R) :
    G.dist z x.val = R := by
  have hxle := dist_le_of_mem_ball G z R x
  apply le_antisymm hxle
  by_contra hlt
  have hn : G.dist z x.val + 1 ≤ R := by omega
  apply hy
  change G.edist z y ≤ (R : ℕ∞)
  calc
    G.edist z y ≤ G.edist z x.val + G.edist x.val y := G.edist_triangle
    _ = (G.dist z x.val : ℕ∞) + 1 := by
      rw [← coe_dist_eq_edist_of_mem_ball G z R x, edist_eq_one_iff_adj.mpr hxy]
    _ = ((G.dist z x.val + 1 : ℕ) : ℕ∞) := by rw [ENat.coe_add, ENat.coe_one]
    _ ≤ (R : ℕ∞) := ENat.coe_le_coe.mpr hn

/-- Binary cut costs are invariant under actual graph isomorphisms. -/
theorem cost_iso {W : Type v} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) (b : W → Bool) :
    cost G (fun x => b (f x)) = cost H b := by
  classical
  have hmap : ∀ e : Sym2 V,
      e ∈ defects G (fun x => b (f x)) ↔ Sym2.map f e ∈ defects H b := by
    intro e
    refine Sym2.ind (fun x y => ?_) e
    simp only [Sym2.map_pair_eq, mk_mem_defects, f.map_adj_iff]
  unfold cost
  refine Finset.card_bij (fun e _ => Sym2.map f e) ?_ ?_ ?_
  · intro e he
    exact (hmap e).mp he
  · intro e he e' he' heq
    exact Sym2.map.injective f.injective heq
  · intro e he
    revert he
    refine Sym2.ind (fun x y he => ?_) e
    refine ⟨s(f.symm x, f.symm y), ?_, ?_⟩
    · apply (hmap _).mpr
      simpa using he
    · simp

/-- Actual frustration is invariant under graph isomorphisms. -/
theorem tau_iso {W : Type v} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) : tau G = tau H := by
  apply le_antisymm
  · obtain ⟨b, hb⟩ := tau_attained H
    calc
      tau G ≤ cost G (fun x => b (f x)) := tau_le_cost _ _
      _ = cost H b := cost_iso f b
      _ = tau H := hb
  · obtain ⟨b, hb⟩ := tau_attained G
    calc
      tau H ≤ cost H (fun x => b (f.symm x)) := tau_le_cost _ _
      _ = cost G b := cost_iso f.symm b
      _ = tau G := hb

/-- Intrinsic radius is preserved when an actual witness is relabeled. -/
theorem radius_iso {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) {r : ℕ} (hr : HasRadius G r) : HasRadius H r := by
  obtain ⟨z, hz⟩ := hr
  refine ⟨f z, fun x => ?_⟩
  have h := (edist_map_le f.toHom z (f.symm x)).trans (hz (f.symm x))
  change H.edist (f z) (f (f.symm x)) ≤ (r : ℕ∞) at h
  simpa only [RelIso.apply_symm_apply] using h

/-- Pressure in an induced subgraph is pressure in the original graph.
The witness is flattened by an isomorphism, preserving its own cost and
its original intrinsic metric rather than charging the ambient budget. -/
theorem pressure_induce [Finite V] (G : SimpleGraph V) (B : Set V)
    (hp : Pressure (G.induce B)) : Pressure G := by
  classical
  obtain ⟨T, k, hk, ht, hr⟩ := hp
  let A : Set V := {x | ∃ h : x ∈ B, (⟨x, h⟩ : B) ∈ T}
  let f : (G.induce B).induce T ≃g G.induce A :=
    { toEquiv :=
        { toFun := fun x => ⟨x.val.val, ⟨x.val.property, x.property⟩⟩
          invFun := fun x => ⟨⟨x.val, x.property.choose⟩, x.property.choose_spec⟩
          left_inv := fun x => by apply Subtype.ext; apply Subtype.ext; rfl
          right_inv := fun x => by apply Subtype.ext; rfl }
      map_rel_iff' := by intro x y; rfl }
  exact ⟨A, k, hk, (tau_iso f).symm.trans ht, radius_iso f hr⟩

/-- The coarser shared padding pays all projected endpoint neighborhoods,
including eight levels of expansion for each forbidden run start. -/
theorem padding_width {m t q : ℕ} (ht : t < m) (hq : q ≤ 2 * t) :
    q * (2 * rho t + 9) + 9 ≤ padding m := by
  have hr : rho t ≤ rho (m - 1) := Cluster.rho_mono (by omega)
  have hp : t * rho t ≤ m * rho (m - 1) := Nat.mul_le_mul ht.le hr
  unfold padding
  calc
    q * (2 * rho t + 9) + 9 ≤ (2 * t) * (2 * rho t + 9) + 9 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ hq) _
    _ = 4 * (t * rho t) + 18 * t + 9 := by ring
    _ ≤ 4 * m * rho (m - 1) + 20 * m + 10 := by nlinarith

/-- A proper coloring of a cluster ball, unchanged on its outer radial level.
This is sufficient for gluing even when the ball is an entire component. -/
def BoundaryRepair (G : SimpleGraph V) (b : V → Bool) (C : Cluster V) : Prop :=
  ∃ c : (G.induce (ball G C.center C.outer)).Coloring (Fin 3),
    ∀ x : ball G C.center C.outer, G.dist C.center x.val = C.outer →
      c x = base (b x.val)

/-- An old bad edge in a final ball lies wholly below its padding annulus. -/
theorem old_good_above_inner [Finite V] {G : SimpleGraph V} {b : V → Bool}
    {S : Finset (Cluster V)} (hS : ClusterPartition G (defects G b) S)
    {C : Cluster V} (hC : C ∈ S) {x y : ball G C.center C.outer}
    (hxy : (G.induce (ball G C.center C.outer)).Adj x y)
    (hlev : C.inner < G.dist C.center x.val ∨ C.inner < G.dist C.center y.val) :
    b x.val ≠ b y.val := by
  intro hb
  have he : s(x.val, y.val) ∈ defects G b := (mk_mem_defects _ _ _ _).mpr ⟨hxy, hb⟩
  have heC := hS.endpoint_mem_part hC he (Sym2.mem_mk_left _ _) x.property
  have hx : G.dist C.center x.val ≤ C.inner :=
    ENat.toNat_le_of_le_coe ((hS.valid C hC).endpoints _ heC _ (Sym2.mem_mk_left _ _))
  have hy : G.dist C.center y.val ≤ C.inner :=
    ENat.toNat_le_of_le_coe ((hS.valid C hC).endpoints _ heC _ (Sym2.mem_mk_right _ _))
  omega

/-- The third color is not one of the two old binary colors. -/
theorem base_ne_two (a : Bool) : base a ≠ (2 : Fin 3) := by
  cases a <;> decide

/-- Repair a singleton part by recoloring its chosen old endpoint. -/
theorem singleton_boundary_repair [Finite V] {G : SimpleGraph V} {b : V → Bool}
    {S : Finset (Cluster V)} (hS : ClusterPartition G (defects G b) S)
    {C : Cluster V} (hC : C ∈ S) (hm : C.part.card = 1) : BoundaryRepair G b C := by
  classical
  have hv := hS.valid C hC
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hm
  have hc : C.center ∈ e := by simpa [ends, he] using hv.center_mem
  let f : ball G C.center C.outer → Fin 3 := fun x =>
    if x.val = C.center then 2 else base (b x.val)
  have hf : ∀ ⦃x y : ball G C.center C.outer⦄,
      (G.induce (ball G C.center C.outer)).Adj x y → f x ≠ f y := by
    intro x y hxy
    by_cases hx : x.val = C.center
    · by_cases hy : y.val = C.center
      · exact False.elim (hxy.ne (Subtype.ext (hx.trans hy.symm)))
      · simpa only [f, if_pos hx, if_neg hy] using (base_ne_two (b y.val)).symm
    · by_cases hy : y.val = C.center
      · simpa only [f, if_neg hx, if_pos hy] using base_ne_two (b x.val)
      · simp only [f, if_neg hx, if_neg hy]
        intro hcolor
        have hb := base_injective hcolor
        have hbad : s(x.val, y.val) ∈ defects G b :=
          (mk_mem_defects _ _ _ _).mpr ⟨hxy, hb⟩
        have hpart := hS.endpoint_mem_part hC hbad (Sym2.mem_mk_left _ _) x.property
        have hpair : s(x.val, y.val) = e := by simpa [he] using hpart
        have hce : C.center ∈ s(x.val, y.val) := hpair.symm ▸ hc
        rcases Sym2.mem_iff.mp hce with h | h
        · exact hx h.symm
        · exact hy h.symm
  refine ⟨Coloring.mk f (fun {_ _} h => hf h), ?_⟩
  intro x hlevel
  have hx : x.val ≠ C.center := by
    intro hx
    have hz : G.dist C.center x.val = 0 := by simp [hx]
    have hg := hv.gap
    omega
  change f x = base (b x.val)
  simp only [f, if_neg hx]

/-- A lower-cost localized repair can be patched back to the old binary phase
in the parent ball.  Its new defect endpoints provide all projected centers. -/
theorem boundary_repair_of_repair [Finite V] {G : SimpleGraph V} {b : V → Bool}
    {S : Finset (Cluster V)} (hS : ClusterPartition G (defects G b) S)
    {C : Cluster V} (hC : C ∈ S) (hm : 2 ≤ C.part.card)
    (b' : ball G C.center C.outer → Bool)
    (ht : cost (G.induce (ball G C.center C.outer)) b' < C.part.card)
    (hrepair : Repair (G.induce (ball G C.center C.outer)) b') :
    BoundaryRepair G b C := by
  classical
  let H := G.induce (ball G C.center C.outer)
  let level : ball G C.center C.outer → ℕ := fun x => G.dist C.center x.val
  let D := ends (defects H b')
  let t := cost H b'
  obtain ⟨c', hc'⟩ := hrepair
  have hD : D.card ≤ 2 * t := card_ends_le (defects H b')
  have hw : D.card * (2 * rho t + 9) + 9 ≤ padding C.part.card :=
    padding_width (show t < C.part.card from ht) hD
  have hp := (hS.valid C hC).padded hm
  have hwidth : C.inner + D.card * (2 * rho t + 9) + 9 ≤ C.outer := by omega
  obtain ⟨a, ha, haR, hclean⟩ := exists_clean_nine D level (rho t) C.inner C.outer hwidth
  let s := a + 2
  have hs : 2 ≤ s := by dsimp [s]; omega
  have hl : ∀ ⦃x y : ball G C.center C.outer⦄, H.Adj x y →
      level x ≤ level y + 1 ∧ level y ≤ level x + 1 := by
    intro x y hxy
    exact level_lipschitz G C.center (ball G C.center C.outer) hxy
  have hb : ∀ ⦃x y : ball G C.center C.outer⦄, H.Adj x y →
      (s - 2 ≤ level x ∨ s - 2 ≤ level y) → b x.val ≠ b y.val := by
    intro x y hxy hlev
    apply old_good_above_inner hS hC hxy
    dsimp [s, level] at hlev
    omega
  have hband : ∀ x : ball G C.center C.outer,
      s - 2 ≤ level x → level x ≤ s + 6 → c' x = base (b' x) := by
    intro x hxlo hxhi
    by_contra hx
    obtain ⟨z, hz, hzx⟩ := hc' x hx
    have hproj := radial_projection G C.center C.outer hzx
    apply hclean z hz (level x) (by dsimp [s] at hxlo; omega)
      (by dsimp [s] at hxhi; omega)
    exact ⟨hproj.2, hproj.1⟩
  obtain ⟨c, _hin, hout⟩ := phase_patch H (fun x => b x.val) b' c' level s hs hl hb hband
  refine ⟨c, ?_⟩
  intro x hx
  apply hout
  change s + 3 ≤ G.dist C.center x.val
  dsimp [s]
  omega

/-- A cluster either pays its own assigned cost, inherits lower-cost pressure,
or has a boundary-compatible local repair. -/
theorem cluster_pressure_or_patch [Finite V] {G : SimpleGraph V} {b : V → Bool}
    {S : Finset (Cluster V)} (hS : ClusterPartition G (defects G b) S)
    {C : Cluster V} (hC : C ∈ S)
    (hrec : ∀ b' : ball G C.center C.outer → Bool,
      cost (G.induce (ball G C.center C.outer)) b' < C.part.card →
        Pressure (G.induce (ball G C.center C.outer)) ∨
          Repair (G.induce (ball G C.center C.outer)) b') :
    Pressure G ∨ BoundaryRepair G b C := by
  have hv := hS.valid C hC
  by_cases hm : C.part.card = 1
  · exact Or.inr (singleton_boundary_repair hS hC hm)
  have hm₂ : 2 ≤ C.part.card := by have hp := hv.nonempty.card_pos; omega
  by_cases ht : C.part.card ≤ tau (G.induce (ball G C.center C.outer))
  · exact Or.inl (hS.pressure_of_tau_ge hC hm₂ ht)
  obtain ⟨b', hb'⟩ := tau_attained (G.induce (ball G C.center C.outer))
  have hlt : cost (G.induce (ball G C.center C.outer)) b' < C.part.card := by omega
  rcases hrec b' hlt with hp | hr
  · exact Or.inl (pressure_induce G (ball G C.center C.outer) hp)
  · exact Or.inr (boundary_repair_of_repair hS hC hm₂ b' hlt hr)

/-- Simultaneously glue the separated boundary-compatible cluster repairs.
Every changed vertex remains in one of the original cluster balls, whose
center is an old defect endpoint and whose radius is at most the total budget. -/
theorem global_repair [Finite V] {G : SimpleGraph V} {b : V → Bool}
    {S : Finset (Cluster V)} (hS : ClusterPartition G (defects G b) S)
    (hpatch : ∀ C ∈ S, BoundaryRepair G b C) : Repair G b := by
  classical
  let cp : (C : S) → (G.induce (ball G C.val.center C.val.outer)).Coloring (Fin 3) :=
    fun C => (hpatch C.val C.property).choose
  have hcp : ∀ (C : S) (x : ball G C.val.center C.val.outer),
      G.dist C.val.center x.val = C.val.outer → cp C x = base (b x.val) := by
    intro C
    exact (hpatch C.val C.property).choose_spec
  let inside : V → Prop := fun x => ∃ C : S, x ∈ ball G C.val.center C.val.outer
  let f : V → Fin 3 := fun x =>
    if hx : inside x then cp hx.choose ⟨x, hx.choose_spec⟩ else base (b x)
  have hon : ∀ (C : S) (x : V) (hx : x ∈ ball G C.val.center C.val.outer),
      f x = cp C ⟨x, hx⟩ := by
    intro C x hx
    have hi : inside x := ⟨C, hx⟩
    have howner : hi.choose = C := by
      apply Subtype.ext
      by_contra hne
      exact (Set.disjoint_left.mp
        (hS.outer_disjoint hi.choose.property C.property hne)) hi.choose_spec hx
    simp only [f, dif_pos hi]
    cases howner
    rfl
  have hoff : ∀ x : V, ¬ inside x → f x = base (b x) := by
    intro x hx
    simp only [f, dif_neg hx]
  have hgood : ∀ x : V, ¬ inside x → ∀ y : V, G.Adj x y → b x ≠ b y := by
    intro x hx y hxy hb
    have he : s(x, y) ∈ defects G b := (mk_mem_defects _ _ _ _).mpr ⟨hxy, hb⟩
    obtain ⟨C, hC, heC⟩ := hS.covers _ he
    exact hx ⟨⟨C, hC⟩, (hS.valid C hC).endpoints_outer heC (Sym2.mem_mk_left _ _)⟩
  have hinside : ∀ (C : S) (x : V) (hx : x ∈ ball G C.val.center C.val.outer)
      (y : V), G.Adj x y → f x ≠ f y := by
    intro C x hx y hxy
    by_cases hy : y ∈ ball G C.val.center C.val.outer
    · rw [hon C x hx, hon C y hy]
      exact (cp C).valid (show (G.induce (ball G C.val.center C.val.outer)).Adj
        ⟨x, hx⟩ ⟨y, hy⟩ from hxy)
    · have hyout : ¬ inside y := by
        rintro ⟨D, hyD⟩
        by_cases hCD : C = D
        · subst D
          exact hy hyD
        · have hne : C.val ≠ D.val := fun h => hCD (Subtype.ext h)
          exact (hS.outer_nonadjacent C.property D.property hne hx hyD) hxy
      have hfx : f x = base (b x) :=
        (hon C x hx).trans (hcp C ⟨x, hx⟩ (frontier_level G C.val.center C.val.outer
          ⟨x, hx⟩ hxy hy))
      rw [hfx, hoff y hyout]
      exact fun h => (hgood y hyout x hxy.symm) (base_injective h).symm
  have hf : ∀ ⦃x y : V⦄, G.Adj x y → f x ≠ f y := by
    intro x y hxy
    by_cases hx : inside x
    · obtain ⟨C, hxC⟩ := hx
      exact hinside C x hxC y hxy
    · by_cases hy : inside y
      · obtain ⟨C, hyC⟩ := hy
        exact (hinside C y hyC x hxy.symm).symm
      · rw [hoff x hx, hoff y hy]
        exact fun h => (hgood x hx y hxy) (base_injective h)
  refine ⟨Coloring.mk f (fun {_ _} h => hf h), ?_⟩
  intro x hchange
  change f x ≠ base (b x) at hchange
  have hi : inside x := by
    by_contra hx
    exact hchange (hoff x hx)
  obtain ⟨C, hxC⟩ := hi
  exact ⟨C.val.center, hS.center_mem_ends C.property,
    hxC.trans (ENat.coe_le_coe.mpr (hS.radius_le_total C.property))⟩

/-- Strong induction over cut cost, generalized over all finite vertex types.
The zero-cost case is the empty cluster family; count-one clusters are repaired
without recursion. Every recursive call has cost below its part count. -/
theorem dichotomy_at (K : ℕ) :
    ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (b : V → Bool),
      cost G b = K → Pressure G ∨ Repair G b := by
  induction K using Nat.strong_induction_on with
  | h K ih =>
    intro V hV G b hK
    classical
    by_cases hp : Pressure G
    · exact Or.inl hp
    obtain ⟨S, hS⟩ := defect_clustering G b
    have hpatch : ∀ C ∈ S, BoundaryRepair G b C := by
      intro C hC
      have hm : C.part.card ≤ K := by
        have hc := hS.part_card_le hC
        change C.part.card ≤ cost G b at hc
        omega
      have hrec : ∀ b' : ball G C.center C.outer → Bool,
          cost (G.induce (ball G C.center C.outer)) b' < C.part.card →
            Pressure (G.induce (ball G C.center C.outer)) ∨
              Repair (G.induce (ball G C.center C.outer)) b' := by
        intro b' ht
        have htK : cost (G.induce (ball G C.center C.outer)) b' < K := by omega
        exact ih _ htK _ b' rfl
      exact (cluster_pressure_or_patch hS hC hrec).resolve_left hp
    exact Or.inr (global_repair hS hpatch)

end PressureProof

/-- Every binary cut of a finite graph either exhibits own-cost bounded-radius
pressure or admits a localized proper three-color repair. -/
theorem pressure_or_repair [Finite V] (G : SimpleGraph V) (b : V → Bool) :
    Pressure G ∨ Repair G b :=
  PressureProof.dichotomy_at (cost G b) G b rfl

/-- A finite graph that is not three-colorable has an induced pressure witness
at that witness's own frustration level. -/
theorem pressure_of_not_colorable [Finite V] (G : SimpleGraph V)
    (hG : ¬ G.Colorable 3) : Pressure G := by
  rcases pressure_or_repair G (fun _ => false) with hp | ⟨c, _hc⟩
  · exact hp
  · exact False.elim (hG ⟨c⟩)

end E74
