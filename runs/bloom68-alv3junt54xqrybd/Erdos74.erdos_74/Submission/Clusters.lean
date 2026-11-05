import Submission.Basic

/-!
# Padded defect-ball clustering (extended graph metric)

Public interface (in namespace `E74`):

* `Cluster V` has fields `part : Finset (Sym2 V)`, `center : V`, and
  `inner outer : ℕ`.
* `Cluster.Valid G C` asserts nonempty assigned edges, an assigned endpoint as
  center, all assigned endpoints in `ball G C.center C.inner`,
  `C.outer ≤ rho C.part.card`, padding for counts at least two, and
  `C.inner + 1 ≤ C.outer`. A count-one cluster has radii exactly `1, 4`.
* `ClusterPartition G F S` asserts validity, disjoint assigned parts with union
  `F`, and extended center distances greater than `C.outer + D.outer + 1`.
* `padded_clustering (G : SimpleGraph V) (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, e ∈ G.edgeSet) :
    ∃ S : Finset (Cluster V), ClusterPartition G F S`.

The partition interface also provides `union_parts` (under `DecidableEq V`),
`sum_card`, `count_le`, `empty_iff`, `sum_outer_le`, `outer_disjoint`,
`outer_nonadjacent`, `endpoint_mem_part`, `endpoint_inner`, and
`annulus_no_endpoint`. The endpoint exclusion lemma has signature

```
ClusterPartition.endpoint_mem_part (hS : ClusterPartition G F S)
    (hC : C ∈ S) (he : e ∈ F) (hxe : x ∈ e)
    (hx : x ∈ ball G C.center C.outer) : e ∈ C.part
```

`defect_clustering G b` specializes the construction to `defects G b`.
`ClusterPartition.cost_induce_ball_eq hS hC` gives the exact local old-cut cost
`C.part.card`, and `pressure_of_tau_ge hS hC hm ht` supplies `Pressure G` if
this local count is at least two and the ball's frustration pays the count.
`ball_hasRadius G z r` proves `HasRadius (G.induce (ball G z r)) r`.
All metrics below are `G.edist`; there is no unguarded natural-number graph distance.

Construction: initialize singleton edges, then minimize the number of valid
clusters. A contacting pair can be replaced by a cluster with first center,
inner radius `R₁ + 2 * R₂ + 1`, and outer radius `inner + padding (a + b)`.
Both old outer balls lie in the new inner ball. The coarse shared recurrence
pays this merge. Minimality therefore gives disjoint, nonadjacent outer balls.
-/

namespace E74

open SimpleGraph
open scoped BigOperators

universe u
variable {V : Type u}

/-- A finite assigned edge set together with a named pair of ball radii. -/
structure Cluster (V : Type u) where
  part : Finset (Sym2 V)
  center : V
  inner : ℕ
  outer : ℕ

namespace Cluster

/-- The invariants preserved by singleton initialization and every merge. -/
structure Valid (G : SimpleGraph V) (C : Cluster V) : Prop where
  nonempty : C.part.Nonempty
  center_mem : C.center ∈ ends C.part
  endpoints : ∀ e ∈ C.part, ∀ x ∈ e, x ∈ ball G C.center C.inner
  radius_le : C.outer ≤ rho C.part.card
  padded : 2 ≤ C.part.card → C.inner + padding C.part.card ≤ C.outer
  gap : C.inner + 1 ≤ C.outer
  singleton : C.part.card = 1 → C.inner = 1 ∧ C.outer = 4

/-- The coarse radius budget is monotone. -/
theorem rho_mono : Monotone rho := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [rho]
  nlinarith

/-- The positive-step form of the shared recurrence. -/
theorem rho_of_pos {m : ℕ} (hm : 0 < m) :
    rho m = (100 * m + 100) * (rho (m - 1) + 1) := by
  cases m with
  | zero => omega
  | succ n => simp [rho]

/-- The shared recurrence pays the largest possible merge at count `m`. -/
theorem merge_budget {m : ℕ} (hm : 2 ≤ m) :
    3 * rho (m - 1) + 1 + padding m ≤ rho m := by
  rw [rho_of_pos (by omega : 0 < m), padding]
  have hprod : 0 ≤ m * rho (m - 1) := Nat.zero_le _
  nlinarith

/-- A chosen endpoint of an unordered edge, with the initial radii `1,4`. -/
noncomputable def singleton (e : Sym2 V) : Cluster V :=
  ⟨{e}, e.out.1, 1, 4⟩

@[simp] theorem singleton_part (e : Sym2 V) : (singleton e).part = {e} := rfl

/-- Distinct edges give distinct singleton clusters. -/
theorem singleton_injective : Function.Injective (singleton (V := V)) := by
  intro e f h
  have hp := congrArg Cluster.part h
  simpa using hp

/-- Initial clusters are valid for actual edges, including in disconnected graphs. -/
theorem singleton_valid (G : SimpleGraph V) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    Valid G (singleton e) := by
  classical
  have hout : s(e.out.1, e.out.2) = e := e.out_eq
  have hadj : G.Adj e.out.1 e.out.2 :=
    (G.mem_edgeSet).mp (hout.symm ▸ he)
  refine ⟨by simp [singleton], ?_, ?_, ?_, ?_, by norm_num [singleton], ?_⟩
  · simp [singleton, ends, Sym2.out_fst_mem]
  · intro f hf x hx
    have hfe : f = e := by simpa [singleton] using hf
    subst f
    rw [← hout, Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · simp [singleton, ball]
    · change G.edist e.out.1 e.out.2 ≤ (1 : ℕ∞)
      exact le_of_eq (edist_eq_one_iff_adj.mpr hadj)
  · norm_num [singleton, rho]
  · simp [singleton]
  · intro _
    exact ⟨rfl, rfl⟩

/-- The explicit merge rule, retaining the first center. -/
noncomputable def merge (C D : Cluster V) : Cluster V := by
  classical
  exact
    { part := C.part ∪ D.part
      center := C.center
      inner := C.outer + 2 * D.outer + 1
      outer := C.outer + 2 * D.outer + 1 + padding (C.part ∪ D.part).card }

/-- The first old outer ball lies in the new inner ball. -/
theorem outer_subset_merge_left (G : SimpleGraph V) (C D : Cluster V) :
    ball G C.center C.outer ⊆ ball G (merge C D).center (merge C D).inner := by
  intro x hx
  exact hx.trans (ENat.coe_le_coe.mpr (by dsimp [merge]; omega))

/-- Contact of the centers puts the second old outer ball in the new inner ball. -/
theorem outer_subset_merge_right (G : SimpleGraph V) (C D : Cluster V)
    (hcontact : G.edist C.center D.center ≤ ((C.outer + D.outer + 1 : ℕ) : ℕ∞)) :
    ball G D.center D.outer ⊆ ball G (merge C D).center (merge C D).inner := by
  intro x hx
  change G.edist C.center x ≤ ((C.outer + 2 * D.outer + 1 : ℕ) : ℕ∞)
  calc
    G.edist C.center x ≤ G.edist C.center D.center + G.edist D.center x :=
      G.edist_triangle
    _ ≤ ((C.outer + D.outer + 1 : ℕ) : ℕ∞) + (D.outer : ℕ∞) :=
      add_le_add hcontact hx
    _ = ((C.outer + 2 * D.outer + 1 : ℕ) : ℕ∞) := by
      rw [← ENat.coe_add]
      congr 1
      omega

/-- Two disjoint nonempty parts strictly increase their assigned counts. -/
theorem merge_card (C D : Cluster V) (hd : Disjoint C.part D.part) :
    (merge C D).part.card = C.part.card + D.part.card := by
  classical
  exact Finset.card_union_of_disjoint hd

/-- Every contacting pair of valid clusters with disjoint parts has a valid merge. -/
theorem merge_valid (G : SimpleGraph V) (C D : Cluster V)
    (hC : Valid G C) (hD : Valid G D) (hd : Disjoint C.part D.part)
    (hcontact : G.edist C.center D.center ≤ ((C.outer + D.outer + 1 : ℕ) : ℕ∞)) :
    Valid G (merge C D) := by
  classical
  have hcard := merge_card C D hd
  have ha : 0 < C.part.card := hC.nonempty.card_pos
  have hb : 0 < D.part.card := hD.nonempty.card_pos
  have hm : 2 ≤ (merge C D).part.card := by omega
  have hCa : C.part.card ≤ (merge C D).part.card - 1 := by omega
  have hDb : D.part.card ≤ (merge C D).part.card - 1 := by omega
  have hR₁ := hC.radius_le.trans (rho_mono hCa)
  have hR₂ := hD.radius_le.trans (rho_mono hDb)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hC.nonempty.mono Finset.subset_union_left
  · obtain ⟨e, he, hx⟩ := Finset.mem_biUnion.mp hC.center_mem
    exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_union_left _ he, hx⟩
  · intro e he x hx
    rcases Finset.mem_union.mp he with he | he
    · apply outer_subset_merge_left G C D
      exact (hC.endpoints e he x hx).trans (ENat.coe_le_coe.mpr (by have := hC.gap; omega))
    · apply outer_subset_merge_right G C D hcontact
      exact (hD.endpoints e he x hx).trans (ENat.coe_le_coe.mpr (by have := hD.gap; omega))
  · calc
      (merge C D).outer ≤
          3 * rho ((merge C D).part.card - 1) + 1 + padding (merge C D).part.card := by
        dsimp only [merge] at *
        omega
      _ ≤ rho (merge C D).part.card := merge_budget hm
  · intro _
    exact le_rfl
  · dsimp only [merge]
    unfold padding
    omega
  · intro h
    omega

end Cluster

/-- A partition by valid clusters before imposing separation of the outer balls. -/
structure ClusterFamily (G : SimpleGraph V) (F : Finset (Sym2 V))
    (S : Finset (Cluster V)) : Prop where
  valid : ∀ C ∈ S, Cluster.Valid G C
  part_subset : ∀ C ∈ S, C.part ⊆ F
  parts_disjoint : ∀ C ∈ S, ∀ D ∈ S, C ≠ D → Disjoint C.part D.part
  covers : ∀ e ∈ F, ∃ C ∈ S, e ∈ C.part

/-- A terminal finite partition into separated padded extended-metric balls. -/
structure ClusterPartition (G : SimpleGraph V) (F : Finset (Sym2 V))
    (S : Finset (Cluster V)) : Prop extends ClusterFamily G F S where
  separated : ∀ C ∈ S, ∀ D ∈ S, C ≠ D →
    ¬ G.edist C.center D.center ≤ ((C.outer + D.outer + 1 : ℕ) : ℕ∞)

namespace ClusterFamily

/-- The initial family consists of one cluster for each assigned edge. -/
noncomputable def initial (F : Finset (Sym2 V)) : Finset (Cluster V) := by
  classical
  exact F.image Cluster.singleton

/-- The singleton initialization is a finite valid edge partition. -/
theorem initial_valid (G : SimpleGraph V) (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, e ∈ G.edgeSet) : ClusterFamily G F (initial F) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hC
    exact Cluster.singleton_valid G (hF e he)
  · intro C hC
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hC
    simpa using (Finset.singleton_subset_iff.mpr he)
  · intro C hC D hD hne
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hD
    have hef : e ≠ f := fun h => hne (congrArg Cluster.singleton h)
    simpa only [Cluster.singleton_part, Finset.disjoint_singleton_left,
      Finset.mem_singleton] using hef
  · intro e he
    exact ⟨Cluster.singleton e, Finset.mem_image_of_mem _ he, by simp⟩

/-- Replace two clusters by their explicit padded merge. -/
noncomputable def replace (S : Finset (Cluster V)) (C D : Cluster V) :
    Finset (Cluster V) := by
  classical
  exact insert (Cluster.merge C D) ((S.erase C).erase D)

/-- Membership in the replacement family. -/
theorem mem_replace (S : Finset (Cluster V)) (C D X : Cluster V) :
    X ∈ replace S C D ↔
      X = Cluster.merge C D ∨ (X ∈ S ∧ X ≠ C ∧ X ≠ D) := by
  classical
  simp only [replace, Finset.mem_insert, Finset.mem_erase]
  tauto

/-- Replacement preserves the edge partition and all individual cluster invariants. -/
theorem replace_valid {G : SimpleGraph V} {F : Finset (Sym2 V)}
    {S : Finset (Cluster V)} (hS : ClusterFamily G F S)
    {C D : Cluster V} (hC : C ∈ S) (hD : D ∈ S) (hne : C ≠ D)
    (hcontact : G.edist C.center D.center ≤ ((C.outer + D.outer + 1 : ℕ) : ℕ∞)) :
    ClusterFamily G F (replace S C D) := by
  classical
  have hM := Cluster.merge_valid G C D (hS.valid C hC) (hS.valid D hD)
    (hS.parts_disjoint C hC D hD hne) hcontact
  have hdisj : ∀ X ∈ S, X ≠ C → X ≠ D →
      Disjoint (Cluster.merge C D).part X.part := by
    intro X hX hXC hXD
    change Disjoint (C.part ∪ D.part) X.part
    exact Finset.disjoint_union_left.mpr
      ⟨hS.parts_disjoint C hC X hX hXC.symm,
       hS.parts_disjoint D hD X hX hXD.symm⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X hX
    rcases (mem_replace S C D X).mp hX with rfl | ⟨hX, hXC, hXD⟩
    · exact hM
    · exact hS.valid X hX
  · intro X hX
    rcases (mem_replace S C D X).mp hX with rfl | ⟨hX, hXC, hXD⟩
    · exact Finset.union_subset (hS.part_subset C hC) (hS.part_subset D hD)
    · exact hS.part_subset X hX
  · intro X hX Y hY hXY
    rcases (mem_replace S C D X).mp hX with rfl | ⟨hX, hXC, hXD⟩
    · rcases (mem_replace S C D Y).mp hY with rfl | ⟨hY, hYC, hYD⟩
      · exact False.elim (hXY rfl)
      · exact hdisj Y hY hYC hYD
    · rcases (mem_replace S C D Y).mp hY with rfl | ⟨hY, hYC, hYD⟩
      · exact (hdisj X hX hXC hXD).symm
      · exact hS.parts_disjoint X hX Y hY hXY
  · intro e he
    obtain ⟨X, hX, heX⟩ := hS.covers e he
    by_cases hXC : X = C
    · subst X
      exact ⟨Cluster.merge C D, (mem_replace S C D _).mpr (Or.inl rfl),
        Finset.mem_union_left _ heX⟩
    · by_cases hXD : X = D
      · subst X
        exact ⟨Cluster.merge C D, (mem_replace S C D _).mpr (Or.inl rfl),
          Finset.mem_union_right _ heX⟩
      · exact ⟨X, (mem_replace S C D X).mpr (Or.inr ⟨hX, hXC, hXD⟩), heX⟩

/-- Every replacement of two distinct present clusters reduces the family size. -/
theorem replace_card_lt {S : Finset (Cluster V)} {C D : Cluster V}
    (hC : C ∈ S) (hD : D ∈ S) (hne : C ≠ D) :
    (replace S C D).card < S.card := by
  classical
  have hD' : D ∈ S.erase C := Finset.mem_erase.mpr ⟨hne.symm, hD⟩
  have h₁ := Finset.card_erase_of_mem hC
  have h₂ := Finset.card_erase_of_mem hD'
  have hp := Finset.card_pos.mpr ⟨D, hD'⟩
  have hi := Finset.card_insert_le (Cluster.merge C D) ((S.erase C).erase D)
  change (insert (Cluster.merge C D) ((S.erase C).erase D)).card < S.card
  omega

end ClusterFamily

/-- Finite padded clustering of any finite actual edge set. The vertex type need
not itself be finite: finite assignment and cluster-count minimization suffice. -/
theorem padded_clustering (G : SimpleGraph V) (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, e ∈ G.edgeSet) :
    ∃ S : Finset (Cluster V), ClusterPartition G F S := by
  classical
  obtain ⟨S, hS, hmin⟩ := exists_minimalFor_of_wellFoundedLT
    (ClusterFamily G F) Finset.card
    ⟨ClusterFamily.initial F, ClusterFamily.initial_valid G F hF⟩
  refine ⟨S, { toClusterFamily := hS, separated := ?_ }⟩
  intro C hC D hD hne hcontact
  have hv := hS.replace_valid hC hD hne hcontact
  have hlt := ClusterFamily.replace_card_lt hC hD hne
  have hge := hmin hv hlt.le
  omega

namespace Cluster

/-- A valid cluster's inner radius is at most its outer radius. -/
theorem Valid.inner_le_outer {G : SimpleGraph V} {C : Cluster V} (hC : Valid G C) :
    C.inner ≤ C.outer := by
  have := hC.gap
  omega

/-- Assigned endpoints also lie in the outer ball. -/
theorem Valid.endpoints_outer {G : SimpleGraph V} {C : Cluster V} (hC : Valid G C)
    {e : Sym2 V} (he : e ∈ C.part) {x : V} (hx : x ∈ e) :
    x ∈ ball G C.center C.outer :=
  (hC.endpoints e he x hx).trans (ENat.coe_le_coe.mpr hC.inner_le_outer)

/-- All assigned endpoint vertices are in the inner ball. -/
theorem Valid.ends_inner {G : SimpleGraph V} {C : Cluster V} (hC : Valid G C)
    {x : V} (hx : x ∈ ends C.part) : x ∈ ball G C.center C.inner := by
  classical
  obtain ⟨e, he, hxe⟩ := Finset.mem_biUnion.mp hx
  exact hC.endpoints e he x (Sym2.mem_toFinset.mp hxe)

/-- Two vertices in the outer balls at extended distance at most one force
center contact. This covers both ball intersection and an edge between balls. -/
theorem contact_of_ball_mem (G : SimpleGraph V) {C D : Cluster V} {x y : V}
    (hx : x ∈ ball G C.center C.outer) (hy : y ∈ ball G D.center D.outer)
    (hxy : G.edist x y ≤ 1) :
    G.edist C.center D.center ≤ ((C.outer + D.outer + 1 : ℕ) : ℕ∞) := by
  have hy' : G.edist y D.center ≤ (D.outer : ℕ∞) := by
    rw [G.edist_comm]
    exact hy
  calc
    G.edist C.center D.center ≤ G.edist C.center x + G.edist x D.center :=
      G.edist_triangle
    _ ≤ G.edist C.center x + (G.edist x y + G.edist y D.center) :=
      add_le_add (le_refl _) G.edist_triangle
    _ ≤ (C.outer : ℕ∞) + (1 + (D.outer : ℕ∞)) :=
      add_le_add hx (add_le_add hxy hy')
    _ = ((C.outer + D.outer + 1 : ℕ) : ℕ∞) := by
      simp [add_assoc, add_comm]

/-- Superadditivity of the shared coarse budget, including zero counts. -/
theorem rho_add (a b : ℕ) : rho a + rho b ≤ rho (a + b) := by
  by_cases ha : a = 0
  · simp [ha, rho]
  by_cases hb : b = 0
  · simp [hb, rho]
  have hm : 2 ≤ a + b := by omega
  have h₁ := rho_mono (show a ≤ a + b - 1 by omega)
  have h₂ := rho_mono (show b ≤ a + b - 1 by omega)
  have h₃ := merge_budget hm
  omega

/-- The sum of individual radius budgets is paid by the total assigned count. -/
theorem rho_sum_le {ι : Type*} (s : Finset ι) (m : ι → ℕ) :
    (∑ i ∈ s, rho (m i)) ≤ rho (∑ i ∈ s, m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rho]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (add_le_add (le_refl _) ih).trans (rho_add _ _)

end Cluster

namespace ClusterPartition

variable {G : SimpleGraph V} {F : Finset (Sym2 V)} {S : Finset (Cluster V)}

/-- The assigned parts have union exactly `F`. -/
theorem union_parts [DecidableEq V] (hS : ClusterPartition G F S) :
    S.biUnion Cluster.part = F := by
  ext e
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨C, hC, he⟩
    exact hS.part_subset C hC he
  · exact hS.covers e

/-- The assigned counts add up to the original edge count. -/
theorem sum_card (hS : ClusterPartition G F S) :
    (∑ C ∈ S, C.part.card) = F.card := by
  classical
  rw [← hS.union_parts]
  exact (Finset.card_biUnion (fun C hC D hD hne =>
    hS.parts_disjoint C hC D hD hne)).symm

/-- There are at most as many clusters as assigned edges. -/
theorem count_le (hS : ClusterPartition G F S) : S.card ≤ F.card := by
  calc
    S.card = ∑ C ∈ S, 1 := by simp
    _ ≤ ∑ C ∈ S, C.part.card :=
      Finset.sum_le_sum (fun C hC => (hS.valid C hC).nonempty.card_pos)
    _ = F.card := hS.sum_card

/-- Empty edge input has exactly the empty cluster family, and conversely. -/
theorem empty_iff (hS : ClusterPartition G F S) : S = ∅ ↔ F = ∅ := by
  classical
  constructor
  · intro h
    simpa [h] using hS.union_parts.symm
  · intro h
    apply Finset.card_eq_zero.mp
    have hc := hS.count_le
    have hz : F.card = 0 := by simp [h]
    omega

/-- Each local assigned count is bounded by the original total count. -/
theorem part_card_le (hS : ClusterPartition G F S) {C : Cluster V} (hC : C ∈ S) :
    C.part.card ≤ F.card := Finset.card_le_card (hS.part_subset C hC)

/-- Every named center is an endpoint of an original assigned edge. -/
theorem center_mem_ends (hS : ClusterPartition G F S) {C : Cluster V} (hC : C ∈ S) :
    C.center ∈ ends F := by
  classical
  obtain ⟨e, he, hce⟩ := Finset.mem_biUnion.mp (hS.valid C hC).center_mem
  exact Finset.mem_biUnion.mpr ⟨e, hS.part_subset C hC he, hce⟩

/-- Each outer radius is also bounded by the total edge budget. -/
theorem radius_le_total (hS : ClusterPartition G F S) {C : Cluster V} (hC : C ∈ S) :
    C.outer ≤ rho F.card :=
  (hS.valid C hC).radius_le.trans (Cluster.rho_mono (hS.part_card_le hC))

/-- In fact the sum of all final outer radii is paid by `rho F.card`. -/
theorem sum_outer_le (hS : ClusterPartition G F S) :
    (∑ C ∈ S, C.outer) ≤ rho F.card := by
  calc
    (∑ C ∈ S, C.outer) ≤ ∑ C ∈ S, rho C.part.card :=
      Finset.sum_le_sum (fun C hC => (hS.valid C hC).radius_le)
    _ ≤ rho (∑ C ∈ S, C.part.card) := Cluster.rho_sum_le S (fun C => C.part.card)
    _ = rho F.card := congrArg rho hS.sum_card

/-- Distinct final outer balls are disjoint. -/
theorem outer_disjoint (hS : ClusterPartition G F S) {C D : Cluster V}
    (hC : C ∈ S) (hD : D ∈ S) (hne : C ≠ D) :
    Disjoint (ball G C.center C.outer) (ball G D.center D.outer) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hS.separated C hC D hD hne
    (Cluster.contact_of_ball_mem G hx hy (by simp))

/-- No edge of the ambient graph joins two distinct final outer balls. -/
theorem outer_nonadjacent (hS : ClusterPartition G F S) {C D : Cluster V}
    (hC : C ∈ S) (hD : D ∈ S) (hne : C ≠ D) {x y : V}
    (hx : x ∈ ball G C.center C.outer) (hy : y ∈ ball G D.center D.outer) :
    ¬ G.Adj x y := by
  intro hxy
  exact hS.separated C hC D hD hne
    (Cluster.contact_of_ball_mem G hx hy (le_of_eq (edist_eq_one_iff_adj.mpr hxy)))

/-- An original assigned edge with even one endpoint in an outer ball belongs
 to that ball's own part; there are no other old defect endpoints in it. -/
theorem endpoint_mem_part (hS : ClusterPartition G F S) {C : Cluster V}
    (hC : C ∈ S) {e : Sym2 V} (he : e ∈ F) {x : V} (hxe : x ∈ e)
    (hx : x ∈ ball G C.center C.outer) : e ∈ C.part := by
  classical
  obtain ⟨D, hD, heD⟩ := hS.covers e he
  by_cases hCD : C = D
  · simpa [hCD] using heD
  · exact False.elim ((Set.disjoint_left.mp (hS.outer_disjoint hC hD hCD)) hx
      ((hS.valid D hD).endpoints_outer heD hxe))

/-- Inside a final outer ball all original defect endpoints are already in the
 inner ball, so the entire padding annulus is free of such endpoints. -/
theorem endpoint_inner (hS : ClusterPartition G F S) {C : Cluster V} (hC : C ∈ S)
    {x : V} (hxe : x ∈ ends F) (hx : x ∈ ball G C.center C.outer) :
    x ∈ ball G C.center C.inner := by
  classical
  obtain ⟨e, he, hxe⟩ := Finset.mem_biUnion.mp hxe
  have hx' := Sym2.mem_toFinset.mp hxe
  exact (hS.valid C hC).endpoints e (hS.endpoint_mem_part hC he hx' hx) x hx'

/-- The padding annulus has no original assigned endpoint. -/
theorem annulus_no_endpoint (hS : ClusterPartition G F S) {C : Cluster V}
    (hC : C ∈ S) {x : V} (hx : x ∈ ball G C.center C.outer)
    (hinner : x ∉ ball G C.center C.inner) : x ∉ ends F := by
  intro he
  exact hinner (hS.endpoint_inner hC he hx)

/-- An original edge is assigned to a cluster exactly when both endpoints
 lie in that cluster's outer ball. -/
theorem mem_part_iff (hS : ClusterPartition G F S) {C : Cluster V} (hC : C ∈ S)
    {e : Sym2 V} (he : e ∈ F) :
    e ∈ C.part ↔ ∀ x ∈ e, x ∈ ball G C.center C.outer := by
  constructor
  · intro heC x hx
    exact (hS.valid C hC).endpoints_outer heC hx
  · intro hall
    exact hS.endpoint_mem_part hC he (Sym2.out_fst_mem e) (hall _ (Sym2.out_fst_mem e))

/-- No original assigned edge crosses the boundary of a final outer ball. -/
theorem crossing_not_mem (hS : ClusterPartition G F S) {C : Cluster V} (hC : C ∈ S)
    {x y : V} (hx : x ∈ ball G C.center C.outer)
    (hy : y ∉ ball G C.center C.outer) : s(x,y) ∉ F := by
  intro he
  have heC := hS.endpoint_mem_part hC he (Sym2.mem_mk_left x y) hx
  exact hy ((hS.valid C hC).endpoints_outer heC (Sym2.mem_mk_right x y))

end ClusterPartition

/-- A bounded-length walk from a center stays in its extended-metric ball. -/
theorem walk_support_subset_ball (G : SimpleGraph V) {z x : V} {r : ℕ}
    (p : G.Walk z x) (hlen : (p.length : ℕ∞) ≤ (r : ℕ∞)) :
    ∀ y ∈ p.support, y ∈ ball G z r := by
  classical
  intro y hy
  calc
    G.edist z y ≤ ((p.takeUntil y hy).length : ℕ∞) := (p.takeUntil y hy).edist_le
    _ ≤ (p.length : ℕ∞) := ENat.coe_le_coe.mpr (p.length_takeUntil_le hy)
    _ ≤ (r : ℕ∞) := hlen

/-- Every induced extended-metric ball has intrinsic radius at most its named
 radius. A shortest ambient walk stays in the ball and lifts without changing length. -/
theorem ball_hasRadius (G : SimpleGraph V) (z : V) (r : ℕ) :
    HasRadius (G.induce (ball G z r)) r := by
  classical
  have hz : z ∈ ball G z r := by simp [ball]
  refine ⟨⟨z, hz⟩, ?_⟩
  intro x
  have hx : G.edist z x.val ≤ (r : ℕ∞) := x.property
  obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top
    (ne_top_of_le_ne_top (ENat.coe_ne_top r) hx)
  have hlen : (p.length : ℕ∞) ≤ (r : ℕ∞) := hp.trans_le hx
  have hs := walk_support_subset_ball G p hlen
  have hplength : (p.induce (ball G z r) hs).length = p.length := by
    simpa only [Walk.length_map] using congrArg Walk.length (p.map_induce hs)
  exact (p.induce (ball G z r) hs).edist_le.trans (by simpa only [hplength] using hlen)

namespace ClusterPartition
variable {G : SimpleGraph V} {S : Finset (Cluster V)}

/-- The old binary cut has exactly the assigned local bad-edge count on the
 induced outer ball, not just an upper bound by the ambient cut budget. -/
theorem cost_induce_ball_eq [Finite V] {b : V → Bool}
    (hS : ClusterPartition G (defects G b) S) {C : Cluster V} (hC : C ∈ S) :
    cost (G.induce (ball G C.center C.outer)) (fun x => b x.val) = C.part.card := by
  classical
  let B := ball G C.center C.outer
  have hmap : ∀ e : Sym2 B,
      e ∈ defects (G.induce B) (fun x => b x.val) ↔
        Sym2.map Subtype.val e ∈ defects G b := by
    intro e
    refine Sym2.ind (fun x y => ?_) e
    simp
  unfold cost
  refine Finset.card_bij (fun e _ => Sym2.map Subtype.val e) ?_ ?_ ?_
  · intro e he
    apply (hS.mem_part_iff hC ((hmap e).mp he)).mpr
    intro x hx
    obtain ⟨x', hx', rfl⟩ := Sym2.mem_map.mp hx
    exact x'.property
  · intro e₁ he₁ e₂ he₂ heq
    exact Sym2.map.injective Subtype.val_injective heq
  · intro e heC
    revert heC
    refine Sym2.ind (fun x y heC => ?_) e
    let x' : B := ⟨x, (hS.valid C hC).endpoints_outer heC (Sym2.mem_mk_left x y)⟩
    let y' : B := ⟨y, (hS.valid C hC).endpoints_outer heC (Sym2.mem_mk_right x y)⟩
    refine ⟨s(x',y'), ?_, rfl⟩
    apply (mk_mem_defects _ _ _ _).mpr
    change G.Adj x y ∧ b x = b y
    exact (mk_mem_defects G b x y).mp (hS.part_subset C hC heC)

/-- The assigned count bounds the actual frustration of its induced ball. -/
theorem tau_le_part_card [Finite V] {b : V → Bool}
    (hS : ClusterPartition G (defects G b) S) {C : Cluster V} (hC : C ∈ S) :
    tau (G.induce (ball G C.center C.outer)) ≤ C.part.card := by
  rw [← hS.cost_induce_ball_eq hC]
  exact tau_le_cost _ _

/-- A ball that pays its assigned count gives pressure at that exact OWN level. -/
theorem pressure_of_tau_ge [Finite V] {b : V → Bool}
    (hS : ClusterPartition G (defects G b) S) {C : Cluster V} (hC : C ∈ S)
    (hm : 2 ≤ C.part.card)
    (ht : C.part.card ≤ tau (G.induce (ball G C.center C.outer))) : Pressure G := by
  refine ⟨ball G C.center C.outer, C.part.card, hm,
    le_antisymm (hS.tau_le_part_card hC) ht, ?_⟩
  obtain ⟨z, hz⟩ := ball_hasRadius G C.center C.outer
  exact ⟨z, fun x => (hz x).trans (ENat.coe_le_coe.mpr (hS.valid C hC).radius_le)⟩

end ClusterPartition

/-- Padded clustering for the actual monochromatic edges of a finite binary cut. -/
theorem defect_clustering [Finite V] (G : SimpleGraph V) (b : V → Bool) :
    ∃ S : Finset (Cluster V), ClusterPartition G (defects G b) S :=
  padded_clustering G (defects G b) (fun e he => ((mem_defects G b e).mp he).1)

end E74
