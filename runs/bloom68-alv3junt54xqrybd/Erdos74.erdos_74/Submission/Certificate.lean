import Submission.Basic

/-!
# Actual bounded-radius frustration certificates

The post-deletion diameter estimate used here is deliberately generous.  Every
vertex remains within the original radius of either the original center or an
endpoint of a deleted edge.  A finite graph on these centers is used only as
bookkeeping: all final witness walks, and all certificate edges, are edges of
the original graph.  Branching is over every edge of every chosen odd-walk
witness; no disjoint-cycle packing or preservation of radius after pruning is
asserted.
-/

namespace E74

open SimpleGraph

universe u v
variable {V : Type u}

namespace Certificate


/-- Endpoint membership, including unordered pairs that are not graph edges. -/
theorem mem_ends (F : Finset (Sym2 V)) (x : V) :
    x ∈ ends F ↔ ∃ e ∈ F, x ∈ e := by
  classical
  simp [ends]

/-- Counting both ends of every edge is a harmless overestimate. -/
theorem card_ends_le (F : Finset (Sym2 V)) : (ends F).card ≤ 2 * F.card := by
  classical
  calc
    (ends F).card ≤ ∑ e ∈ F, e.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ F, 2 := Finset.sum_le_sum fun e _ => by
      rw [Sym2.card_toFinset]
      split_ifs <;> omega
    _ = 2 * F.card := by simp [Nat.mul_comm]

/-- A suffix after the last deleted edge is a walk from an allowed center. -/
theorem walk_after_deletions (G : SimpleGraph V) (F : Finset (Sym2 V))
    {z x : V} (p : G.Walk z x) :
    ∃ c : V, (c = z ∨ c ∈ ends F) ∧
      ∃ q : (G.deleteEdges (F : Set (Sym2 V))).Walk c x, q.length ≤ p.length := by
  classical
  induction p with
  | nil => exact ⟨_, Or.inl rfl, .nil, by simp⟩
  | @cons z y x h p ih =>
    obtain ⟨c, hc, q, hq⟩ := ih
    rcases hc with hc | hc
    · subst c
      by_cases he : s(z, y) ∈ F
      · refine ⟨y, Or.inr ?_, q, ?_⟩
        · exact (mem_ends F y).2 ⟨s(z, y), he, Sym2.mem_mk_right _ _⟩
        · simp only [Walk.length_cons]
          omega
      · refine ⟨z, Or.inl rfl, q.cons ?_, ?_⟩
        · exact deleteEdges_adj.2 ⟨h, he⟩
        · simp only [Walk.length_cons]
          omega
    · refine ⟨c, Or.inr hc, q, ?_⟩
      simp only [Walk.length_cons]
      omega

/-- Extended distance bounded by a natural number yields an actual short walk. -/
theorem short_walk_of_edist {G : SimpleGraph V} {x y : V} {r : ℕ}
    (h : G.edist x y ≤ (r : ℕ∞)) :
    ∃ p : G.Walk x y, p.length ≤ r := by
  have hn : G.edist x y ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top r) h
  obtain ⟨p, hp⟩ := G.exists_walk_of_edist_ne_top hn
  exact ⟨p, ENat.coe_le_coe.1 (hp ▸ h)⟩

open Classical in
/-- The original center and deleted-edge ends form an intrinsic residual cover. -/
theorem deletion_cover (G : SimpleGraph V) (F : Finset (Sym2 V))
    {z : V} {R : ℕ} (hr : ∀ x, G.edist z x ≤ (R : ℕ∞)) :
    ∀ x, ∃ c ∈ insert z (ends F),
      (G.deleteEdges (F : Set (Sym2 V))).edist c x ≤ (R : ℕ∞) := by
  classical
  intro x
  obtain ⟨p, hp⟩ := short_walk_of_edist (hr x)
  obtain ⟨c, hc, q, hq⟩ := walk_after_deletions G F p
  refine ⟨c, ?_, q.edist_le.trans ?_⟩
  · simpa only [Finset.mem_insert, eq_comm] using hc
  · exact ENat.coe_le_coe.2 (hq.trans hp)

/-- A finite radius cover bounds the diameter of each reachable component.
The auxiliary graph on centers does not replace any original edge. -/
theorem cover_diameter (G : SimpleGraph V) (C : Finset V) (R : ℕ)
    (hcover : ∀ x, ∃ c ∈ C, G.edist c x ≤ (R : ℕ∞))
    {x y : V} (hxy : G.Reachable x y) :
    G.edist x y ≤ (C.card * (2 * R + 1) + 2 * R : ℕ) := by
  classical
  let f : V → C := fun v => ⟨(hcover v).choose, (hcover v).choose_spec.1⟩
  have hf (v : V) : G.edist (f v).val v ≤ (R : ℕ∞) := (hcover v).choose_spec.2
  let Q : SimpleGraph C :=
    { Adj := fun c d => c ≠ d ∧ G.edist c.val d.val ≤ (2 * R + 1 : ℕ)
      symm := by
        intro c d h
        refine ⟨h.1.symm, ?_⟩
        rw [G.edist_comm]
        exact h.2
      loopless := by intro c h; exact h.1 rfl }
  have step {a b : V} (h : G.Adj a b) : Q.Reachable (f a) (f b) := by
    by_cases hab : f a = f b
    · rw [hab]
    · apply Adj.reachable
      refine ⟨hab, ?_⟩
      calc
        G.edist (f a).val (f b).val ≤
            G.edist (f a).val a + G.edist a (f b).val := G.edist_triangle
        _ ≤ (R : ℕ∞) + (G.edist a b + G.edist b (f b).val) :=
          add_le_add (hf a) G.edist_triangle
        _ ≤ (R : ℕ∞) + (1 + R) := by
          gcongr
          · exact le_of_eq (edist_eq_one_iff_adj.2 h)
          · rw [G.edist_comm]
            exact hf b
        _ = (2 * R + 1 : ℕ) := by simp only [Nat.cast_add, Nat.cast_mul]; ring
  have mapped {a b : V} (p : G.Walk a b) : Q.Reachable (f a) (f b) := by
    induction p with
    | nil => exact .rfl
    | cons h p ih => exact (step h).trans ih
  have hc : Q.Reachable (f x) (f y) := hxy.elim mapped
  obtain ⟨p, hp⟩ := hc.exists_isPath
  have plen : p.length ≤ C.card := by
    have hlt := hp.length_lt
    rw [Fintype.card_coe] at hlt
    omega
  have lift {c d : C} (q : Q.Walk c d) :
      G.edist c.val d.val ≤ (q.length * (2 * R + 1) : ℕ) := by
    induction q with
    | nil => simp
    | @cons c e d h q ih =>
      calc
        G.edist c.val d.val ≤ G.edist c.val e.val + G.edist e.val d.val :=
          G.edist_triangle
        _ ≤ (2 * R + 1 : ℕ) + (q.length * (2 * R + 1) : ℕ) := add_le_add h.2 ih
        _ = ((q.cons h).length * (2 * R + 1) : ℕ) := by
          simp only [Walk.length_cons, Nat.add_mul, Nat.one_mul, Nat.cast_add]
          exact add_comm _ _
  calc
    G.edist x y ≤ G.edist x (f x).val + G.edist (f x).val y := G.edist_triangle
    _ ≤ (R : ℕ∞) + (G.edist (f x).val (f y).val + G.edist (f y).val y) :=
      add_le_add (by rw [G.edist_comm]; exact hf x) G.edist_triangle
    _ ≤ (R : ℕ∞) + ((p.length * (2 * R + 1) : ℕ) + R) :=
      add_le_add le_rfl (add_le_add (lift p) (hf y))
    _ ≤ (R : ℕ∞) + ((C.card * (2 * R + 1) : ℕ) + R) := by
      gcongr
    _ = (C.card * (2 * R + 1) + 2 * R : ℕ) := by
      simp only [Nat.cast_add, Nat.cast_mul]
      ring

/-- A convenient residual component diameter bound. -/
theorem deletion_diameter (G : SimpleGraph V) (F : Finset (Sym2 V))
    {R : ℕ} (hr : HasRadius G R) {x y : V}
    (hxy : (G.deleteEdges (F : Set (Sym2 V))).Reachable x y) :
    (G.deleteEdges (F : Set (Sym2 V))).edist x y ≤
      ((2 * F.card + 2) * (2 * R + 1) : ℕ) := by
  classical
  obtain ⟨z, hz⟩ := hr
  have hd := cover_diameter _ (insert z (ends F)) R (deletion_cover G F hz) hxy
  have he := card_ends_le F
  have hi := Finset.card_insert_le z (ends F)
  refine hd.trans (ENat.coe_le_coe.2 ?_)
  nlinarith

/-- Along a walk with no monochromatic edge, binary colors alternate. -/
theorem walk_even_iff {G : SimpleGraph V} {x y : V} (p : G.Walk x y)
    (b : V → Bool) (hb : ∀ e ∈ p.edges, ¬ Mono b e) :
    Even p.length ↔ b x = b y := by
  revert hb
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
    intro hb
    have hxy : b x ≠ b y := hb s(x, y) (by simp)
    have ht : ∀ e ∈ p.edges, ¬ Mono b e := fun e he => hb e (by simp [he])
    rw [Walk.length_cons, Nat.even_add_one, ih ht]
    cases hx : b x <;> cases hy : b y <;> cases hz : b z <;> simp_all

/-- An odd closed walk is a finite edge witness hit by every binary coloring. -/
theorem odd_walk_hit {G : SimpleGraph V} {x : V} (p : G.Walk x x)
    (ho : Odd p.length) (b : V → Bool) :
    ∃ e ∈ p.edges, Mono b e := by
  by_contra hn
  push_neg at hn
  have he := (walk_even_iff p b hn).2 rfl
  exact (Nat.not_even_iff_odd.2 ho) he


/-- A diameter bound converts failure of a binary coloring into a short actual
odd closed walk. Components may be disconnected from one another. -/
theorem short_odd_walk (G : SimpleGraph V) (D : ℕ)
    (hd : ∀ {x y}, G.Reachable x y → G.edist x y ≤ (D : ℕ∞))
    (hn : ∀ b : V → Bool, ∃ x y, G.Adj x y ∧ b x = b y) :
    ∃ (x : V) (p : G.Walk x x), Odd p.length ∧ p.length ≤ 2 * D + 1 := by
  classical
  let root (x : V) : V := (G.connectedComponentMk x).out
  have hr (x : V) : G.Reachable (root x) x :=
    ConnectedComponent.exact (Quot.out_eq (G.connectedComponentMk x))
  let b (x : V) : Bool := decide (Even (G.dist (root x) x))
  obtain ⟨x, y, hxy, hb⟩ := hn b
  have heq : root x = root y :=
    congrArg Quot.out (ConnectedComponent.connectedComponentMk_eq_of_adj hxy)
  have hry : G.Reachable (root x) y := (hr x).trans hxy.reachable
  obtain ⟨p, hp⟩ := (hr x).exists_walk_length_eq_dist
  obtain ⟨q, hq⟩ := hry.exists_walk_length_eq_dist
  have hpar : Even p.length ↔ Even q.length := by
    have h : decide (Even p.length) = decide (Even q.length) := by
      simpa only [b, hp, hq, heq] using hb
    exact decide_eq_decide.1 h
  have hpD : p.length ≤ D := ENat.coe_le_coe.1 <| by
    rw [hp, (hr x).coe_dist_eq_edist]
    exact hd (hr x)
  have hqD : q.length ≤ D := ENat.coe_le_coe.1 <| by
    rw [hq, hry.coe_dist_eq_edist]
    exact hd hry
  let w : G.Walk (root x) (root x) := (p.append hxy.toWalk).append q.reverse
  have hw : w.length = p.length + 1 + q.length := by simp [w]
  refine ⟨root x, w, ?_, ?_⟩
  · rw [hw, ← Nat.not_even_iff_odd, Nat.even_add, Nat.even_add_one]
    tauto
  · rw [hw]
    omega

/-- Deleting fewer than `k` edges cannot remove every binary-cut defect. -/
theorem deletion_not_binary [Finite V] (G : SimpleGraph V) {k : ℕ}
    (hk : k ≤ tau G) (F : Finset (Sym2 V)) (hF : F.card < k) :
    ∀ b : V → Bool, ∃ x y,
      (G.deleteEdges (F : Set (Sym2 V))).Adj x y ∧ b x = b y := by
  classical
  intro b
  by_contra hn
  push_neg at hn
  have hs : defects G b ⊆ F := by
    intro e
    refine Sym2.ind ?_ e
    intro x y he
    obtain ⟨ha, hm⟩ := (mk_mem_defects G b x y).1 he
    by_contra hnot
    exact hn x y (deleteEdges_adj.2 ⟨ha, hnot⟩) hm
  have hcost : cost G b ≤ F.card := Finset.card_le_card hs
  have ht := tau_le_cost G b
  omega

/-- Uniform upper bound on witness edge counts at every branching node. -/
def witnessBound (R k : ℕ) : ℕ := 2 * ((2 * k + 2) * (2 * R + 1)) + 1

/-- An actual finite nonbipartite edge witness avoiding any small deletion set. -/
theorem deletion_witness [Finite V] (G : SimpleGraph V) {R k : ℕ}
    (hr : HasRadius G R) (hk : k ≤ tau G)
    (F : Finset (Sym2 V)) (hF : F.card < k) :
    ∃ A : Finset (Sym2 V),
      (∀ e ∈ A, e ∈ G.edgeSet ∧ e ∉ F) ∧
      A.card ≤ witnessBound R k ∧
      ∀ b : V → Bool, ∃ e ∈ A, Mono b e := by
  classical
  let D := (2 * F.card + 2) * (2 * R + 1)
  obtain ⟨x, p, ho, hp⟩ := short_odd_walk
    (G.deleteEdges (F : Set (Sym2 V))) D
    (fun h => deletion_diameter G F hr h) (deletion_not_binary G hk F hF)
  refine ⟨p.edges.toFinset, ?_, ?_, ?_⟩
  · intro e he
    have hm := p.edges_subset_edgeSet (List.mem_toFinset.1 he)
    simpa only [edgeSet_deleteEdges, Set.mem_diff, Finset.mem_coe] using hm
  · calc
      p.edges.toFinset.card ≤ p.edges.length := List.toFinset_card_le p.edges
      _ = p.length := p.length_edges
      _ ≤ 2 * D + 1 := hp
      _ ≤ witnessBound R k := by
        unfold D witnessBound
        gcongr
  · intro b
    obtain ⟨e, he, hm⟩ := odd_walk_hit p ho b
    exact ⟨e, List.mem_toFinset.2 he, hm⟩

open Classical in
/-- Complete edge branching, expressed as a lower bound for every binary cut.
The deletion history is retained only to ensure that a selected root defect
is distinct from all defects in its corresponding child certificate. -/
theorem branch_certificate (G : SimpleGraph V) (k M : ℕ)
    (hw : ∀ F : Finset (Sym2 V), F.card < k →
      ∃ A : Finset (Sym2 V),
        (∀ e ∈ A, e ∈ G.edgeSet ∧ e ∉ F) ∧ A.card ≤ M ∧
        ∀ b : V → Bool, ∃ e ∈ A, Mono b e) :
    ∀ (n : ℕ) (F : Finset (Sym2 V)), F.card + n ≤ k →
      ∃ C : Finset (Sym2 V),
        (∀ e ∈ C, e ∈ G.edgeSet ∧ e ∉ F) ∧
        (∀ b : V → Bool, n ≤ (C.filter (Mono b)).card) ∧
        C.card + 1 ≤ (M + 1) ^ n := by
  classical
  intro n
  induction n with
  | zero =>
    intro F hF
    exact ⟨∅, by simp, by simp, by simp⟩
  | succ n ih =>
    intro F hF
    obtain ⟨A, hAedge, hAcard, hAhit⟩ := hw F (by omega)
    have child (e : A) :
        ∃ B : Finset (Sym2 V),
          (∀ d ∈ B, d ∈ G.edgeSet ∧ d ∉ insert e.val F) ∧
          (∀ b : V → Bool, n ≤ (B.filter (Mono b)).card) ∧
          B.card + 1 ≤ (M + 1) ^ n := by
      apply ih (insert e.val F)
      rw [Finset.card_insert_of_notMem (hAedge e.val e.prop).2]
      omega
    choose B hBedge hBcost hBcard using child
    let C := A ∪ A.attach.biUnion B
    have hBC (e : A) : B e ⊆ C := by
      intro d hd
      exact Finset.mem_union.2 <| Or.inr <|
        Finset.mem_biUnion.2 ⟨e, by simp, hd⟩
    have hCedge : ∀ d ∈ C, d ∈ G.edgeSet ∧ d ∉ F := by
      intro d hd
      rcases Finset.mem_union.1 hd with hd | hd
      · exact hAedge d hd
      · obtain ⟨e, _, hd⟩ := Finset.mem_biUnion.1 hd
        obtain ⟨hg, hf⟩ := hBedge e d hd
        exact ⟨hg, fun hm => hf (Finset.mem_insert_of_mem hm)⟩
    refine ⟨C, hCedge, ?_, ?_⟩
    · intro b
      obtain ⟨e, he, hm⟩ := hAhit b
      let ei : A := ⟨e, he⟩
      have heB : e ∉ B ei := by
        intro hd
        exact (hBedge ei e hd).2 (Finset.mem_insert_self _ _)
      have hsub : insert e ((B ei).filter (Mono b)) ⊆ C.filter (Mono b) := by
        intro d hd
        rcases Finset.mem_insert.1 hd with rfl | hd
        · exact Finset.mem_filter.2 ⟨Finset.mem_union.2 (Or.inl he), hm⟩
        · obtain ⟨hdB, hdmono⟩ := Finset.mem_filter.1 hd
          exact Finset.mem_filter.2 ⟨hBC ei hdB, hdmono⟩
      have hcount := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (fun h => heB (Finset.mem_filter.1 h).1)] at hcount
      have hb := hBcost ei b
      omega
    · have hsum : (∑ e ∈ A.attach, (B e).card) + A.card ≤
          A.card * (M + 1) ^ n := by
        have h := Finset.sum_le_sum (fun e (_he : e ∈ A.attach) => hBcard e)
        simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_attach,
          smul_eq_mul, mul_one] using h
      have hu := Finset.card_union_le A (A.attach.biUnion B)
      have hb := Finset.card_biUnion_le (s := A.attach) (t := B)
      have hpow : 1 ≤ (M + 1) ^ n := Nat.one_le_pow n (M + 1) (by omega)
      dsimp [C]
      rw [pow_succ]
      nlinarith


open Classical in
/-- Restricting to the actual selected endpoints retains the certified cost.
We can keep all induced edges; this only makes the cut lower bound stronger. -/
theorem induce_ends_tau [Finite V] (G : SimpleGraph V) (C : Finset (Sym2 V))
    {k : ℕ} (hedge : ∀ e ∈ C, e ∈ G.edgeSet)
    (hcut : ∀ b : V → Bool, k ≤ (C.filter (Mono b)).card) :
    k ≤ tau (G.induce (ends C : Set V)) := by
  classical
  let S : Set V := (ends C : Set V)
  obtain ⟨b, hb⟩ := tau_attained (G.induce S)
  let bV : V → Bool := fun x => if hx : x ∈ S then b ⟨x, hx⟩ else false
  have hs : C.filter (Mono bV) ⊆
      (defects (G.induce S) b).image (Sym2.map (Subtype.val : S → V)) := by
    intro e
    refine Sym2.ind ?_ e
    intro x y he
    obtain ⟨heC, hm⟩ := Finset.mem_filter.1 he
    have hx : x ∈ S := (mem_ends C x).2 ⟨s(x, y), heC, Sym2.mem_mk_left _ _⟩
    have hy : y ∈ S := (mem_ends C y).2 ⟨s(x, y), heC, Sym2.mem_mk_right _ _⟩
    refine Finset.mem_image.2 ⟨s(⟨x, hx⟩, ⟨y, hy⟩), ?_, rfl⟩
    apply (mk_mem_defects (G.induce S) b ⟨x, hx⟩ ⟨y, hy⟩).2
    refine ⟨hedge s(x, y) heC, ?_⟩
    simpa only [mono_mk, bV, dif_pos hx, dif_pos hy] using hm
  have hcard := (Finset.card_le_card hs).trans Finset.card_image_le
  have hkcost : k ≤ cost (G.induce S) b := (hcut bV).trans hcard
  rwa [hb] at hkcost


/-- Monochromaticity is exactly preserved when endpoints are mapped. -/
@[simp] theorem mono_map {W : Type v} (f : W → V) (b : V → Bool) (e : Sym2 W) :
    Mono b (Sym2.map f e) ↔ Mono (b ∘ f) e := by
  refine Sym2.ind ?_ e
  intro x y
  rfl

/-- The witness-size bound is monotone in both its budgets. -/
theorem witnessBound_mono {R R' k k' : ℕ} (hR : R ≤ R') (hk : k ≤ k') :
    witnessBound R k ≤ witnessBound R' k' := by
  unfold witnessBound
  gcongr

end Certificate

/-- An explicit, deliberately loose finite order bound.
Only the selected radius and selected frustration level occur in it. -/
def certificateBound (R k : ℕ) : ℕ :=
  2 * (Certificate.witnessBound R k + 1) ^ k

/-- Bounded-radius actual certificate extraction, also valid at levels zero
and one.  The output graph may simply be the induced graph on the selected
finite support; no post-extraction radius or chromatic claim is needed. -/
theorem radius_certificate_all [Finite V] (G : SimpleGraph V) {R k : ℕ}
    (hr : HasRadius G R) (ht : k ≤ tau G) :
    ∃ S : Set V, S.Finite ∧ ∃ H : SimpleGraph S,
      H ≤ G.induce S ∧ k ≤ tau H ∧ S.ncard ≤ certificateBound R k := by
  classical
  obtain ⟨C, hCedge, hCcut, hCcard⟩ := Certificate.branch_certificate G k
    (Certificate.witnessBound R k) (Certificate.deletion_witness G hr ht) k ∅ (by simp)
  refine ⟨(ends C : Set V), Set.toFinite _, G.induce (ends C : Set V), le_rfl,
    Certificate.induce_ends_tau G C (fun e he => (hCedge e he).1) hCcut, ?_⟩
  rw [Set.ncard_coe_finset]
  have he := Certificate.card_ends_le C
  unfold certificateBound
  omega

/-- Public useful-level version of bounded-radius certificate extraction. -/
theorem radius_certificate [Finite V] (G : SimpleGraph V) {R k : ℕ}
    (hr : HasRadius G R) (_hk : 2 ≤ k) (ht : k ≤ tau G) :
    ∃ S : Set V, S.Finite ∧ ∃ H : SimpleGraph S,
      H ≤ G.induce S ∧ k ≤ tau H ∧ S.ncard ≤ certificateBound R k :=
  radius_certificate_all G hr ht


/-- Monotonicity in both radius and the selected frustration level. -/
theorem certificateBound_mono {R R' k k' : ℕ} (hR : R ≤ R') (hk : k ≤ k') :
    certificateBound R k ≤ certificateBound R' k' := by
  unfold certificateBound
  apply Nat.mul_le_mul_left
  calc
    (Certificate.witnessBound R k + 1) ^ k ≤
        (Certificate.witnessBound R' k' + 1) ^ k :=
      Nat.pow_le_pow_left (Nat.add_le_add_right (Certificate.witnessBound_mono hR hk) 1) k
    _ ≤ (Certificate.witnessBound R' k' + 1) ^ k' :=
      Nat.pow_le_pow_right (by omega) hk

/-- The finite bound dominates its level, so its inverse profile is unbounded. -/
theorem le_certificateBound (R k : ℕ) : k ≤ certificateBound R k := by
  by_cases hk : k = 0
  · simp [hk]
  · have hp := Nat.le_self_pow hk (Certificate.witnessBound R k + 1)
    have hb : k ≤ Certificate.witnessBound R k + 1 := by
      unfold Certificate.witnessBound
      nlinarith
    unfold certificateBound
    omega

/-- The universal bound at a pressure witness's own selected level. -/
def ownCertificateBound (k : ℕ) : ℕ := certificateBound (rho k) k

/-- Actual pressure reification. The chosen level is not replaced by the total
ambient cut budget. All output vertices and edges belong to the ambient graph. -/
theorem pressure_certificate [Finite V] (G : SimpleGraph V) (hp : Pressure G) :
    ∃ (S : Set V) (k : ℕ), S.Finite ∧ 2 ≤ k ∧ ∃ H : SimpleGraph S,
      H ≤ G.induce S ∧ k ≤ tau H ∧ S.ncard ≤ ownCertificateBound k := by
  classical
  obtain ⟨U, k, hk, hkt, hr⟩ := hp
  have ht : k ≤ tau (G.induce U) := le_of_eq hkt.symm
  obtain ⟨C, hCedge, hCcut, hCcard⟩ := Certificate.branch_certificate (G.induce U) k
    (Certificate.witnessBound (rho k) k)
    (Certificate.deletion_witness (G.induce U) hr ht) k ∅ (by simp)
  let f : Sym2 U → Sym2 V := Sym2.map (Subtype.val : U → V)
  let C' : Finset (Sym2 V) := C.image f
  have hf : Function.Injective f := Sym2.map.injective Subtype.val_injective
  have hmapedge (e : Sym2 U) : e ∈ C → f e ∈ G.edgeSet := by
    refine Sym2.ind ?_ e
    intro x y he
    exact (hCedge s(x, y) he).1
  have hC'edge : ∀ e ∈ C', e ∈ G.edgeSet := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 he
    exact hmapedge d hd
  have hC'cut (b : V → Bool) : k ≤ (C'.filter (Mono b)).card := by
    have heq : C'.filter (Mono b) =
        (C.filter (Mono (b ∘ (Subtype.val : U → V)))).image f := by
      dsimp [C']
      rw [Finset.filter_image]
      congr 1
      ext e
      simp only [Finset.mem_filter, f, Certificate.mono_map]
    rw [heq, Finset.card_image_of_injective _ hf]
    exact hCcut (b ∘ Subtype.val)
  refine ⟨(ends C' : Set V), k, Set.toFinite _, hk,
    G.induce (ends C' : Set V), le_rfl,
    Certificate.induce_ends_tau G C' hC'edge hC'cut, ?_⟩
  rw [Set.ncard_coe_finset]
  have he := Certificate.card_ends_le C'
  have hc : C'.card ≤ C.card := Finset.card_image_le
  unfold ownCertificateBound certificateBound
  omega

/-- In particular, the own-level certificate bound is unbounded. -/
theorem le_ownCertificateBound (k : ℕ) : k ≤ ownCertificateBound k :=
  le_certificateBound (rho k) k


/-- The integer own-level bound can be used directly to define a monotone
unbounded inverse profile, without a real-valued asymptotic estimate. -/
theorem ownCertificateBound_mono : Monotone ownCertificateBound := by
  have hρ : Monotone rho := by
    apply monotone_nat_of_le_succ
    intro n
    simp only [rho]
    nlinarith
  intro a b hab
  exact certificateBound_mono (hρ hab) hab

/-- The own-level order budget diverges along the natural numbers. -/
theorem ownCertificateBound_tendsto :
    Filter.Tendsto ownCertificateBound Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_atTop_of_monotone ownCertificateBound_mono
    (fun k => ⟨k, le_ownCertificateBound k⟩)

end E74
