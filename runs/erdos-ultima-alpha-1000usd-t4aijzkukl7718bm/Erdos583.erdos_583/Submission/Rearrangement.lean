import Submission.Work

/-! Global incidence counting for normal trail systems. This identifies escape
neighbors but does not yet construct a global simplicity-improving exchange. -/

open SimpleGraph Erdos583Work
namespace Erdos583RearrangementDevelopment
namespace NormalTrailSystem

noncomputable def endpointEquiv {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) : Fin k × Bool ≃ V :=
  Equiv.ofBijective _ T.endpoint_bijective

noncomputable def owner {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (v : V) : Fin k := (endpointEquiv T).symm v |>.1

lemma endpoint_mem_support {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (x : Fin k × Bool) :
    endpointEquiv T x ∈ (T.walk x.1).support := by
  rcases x with ⟨i, b⟩
  cases b <;> simp [endpointEquiv]

lemma owner_spec {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (v : V) :
    v = T.start (owner T v) ∨ v = T.finish (owner T v) := by
  have h := (endpointEquiv T).apply_symm_apply v
  change (if ((endpointEquiv T).symm v).2 then
    T.start (owner T v) else T.finish (owner T v)) = v at h
  split_ifs at h with hb
  · exact Or.inl h.symm
  · exact Or.inr h.symm

lemma endpoint_iff_owner {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (v : V) (i : Fin k) :
    (v = T.start i ∨ v = T.finish i) ↔ owner T v = i := by
  constructor
  · rintro (hv | hv)
    · have he : v = endpointEquiv T (i,true) := hv
      simp [owner, he]
    · have he : v = endpointEquiv T (i,false) := hv
      simp [owner, he]
  · intro hi
    simpa only [hi] using owner_spec T v

lemma subgraph_injective {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) : Function.Injective (fun i ↦ (T.walk i).toSubgraph) := by
  intro i j hij
  dsimp only at hij
  by_contra hne
  have hnotnil : ¬(T.walk i).Nil := Walk.not_nil_of_ne (T.endpoints_ne i)
  have he : s(T.start i, (T.walk i).snd) ∈ (T.walk i).toSubgraph.edgeSet :=
    (T.walk i).toSubgraph_adj_snd hnotnil
  exact Set.disjoint_left.mp (T.disjoint hne) he (by rw [← hij]; exact he)

noncomputable def parts {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) : Finset G.Subgraph := by
  classical
  exact Finset.univ.image (fun i ↦ (T.walk i).toSubgraph)

lemma parts_decomposition {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) : IsDecomposition G (parts T) := by
  classical
  constructor
  · intro H hH K hK hHK
    change H ∈ Finset.univ.image (fun i ↦ (T.walk i).toSubgraph) at hH
    change K ∈ Finset.univ.image (fun i ↦ (T.walk i).toSubgraph) at hK
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hK
    exact T.disjoint (fun hh ↦ hHK (congrArg (fun i ↦ (T.walk i).toSubgraph) hh))
  · ext e
    simp only [parts, Set.mem_iUnion, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨H, ⟨i, rfl⟩, he⟩
      exact (T.cover e).mpr ⟨i, he⟩
    · intro he
      obtain ⟨i, hi⟩ := (T.cover e).mp he
      exact ⟨(T.walk i).toSubgraph, ⟨i, rfl⟩, hi⟩

lemma degree_sum {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ} (T : NormalTrailSystem G k) (v : V) :
    G.degree v = ∑ i, ((T.walk i).toSubgraph.neighborSet v).ncard := by
  classical
  rw [(parts_decomposition T).degree_eq_sum, parts, Finset.sum_image]
  intro i _ j _ hij
  exact subgraph_injective T hij

lemma odd_degree {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ} (T : NormalTrailSystem G k) (v : V) :
    Odd (G.degree v) := by
  classical
  rw [degree_sum T, Finset.odd_sum_iff_odd_card_odd]
  have hf : (Finset.univ.filter fun i ↦
      Odd ((T.walk i).toSubgraph.neighborSet v).ncard) = {owner T v} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      trail_neighbor_ncard_odd_iff (T.isTrail i), endpoint_iff_owner T, eq_comm]
    exact and_iff_right (T.endpoints_ne i)
  rw [hf]
  simp

noncomputable def containing {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (v : V) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter (fun i ↦ v ∈ (T.walk i).support)

/-- The vertices whose endpoint-owning trail visits v. -/
noncomputable def blockedVertices {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (v : V) : Finset V := by
  classical
  exact ((containing T v).product Finset.univ).image (endpointEquiv T)

lemma blocked_card {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (v : V) :
    (blockedVertices T v).card = 2*(containing T v).card := by
  classical
  rw [blockedVertices, Finset.card_image_of_injective _ (endpointEquiv T).injective]
  simp [Nat.mul_comm]

lemma mem_blocked_iff {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (v w : V) :
    w ∈ blockedVertices T v ↔ v ∈ (T.walk (owner T w)).support := by
  classical
  rw [blockedVertices]
  constructor
  · intro hw
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hw
    have hx' : v ∈ (T.walk x.1).support := by
      simpa only [containing, Finset.mem_filter, Finset.mem_univ, true_and] using
        (Finset.mem_product.mp hx).1
    have hi : owner T w = x.1 := by simp [owner, ← he]
    rw [hi]
    exact hx'
  · intro hw
    refine Finset.mem_image.mpr ⟨(endpointEquiv T).symm w,
      Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩, (endpointEquiv T).apply_symm_apply w⟩
    simpa only [containing, Finset.mem_filter, Finset.mem_univ, true_and] using hw

lemma self_mem_blocked {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (v : V) : v ∈ blockedVertices T v := by
  rw [mem_blocked_iff]
  have h := endpoint_mem_support T ((endpointEquiv T).symm v)
  simpa only [Equiv.apply_symm_apply] using h

/-- Neighbors whose endpoint-owning trail avoids v. -/
noncomputable def escapeNeighbors {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ} (T : NormalTrailSystem G k) (v : V) : Finset V := by
  classical
  exact G.neighborFinset v \ blockedVertices T v

lemma mem_escape_iff {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ} (T : NormalTrailSystem G k) (v w : V) :
    w ∈ escapeNeighbors T v ↔ G.Adj v w ∧ v ∉ (T.walk (owner T w)).support := by
  classical
  simp only [escapeNeighbors, Finset.mem_sdiff, mem_neighborFinset, mem_blocked_iff]

/-- At most 2t-1 neighbors can be blocked when t trails visit v: one of the
2t distinct endpoints of those trails is v itself, which is not its own neighbor. -/
lemma escape_bound {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ} (T : NormalTrailSystem G k) (v : V) :
    G.degree v + 1 ≤ 2*(containing T v).card + (escapeNeighbors T v).card := by
  classical
  have hsub : G.neighborFinset v ∩ blockedVertices T v ⊆ (blockedVertices T v).erase v := by
    intro w hw
    obtain ⟨hwN, hwB⟩ := Finset.mem_inter.mp hw
    have ha : G.Adj v w := by simpa using hwN
    exact Finset.mem_erase.mpr ⟨ha.ne.symm, hwB⟩
  have hle := Finset.card_le_card hsub
  have hcount := Finset.card_sdiff_add_card_inter (G.neighborFinset v) (blockedVertices T v)
  have herase := Finset.card_erase_add_one (self_mem_blocked T v)
  rw [blocked_card T] at herase
  change (escapeNeighbors T v).card + _ = G.degree v at hcount
  omega

lemma sum_containing_card {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) : ∑ v, (containing T v).card = T.score := by
  classical
  simp only [containing, Finset.card_filter]
  rw [Finset.sum_comm]
  unfold Erdos583Work.NormalTrailSystem.score
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.card_filter, Walk.verts_toSubgraph, Set.ncard_eq_toFinset_card']
  congr 1
  ext v
  simp

/-- A nonsimple normal trail system must have a vertex with a strict local
incidence deficit. -/
lemma exists_local_deficit {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ} (T : NormalTrailSystem G k)
    (hn : ¬∀ i, (T.walk i).IsPath) :
    ∃ v, 2*(containing T v).card < G.degree v + 1 := by
  classical
  have hs : T.score < G.edgeSet.ncard + k :=
    lt_of_le_of_ne T.score_le_edges_add (fun hh ↦ hn (T.score_eq_edges_add_iff.mp hh))
  by_contra! h
  have hh := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) ↦ h v)
  rw [Finset.sum_add_distrib, G.sum_degrees_eq_twice_card_edges,
    ← Finset.mul_sum, sum_containing_card T] at hh
  have he : G.edgeFinset.card = G.edgeSet.ncard := by
    rw [← Set.ncard_coe_finset, coe_edgeFinset]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, he] at hh
  have hc := T.twice_card
  omega

/-- Every nonsimple normal trail system has at least two escape neighbors at
some vertex. The theorem supplies targets, not a route of valid exchanges to them. -/
lemma exists_two_escape_neighbors {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ} (T : NormalTrailSystem G k)
    (hn : ¬∀ i, (T.walk i).IsPath) :
    ∃ v, 2 ≤ (escapeNeighbors T v).card := by
  obtain ⟨v, hv⟩ := exists_local_deficit T hn
  have hb := escape_bound T v
  obtain ⟨d, hd⟩ := odd_degree T v
  exact ⟨v, by omega⟩

/-- Permuting starting slots preserves bijectivity of the full endpoint map. -/
lemma permute_starts_bijective {V I : Type*} (a b : I → V)
    (hf : Function.Bijective (fun x : I × Bool ↦ if x.2 then a x.1 else b x.1))
    (e : I ≃ I) :
    Function.Bijective (fun x : I × Bool ↦ if x.2 then a (e x.1) else b x.1) := by
  let E : I × Bool ≃ I × Bool :=
    { toFun := fun x ↦ (if x.2 then e x.1 else x.1, x.2)
      invFun := fun x ↦ (if x.2 then e.symm x.1 else x.1, x.2)
      left_inv := by rintro ⟨i, c⟩; cases c <;> simp
      right_inv := by rintro ⟨i, c⟩; cases c <;> simp }
  have hfun : (fun x : I × Bool ↦ if x.2 then a (e x.1) else b x.1) =
      (fun x : I × Bool ↦ if x.2 then a x.1 else b x.1) ∘ E := by
    funext x
    rcases x with ⟨i, c⟩
    cases c <;> rfl
  rw [hfun]
  exact hf.comp E.bijective

lemma sum_extract_two {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → ℕ) (i j : I) (hij : i ≠ j) :
    ∑ l, f l = f i + f j + ∑ l ∈ (Finset.univ.erase i).erase j, f l := by
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ i),
    ← Finset.add_sum_erase (Finset.univ.erase i) f
      (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  omega

/-- Lift a two-trail replacement with exchanged starting endpoints to a
normal system, recording its exact effect on the global incidence score. -/
lemma replace_two_starts {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i j : Fin k) (hij : i ≠ j)
    (p : G.Walk (T.start j) (T.finish i)) (q : G.Walk (T.start i) (T.finish j))
    (hp : p.IsTrail) (hq : q.IsTrail)
    (hpq : Disjoint p.toSubgraph.edgeSet q.toSubgraph.edgeSet)
    (hu : p.toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet =
      (T.walk i).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet) :
    ∃ S : NormalTrailSystem G k,
      (S.walk i).toSubgraph = p.toSubgraph ∧
      (S.walk j).toSubgraph = q.toSubgraph ∧
      (∀ l, l ≠ i → l ≠ j → (S.walk l).toSubgraph = (T.walk l).toSubgraph) ∧
      S.score + (T.walk i).toSubgraph.verts.ncard + (T.walk j).toSubgraph.verts.ncard =
        T.score + p.toSubgraph.verts.ncard + q.toSubgraph.verts.ncard := by
  classical
  let a : Fin k → V := fun l ↦ T.start (Equiv.swap i j l)
  have hwalk (l : Fin k) : ∃ r : G.Walk (a l) (T.finish l), r.IsTrail ∧
      r.toSubgraph = if l=i then p.toSubgraph else if l=j then q.toSubgraph else (T.walk l).toSubgraph := by
    by_cases hli : l = i
    · subst l
      rw [show a i = T.start j by simp [a]]
      simp only [↓reduceIte]
      exact ⟨p, hp, rfl⟩
    · by_cases hlj : l = j
      · subst l
        rw [show a j = T.start i by simp [a]]
        simp only [if_neg hij.symm, ↓reduceIte]
        exact ⟨q, hq, rfl⟩
      · have ha : a l = T.start l := by simp [a, Equiv.swap_apply_of_ne_of_ne hli hlj]
        rw [ha]
        simp only [if_neg hli, if_neg hlj]
        exact ⟨T.walk l, T.isTrail l, rfl⟩
  choose r hr hre using hwalk
  have hri : (r i).toSubgraph = p.toSubgraph := by simpa using hre i
  have hrj : (r j).toSubgraph = q.toSubgraph := by simpa [hij.symm] using hre j
  have hrl (l : Fin k) (hli : l ≠ i) (hlj : l ≠ j) :
      (r l).toSubgraph = (T.walk l).toSubgraph := by simpa [hli, hlj] using hre l
  have hcross (l : Fin k) (hli : l ≠ i) (hlj : l ≠ j) :
      Disjoint (p.toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet) (T.walk l).toSubgraph.edgeSet := by
    rw [hu]
    exact disjoint_sup_left.mpr ⟨T.disjoint hli.symm, T.disjoint hlj.symm⟩
  have hdis : Pairwise fun l m ↦ Disjoint (r l).toSubgraph.edgeSet (r m).toSubgraph.edgeSet := by
    intro l m hlm
    by_cases hli : l = i
    · subst l
      rw [hri]
      by_cases hmj : m = j
      · subst m; rw [hrj]; exact hpq
      · rw [hrl m hlm.symm hmj]
        exact (disjoint_sup_left.mp (hcross m hlm.symm hmj)).1
    · by_cases hlj : l = j
      · subst l
        rw [hrj]
        by_cases hmi : m = i
        · subst m; rw [hri]; exact hpq.symm
        · rw [hrl m hmi hlm.symm]
          exact (disjoint_sup_left.mp (hcross m hmi hlm.symm)).2
      · rw [hrl l hli hlj]
        by_cases hmi : m = i
        · subst m; rw [hri]
          exact (disjoint_sup_left.mp (hcross l hli hlj)).1.symm
        · by_cases hmj : m = j
          · subst m; rw [hrj]
            exact (disjoint_sup_left.mp (hcross l hli hlj)).2.symm
          · rw [hrl m hmi hmj]
            exact T.disjoint hlm
  have hcover (e : Sym2 V) : e ∈ G.edgeSet ↔ ∃ l, e ∈ (r l).toSubgraph.edgeSet := by
    constructor
    · intro he
      obtain ⟨l, hl⟩ := (T.cover e).mp he
      by_cases hli : l = i
      · subst l
        have hh : e ∈ p.toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet := hu.symm ▸ Or.inl hl
        exact hh.elim (fun h ↦ ⟨i, hri.symm ▸ h⟩) (fun h ↦ ⟨j, hrj.symm ▸ h⟩)
      · by_cases hlj : l = j
        · subst l
          have hh : e ∈ p.toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet := hu.symm ▸ Or.inr hl
          exact hh.elim (fun h ↦ ⟨i, hri.symm ▸ h⟩) (fun h ↦ ⟨j, hrj.symm ▸ h⟩)
        · exact ⟨l, (hrl l hli hlj).symm ▸ hl⟩
    · rintro ⟨l, hl⟩
      exact (r l).toSubgraph.edgeSet_subset hl
  let S : NormalTrailSystem G k :=
    { start := a
      finish := T.finish
      walk := r
      isTrail := hr
      endpoint_bijective := permute_starts_bijective T.start T.finish T.endpoint_bijective (Equiv.swap i j)
      disjoint := hdis
      cover := hcover }
  refine ⟨S, hri, hrj, hrl, ?_⟩
  have hsum : ∑ l ∈ (Finset.univ.erase i).erase j, (S.walk l).toSubgraph.verts.ncard =
      ∑ l ∈ (Finset.univ.erase i).erase j, (T.walk l).toSubgraph.verts.ncard := by
    apply Finset.sum_congr rfl
    intro l hl
    obtain ⟨hlj, hl⟩ := Finset.mem_erase.mp hl
    have hli := (Finset.mem_erase.mp hl).1
    change (r l).toSubgraph.verts.ncard = _
    rw [hrl l hli hlj]
  have hS := sum_extract_two (fun l ↦ (S.walk l).toSubgraph.verts.ncard) i j hij
  have hT := sum_extract_two (fun l ↦ (T.walk l).toSubgraph.verts.ncard) i j hij
  change S.score = (r i).toSubgraph.verts.ncard + (r j).toSubgraph.verts.ncard + _ at hS
  rw [hri, hrj, hsum] at hS
  change T.score = _ at hT
  dsimp only at hS hT
  omega

/-- An available escape edge at a repeated starting vertex gives a strictly
higher-scoring normal trail system. -/
lemma improve_of_start_slide {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i j : Fin k) (hij : i ≠ j)
    (h : G.Adj (T.start i) (T.start j)) (p : G.Walk (T.start j) (T.finish i))
    (hpi : T.walk i = Walk.cons h p) (hv : T.start i ∈ p.support)
    (havoid : T.start i ∉ (T.walk j).support) :
    ∃ S : NormalTrailSystem G k, T.score < S.score := by
  have hp : (Walk.cons h p).IsTrail := hpi ▸ T.isTrail i
  have hd : Disjoint (Walk.cons h p).toSubgraph.edgeSet (T.walk j).toSubgraph.edgeSet :=
    hpi ▸ T.disjoint hij
  obtain ⟨hp', hq', hd', hu, _, hlt⟩ := trail_endpoint_slide h p (T.walk j) hp (T.isTrail j) hd hv
  obtain ⟨S, _, _, _, hs⟩ := replace_two_starts T i j hij p (Walk.cons h (T.walk j)) hp' hq' hd'
    (by rw [hpi]; exact hu.symm)
  have hlt' := hlt havoid
  rw [hpi] at hs
  exact ⟨S, by omega⟩


/-- Independently reversing members preserves the normal system and its score. -/
lemma orient {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (eps : Fin k → Bool) :
    ∃ S : NormalTrailSystem G k, S.score = T.score ∧
      ∀ i, S.start i = (if eps i then T.finish i else T.start i) ∧
        S.finish i = (if eps i then T.start i else T.finish i) ∧
        (S.walk i).toSubgraph = (T.walk i).toSubgraph := by
  classical
  let a (i : Fin k) := if eps i then T.finish i else T.start i
  let b (i : Fin k) := if eps i then T.start i else T.finish i
  let E : Fin k × Bool ≃ Fin k × Bool :=
    { toFun := fun x ↦ (x.1, if eps x.1 then !x.2 else x.2)
      invFun := fun x ↦ (x.1, if eps x.1 then !x.2 else x.2)
      left_inv := by rintro ⟨i, c⟩; cases h : eps i <;> simp [h]
      right_inv := by rintro ⟨i, c⟩; cases h : eps i <;> simp [h] }
  have hfun : (fun x : Fin k × Bool ↦ if x.2 then a x.1 else b x.1) =
      (fun x : Fin k × Bool ↦ if x.2 then T.start x.1 else T.finish x.1) ∘ E := by
    funext x
    rcases x with ⟨i, c⟩
    cases c <;> cases h : eps i <;> simp [a, b, E, h]
  have hwalk (i : Fin k) : ∃ p : G.Walk (a i) (b i),
      p.IsTrail ∧ p.toSubgraph = (T.walk i).toSubgraph := by
    cases he : eps i
    · rw [show a i = T.start i by simp [a, he], show b i = T.finish i by simp [b, he]]
      exact ⟨T.walk i, T.isTrail i, rfl⟩
    · rw [show a i = T.finish i by simp [a, he], show b i = T.start i by simp [b, he]]
      exact ⟨(T.walk i).reverse, (T.isTrail i).reverse, by simp⟩
  choose p hp hpe using hwalk
  let S : NormalTrailSystem G k :=
    { start := a
      finish := b
      walk := p
      isTrail := hp
      endpoint_bijective := by rw [hfun]; exact T.endpoint_bijective.comp E.bijective
      disjoint := by intro i j hij; rw [hpe i, hpe j]; exact T.disjoint hij
      cover := by intro e; simp_rw [hpe]; exact T.cover e }
  refine ⟨S, ?_, fun i ↦ ⟨rfl, rfl, hpe i⟩⟩
  unfold Erdos583Work.NormalTrailSystem.score
  apply Finset.sum_congr rfl
  intro i _
  change (p i).toSubgraph.verts.ncard = _
  rw [hpe]

lemma walk_copy_subgraph {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (p : G.Walk a b) (ha : a = c) (hb : b = d) : (p.copy ha hb).toSubgraph = p.toSubgraph := by
  subst c d
  rfl

/-- Direct escape slides are available regardless of which endpoint of the
receiving trail is stored as its start. -/
lemma improve_of_escape_slide {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i : Fin k) {w : V}
    (h : G.Adj (T.start i) w) (p : G.Walk w (T.finish i))
    (hpi : T.walk i = Walk.cons h p) (hv : T.start i ∈ p.support)
    (havoid : T.start i ∉ (T.walk (owner T w)).support) :
    ∃ S : NormalTrailSystem G k, T.score < S.score := by
  classical
  let j := owner T w
  change T.start i ∉ (T.walk j).support at havoid
  have hown : w = T.start j ∨ w = T.finish j := owner_spec T w
  clear_value j
  have hij : i ≠ j := by
    intro hh
    apply havoid
    rw [← hh]
    simp
  rcases hown with hw | hw
  · have hw' : w = T.start j := hw
    subst w
    exact improve_of_start_slide T i j hij h p hpi hv havoid
  · have hw' : w = T.finish j := hw
    obtain ⟨R, hscore, hR⟩ := orient T (fun l ↦ decide (l=j))
    have hi : R.start i = T.start i := by simpa [hij] using (hR i).1
    have hi' : R.finish i = T.finish i := by simpa [hij] using (hR i).2.1
    have hj : R.start j = w := by simpa [hw'] using (hR j).1
    have hj' : R.finish j = T.start j := by simpa using (hR j).2.1
    let Q : G.Walk (T.start i) (T.start j) := Walk.cons h ((T.walk j).reverse.copy hw'.symm rfl)
    have hp : (Walk.cons h p).IsTrail := hpi ▸ T.isTrail i
    have hq : ((T.walk j).reverse.copy hw'.symm rfl).IsTrail := by
      simpa using (T.isTrail j).reverse
    have hqS : ((T.walk j).reverse.copy hw'.symm rfl).toSubgraph = (T.walk j).toSubgraph := by
      rw [walk_copy_subgraph, Walk.toSubgraph_reverse]
    have hd : Disjoint (Walk.cons h p).toSubgraph.edgeSet
        ((T.walk j).reverse.copy hw'.symm rfl).toSubgraph.edgeSet := by
      rw [hqS, ← hpi]
      exact T.disjoint hij
    obtain ⟨hp', hQ, hd', hu, _, hlt⟩ := trail_endpoint_slide h p
      ((T.walk j).reverse.copy hw'.symm rfl) hp hq hd hv
    have hnot : T.start i ∉ ((T.walk j).reverse.copy hw'.symm rfl).support := by
      simpa using havoid
    have hlt' := hlt hnot
    let P' : G.Walk (R.start j) (R.finish i) := p.copy hj.symm hi'.symm
    let Q' : G.Walk (R.start i) (R.finish j) := Q.copy hi.symm hj'.symm
    have hP' : P'.IsTrail := by simpa [P'] using hp'
    have hQ' : Q'.IsTrail := by simpa [Q', Q] using hQ
    have hPe : P'.toSubgraph = p.toSubgraph := walk_copy_subgraph _ _ _
    have hQe : Q'.toSubgraph = Q.toSubgraph := walk_copy_subgraph _ _ _
    obtain ⟨S, _, _, _, hs⟩ := replace_two_starts R i j hij P' Q' hP' hQ'
      (by rw [hPe, hQe]; exact hd')
      (by rw [hPe, hQe, (hR i).2.2, (hR j).2.2, hpi, ← hqS]; exact hu.symm)
    rw [(hR i).2.2, (hR j).2.2, hscore, hPe, hQe, hpi, ← hqS] at hs
    exact ⟨S, by dsimp only [Q] at hs; omega⟩

/-- In a maximum-score system, the first neighbor of an endpoint-repeating
trail cannot be an escape neighbor. This does not address internal repetitions. -/
lemma max_score_start_neighbor_blocked {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (hmax : ∀ S : NormalTrailSystem G k, S.score ≤ T.score)
    (i : Fin k) {w : V} (h : G.Adj (T.start i) w) (p : G.Walk w (T.finish i))
    (hpi : T.walk i = Walk.cons h p) (hv : T.start i ∈ p.support) :
    T.start i ∈ (T.walk (owner T w)).support := by
  by_contra hn
  obtain ⟨S, hS⟩ := improve_of_escape_slide T i h p hpi hv hn
  exact (not_lt_of_ge (hmax S)) hS

end NormalTrailSystem

/-- When a repeated first neighbor is the other endpoint of the same trail,
cyclically reordering its three pieces exposes the old final tail at the start.
The complete subgraph, hence its vertex-incidence contribution, is unchanged. -/
lemma trail_same_owner_rotation {V : Type*} {G : SimpleGraph V} {v w : V}
    (h : G.Adj v w) (p : G.Walk w v) (q : G.Walk v w)
    (ht : (Walk.cons h (p.append q)).IsTrail) :
    ((q.append p).concat h).IsTrail ∧
      ((q.append p).concat h).toSubgraph = (Walk.cons h (p.append q)).toSubgraph := by
  have hperm : (Walk.cons h (p.append q)).edges.Perm ((q.append p).concat h).edges := by
    simp only [Walk.edges_cons, Walk.edges_append, Walk.edges_concat, List.concat_eq_append]
    calc
      (s(v,w) :: (p.edges ++ q.edges)).Perm (s(v,w) :: (q.edges ++ p.edges)) :=
        List.Perm.cons _ List.perm_append_comm
      (s(v,w) :: (q.edges ++ p.edges)).Perm ((q.edges ++ p.edges) ++ [s(v,w)]) := by
        simpa only [List.singleton_append] using
          (List.perm_append_comm (l₁ := [s(v,w)]) (l₂ := q.edges ++ p.edges))
  refine ⟨(Walk.isTrail_def _).mpr (hperm.nodup_iff.mp ht.edges_nodup), ?_⟩
  rw [Walk.concat_eq_append, Walk.toSubgraph_append, Walk.toSubgraph_cons_nil_eq_subgraphOfAdj]
  change (q.append p).toSubgraph ⊔ G.subgraphOfAdj h =
    G.subgraphOfAdj h ⊔ (p.append q).toSubgraph
  simp only [Walk.toSubgraph_append]
  ac_rfl

open scoped Classical in
/-- An injective successor relation on a finite set cannot trap a starting
point that is not in its image. This is the finite chain step needed for an
alternating-tail argument; it makes no assertion that trail exchanges realize
its successors. -/
lemma exists_first_exit_of_injective_successor {α : Type*} [Finite α]
    (S : Finset α) (f : α → α) (hf : Set.InjOn f (S : Set α))
    (x : α) (hx : x ∉ S.image f) :
    ∃ n : ℕ, f^[n] x ∉ S ∧ ∀ m < n, f^[m] x ∈ S := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  have hex : ∃ n : ℕ, f^[n] x ∉ S := by
    by_contra! hall
    let R : Finset α := (Set.range fun n : ℕ ↦ f^[n] x).toFinset
    have hRx : x ∈ R := Set.mem_toFinset.mpr ⟨0, rfl⟩
    have hRS : R ⊆ S := by
      intro y hy
      obtain ⟨n, rfl⟩ := Set.mem_toFinset.mp hy
      exact hall n
    have hclosed : R.image f ⊆ R := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨n, rfl⟩ := Set.mem_toFinset.mp hz
      exact Set.mem_toFinset.mpr ⟨n+1, Function.iterate_succ_apply' f n x⟩
    have hcard : (R.image f).card = R.card :=
      Finset.card_image_iff.mpr (hf.mono hRS)
    have hEq : R.image f = R := Finset.eq_of_subset_of_card_le hclosed (by rw [hcard])
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp (hEq.symm ▸ hRx)
    exact hx (Finset.mem_image.mpr ⟨y, hRS hy, hxy⟩)
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro m hm
  exact not_not.mp (Nat.find_min hex hm)


/-- Edge-disjoint nonempty endpoint-to-root segments have distinct final
neighbors. This provides injectivity for an alternating-tail successor map. -/
lemma tail_last_neighbor_injective {V I : Type*} {G : SimpleGraph V}
    {v : V} {a : I → V} (p : ∀ i, G.Walk (a i) v)
    (hne : ∀ i, a i ≠ v)
    (hd : Pairwise fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet) :
    Function.Injective (fun i ↦ (p i).penultimate) := by
  intro i j hij
  dsimp only at hij
  by_contra hn
  have hi : s((p i).penultimate,v) ∈ (p i).toSubgraph.edgeSet :=
    (p i).toSubgraph_adj_penultimate (Walk.not_nil_of_ne (hne i))
  have hj : s((p j).penultimate,v) ∈ (p j).toSubgraph.edgeSet :=
    (p j).toSubgraph_adj_penultimate (Walk.not_nil_of_ne (hne j))
  rw [hij] at hi
  exact Set.disjoint_left.mp (hd hn) hi hj

lemma closed_prefix_neighbor_not_tail_image {V I : Type*} {G : SimpleGraph V}
    {v : V} {a : I → V} (p : ∀ i, G.Walk (a i) v) (hne : ∀ i, a i ≠ v)
    (c : G.Walk v v) (hc : ¬c.Nil)
    (hd : ∀ i, Disjoint c.toSubgraph.edgeSet (p i).toSubgraph.edgeSet) :
    c.snd ∉ Set.range (fun i ↦ (p i).penultimate) := by
  rintro ⟨i, hi⟩
  dsimp only at hi
  have h1 : s(v,c.snd) ∈ c.toSubgraph.edgeSet := c.toSubgraph_adj_snd hc
  have h2 : s(v,(p i).penultimate) ∈ (p i).toSubgraph.edgeSet :=
    ((p i).toSubgraph_adj_penultimate (Walk.not_nil_of_ne (hne i))).symm
  rw [hi] at h2
  exact Set.disjoint_left.mp (hd i) h1 h2

end Erdos583RearrangementDevelopment
