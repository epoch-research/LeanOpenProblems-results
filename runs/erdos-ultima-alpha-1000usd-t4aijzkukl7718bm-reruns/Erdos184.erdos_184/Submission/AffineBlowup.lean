import Submission.TourCover

/-!
Affine lifts of an edge-bijective cycle cover into independent blowups.
These are auxiliary results, not a settlement of Erdős 184.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.AffineBlowup

variable {V W F : Type*} [Field F]
variable {G : SimpleGraph V} {K : SimpleGraph W}

/-- The independent blowup with one field-labelled fibre over each vertex. -/
def graph (G : SimpleGraph V) (F : Type*) : SimpleGraph (V × F) :=
  G.comap Prod.fst

/-- Distinct occurrences in a fibre receive distinct offsets. -/
def SeparatesFibres (f : W → V) (offset : W → F) : Prop :=
  ∀ i j, f i = f j → offset i = offset j → i = j

/-- A two-parameter affine lift of a graph homomorphism. -/
def lift (f : K →g G) (colour : V → F) (offset : W → F) (a b : F) :
    K →g graph G F where
  toFun i := (f i, a + colour (f i) * b + offset i)
  map_rel' := fun h => f.map_rel h

lemma lift_injective (f : K →g G) (colour : V → F) (offset : W → F)
    (ho : SeparatesFibres f offset) (a b : F) :
    Function.Injective (lift f colour offset a b) := by
  intro i j h
  have hf : f i = f j := congrArg Prod.fst h
  have hd := congrArg Prod.snd h
  change a + colour (f i) * b + offset i = a + colour (f j) * b + offset j at hd
  rw [hf] at hd
  exact ho i j hf (add_left_cancel hd)

/-- An injective homomorphism is an isomorphism onto its mapped top subgraph. -/
noncomputable def imageIso {U Z : Type*} {A : SimpleGraph U} {B : SimpleGraph Z}
    (f : A →g B) (hf : Function.Injective f) :
    A ≃g ((⊤ : A.Subgraph).map f).coe where
  toEquiv := Equiv.ofBijective
    (fun u => (⟨f u, ⟨u, Set.mem_univ _, rfl⟩⟩ : ((⊤ : A.Subgraph).map f).verts))
    ⟨fun _ _ h => hf (congrArg Subtype.val h), by
      rintro ⟨z, u, _, rfl⟩
      exact ⟨u, rfl⟩⟩
  map_rel_iff' := by
    intro u v
    change (∃ x y, A.Adj x y ∧ f x = f u ∧ f y = f v) ↔ A.Adj u v
    constructor
    · rintro ⟨x,y,h,hx,hy⟩
      obtain rfl := hf hx
      obtain rfl := hf hy
      exact h
    · intro h
      exact ⟨u,v,h,rfl,rfl⟩

lemma affine_pair_unique {c d r s a b a' b' : F} (hc : c ≠ d)
    (h1 : a + c*b + r = a' + c*b' + r)
    (h2 : a + d*b + s = a' + d*b' + s) : a = a' ∧ b = b' := by
  have hm : (c-d)*(b-b') = 0 := by linear_combination h1 - h2
  have hb : b = b' := sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hc))
  subst b'
  exact ⟨add_right_cancel (add_right_cancel h1), rfl⟩

lemma affine_pair_surjective {c d : F} (hc : c ≠ d) (r s x y : F) :
    ∃ a b : F, a + c*b + r = x ∧ a + d*b + s = y := by
  let b := (y - s - (x-r)) / (d-c)
  refine ⟨x-r-c*b, b, by ring, ?_⟩
  dsimp [b]
  field_simp [sub_ne_zero.mpr hc.symm]
  ring

/-- The image of the regular-two source under one affine lift. -/
def piece (f : K →g G) (colour : V → F) (offset : W → F) (a b : F) :
    (graph G F).Subgraph := (⊤ : K.Subgraph).map (lift f colour offset a b)

lemma piece_cycles [Fintype W] [Fintype V] [Fintype F]
    (f : K →g G) (colour : V → F) (offset : W → F)
    (ho : SeparatesFibres f offset) (hc : K.Connected) (hr : K.IsRegularOfDegree 2)
    (a b : F) :
    (piece f colour offset a b).coe.Connected ∧
      (piece f colour offset a b).coe.IsRegularOfDegree 2 := by
  let e := imageIso (lift f colour offset a b) (lift_injective f colour offset ho a b)
  refine ⟨e.connected_iff.mp hc, ?_⟩
  intro v
  obtain ⟨u, rfl⟩ := e.surjective v
  have he := e.degree_eq u
  have hu := hr u
  simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at he hu ⊢
  exact he.trans hu

lemma edge_parameters (f : K →g G) (colour : V → F) (offset : W → F)
    (hi : Set.InjOn (Sym2.map f) K.edgeSet)
    (hc : ∀ {u v}, G.Adj u v → colour u ≠ colour v)
    {a b a' b' : F} {u v : V × F}
    (h1 : (piece f colour offset a b).Adj u v)
    (h2 : (piece f colour offset a' b').Adj u v) : a = a' ∧ b = b' := by
  obtain ⟨i,j,hij,hiu,hjv⟩ := h1
  obtain ⟨k,l,hkl,hku,hlv⟩ := h2
  have hik : f i = f k := (congrArg Prod.fst hiu).trans (congrArg Prod.fst hku).symm
  have hjl : f j = f l := (congrArg Prod.fst hjv).trans (congrArg Prod.fst hlv).symm
  have he : s(i,j) = s(k,l) := hi hij hkl (by simp only [Sym2.map_pair_eq, hik, hjl])
  rcases Sym2.eq_iff.mp he with ⟨hik',hjl'⟩ | ⟨hil',hjk'⟩
  · subst k
    subst l
    exact affine_pair_unique (hc (f.map_rel hij))
      ((congrArg Prod.snd hiu).trans (congrArg Prod.snd hku).symm)
      ((congrArg Prod.snd hjv).trans (congrArg Prod.snd hlv).symm)
  · subst l
    subst k
    exact ((f.map_rel hij).ne hik).elim

lemma edge_covered (f : K →g G) (colour : V → F) (offset : W → F)
    (hs : Set.SurjOn (Sym2.map f) K.edgeSet G.edgeSet)
    (hc : ∀ {u v}, G.Adj u v → colour u ≠ colour v)
    {u v : V × F} (h : (graph G F).Adj u v) :
    ∃ a b : F, (piece f colour offset a b).Adj u v := by
  obtain ⟨e,he,hf⟩ := hs (show s(u.1,v.1) ∈ G.edgeSet from h)
  induction e using Sym2.ind with
  | h i j =>
    rw [Sym2.map_pair_eq, Sym2.eq_iff] at hf
    rcases hf with ⟨hi,hj⟩ | ⟨hj,hi⟩
    · obtain ⟨a,b,ha,hb⟩ := affine_pair_surjective (hc (f.map_rel he))
        (offset i) (offset j) u.2 v.2
      refine ⟨a,b,i,j,he,?_,?_⟩
      · exact Prod.ext hi ha
      · exact Prod.ext hj hb
    · obtain ⟨a,b,ha,hb⟩ := affine_pair_surjective (hc (f.map_rel he.symm))
        (offset j) (offset i) u.2 v.2
      refine ⟨a,b,j,i,he.symm,?_,?_⟩
      · exact Prod.ext hi ha
      · exact Prod.ext hj hb

noncomputable def decomposition [Fintype F]
    (f : K →g G) (colour : V → F) (offset : W → F) : Finset (graph G F).Subgraph :=
  Finset.univ.image (fun p : F × F => piece f colour offset p.1 p.2)

lemma decomposition_card_le [Fintype F]
    (f : K →g G) (colour : V → F) (offset : W → F) :
    (decomposition f colour offset).card ≤ Fintype.card F ^ 2 := by
  calc
    _ ≤ (Finset.univ : Finset (F × F)).card := Finset.card_image_le
    _ = _ := by simp [pow_two]

lemma decomposition_exact [Fintype F]
    (f : K →g G) (colour : V → F) (offset : W → F)
    (hi : Set.InjOn (Sym2.map f) K.edgeSet)
    (hs : Set.SurjOn (Sym2.map f) K.edgeSet G.edgeSet)
    (hc : ∀ {u v}, G.Adj u v → colour u ≠ colour v) :
    IsDecomposition (graph G F) (decomposition f colour offset) := by
  constructor
  · intro H hH J hJ hne
    obtain ⟨⟨a,b⟩,_,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨⟨a',b'⟩,_,rfl⟩ := Finset.mem_image.mp hJ
    apply Set.disjoint_left.mpr
    intro e he he'
    induction e using Sym2.ind with
    | h u v =>
      obtain ⟨rfl,rfl⟩ := edge_parameters f colour offset hi hc he he'
      exact hne rfl
  · ext e
    induction e using Sym2.ind with
    | h u v =>
      simp only [Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨H,_,he⟩
        exact H.edgeSet_subset he
      · intro he
        obtain ⟨a,b,hab⟩ := edge_covered f colour offset hs hc he
        exact ⟨piece f colour offset a b, Finset.mem_image.mpr ⟨(a,b), Finset.mem_univ _, rfl⟩,hab⟩

/-- A properly coloured edge-bijective regular-two cover with fibre-separating
labels gives at most `q²` genuine simple cycles in the independent `q`-blowup. -/
theorem affine_decomposition [Fintype W] [Fintype V] [Fintype F]
    (f : K →g G) (colour : V → F) (offset : W → F)
    (ho : SeparatesFibres f offset) (hconn : K.Connected) (hreg : K.IsRegularOfDegree 2)
    (hi : Set.InjOn (Sym2.map f) K.edgeSet)
    (hs : Set.SurjOn (Sym2.map f) K.edgeSet G.edgeSet)
    (hc : ∀ {u v}, G.Adj u v → colour u ≠ colour v) :
    ∃ D : Finset (graph G F).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (graph G F) D ∧ D.card ≤ Fintype.card F ^ 2 := by
  refine ⟨decomposition f colour offset, ?_, decomposition_exact f colour offset hi hs hc,
    decomposition_card_le f colour offset⟩
  intro H hH
  obtain ⟨⟨a,b⟩,_,rfl⟩ := Finset.mem_image.mp hH
  exact piece_cycles f colour offset ho hconn hreg a b

end Erdos184.AffineBlowup
