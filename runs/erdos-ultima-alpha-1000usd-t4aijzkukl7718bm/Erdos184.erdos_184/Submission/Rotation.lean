import FormalConjecturesUtil

/-! Path-rotation lemmas for cycle decompositions. -/

open SimpleGraph
open scoped List
namespace Erdos184Rotation

variable {V : Type*} {G : SimpleGraph V} {u v : V}

def rotatePath (p : G.Walk u v) (i : ℕ) (hi : G.Adj u (p.getVert i)) :
    G.Walk (p.getVert (i - 1)) v :=
  (p.take (i - 1)).reverse.append (.cons hi (p.drop i))

lemma rotatePath_length (p : G.Walk u v) (i : ℕ) (hi : G.Adj u (p.getVert i))
    (hi0 : 1 ≤ i) (hil : i ≤ p.length) : (rotatePath p i hi).length = p.length := by
  simp only [rotatePath, Walk.length_append, Walk.length_reverse, Walk.take_length,
    Walk.length_cons, Walk.drop_length]
  omega

lemma rotatePath_support (p : G.Walk u v) (i : ℕ) (hi : G.Adj u (p.getVert i))
    (hi0 : 1 ≤ i) (hil : i ≤ p.length) :
    (rotatePath p i hi).support = (p.support.take i).reverse ++ p.support.drop i := by
  simp only [rotatePath, Walk.support_append, Walk.support_reverse,
    Walk.take_support_eq_support_take_succ, Walk.support_cons, List.tail_cons,
    Walk.drop_support_eq_support_drop_min, Nat.min_eq_left hil,
    Nat.sub_add_cancel hi0]

lemma rotatePath_isPath {p : G.Walk u v} (hp : p.IsPath) (i : ℕ)
    (hi : G.Adj u (p.getVert i)) (hi0 : 1 ≤ i) (hil : i ≤ p.length) :
    (rotatePath p i hi).IsPath := by
  rw [Walk.isPath_def, rotatePath_support p i hi hi0 hil]
  have hperm : (p.support.take i).reverse ++ p.support.drop i ~ p.support := by
    calc
      _ ~ p.support.take i ++ p.support.drop i :=
        (List.reverse_perm _).append_right _
      _ = _ := List.take_append_drop _ _
  exact hperm.nodup_iff.mpr hp.support_nodup

lemma rotatePath_getVert_ge (p : G.Walk u v) (i : ℕ) (hi : G.Adj u (p.getVert i))
    (hi0 : 1 ≤ i) (hil : i ≤ p.length) (j : ℕ) (hij : i ≤ j) :
    (rotatePath p i hi).getVert j = p.getVert j := by
  have ht : i - 1 ≤ p.length := by omega
  simp only [rotatePath, Walk.getVert_append, Walk.length_reverse, Walk.take_length,
    Nat.min_eq_left ht, if_neg (show ¬j < i - 1 by omega)]
  rw [Walk.getVert_cons _ _ (by omega), Walk.drop_getVert]
  congr 1
  omega

lemma take_isPath {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) (j : ℕ) : (p.take j).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [SimpleGraph.Walk.take_support_eq_support_take_succ]
  exact hp.support_nodup.take

lemma endpoint_edge_notMem {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) (hlen : 2 ≤ p.length) : s(u,v) ∉ p.edges := by
  intro h
  have hs := hp.eq_snd_of_mem_edges h
  have heq : p.getVert 1 = p.getVert p.length := by
    simpa [SimpleGraph.Walk.snd] using hs.symm
  have := hp.getVert_injOn (show 1 ≤ p.length by omega) (show p.length ≤ p.length by rfl) heq
  omega

lemma close_prefix_isCycle {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) (j : ℕ) (hj : j ≤ p.length) (hj2 : 2 ≤ j)
    (hadj : G.Adj u (p.getVert j)) :
    (SimpleGraph.Walk.cons hadj (p.take j).reverse).IsCycle := by
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨(take_isPath hp j).reverse, ?_⟩
  rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]
  apply endpoint_edge_notMem (take_isPath hp j)
  simpa [SimpleGraph.Walk.take_length, Nat.min_eq_left hj] using hj2


open scoped Classical in
lemma pairwise_small_inter_union_bound {α β : Type*} (S : Finset α) (A : α → Finset β)
    (hinter : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (A a ∩ A b).card ≤ 1) :
    2 * (∑ a ∈ S, (A a).card) + S.card ≤
      2 * (S.biUnion A).card + S.card * S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hS : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (A a ∩ A b).card ≤ 1 := by
      intro b hb c hc hbc
      exact hinter b (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc) hbc
    have hi := ih hS
    have hinter' : (A a ∩ S.biUnion A).card ≤ S.card := by
      rw [Finset.inter_biUnion]
      simpa using Finset.card_biUnion_le_card_mul S (fun b => A a ∩ A b) 1 (by
        intro b hb
        exact hinter a (Finset.mem_insert_self _ _) b (Finset.mem_insert_of_mem hb)
          (by intro hab; subst b; exact ha hb))
    have hu := Finset.card_union_add_card_inter (A a) (S.biUnion A)
    simp only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
      Finset.biUnion_insert]
    nlinarith

lemma longest_path_neighbors_mem {p : G.Walk u v} (hp : p.IsPath)
    (hmax : ∀ a b (q : G.Walk a b), q.IsPath → q.length ≤ p.length) :
    ∀ w, G.Adj u w → w ∈ p.support := by
  intro w hw
  by_contra hnot
  have hq : (Walk.cons hw.symm p).IsPath :=
    (Walk.cons_isPath_iff _ _).mpr ⟨hp, hnot⟩
  have hlen := hmax w v (.cons hw.symm p) hq
  simp only [Walk.length_cons] at hlen
  omega

lemma path_neighbor_index_lt {p : G.Walk u v} (hp : p.IsPath) (k : ℕ) (hk : 2 ≤ k)
    (hno : ∀ a (c : G.Walk a a), c.IsCycle → c.length ≤ k)
    (j : ℕ) (hj : j ≤ p.length) (hadj : G.Adj u (p.getVert j)) : j < k := by
  by_contra! hjk
  have hc := hno u (.cons hadj (p.take j).reverse)
    (close_prefix_isCycle hp j hj (by omega) hadj)
  simp only [Walk.length_cons, Walk.length_reverse, Walk.take_length,
    Nat.min_eq_left hj] at hc
  omega

open scoped Classical in
lemma rotation_neighbors_prefix [Fintype V] {p : G.Walk u v} (hp : p.IsPath)
    (hmax : ∀ a b (q : G.Walk a b), q.IsPath → q.length ≤ p.length)
    (k : ℕ) (hk : 2 ≤ k)
    (hno : ∀ a (c : G.Walk a a), c.IsCycle → c.length ≤ k)
    (i : ℕ) (hi0 : 1 ≤ i) (hil : i ≤ p.length) (hi : G.Adj u (p.getVert i)) :
    G.neighborFinset (p.getVert (i - 1)) ⊆ (Finset.range k).image p.getVert := by
  classical
  let q := rotatePath p i hi
  have hq : q.IsPath := rotatePath_isPath hp i hi hi0 hil
  have hql : q.length = p.length := rotatePath_length p i hi hi0 hil
  have hqmax : ∀ a b (r : G.Walk a b), r.IsPath → r.length ≤ q.length := by
    simpa only [hql] using hmax
  have hik : i < k := path_neighbor_index_lt hp k hk hno i hil hi
  intro w hw
  have hwAdj : G.Adj (p.getVert (i - 1)) w := G.mem_neighborFinset _ _ |>.mp hw
  have hwq := longest_path_neighbors_mem hq hqmax w hwAdj
  have hwp : w ∈ p.support := by
    rw [rotatePath_support p i hi hi0 hil] at hwq
    simp only [List.mem_append, List.mem_reverse] at hwq
    rcases hwq with h | h
    · exact List.mem_of_mem_take h
    · exact List.mem_of_mem_drop h
  obtain ⟨j, hjw, hj⟩ := Walk.mem_support_iff_exists_getVert.mp hwp
  have hjk : j < k := by
    by_contra! hjk
    have hij : i ≤ j := by omega
    have heq : q.getVert j = w := (rotatePath_getVert_ge p i hi hi0 hil j hij).trans hjw
    have hadj : G.Adj (p.getVert (i - 1)) (q.getVert j) := heq.symm ▸ hwAdj
    have hlt := path_neighbor_index_lt hq k hk hno j (by omega) hadj
    omega
  exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjk, hjw⟩

open scoped Classical in
lemma min_degree_square_le_of_no_long_cycle [Fintype V] [Nonempty V]
    (d k : ℕ) (hk : 2 ≤ k) (hdeg : ∀ x, d ≤ G.degree x)
    (hinter : ∀ x y, x ≠ y → (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 1)
    (hno : ∀ a (c : G.Walk a a), c.IsCycle → c.length ≤ k) :
    d * d + d ≤ 2 * k := by
  classical
  obtain ⟨u, v, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  let I := (Finset.Icc 1 p.length).filter (fun i => G.Adj u (p.getVert i))
  have hImem : ∀ i, i ∈ I ↔ 1 ≤ i ∧ i ≤ p.length ∧ G.Adj u (p.getVert i) := by
    intro i
    simp only [I, Finset.mem_filter, Finset.mem_Icc, and_assoc]
  have hIcard : I.card = G.degree u := by
    rw [← G.card_neighborFinset_eq_degree]
    apply Finset.card_bij (fun i _ => p.getVert i)
    · intro i hi
      exact (G.mem_neighborFinset _ _).mpr ((hImem i).mp hi).2.2
    · intro i hi j hj heq
      exact hp.getVert_injOn ((hImem i).mp hi).2.1 ((hImem j).mp hj).2.1 heq
    · intro w hw
      have hwa : G.Adj u w := (G.mem_neighborFinset _ _).mp hw
      obtain ⟨i, hiw, hil⟩ := Walk.mem_support_iff_exists_getVert.mp
        (longest_path_neighbors_mem hp hmax w hwa)
      have hi0 : 1 ≤ i := by
        by_contra! hi0
        have hi : i = 0 := by omega
        have huw : u = w := by simpa [hi] using hiw
        exact hwa.ne huw
      exact ⟨i, (hImem i).mpr ⟨hi0, hil, hiw.symm ▸ hwa⟩, hiw⟩
  let R := I.image (fun i => p.getVert (i - 1))
  have hRcard : R.card = G.degree u := by
    rw [← hIcard]
    apply Finset.card_image_iff.mpr
    intro i hi j hj heq
    have hi' := (hImem i).mp hi
    have hj' := (hImem j).mp hj
    have he := hp.getVert_injOn (show i - 1 ≤ p.length by omega)
      (show j - 1 ≤ p.length by omega) heq
    omega
  obtain ⟨S, hSR, hScard⟩ := Finset.exists_subset_card_eq
    (show d ≤ R.card by rw [hRcard]; exact hdeg u)
  have hSprefix : S.biUnion (fun x => G.neighborFinset x) ⊆ (Finset.range k).image p.getVert := by
    intro w hw
    obtain ⟨x, hx, hwx⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp (hSR hx)
    have hi' := (hImem i).mp hi
    subst x
    exact rotation_neighbors_prefix hp hmax k hk hno i hi'.1 hi'.2.1 hi'.2.2 hwx
  have hScount : (S.biUnion (fun x => G.neighborFinset x)).card ≤ k := by
    exact (Finset.card_le_card hSprefix).trans (Finset.card_image_le.trans (by simp))
  have hsum : d * d ≤ ∑ x ∈ S, (G.neighborFinset x).card := by
    calc
      d * d = ∑ _x ∈ S, d := by simp [hScard]
      _ ≤ _ := Finset.sum_le_sum (fun x _ => by simpa using hdeg x)
  have hbound := pairwise_small_inter_union_bound S (fun x => G.neighborFinset x)
    (fun x _ y _ hxy => hinter x y hxy)
  rw [hScard] at hbound
  nlinarith

/-- No two distinct vertices have two distinct common neighbors. -/
def UniqueCommonNeighbors (G : SimpleGraph V) : Prop :=
  ∀ {x y z w : V}, x ≠ y → G.Adj x z → G.Adj y z → G.Adj x w → G.Adj y w → z = w

lemma UniqueCommonNeighbors.mono {H : SimpleGraph V} (h : UniqueCommonNeighbors G)
    (hHG : H ≤ G) : UniqueCommonNeighbors H := by
  intro x y z w hxy hxz hyz hxw hyw
  exact h hxy (hHG hxz) (hHG hyz) (hHG hxw) (hHG hyw)

lemma UniqueCommonNeighbors.induce (h : UniqueCommonNeighbors G) (S : Set V) :
    UniqueCommonNeighbors (G.induce S) := by
  intro x y z w hxy hxz hyz hxw hyw
  exact Subtype.ext (h (fun heq => hxy (Subtype.ext heq)) hxz hyz hxw hyw)

open scoped Classical in
lemma UniqueCommonNeighbors.card_inter_le [Fintype V] (h : UniqueCommonNeighbors G)
    (x y : V) (hxy : x ≠ y) :
    (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro z hz w hw
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hz hw
  exact h hxy hz.1 hz.2 hw.1 hw.2

universe u

open scoped Classical in
lemma unique_neighbors_edges_le_of_no_long_cycle {V : Type u} [Fintype V]
    (G : SimpleGraph V) (d k : ℕ) (hd : 0 < d) (hk : 2 ≤ k)
    (hdk : 2 * k < d * d + d) (huni : UniqueCommonNeighbors G)
    (hno : ∀ u (p : G.Walk u u), p.IsCycle → p.length ≤ k) :
    G.edgeFinset.card ≤ (d - 1) * Fintype.card V := by
  classical
  have main : ∀ n : ℕ, ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
      Fintype.card W = n → UniqueCommonNeighbors H →
      (∀ u (p : H.Walk u u), p.IsCycle → p.length ≤ k) →
      H.edgeFinset.card ≤ (d - 1) * n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ H hcard huniH hnoH
      cases isEmpty_or_nonempty W with
      | inl he =>
        have hbot : H = ⊥ := by ext a; exact isEmptyElim a
        subst H
        simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
          SimpleGraph.edgeSet_bot]
        simp
      | inr he =>
        obtain ⟨v, hv⟩ : ∃ v, H.degree v < d := by
          by_contra! hn
          have hb := min_degree_square_le_of_no_long_cycle d k hk hn
            huniH.card_inter_le hnoH
          omega
        let S : Set W := {v}ᶜ
        let K := H.induce S
        have hc : Fintype.card S = Fintype.card W - 1 := by
          change Fintype.card ↑({v}ᶜ : Set W) = _
          rw [Fintype.card_compl_set]
          simp only [Fintype.card_unique]
        have hpos : 0 < n := hcard ▸ Fintype.card_pos
        have hsmall : Fintype.card S < n := by omega
        have hnoK : ∀ u (p : K.Walk u u), p.IsCycle → p.length ≤ k := by
          intro u p hp
          let e : K ↪g H := SimpleGraph.Embedding.induce S
          have hp' := SimpleGraph.Walk.IsCycle.map (f := e.toHom) e.injective hp
          have hlen := hnoH (e u) (p.map e.toHom) hp'
          simpa using hlen
        have hb := ih (Fintype.card S) hsmall K rfl (huniH.induce S) hnoK
        have hem : K.edgeFinset.card + H.degree v = H.edgeFinset.card := by
          change (H.induce {v}ᶜ).edgeFinset.card + H.degree v = H.edgeFinset.card
          rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
            SimpleGraph.card_edgeFinset_deleteIncidenceSet,
            Nat.sub_add_cancel (H.degree_le_card_edgeFinset v)]
        rw [hc, hcard] at hb
        have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
        simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hb hem ⊢
        simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hv hem
        have hksub : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
        nlinarith
  exact main _ G rfl huni hno


#print axioms unique_neighbors_edges_le_of_no_long_cycle
#print axioms min_degree_square_le_of_no_long_cycle
#print axioms rotation_neighbors_prefix
#print axioms rotatePath_isPath
end Erdos184Rotation
