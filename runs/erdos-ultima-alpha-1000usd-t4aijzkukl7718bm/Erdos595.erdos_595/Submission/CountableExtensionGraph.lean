import Submission.Work

/-!
A countable K4-free graph realizing every finite allowable neighborhood.
It supplies an explicit generic base for testing ultrafilter constructions.
This is an auxiliary construction, not a settlement of Erdős 595.
-/

open SimpleGraph Set
namespace Erdos595CountableExtension

mutual
inductive Node where
  | mk : ℕ → Forest → Node
  deriving DecidableEq, Countable
inductive Forest where
  | nil : Forest
  | cons : Node → Forest → Forest
  deriving DecidableEq, Countable
end

mutual
def rank : Node → ℕ
  | .mk n l => n + mass l + 1
def mass : Forest → ℕ
  | .nil => 0
  | .cons x l => rank x + mass l + 1
end

def Mem (x : Node) : Forest → Prop
  | .nil => False
  | .cons y l => x = y ∨ Mem x l

lemma rank_lt_mass {x : Node} {l : Forest} (h : Mem x l) : rank x < mass l := by
  cases l with
  | nil => exact h.elim
  | cons y l =>
    rcases h with rfl | h
    · simp only [mass]; omega
    · have := rank_lt_mass h
      simp only [mass]; omega

termination_by sizeOf l

def Child (x : Node) : Node → Prop
  | .mk _ l => Mem x l

lemma child_rank {x y : Node} (h : Child x y) : rank x < rank y := by
  cases y with
  | mk n l =>
    have := rank_lt_mass h
    simp only [rank]; omega

def raw : SimpleGraph Node where
  Adj x y := Child x y ∨ Child y x
  symm := fun _ _ h => h.symm
  loopless := fun _ h => h.elim (fun h => (lt_irrefl _ (child_rank h)))
    (fun h => (lt_irrefl _ (child_rank h)))

def TFChildren (l : Forest) : Prop :=
  ∀ x y z, Mem x l → Mem y l → Mem z l → raw.Adj x y → raw.Adj x z → raw.Adj y z → False

mutual
def Good : Node → Prop
  | .mk _ l => GoodForest l ∧ TFChildren l
def GoodForest : Forest → Prop
  | .nil => True
  | .cons x l => Good x ∧ GoodForest l
end

lemma good_mem {l : Forest} (h : GoodForest l) {x : Node} (hx : Mem x l) : Good x := by
  cases l with
  | nil => exact hx.elim
  | cons y l =>
    rcases hx with rfl | hx
    · exact h.1
    · exact good_mem h.2 hx

termination_by sizeOf l

abbrev Vertex := {x : Node // Good x}
def G : SimpleGraph Vertex := raw.induce Good

theorem G_cliqueFree : G.CliqueFree 4 := by
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have ha : ∀ i j : Fin 4, i ≠ j → G.Adj (e i) (e j) :=
    fun i j hij => e.map_rel_iff.mpr hij
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (fun j : Fin 4 => rank (e j).val)
    Finset.univ_nonempty
  have hc : ∀ j : Fin 4, i ≠ j → Child (e j).val (e i).val := by
    intro j hij
    have h := ha i j hij
    change raw.Adj (e i).val (e j).val at h
    rcases h with h | h
    · have hlt := child_rank h
      have hle := hi j (Finset.mem_univ j)
      omega
    · exact h
  have hgood := (e i).property
  cases he : (e i).val with
  | mk n l =>
    rw [he] at hgood hc
    have ht : TFChildren l := hgood.2
    fin_cases i
    · exact ht (e 1).val (e 2).val (e 3).val
        (hc 1 (by decide)) (hc 2 (by decide)) (hc 3 (by decide))
        (ha 1 2 (by decide)) (ha 1 3 (by decide)) (ha 2 3 (by decide))
    · exact ht (e 0).val (e 2).val (e 3).val
        (hc 0 (by decide)) (hc 2 (by decide)) (hc 3 (by decide))
        (ha 0 2 (by decide)) (ha 0 3 (by decide)) (ha 2 3 (by decide))
    · exact ht (e 0).val (e 1).val (e 3).val
        (hc 0 (by decide)) (hc 1 (by decide)) (hc 3 (by decide))
        (ha 0 1 (by decide)) (ha 0 3 (by decide)) (ha 1 3 (by decide))
    · exact ht (e 0).val (e 1).val (e 2).val
        (hc 0 (by decide)) (hc 1 (by decide)) (hc 2 (by decide))
        (ha 0 1 (by decide)) (ha 0 2 (by decide)) (ha 1 2 (by decide))

def forest : List Vertex → Forest
  | [] => .nil
  | x :: l => .cons x.val (forest l)

lemma mem_forest (l : List Vertex) (x : Node) :
    Mem x (forest l) ↔ ∃ v ∈ l, v.val = x := by
  induction l with
  | nil => simp [forest,Mem]
  | cons v l ih =>
    simp only [forest,Mem,List.mem_cons,exists_eq_or_imp,ih]
    constructor
    · rintro (rfl | h)
      · exact Or.inl rfl
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h

lemma forest_good (l : List Vertex) : GoodForest (forest l) := by
  induction l with
  | nil => trivial
  | cons x l ih => exact ⟨x.property,ih⟩

lemma forest_triangleFree (s : Finset Vertex) (hs : (G.induce (s : Set Vertex)).CliqueFree 3) :
    TFChildren (forest s.toList) := by
  classical
  intro x y z hx hy hz hxy hxz hyz
  obtain ⟨a,ha,rfl⟩ := (mem_forest _ _).mp hx
  obtain ⟨b,hb,rfl⟩ := (mem_forest _ _).mp hy
  obtain ⟨c,hc,rfl⟩ := (mem_forest _ _).mp hz
  have ha' : a ∈ s := Finset.mem_toList.mp ha
  have hb' : b ∈ s := Finset.mem_toList.mp hb
  have hc' : c ∈ s := Finset.mem_toList.mp hc
  exact hs _ (SimpleGraph.is3Clique_triple_iff.mpr
    (show (G.induce (s : Set Vertex)).Adj ⟨a,ha'⟩ ⟨b,hb'⟩ ∧
      (G.induce (s : Set Vertex)).Adj ⟨a,ha'⟩ ⟨c,hc'⟩ ∧
      (G.induce (s : Set Vertex)).Adj ⟨b,hb'⟩ ⟨c,hc'⟩ from ⟨hxy,hxz,hyz⟩))

/-- Every finite allowable neighborhood is realized by a fresh vertex. -/
theorem finite_extension (s t : Finset Vertex)
    (hs : (G.induce (s : Set Vertex)).CliqueFree 3) (hst : Disjoint s t) :
    ∃ v : Vertex, v ∉ s ∪ t ∧ (∀ w ∈ s, G.Adj v w) ∧ (∀ w ∈ t, ¬G.Adj v w) := by
  classical
  let n := (s ∪ t).sup (fun v => rank v.val) + 1
  let v : Vertex := ⟨Node.mk n (forest s.toList),forest_good _ ,forest_triangleFree s hs⟩
  have hlt : ∀ w ∈ s ∪ t, rank w.val < rank v.val := by
    intro w hw
    have hle := Finset.le_sup (f := fun v : Vertex => rank v.val) hw
    change rank w.val ≤ (s ∪ t).sup (fun v : Vertex => rank v.val) at hle
    dsimp only [v,rank,n]
    omega
  have hv : v ∉ s ∪ t := fun h => lt_irrefl _ (hlt v h)
  have hadj : ∀ w ∈ s ∪ t, G.Adj v w ↔ w ∈ s := by
    intro w hw
    have hlt' := hlt w hw
    change (Child v.val w.val ∨ Child w.val v.val) ↔ w ∈ s
    constructor
    · rintro (h | h)
      · exact (lt_asymm hlt' (child_rank h)).elim
      · obtain ⟨x,hx,he⟩ := (mem_forest s.toList w.val).mp h
        have hxw : x = w := Subtype.ext he
        simpa only [hxw,Finset.mem_toList] using hx
    · intro h
      exact Or.inr ((mem_forest s.toList w.val).mpr ⟨w,Finset.mem_toList.mpr h,rfl⟩)
  refine ⟨v,hv,fun w hw => (hadj w (Finset.mem_union_left _ hw)).mpr hw,?_⟩
  intro w hw hadj'
  exact Finset.disjoint_left.mp hst ((hadj w (Finset.mem_union_right _ hw)).mp hadj') hw

def seed (n : ℕ) : Vertex := ⟨.mk n .nil,by simp [Good,GoodForest,TFChildren,Mem]⟩

lemma seed_injective : Function.Injective seed := by
  intro m n h
  have hh := congrArg (fun v : Vertex => v.val) h
  simpa only [seed,Node.mk.injEq,and_true] using hh

instance : Infinite Vertex := Infinite.of_injective seed seed_injective

lemma pair_triangleFree (a b : Vertex) : (G.induce (↑({a,b} : Finset Vertex) : Set Vertex)).CliqueFree 3 := by
  classical
  apply SimpleGraph.cliqueFree_of_card_lt
  have hc : ({a,b} : Finset Vertex).card ≤ 2 := Finset.card_le_two
  have he : Fintype.card (↑({a,b} : Finset Vertex) : Set Vertex) = ({a,b} : Finset Vertex).card :=
    Fintype.card_coe _
  omega

/-- In particular every two original vertices have a common neighbor. -/
theorem pair_common (a b : Vertex) : ∃ v, G.Adj a v ∧ G.Adj b v := by
  classical
  obtain ⟨v,_,hv,_⟩ := finite_extension {a,b} ∅ (pair_triangleFree a b) (by simp)
  exact ⟨v,(hv a (by simp)).symm,(hv b (by simp)).symm⟩

#print axioms G_cliqueFree
#print axioms finite_extension
#print axioms pair_common
end Erdos595CountableExtension
