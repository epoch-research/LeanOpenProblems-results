import Submission.Work

/-!
A K4-free graph can be embedded in a maximal K4-free graph without changing
its countable triangle-free edge coverability. New diamonds are attached only
to nonedges. This is a limitation of a maximality-based approach, not a solution
of Erdős 595.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595DiamondCompletion
open Erdos595Work
universe u
variable {V : Type u}

inductive Node (V : Type u) where
  | leaf : V → Node V
  | fork : Bool → Node V → Node V → Node V

open Node

def height : Node V → ℕ
  | leaf _ => 0
  | fork _ a b => max (height a) (height b) + 1

def Child (a : Node V) : Node V → Prop
  | leaf _ => False
  | fork _ b c => a = b ∨ a = c

lemma child_height {a b : Node V} (h : Child a b) : height a < height b := by
  cases b with
  | leaf v => exact h.elim
  | fork t b c =>
    rcases h with rfl | rfl <;> simp only [height] <;> omega

def Mate : Node V → Node V → Prop
  | fork t a b, fork s c d => t ≠ s ∧ a = c ∧ b = d
  | _, _ => False

lemma mate_symm {a b : Node V} (h : Mate a b) : Mate b a := by
  cases a <;> cases b <;> simp_all [Mate, eq_comm]

lemma mate_height {a b : Node V} (h : Mate a b) : height a = height b := by
  cases a <;> cases b <;> simp_all [Mate, height]

def Adj (G : SimpleGraph V) (a b : Node V) : Prop :=
  (∃ v w, a = leaf v ∧ b = leaf w ∧ G.Adj v w) ∨
  Child a b ∨ Child b a ∨ Mate a b

lemma adj_symm {G : SimpleGraph V} {a b : Node V} (h : Adj G a b) : Adj G b a := by
  rcases h with ⟨v,w,rfl,rfl,h⟩ | h | h | h
  · exact Or.inl ⟨w,v,rfl,rfl,h.symm⟩
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (mate_symm h)))

lemma adj_irrefl (G : SimpleGraph V) (a : Node V) : ¬Adj G a a := by
  rintro (⟨v,w,hv,hw,h⟩ | h | h | h)
  · exact h.ne (Node.leaf.inj (hv.symm.trans hw))
  · exact Nat.lt_irrefl _ (child_height h)
  · exact Nat.lt_irrefl _ (child_height h)
  · cases a <;> simp_all [Mate]

@[simp] lemma adj_leaf (G : SimpleGraph V) (v w : V) :
    Adj G (leaf v) (leaf w) ↔ G.Adj v w := by
  simp [Adj, Child, Mate]

def Valid (G : SimpleGraph V) : Node V → Prop
  | leaf _ => True
  | fork _ a b => Valid G a ∧ Valid G b ∧ ¬Adj G a b

abbrev Vertex (G : SimpleGraph V) := {a : Node V // Valid G a}

def graph (G : SimpleGraph V) : SimpleGraph (Vertex G) where
  Adj a b := Adj G a.val b.val
  symm := fun _ _ h => adj_symm h
  loopless := fun a => adj_irrefl G a.val

lemma lower_neighbor {G : SimpleGraph V} {a b x : Node V} {t : Bool}
    (h : Adj G (fork t a b) x) (hx : height x ≤ height (fork t a b)) :
    x = a ∨ x = b ∨ x = fork (!t) a b := by
  rcases h with ⟨v,w,h,_,_⟩ | h | h | h
  · cases h
  · have hh := child_height h
    omega
  · exact h.imp_right Or.inl
  · cases x with
    | leaf v => exact h.elim
    | fork s c d =>
      rcases h with ⟨ht,rfl,rfl⟩
      right; right
      cases t <;> cases s <;> simp_all

lemma no_adj_children {G : SimpleGraph V} {a b x y : Node V}
    (h : ¬Adj G a b) (hx : x = a ∨ x = b) (hy : y = a ∨ y = b) :
    ¬Adj G x y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact adj_irrefl G _
  · exact h
  · exact fun h' => h (adj_symm h')
  · exact adj_irrefl G _

lemma no_three_lower {G : SimpleGraph V} {a b x y z : Node V} {t : Bool}
    (hv : Valid G (fork t a b))
    (hfx : Adj G (fork t a b) x) (hfy : Adj G (fork t a b) y)
    (hfz : Adj G (fork t a b) z)
    (hx : height x ≤ height (fork t a b))
    (hy : height y ≤ height (fork t a b))
    (hz : height z ≤ height (fork t a b))
    (hxy : Adj G x y) (hxz : Adj G x z) (hyz : Adj G y z) : False := by
  have hx' := lower_neighbor hfx hx
  have hy' := lower_neighbor hfy hy
  have hz' := lower_neighbor hfz hz
  have hab := hv.2.2
  by_cases hm : x = fork (!t) a b
  · subst x
    have hnY : y ≠ fork (!t) a b := fun he => adj_irrefl G _ (he ▸ hxy)
    have hnZ : z ≠ fork (!t) a b := fun he => adj_irrefl G _ (he ▸ hxz)
    exact no_adj_children hab (by tauto) (by tauto) hyz
  · have hcX : x = a ∨ x = b := by tauto
    have hmY : y = fork (!t) a b := by
      by_contra hn
      exact no_adj_children hab hcX (by tauto) hxy
    have hmZ : z = fork (!t) a b := by
      by_contra hn
      exact no_adj_children hab hcX (by tauto) hxz
    exact adj_irrefl G _ (hmY ▸ hmZ ▸ hyz)

#print axioms no_three_lower


lemma leaf_of_height_zero {x : Node V} (hx : height x = 0) : ∃ v, x = leaf v := by
  cases x with
  | leaf v => exact ⟨v,rfl⟩
  | fork t a b => simp [height] at hx

theorem cliqueFree (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    (graph G).CliqueFree 4 := by
  classical
  by_contra hn
  let f := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have ha (i j : Fin 4) (hij : i ≠ j) : Adj G (f i).val (f j).val :=
    f.map_rel_iff.mpr hij
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin 4 => height (f i).val) (by simp)
  have hm (i : Fin 4) : height (f i).val ≤ height (f j).val := hj i (by simp)
  cases he : (f j).val with
  | leaf v =>
    have hz (i : Fin 4) : height (f i).val = 0 := by
      have h := hm i
      simp only [he,height] at h
      omega
    choose a ha' using fun i => leaf_of_height_zero (hz i)
    have hb (i k : Fin 4) (hik : i ≠ k) : G.Adj (a i) (a k) := by
      have h := ha i k hik
      simpa only [ha' i,ha' k,adj_leaf] using h
    exact no_adj_common_neighbors hG (hb 0 1 (by decide)) (hb 0 2 (by decide))
      (hb 1 2 (by decide)) (hb 0 3 (by decide)) (hb 1 3 (by decide))
      (hb 2 3 (by decide))
  | fork t a b =>
    have hf (i : Fin 3) : Adj G (fork t a b) (f (j.succAbove i)).val := by
      simpa only [he] using ha j (j.succAbove i) (j.succAbove_ne i).symm
    have hm' (i : Fin 3) : height (f (j.succAbove i)).val ≤ height (fork t a b) := by
      simpa only [he] using hm (j.succAbove i)
    have hv : Valid G (fork t a b) := he ▸ (f j).property
    have hn' {i k : Fin 3} (hik : i ≠ k) : j.succAbove i ≠ j.succAbove k :=
      fun h => hik (Fin.succAbove_right_injective h)
    exact no_three_lower hv (hf 0) (hf 1) (hf 2) (hm' 0) (hm' 1) (hm' 2)
      (ha _ _ (hn' (by decide : (0 : Fin 3) ≠ 1)))
      (ha _ _ (hn' (by decide : (0 : Fin 3) ≠ 2)))
      (ha _ _ (hn' (by decide : (1 : Fin 3) ≠ 2)))

def embedding (G : SimpleGraph V) : G ↪g graph G where
  toFun v := ⟨leaf v,trivial⟩
  inj' := fun _ _ h => Node.leaf.inj (congrArg Subtype.val h)
  map_rel_iff' := by intro v w; exact adj_leaf G v w

/-- Every nonedge has an adjacent pair of common neighbors. This includes
pairs of equal vertices; the latter are harmless for maximality. -/
theorem diamond (G : SimpleGraph V) (a b : Vertex G) (hab : ¬(graph G).Adj a b) :
    ∃ p q : Vertex G, (graph G).Adj a p ∧ (graph G).Adj b p ∧
      (graph G).Adj a q ∧ (graph G).Adj b q ∧ (graph G).Adj p q := by
  let p : Vertex G := ⟨fork false a.val b.val,a.property,b.property,hab⟩
  let q : Vertex G := ⟨fork true a.val b.val,a.property,b.property,hab⟩
  refine ⟨p,q,?_,?_,?_,?_,?_⟩
  · exact Or.inr (Or.inl (Or.inl rfl))
  · exact Or.inr (Or.inl (Or.inr rfl))
  · exact Or.inr (Or.inl (Or.inl rfl))
  · exact Or.inr (Or.inl (Or.inr rfl))
  · exact Or.inr (Or.inr (Or.inr ⟨by decide,rfl,rfl⟩))

/-- The completion is maximal on its new carrier. -/
theorem maximal (G : SimpleGraph V) (H : SimpleGraph (Vertex G))
    (hle : graph G ≤ H) (hH : H.CliqueFree 4) : H = graph G := by
  apply le_antisymm ?_ hle
  intro a b hab
  by_contra hn
  obtain ⟨p,q,hap,hbp,haq,hbq,hpq⟩ := diamond G a b hn
  exact no_adj_common_neighbors hH hab (hle hap) (hle hbp) (hle haq) (hle hbq) (hle hpq)

#print axioms cliqueFree
#print axioms maximal

/-- All new edges use just 0 and 1; old colors are left literally unchanged. -/
def paint (c : Sym2 V → ℕ) : Node V → Node V → ℕ
  | leaf v, leaf w => c s(v,w)
  | a,b => if height a = height b then 1 else 0

lemma paint_symm (c : Sym2 V → ℕ) (a b : Node V) : paint c a b = paint c b a := by
  cases a <;> cases b <;> simp [paint,Sym2.eq_swap,eq_comm]

lemma paint_fork (c : Sym2 V → ℕ) (t : Bool) (a b x : Node V) :
    paint c (fork t a b) x = if height (fork t a b) = height x then 1 else 0 := by
  cases x <;> rfl

lemma paint_child (c : Sym2 V → ℕ) {t : Bool} {a b x : Node V}
    (hx : x = a ∨ x = b) : paint c (fork t a b) x = 0 := by
  have hh := child_height (show Child x (fork t a b) from hx)
  rw [paint_fork,if_neg (ne_of_gt hh)]

lemma paint_mate (c : Sym2 V → ℕ) (t : Bool) (a b : Node V) :
    paint c (fork t a b) (fork (!t) a b) = 1 := by
  simp [paint,height]

lemma paint_ne_lower (c : Sym2 V → ℕ) {G : SimpleGraph V}
    {t : Bool} {a b x y : Node V} (hv : Valid G (fork t a b))
    (hfx : Adj G (fork t a b) x) (hfy : Adj G (fork t a b) y)
    (hx : height x ≤ height (fork t a b)) (hy : height y ≤ height (fork t a b))
    (hxy : Adj G x y) : paint c (fork t a b) x ≠ paint c (fork t a b) y := by
  have hx' := lower_neighbor hfx hx
  have hy' := lower_neighbor hfy hy
  by_cases hm : x = fork (!t) a b
  · subst x
    have hnY : y ≠ fork (!t) a b := fun he => adj_irrefl G _ (he ▸ hxy)
    rw [paint_mate,paint_child c (show y = a ∨ y = b by tauto)]
    decide
  · have hcX : x = a ∨ x = b := by tauto
    have hmY : y = fork (!t) a b := by
      by_contra hn
      exact no_adj_children hv.2.2 hcX (by tauto) hxy
    subst y
    rw [paint_child c hcX,paint_mate]
    decide

lemma triangle_at_max {G : SimpleGraph V} (c : Sym2 V → ℕ)
    (hc : ∀ a b d, G.Adj a b → G.Adj a d → G.Adj b d →
      ¬(c s(a,b) = c s(a,d) ∧ c s(a,b) = c s(b,d)))
    (a b d : Vertex G) (hab : (graph G).Adj a b)
    (had : (graph G).Adj a d) (hbd : (graph G).Adj b d)
    (ha : height a.val ≤ height d.val) (hb : height b.val ≤ height d.val) :
    ¬(paint c a.val b.val = paint c a.val d.val ∧
      paint c a.val b.val = paint c b.val d.val) := by
  intro heq
  cases hd : d.val with
  | leaf v =>
    have haz : height a.val = 0 := by simp only [hd,height] at ha; omega
    have hbz : height b.val = 0 := by simp only [hd,height] at hb; omega
    obtain ⟨x,hx⟩ := leaf_of_height_zero haz
    obtain ⟨y,hy⟩ := leaf_of_height_zero hbz
    change Adj G a.val b.val at hab
    change Adj G a.val d.val at had
    change Adj G b.val d.val at hbd
    simp only [hx,hy,hd,adj_leaf] at hab had hbd
    exact hc x y v hab had hbd (by simpa only [hx,hy,hd,paint] using heq)
  | fork t x y =>
    have hv : Valid G (fork t x y) := hd ▸ d.property
    have he : paint c (fork t x y) a.val = paint c (fork t x y) b.val := by
      rw [paint_symm c _ a.val,paint_symm c _ b.val]
      simpa only [hd] using heq.1.symm.trans heq.2
    exact paint_ne_lower c hv (hd ▸ adj_symm had) (hd ▸ adj_symm hbd)
      (hd ▸ ha) (hd ▸ hb) hab he

def color (G : SimpleGraph V) (c : Sym2 V → ℕ) : Sym2 (Vertex G) → ℕ :=
  Sym2.lift ⟨fun a b => paint c a.val b.val,fun a b => paint_symm c a.val b.val⟩


/-- Any prescribed valid old edge coloring extends without relabeling it. -/
theorem color_valid (G : SimpleGraph V) (c : Sym2 V → ℕ)
    (hc : ∀ a b d, G.Adj a b → G.Adj a d → G.Adj b d →
      ¬(c s(a,b) = c s(a,d) ∧ c s(a,b) = c s(b,d))) :
    ∀ a b d, (graph G).Adj a b → (graph G).Adj a d → (graph G).Adj b d →
      ¬(color G c s(a,b) = color G c s(a,d) ∧ color G c s(a,b) = color G c s(b,d)) := by
  intro a b d hab had hbd he
  change paint c a.val b.val = paint c a.val d.val ∧
    paint c a.val b.val = paint c b.val d.val at he
  have hbmax (ha : height a.val ≤ height b.val) (hd : height d.val ≤ height b.val) : False := by
    apply triangle_at_max c hc a d b had hab hbd.symm ha hd
    exact ⟨he.1.symm,by rw [paint_symm c d.val b.val]; exact he.1.symm.trans he.2⟩
  by_cases ha : height a.val ≤ height d.val
  · by_cases hb : height b.val ≤ height d.val
    · exact triangle_at_max c hc a b d hab had hbd ha hb he
    · exact hbmax (ha.trans (le_of_not_ge hb)) (le_of_not_ge hb)
  · by_cases hb : height b.val ≤ height a.val
    · apply triangle_at_max c hc b d a hbd hab.symm had.symm hb (le_of_not_ge ha)
      constructor
      · rw [paint_symm c b.val a.val]
        exact he.2.symm
      · rw [paint_symm c d.val a.val]
        exact he.2.symm.trans he.1
    · exact hbmax (le_of_not_ge hb) ((le_of_not_ge ha).trans (le_of_not_ge hb))

@[simp] theorem color_old (G : SimpleGraph V) (c : Sym2 V → ℕ) (a b : V) :
    color G c s(embedding G a,embedding G b) = c s(a,b) := rfl

/-- Saturating all nonedges with diamonds changes no countable covering status. -/
theorem countable_cover_iff (G : SimpleGraph V) :
    IsCountableUnionOfTriangleFree (graph G) ↔ IsCountableUnionOfTriangleFree G := by
  constructor
  · exact countable_union_of_hom (embedding G).toHom
  · intro h
    obtain ⟨c,hc⟩ := (countable_union_iff_edge_coloring G).mp h
    exact (countable_union_iff_edge_coloring (graph G)).mpr ⟨color G c,color_valid G c hc⟩

/-- In particular, maximality can be imposed without either obtaining a
counterexample or proving a covering theorem. -/
theorem maximal_extension (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    ∃ (W : Type u) (H : SimpleGraph W), Nonempty (G ↪g H) ∧ H.CliqueFree 4 ∧
      (∀ K, H ≤ K → K.CliqueFree 4 → K = H) ∧
      (IsCountableUnionOfTriangleFree H ↔ IsCountableUnionOfTriangleFree G) :=
  ⟨Vertex G,graph G,⟨embedding G⟩,cliqueFree G hG,maximal G,countable_cover_iff G⟩

#print axioms color_valid
#print axioms countable_cover_iff
#print axioms maximal_extension
end Erdos595DiamondCompletion
