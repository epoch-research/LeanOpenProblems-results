import Submission.TreeParityKernel

/-!
# A counterexample to exact unrooted parity kernels

Join two hubs. Attach seven supports to each hub, and two leaves to each support.
The tree has 44 vertices, 43 edges, color classes of size 22, and maximum degree 8.
An exact c=19 kernel would have core size at most 6, which is impossible.

The proof locates the connected core in zero, one, or both hub sides and uses
local three-vertex count inequalities. Finite auxiliary facts use kernel-checked
`decide`; no `native_decide`, extra axioms, or shared-file changes are used.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 1000
open Finset SimpleGraph TreeParityKernel TreeParityKernel.Part
namespace TreeExactKernelCounterexample

abbrev V := Bool × Option (Fin 7 × Fin 3)
def hub (b : Bool) : V := (b, none)
def arm (b : Bool) (i : Fin 7) (j : Fin 3) : V := (b, some (i,j))

def adj (x y : V) : Prop :=
  match x.2, y.2 with
  | none, none => x.1 ≠ y.1
  | none, some (_,j) => x.1 = y.1 ∧ j = 0
  | some (_,j), none => x.1 = y.1 ∧ j = 0
  | some (i,j), some (k,l) => x.1 = y.1 ∧ i = k ∧
      ((j = 0 ∧ l ≠ 0) ∨ (j ≠ 0 ∧ l = 0))
instance : DecidableRel adj := fun x y => by unfold adj; split <;> infer_instance

def T : SimpleGraph V where
  Adj := adj
  symm := by change ∀ x y : V, adj x y → adj y x; decide
  loopless := by change ∀ x : V, ¬ adj x x; decide
instance : DecidableRel T.Adj := inferInstanceAs (DecidableRel adj)

lemma hh (b : Bool) : T.Adj (hub b) (hub (!b)) := by cases b <;> decide
lemma ha (b : Bool) (i : Fin 7) : T.Adj (hub b) (arm b i 0) := by simp [T, adj, hub, arm]
lemma al (b : Bool) (i : Fin 7) (j : Fin 3) (hj : j ≠ 0) :
    T.Adj (arm b i 0) (arm b i j) := by simp [T, adj, arm, hj]

lemma toHub (x : V) : T.Reachable x (hub x.1) := by
  rcases x with ⟨b, o⟩
  cases o with
  | none => exact .rfl
  | some a =>
    rcases a with ⟨i,j⟩
    by_cases hj : j = 0
    · subst j
      exact (ha b i).symm.reachable
    · exact (al b i j hj).symm.reachable.trans (ha b i).symm.reachable

theorem connected : T.Connected := by
  refine ⟨fun x y => ?_⟩
  apply (toHub x).trans
  apply Reachable.trans (v := hub y.1) _ (toHub y).symm
  by_cases h : x.1 = y.1
  · rw [h]
  · have : y.1 = !x.1 := by revert h; cases x.1 <;> cases y.1 <;> simp
    rw [this]
    exact (hh x.1).reachable

theorem card_vertices : Fintype.card V = 44 := by decide

theorem edge_card : T.edgeFinset.card = 43 := by decide

theorem isTree : T.IsTree := by
  apply isTree_iff_connected_and_card.mpr
  refine ⟨connected, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide

def color (x : V) : Bool := match x.2 with
  | none => x.1
  | some (_,j) => if j = 0 then !x.1 else x.1

def coloring : T.Coloring Bool := Coloring.mk color (by decide)

theorem color_card : ∀ b : Bool,
    (univ.filter (fun x => coloring x = b)).card = 22 := by decide

-- Local count algebra.
def ind (p q : Part) : ℕ := if p = q then 1 else 0
def armCount (f : V → Part) (p : Part) (b : Bool) (i : Fin 7) : ℕ :=
  ∑ j, ind (f (arm b i j)) p
def sideCount (f : V → Part) (p : Part) (b : Bool) : ℕ :=
  ∑ i, armCount f p b i

lemma count_ind (f : V → Part) (p : Part) : count f p = ∑ x, ind (f x) p := by
  classical
  rw [count, number_eq_sum]
  apply sum_congr rfl
  intro x _
  by_cases h : f x = p <;> simp [ind, h]

lemma count_split (f : V → Part) (p : Part) (b : Bool) :
    count f p = ind (f (hub b)) p + ind (f (hub (!b))) p +
      sideCount f p b + sideCount f p (!b) := by
  classical
  simp only [count_ind, Fintype.sum_prod_type, Fintype.sum_option,
    Fintype.sum_bool]
  cases b <;> simp only [Bool.not_false, Bool.not_true, hub, sideCount, armCount, arm]
  all_goals omega

lemma arm_three (f : V → Part) (p : Part) (b : Bool) (i : Fin 7) :
    armCount f p b i = ind (f (arm b i 0)) p + ind (f (arm b i 1)) p +
      ind (f (arm b i 2)) p := Fin.sum_univ_three _

lemma ind_zero_iff (p q : Part) : ind p q = 0 ↔ p ≠ q := by simp [ind]

lemma even_hub_arm {f : V → Part} (he : GoodEdges T f) {b : Bool}
    (hb : f (hub b) = even) (i : Fin 7) : armCount f odd b i = 1 := by
  have h0 := (he (ha b i)).1 hb
  have h1 := (he (al b i 1 (by decide))).2 h0
  have h2 := (he (al b i 2 (by decide))).2 h0
  simp [arm_three, ind, h0, h1, h2]

lemma odd_hub_arm {f : V → Part} (he : GoodEdges T f) {b : Bool}
    (hb : f (hub b) = odd) (i : Fin 7) (h0c : f (arm b i 0) ≠ core) :
    armCount f odd b i = 2 := by
  have h0n := (he (ha b i)).2 hb
  have h0 : f (arm b i 0) = even := by cases h : f (arm b i 0) <;> simp_all
  have h1 := (he (al b i 1 (by decide))).1 h0
  have h2 := (he (al b i 2 (by decide))).1 h0
  simp [arm_three, ind, h0, h1, h2]

lemma core_hub_arm {f : V → Part} (he : GoodEdges T f) {b : Bool}
    (hb : f (hub b) = core) (i : Fin 7) :
    armCount f odd b i ≤ 1 + armCount f core b i ∧
    3 ≤ 3 * armCount f odd b i + armCount f core b i := by
  have h0 := he (ha b i).symm
  have h1 := he (al b i 1 (by decide))
  have h2 := he (al b i 2 (by decide))
  have h1' := he (al b i 1 (by decide)).symm
  have h2' := he (al b i 2 (by decide)).symm
  rw [arm_three, arm_three]
  cases e0 : f (arm b i 0) <;> cases e1 : f (arm b i 1) <;>
    cases e2 : f (arm b i 2) <;> simp_all [ind]

-- Connectivity is used only to locate the core, not to require a chosen root.
lemma const_of_reachable {A B : Type} {G : SimpleGraph A} (g : A → B)
    (he : ∀ {x y}, G.Adj x y → g x = g y) {x y : A} (hr : G.Reachable x y) :
    g x = g y := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => rfl
  | cons h p ih => exact (he h).trans ih

lemma adj_same_side : ∀ (b : Bool) (x y : V), x ≠ hub (!b) → y ≠ hub (!b) →
    T.Adj x y → x.1 = y.1 := by decide

def branch (x : V) : Bool × Fin 7 := (x.1, (x.2.getD (0,0)).1)

lemma adj_same_branch : ∀ (x y : V), x.2 ≠ none → y.2 ≠ none →
    T.Adj x y → branch x = branch y := by decide

lemma core_side {f : V → Part} (hc : (T.induce {x | f x = core}).Connected)
    {b : Bool} (hb : f (hub b) = core) (hnb : f (hub (!b)) ≠ core) :
    ∀ x, f x = core → x.1 = b := by
  intro x hx
  have he {v w : {x | f x = core}}
      (ha : (T.induce {x | f x = core}).Adj v w) : v.val.1 = w.val.1 := by
    apply adj_same_side b v.val w.val
    · intro h; exact hnb (h ▸ v.property)
    · intro h; exact hnb (h ▸ w.property)
    · exact ha
  have hh := const_of_reachable (fun v : {x | f x = core} => v.val.1)
    he (hc.preconnected ⟨hub b, hb⟩ ⟨x, hx⟩)
  exact hh.symm

lemma core_one_arm {f : V → Part} (hc : (T.induce {x | f x = core}).Connected)
    (hne : ∃ x, f x = core) (hh : ∀ b, f (hub b) ≠ core) :
    ∃ b i, ∀ (s : Bool) (k : Fin 7) (j : Fin 3),
      f (arm s k j) = core → s = b ∧ k = i := by
  obtain ⟨⟨b,o⟩, hx⟩ := hne
  cases o with
  | none => exact (hh b hx).elim
  | some a =>
    rcases a with ⟨i,j⟩
    refine ⟨b, i, ?_⟩
    have hno (v : {x | f x = core}) : v.val.2 ≠ none := by
      intro ho
      have heq : v.val = hub v.val.1 := by
        exact Prod.ext rfl ho
      exact hh v.val.1 (heq ▸ v.property)
    have he {v w : {x | f x = core}}
        (ha : (T.induce {x | f x = core}).Adj v w) : branch v.val = branch w.val :=
      adj_same_branch v.val w.val (hno v) (hno w) ha
    intro s k l hl
    have hh' := const_of_reachable (fun v : {x | f x = core} => branch v.val)
      he (hc.preconnected ⟨arm s k l, hl⟩ ⟨arm b i j, hx⟩)
    simpa [branch, arm, Prod.mk.injEq] using hh'

lemma side_erase_lower (f : V → Part) (p : Part) (b : Bool) (i : Fin 7) (a : ℕ)
    (hh : ∀ k, k ≠ i → a ≤ armCount f p b k) : 6 * a ≤ sideCount f p b := by
  classical
  calc
    6 * a = ∑ _k ∈ (univ : Finset (Fin 7)).erase i, a := by simp
    _ ≤ ∑ k ∈ (univ : Finset (Fin 7)).erase i, armCount f p b k :=
      sum_le_sum (fun k hk => hh k (mem_erase.mp hk).1)
    _ ≤ sideCount f p b := sum_le_sum_of_subset (erase_subset i univ)

lemma both_hubs_bound {f : V → Part} (he : GoodEdges T f)
    (hh : ∀ b, f (hub b) = core) : count f odd + 2 ≤ 14 + count f core := by
  have hs (b : Bool) : sideCount f odd b ≤ 7 + sideCount f core b := by
    have h := sum_le_sum (fun i (_hi : i ∈ (univ : Finset (Fin 7))) =>
      (core_hub_arm he (hh b) i).1)
    simpa [sideCount, sum_add_distrib] using h
  have ho := count_split f odd false
  have hr := count_split f core false
  simp only [Bool.not_false, hh, ind, if_pos, reduceCtorEq, if_false] at ho hr
  have := hs false
  have := hs true
  omega

lemma one_hub_bound {f : V → Part} (he : GoodEdges T f)
    (hc : (T.induce {x | f x = core}).Connected) {b : Bool}
    (hb : f (hub b) = core) (hnb : f (hub (!b)) ≠ core) :
    67 ≤ 3 * count f odd + count f core := by
  have hs := core_side hc hb hnb
  have hnodd : f (hub (!b)) = odd := by
    have hedge := (he (hh b).symm).1
    cases h : f (hub (!b)) <;> simp_all
  have hnc (i : Fin 7) (j : Fin 3) : f (arm (!b) i j) ≠ core := by
    intro h
    have hh' := hs _ h
    change (!b) = b at hh'
    cases b <;> simp_all
  have hotherU : sideCount f odd (!b) = 14 := by
    simp [sideCount, odd_hub_arm he hnodd, hnc]
  have hotherR : sideCount f core (!b) = 0 := by
    simp [sideCount, armCount, ind, hnc]
  have hsum : 21 ≤ 3 * sideCount f odd b + sideCount f core b := by
    have h := sum_le_sum (fun i (_hi : i ∈ (univ : Finset (Fin 7))) =>
      (core_hub_arm he hb i).2)
    simpa [sideCount, sum_add_distrib, ← mul_sum] using h
  have hu := count_split f odd b
  have hr := count_split f core b
  simp [hb, hnodd, ind, hotherU, hotherR] at hu hr
  omega

lemma no_hub_bound {f : V → Part} (he : GoodEdges T f)
    (hc : (T.induce {x | f x = core}).Connected) (hne : ∃ x, f x = core)
    (hh : ∀ b, f (hub b) ≠ core) : 20 ≤ count f odd := by
  obtain ⟨b,i,hlocal⟩ := core_one_arm hc hne hh
  have hother (k : Fin 7) : f (arm (!b) k 0) ≠ core := by
    intro h
    have hb := (hlocal _ _ _ h).1
    cases b <;> simp_all
  have hrest (k : Fin 7) (hk : k ≠ i) : f (arm b k 0) ≠ core := by
    intro h
    exact hk (hlocal _ _ _ h).2
  have hu := count_split f odd b
  have hbnot := hh b
  cases hb : f (hub b) with
  | core => exact (hbnot hb).elim
  | odd =>
    have hneigh := (he (TreeExactKernelCounterexample.hh b)).2 hb
    have hnnot := hh (!b)
    have hnb : f (hub (!b)) = even := by
      cases hn : f (hub (!b)) <;> simp_all
    have ho : sideCount f odd (!b) = 7 := by
      simp [sideCount, even_hub_arm he hnb]
    have hr : 12 ≤ sideCount f odd b := by
      apply side_erase_lower f odd b i 2
      intro k hk
      exact (odd_hub_arm he hb k (hrest k hk)).ge
    simp [hb, hnb, ind, ho] at hu
    omega
  | even =>
    have hnb := (he (TreeExactKernelCounterexample.hh b)).1 hb
    have ho : sideCount f odd (!b) = 14 := by
      simp [sideCount, odd_hub_arm he hnb, hother]
    have hr : 6 ≤ sideCount f odd b := by
      apply side_erase_lower f odd b i 1
      intro k _
      exact (even_hub_arm he hb k).ge
    simp [hb, hnb, ind, ho] at hu
    omega

lemma no_exact_labels (f : V → Part) (he : GoodEdges T f)
    (hc : (T.induce {x | f x = core}).Connected) (hne : ∃ x, f x = core)
    (hsize : count f core ≤ 6) (hodd : count f odd = 19) : False := by
  by_cases h : ∃ b, f (hub b) = core
  · obtain ⟨b,hb⟩ := h
    by_cases hn : f (hub (!b)) = core
    · have hh' : ∀ s, f (hub s) = core := by
        intro s
        by_cases hs : s = b
        · simpa [hs] using hb
        · have hsn : s = !b := by revert hs; cases s <;> cases b <;> simp
          simpa [hsn] using hn
      have := both_hubs_bound he hh'
      omega
    · have := one_hub_bound he hc hb hn
      omega
  · have hn : ∀ b, f (hub b) ≠ core := by simpa using h
    have := no_hub_bound he hc hne hn
    omega

/-- The exact unrooted conjecture fails on this 44-vertex tree at c=19. -/
theorem no_exact_unrooted : ¬ ∃ R U W : Finset V,
    IsParityKernel T 19 R U W ∧ U.card = 19 := by
  classical
  rintro ⟨R,U,W,h,hUcard⟩
  let f : V → Part := fun x => if x ∈ R then core else if x ∈ U then odd else even
  have hparts (x : V) : x ∈ R ∨ x ∈ U ∨ x ∈ W := by
    have hx := mem_univ x
    rw [← h.partition] at hx
    simpa only [mem_union, or_assoc] using hx
  have hfR (x : V) : f x = core ↔ x ∈ R := by
    by_cases hr : x ∈ R <;> by_cases hu : x ∈ U <;> simp [f, hr, hu]
  have hfU (x : V) : f x = odd ↔ x ∈ U := by
    by_cases hx : x ∈ R
    · have hxu : x ∉ U := fun hu => disjoint_left.mp h.disjointRU hx hu
      simp [f, hx, hxu]
    · simp [f, hx]
  have hfW (x : V) : f x = even ↔ x ∈ W := by
    by_cases hr : x ∈ R
    · have hw : x ∉ W := fun hw => disjoint_left.mp h.disjointRW hr hw
      simp [f, hr, hw]
    · by_cases hu : x ∈ U
      · have hw : x ∉ W := fun hw => disjoint_left.mp h.disjointUW hu hw
        simp [f, hr, hu, hw]
      · have hw := ((hparts x).resolve_left hr).resolve_left hu
        simp [f, hr, hu, hw]
  have he : GoodEdges T f := by
    intro x y hxy
    constructor
    · intro hx
      apply (hfU y).mpr
      exact h.neighbors x ((hfW x).mp hx) hxy
    · intro hx hy
      exact h.independent ((hfU x).mp hx) ((hfU y).mp hy) hxy.ne hxy
  have hset : {x | f x = core} = (R : Set V) := by ext x; exact hfR x
  have hconn : (T.induce {x | f x = core}).Connected := by
    rw [hset]
    exact h.connected
  have hne : ∃ x, f x = core := by
    obtain ⟨x,hx⟩ := h.nonempty
    exact ⟨x,(hfR x).mpr hx⟩
  have hr : count f core = R.card := by
    unfold count number
    congr 1
    ext x
    simp [hfR]
  have hu : count f odd = 19 := by
    rw [← hUcard]
    unfold count number
    congr 1
    ext x
    simp [hfU]
  have hsmall := h.core_card_bound
  rw [card_vertices] at hsmall
  exact no_exact_labels f he hconn hne (by omega) hu

/-- The old at-most conclusion is sharp: no kernel at c=19 uses more than 18 odd
vertices, and `at_most_witness` below attains 18. -/
theorem odd_le_eighteen {R U W : Finset V} (h : IsParityKernel T 19 R U W) :
    U.card ≤ 18 := by
  have hn : U.card ≠ 19 := fun he => no_exact_unrooted ⟨R,U,W,h,he⟩
  have hu := h.odd_le
  omega

theorem maximum_degree : (∀ x, T.degree x ≤ 8) ∧ T.degree (hub false) = 8 := by decide

/-- An at-most kernel with 18 odd vertices still removes exactly 38 vertices. -/
def witnessLabel (x : V) : Part := match x.2 with
  | none => core
  | some (i,j) =>
      if x.1 = false ∧ i.val < 4 then
        if j = 0 then core else odd
      else if j = 0 then odd else even

def witnessR : Finset V := univ.filter (fun x => witnessLabel x = core)
def witnessU : Finset V := univ.filter (fun x => witnessLabel x = odd)
def witnessW : Finset V := univ.filter (fun x => witnessLabel x = even)

theorem at_most_witness : IsParityKernel T 19 witnessR witnessU witnessW ∧
    witnessR.card = 6 ∧ witnessU.card = 18 ∧ witnessW.card = 20 := by
  refine ⟨?_, by decide, by decide, by decide⟩
  refine { disjointRU := by decide
           disjointRW := by decide
           disjointUW := by decide
           partition := ?_
           nonempty := by decide
           connected := by decide
           independent := ?_
           neighbors := ?_
           odd_le := by decide
           outside_ge := by decide }
  · ext x
    cases h : witnessLabel x <;> simp [witnessR, witnessU, witnessW, h]
  · change ∀ x ∈ witnessU, ∀ y ∈ witnessU, x ≠ y → ¬ T.Adj x y
    decide
  · change ∀ w ∈ witnessW, ∀ x, T.Adj w x → x ∈ witnessU
    decide

theorem admissible : 1 ≤ (19 : ℕ) ∧ 19 ≤ 22 ∧ 19 ≤ 43 / 2 := by decide

#print axioms isTree
#print axioms color_card
#print axioms no_exact_unrooted
#print axioms odd_le_eighteen
#print axioms maximum_degree
#print axioms at_most_witness
end TreeExactKernelCounterexample
