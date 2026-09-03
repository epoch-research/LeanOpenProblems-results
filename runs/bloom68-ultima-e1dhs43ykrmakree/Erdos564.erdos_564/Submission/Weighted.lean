import FormalConjecturesUtil

/-!
# Weighted vertex-online strategy transfer

A finite binary strategy exposes graph edges only at their latest endpoint. Its weight `J`
counts vertex introductions in the **entire unrolled tree**, not just along a play: query
weights add the weights of both children. A valid strategy forcing a monochromatic graph
`K_k` gives `Combinatorics.hypergraphRamsey 3 (k + 1) ≤ J + 1`.

Colors are Booleans (`false` = red, `true` = blue). The ambient triple coloring is defined
on all finsets, as in `Combinatorics.hypergraphRamsey`; only its values on triples matter.
-/

namespace WeightedVertexOnline

/-- A finite, fully unrolled strategy. At `query i`, the other endpoint is the latest vertex. -/
inductive MoveTree where
  | done : MoveTree
  | intro (child : MoveTree) : MoveTree
  | query (i : ℕ) (red blue : MoveTree) : MoveTree
  deriving DecidableEq, Repr

/-- Total number of introduction nodes, including introductions in both query branches. -/
def MoveTree.J : MoveTree → ℕ
  | .done => 0
  | .intro child => 1 + child.J
  | .query _ red blue => red.J + blue.J

/-- Selected vertices are the natural indices strictly below `v`.
The finite table records triples `(earlier endpoint, later endpoint, color)`. -/
structure State where
  v : ℕ
  edges : Finset (ℕ × ℕ × Bool)
  deriving DecidableEq

namespace State

/-- The empty initial position. -/
def empty : State := ⟨0, ∅⟩

/-- Introduce the new vertex with index `v`, leaving the color table unchanged. -/
def introduce (s : State) : State := ⟨s.v + 1, s.edges⟩

/-- Record an edge to the latest endpoint. Legality is imposed by `Valid`. -/
def expose (s : State) (i : ℕ) (b : Bool) : State :=
  ⟨s.v, insert (i, s.v - 1, b) s.edges⟩

/-- The table is an ordered, in-bounds, finite partial two-coloring. -/
def WellFormed (s : State) : Prop :=
  (∀ i j b, (i, j, b) ∈ s.edges → i < j ∧ j < s.v) ∧
  (∀ i j a b, (i, j, a) ∈ s.edges → (i, j, b) ∈ s.edges → a = b)

/-- An edge may not be queried twice. -/
def Fresh (s : State) (i : ℕ) : Prop :=
  ∀ b, (i, s.v - 1, b) ∉ s.edges

/-- A monochromatic graph clique using only already exposed edges. -/
def HasClique (s : State) (k : ℕ) : Prop :=
  ∃ K : Finset ℕ, K.card = k ∧ (∀ i ∈ K, i < s.v) ∧
    ∃ b : Bool, ∀ i ∈ K, ∀ j ∈ K, i < j → (i, j, b) ∈ s.edges

/-- Already exposed cliques remain available after a vertex introduction. -/
theorem HasClique.introduce {s : State} {k : ℕ} (h : s.HasClique k) :
    s.introduce.HasClique k := by
  obtain ⟨K, hK, hb, b, hm⟩ := h
  exact ⟨K, hK, fun i hi => Nat.lt_succ_of_lt (hb i hi), b, hm⟩

/-- A single exposed edge is a monochromatic `K₂`. -/
theorem hasClique_two {s : State} {b : Bool} (hv : 2 ≤ s.v)
    (he : (0, 1, b) ∈ s.edges) : s.HasClique 2 := by
  refine ⟨{0, 1}, by decide, ?_, b, ?_⟩
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    omega
  · intro i hi j hj hij
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    have hi0 : i = 0 := by omega
    have hj1 : j = 1 := by omega
    simpa only [hi0, hj1] using he

@[simp] theorem wellFormed_empty : empty.WellFormed := by
  simp [WellFormed, empty]

/-- Introduction preserves the partial-coloring condition. -/
theorem WellFormed.introduce {s : State} (h : s.WellFormed) :
    s.introduce.WellFormed := by
  refine ⟨?_, h.2⟩
  intro i j b he
  obtain ⟨hij, hj⟩ := h.1 i j b he
  exact ⟨hij, Nat.lt_succ_of_lt hj⟩

/-- A fresh, legal query preserves the partial-coloring condition. -/
theorem WellFormed.expose {s : State} (h : s.WellFormed) {i : ℕ}
    (hi : i < s.v - 1) (hf : s.Fresh i) (b : Bool) :
    (s.expose i b).WellFormed := by
  constructor
  · intro p q a he
    simp only [State.expose, Finset.mem_insert, Prod.mk.injEq] at he
    rcases he with ⟨rfl, rfl, rfl⟩ | he
    · exact ⟨hi, by change s.v - 1 < s.v; omega⟩
    · exact h.1 p q a he
  · intro p q a d ha hd
    simp only [State.expose, Finset.mem_insert, Prod.mk.injEq] at ha hd
    rcases ha with ⟨rfl, rfl, rfl⟩ | ha
    · rcases hd with ⟨_, _, rfl⟩ | hd
      · rfl
      · exact False.elim (hf d hd)
    · rcases hd with ⟨rfl, rfl, rfl⟩ | hd
      · exact False.elim (hf a ha)
      · exact h.2 p q a d ha hd

end State

/-- Recursive validity: every position is well formed; terminal positions have a `K_k`;
introductions increment `v`; queries use a fresh edge `(i, v-1)` with `i < v-1`, and
**both** possible answers must have valid continuations. -/
def Valid (k : ℕ) (s : State) : MoveTree → Prop
  | .done => s.WellFormed ∧ s.HasClique k
  | .intro child => s.WellFormed ∧ Valid k s.introduce child
  | .query i red blue => s.WellFormed ∧ i < s.v - 1 ∧ s.Fresh i ∧
      Valid k (s.expose i false) red ∧ Valid k (s.expose i true) blue

/-- A valid strategy from the empty position. -/
def Forces (k : ℕ) (T : MoveTree) : Prop := Valid k State.empty T

/-- Every valid position has an actual finite partial edge coloring. -/
theorem Valid.wellFormed {k : ℕ} {s : State} {T : MoveTree}
    (h : Valid k s T) : s.WellFormed := by
  cases T <;> exact h.1

section Simulation

variable {α : Type*} [DecidableEq α]

/-- A monochromatic complete triple hypergraph on exactly `n` ambient vertices. -/
def HasMonoTripleSet (c : Finset α → Bool) (n : ℕ) : Prop :=
  ∃ S : Finset α, S.card = n ∧
    ∃ b : Bool, ∀ e : Finset α, e ⊆ S → e.card = 3 → c e = b

/-- The reservoir invariant. The map is required to be injective only below `s.v`.
Every exposed edge controls all selected third vertices later than its second endpoint,
as well as every possible third vertex in the disjoint reservoir. -/
structure Realizes (c : Finset α → Bool) (s : State) (f : ℕ → α)
    (R : Finset α) : Prop where
  inj : ∀ ⦃i j : ℕ⦄, i < s.v → j < s.v → f i = f j → i = j
  disjoint : ∀ i, i < s.v → f i ∉ R
  later : ∀ i j b, (i, j, b) ∈ s.edges →
    ∀ l, j < l → l < s.v → c {f i, f j, f l} = b
  reservoir : ∀ i j b, (i, j, b) ∈ s.edges →
    ∀ x ∈ R, c {f i, f j, x} = b

/-- Pick a reservoir vertex, append it to the selected sequence, and remove it from the
reservoir. Old exposed edges already control this new selected third vertex. -/
theorem Realizes.introduce {c : Finset α → Bool} {s : State} {f : ℕ → α}
    {R : Finset α} (h : Realizes c s f R) (hw : s.WellFormed)
    {x : α} (hx : x ∈ R) :
    Realizes c s.introduce (Function.update f s.v x) (R.erase x) := by
  let g := Function.update f s.v x
  have hold (i : ℕ) (hi : i < s.v) : g i = f i := by
    exact Function.update_of_ne (Nat.ne_of_lt hi) x f
  have hnew : g s.v = x := Function.update_self s.v x f
  change Realizes c s.introduce g (R.erase x)
  constructor
  · intro i j hi hj he
    change i < s.v + 1 at hi
    change j < s.v + 1 at hj
    by_cases hi' : i < s.v
    · by_cases hj' : j < s.v
      · exact h.inj hi' hj' (by simpa only [hold i hi', hold j hj'] using he)
      · have hjv : j = s.v := by omega
        subst j
        have he' : f i = x := by simpa only [hold i hi', hnew] using he
        exact False.elim (h.disjoint i hi' (he'.symm ▸ hx))
    · have hiv : i = s.v := by omega
      subst i
      by_cases hj' : j < s.v
      · have he' : x = f j := by simpa only [hnew, hold j hj'] using he
        exact False.elim (h.disjoint j hj' (he' ▸ hx))
      · omega
  · intro i hi
    change i < s.v + 1 at hi
    by_cases hi' : i < s.v
    · rw [hold i hi']
      exact fun hm => h.disjoint i hi' (Finset.mem_of_mem_erase hm)
    · have hiv : i = s.v := by omega
      subst i
      rw [hnew]
      exact Finset.notMem_erase x R
  · intro i j b he l hjl hl
    obtain ⟨hij, hj⟩ := hw.1 i j b he
    rw [hold i (lt_trans hij hj), hold j hj]
    change l < s.v + 1 at hl
    by_cases hl' : l < s.v
    · rw [hold l hl']
      exact h.later i j b he l hjl hl'
    · have hlv : l = s.v := by omega
      subst l
      rw [hnew]
      exact h.reservoir i j b he x hx
  · intro i j b he y hy
    obtain ⟨hij, hj⟩ := hw.1 i j b he
    rw [hold i (lt_trans hij hj), hold j hj]
    exact h.reservoir i j b he y (Finset.mem_of_mem_erase hy)

/-- Retain the color class of a query. For the new edge there are no already selected
third vertices later than its latest endpoint; the remaining condition is exactly the filter. -/
theorem Realizes.expose {c : Finset α → Bool} {s : State} {f : ℕ → α}
    {R : Finset α} (h : Realizes c s f R) (i : ℕ) (b : Bool) :
    Realizes c (s.expose i b) f
      (R.filter (fun x => c {f i, f (s.v - 1), x} = b)) := by
  constructor
  · exact h.inj
  · intro j hj hx
    exact h.disjoint j hj (Finset.mem_filter.mp hx).1
  · intro p q a he l hql hl
    simp only [State.expose, Finset.mem_insert, Prod.mk.injEq] at he
    rcases he with ⟨rfl, rfl, rfl⟩ | he
    · change l < s.v at hl
      omega
    · exact h.later p q a he l hql hl
  · intro p q a he x hx
    simp only [State.expose, Finset.mem_insert, Prod.mk.injEq] at he
    rcases he with ⟨rfl, rfl, rfl⟩ | he
    · exact (Finset.mem_filter.mp hx).2
    · exact h.reservoir p q a he x (Finset.mem_filter.mp hx).1

omit [DecidableEq α] in
/-- The additive query budget: one color class can fund its own continuation plus one
final reservoir vertex. No factor-of-two or maximum-of-branches estimate is used. -/
theorem split_budget (R : Finset α) (d : α → Bool) (a b : ℕ)
    (h : a + b + 1 ≤ R.card) :
    a + 1 ≤ (R.filter (fun x => d x = false)).card ∨
      b + 1 ≤ (R.filter (fun x => d x = true)).card := by
  have hsum := Finset.card_filter_add_card_filter_not (s := R) (fun x => d x = false)
  have hsum' : (R.filter (fun x => d x = false)).card +
      (R.filter (fun x => d x = true)).card = R.card := by
    simpa using hsum
  omega

/-- Every three-element finite set of indices has a strictly increasing enumeration. -/
lemma ordered_triple {S : Finset ℕ} (hS : S.card = 3) :
    ∃ i j l : ℕ, i < j ∧ j < l ∧ S = {i, j, l} := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS
  rcases lt_or_gt_of_ne hab with hab | hba
  · rcases lt_or_gt_of_ne hbc with hbc | hcb
    · exact ⟨a, b, c, hab, hbc, rfl⟩
    · rcases lt_or_gt_of_ne hac with hac | hca
      · exact ⟨a, c, b, hac, hcb, by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
      · exact ⟨c, a, b, hca, hab, by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
  · rcases lt_or_gt_of_ne hac with hac | hca
    · exact ⟨b, a, c, hba, hac, by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    · rcases lt_or_gt_of_ne hbc with hbc | hcb
      · exact ⟨b, c, a, hbc, hca, by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
      · exact ⟨c, b, a, hcb, hba, by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩

/-- To check the triples of an injective finite image, it suffices to check increasing
triples of indices. The pullback finset has exactly three elements by injectivity. -/
lemma mono_image_of_ordered_triples {c : Finset α → Bool} {K : Finset ℕ}
    {f : ℕ → α} {b : Bool} (hf : Set.InjOn f (K : Set ℕ))
    (hm : ∀ i ∈ K, ∀ j ∈ K, ∀ l ∈ K,
      i < j → j < l → c {f i, f j, f l} = b) :
    ∀ e : Finset α, e ⊆ K.image f → e.card = 3 → c e = b := by
  intro e he hecard
  obtain ⟨D, hDK, hDe⟩ := Finset.subset_image_iff.mp he
  have hfD : Set.InjOn f (D : Set ℕ) := by
    intro i hi j hj hij
    exact hf (hDK hi) (hDK hj) hij
  have hDcard : D.card = 3 := by
    rw [← Finset.card_image_iff.mpr hfD, hDe]
    exact hecard
  obtain ⟨i, j, l, hij, hjl, hD⟩ := ordered_triple hDcard
  have hi : i ∈ K := hDK (by simp [hD])
  have hj : j ∈ K := hDK (by simp [hD])
  have hl : l ∈ K := hDK (by simp [hD])
  rw [← hDe, hD]
  simpa using hm i hi j hj l hl hij hjl

/-- A terminal graph clique and one reservoir point give a monochromatic triple clique
of size `k+1`, including when `k` is smaller than three. -/
theorem terminal_transfer {c : Finset α → Bool} {s : State} {f : ℕ → α}
    {R : Finset α} {k : ℕ} (hw : s.WellFormed) (hk : s.HasClique k)
    (h : Realizes c s f R) (hR : R.Nonempty) : HasMonoTripleSet c (k + 1) := by
  obtain ⟨x, hx⟩ := hR
  obtain ⟨K, hKcard, hKbound, b, hKmono⟩ := hk
  let g := Function.update f s.v x
  have hg : Realizes c s.introduce g (R.erase x) := h.introduce hw hx
  let L := insert s.v K
  have hvnot : s.v ∉ K := by
    intro hv
    exact (Nat.lt_irrefl s.v) (hKbound s.v hv)
  have hLcard : L.card = k + 1 := by
    simp [L, Finset.card_insert_of_notMem hvnot, hKcard]
  have hLbound : ∀ i ∈ L, i < s.v + 1 := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · omega
    · have := hKbound i hi
      omega
  have hinj : Set.InjOn g (L : Set ℕ) := by
    intro i hi j hj heq
    exact hg.inj (hLbound i hi) (hLbound j hj) heq
  refine ⟨L.image g, (Finset.card_image_iff.mpr hinj).trans hLcard, b, ?_⟩
  apply mono_image_of_ordered_triples hinj
  intro i hi j hj l hl hij hjl
  have hlbound := hLbound l hl
  have hibound : i < s.v := by omega
  have hjbound : j < s.v := by omega
  have hiK : i ∈ K := (Finset.mem_insert.mp hi).resolve_left (Nat.ne_of_lt hibound)
  have hjK : j ∈ K := (Finset.mem_insert.mp hj).resolve_left (Nat.ne_of_lt hjbound)
  exact hg.later i j b (hKmono i hiK j hjK hij) l hjl hlbound

/-- Weighted reservoir simulation from any valid intermediate state, on any ambient type.
An initial reservoir of size at least `T.J + 1` suffices, independent of the triple coloring. -/
theorem simulate {c : Finset α → Bool} {k : ℕ} (T : MoveTree) :
    ∀ {s : State} {f : ℕ → α} {R : Finset α},
      Valid k s T → Realizes c s f R → T.J + 1 ≤ R.card →
      HasMonoTripleSet c (k + 1) := by
  induction T with
  | done =>
      intro s f R hv hr hb
      exact terminal_transfer hv.1 hv.2 hr (Finset.card_pos.mp (by simpa [MoveTree.J] using hb))
  | intro child ih =>
      intro s f R hv hr hb
      obtain ⟨x, hx⟩ : R.Nonempty := Finset.card_pos.mp (by
        simp only [MoveTree.J] at hb
        omega)
      have hbudget : child.J + 1 ≤ (R.erase x).card := by
        rw [Finset.card_erase_of_mem hx]
        simp only [MoveTree.J] at hb
        omega
      exact ih hv.2 (hr.introduce hv.1 hx) hbudget
  | query i red blue ihr ihb =>
      intro s f R hv hr hb
      obtain ⟨hw, hi, hf, hred, hblue⟩ := hv
      rcases split_budget R (fun x => c {f i, f (s.v - 1), x}) red.J blue.J hb with h | h
      · exact ihr hred (hr.expose i false) h
      · exact ihb hblue (hr.expose i true) h

end Simulation

/-- **Generic weighted vertex-online transfer.** The weight counts every introduction
in the unrolled strategy tree, and no particular strategy or graph Ramsey bound is assumed. -/
theorem weighted_transfer {k : ℕ} {T : MoveTree} (hT : Forces k T) :
    Combinatorics.hypergraphRamsey 3 (k + 1) ≤ T.J + 1 := by
  apply Nat.sInf_le
  intro c
  let f : ℕ → Fin (T.J + 1) := fun _ => ⟨0, by omega⟩
  have hr : Realizes c State.empty f Finset.univ := by
    constructor
    · intro i j hi
      simp [State.empty] at hi
    · intro i hi
      simp [State.empty] at hi
    · intro i j b he
      simp [State.empty] at he
    · intro i j b he
      simp [State.empty] at he
  exact simulate T hT hr (by simp)

/- Concrete nonvacuity and branch-weight checks. -/

namespace Examples

/-- Introduce `n` more vertices before terminating. -/
def finishAfter : ℕ → MoveTree
  | 0 => .done
  | n + 1 => .intro (finishAfter n)

@[simp] theorem finishAfter_J (n : ℕ) : (finishAfter n).J = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [finishAfter, MoveTree.J, ih, Nat.add_comm]

/-- Delaying termination is legal when an exposed clique is already present. -/
theorem finishAfter_valid (n : ℕ) {k : ℕ} {s : State}
    (hw : s.WellFormed) (hk : s.HasClique k) : Valid k s (finishAfter n) := by
  induction n generalizing s with
  | zero => exact ⟨hw, hk⟩
  | succ n ih => exact ⟨hw, ih hw.introduce hk.introduce⟩

/-- Introduce two vertices and query their edge. Optionally introduce `r` more vertices
on the red branch and `b` more on the blue branch. Both answers force a graph `K₂`. -/
def edgeStrategy (r b : ℕ) : MoveTree :=
  .intro (.intro (.query 0 (finishAfter r) (finishAfter b)))

theorem edgeStrategy_forces (r b : ℕ) : Forces 2 (edgeStrategy r b) := by
  let s := State.empty.introduce.introduce
  have hw : s.WellFormed := State.wellFormed_empty.introduce.introduce
  have hi : 0 < s.v - 1 := by decide
  have hf : s.Fresh 0 := by
    simp [s, State.Fresh, State.introduce, State.empty]
  have hc (c : Bool) : (s.expose 0 c).HasClique 2 := by
    apply State.hasClique_two (b := c) (by change 2 ≤ 2; decide)
    simp [s, State.expose, State.introduce, State.empty]
  refine ⟨State.wellFormed_empty, State.wellFormed_empty.introduce, hw, hi, hf, ?_, ?_⟩
  · exact finishAfter_valid r (hw.expose hi hf false) (hc false)
  · exact finishAfter_valid b (hw.expose hi hf true) (hc true)

/-- The two post-query introduction counts add, even though a play visits only one branch. -/
@[simp] theorem edgeStrategy_J (r b : ℕ) : (edgeStrategy r b).J = 2 + r + b := by
  simp only [edgeStrategy, MoveTree.J, finishAfter_J]
  omega

/-- The smallest nontrivial query strategy has weight two. -/
def singleEdge : MoveTree := edgeStrategy 0 0

theorem singleEdge_forces : Forces 2 singleEdge := edgeStrategy_forces 0 0

@[simp] theorem singleEdge_J : singleEdge.J = 2 := by
  simp [singleEdge]

/-- Applying the transfer to a real query strategy gives a monochromatic ambient triple. -/
theorem ramsey_three_le_three : Combinatorics.hypergraphRamsey 3 3 ≤ 3 := by
  simpa using weighted_transfer singleEdge_forces

/-- Two initial introductions, then one red-branch and two blue-branch introductions:
the unrolled weight is five, although the longer play has only four introductions. -/
theorem branching_weight_check : (edgeStrategy 1 2).J = 5 := by simp

/-- This instance also exercises simulation with nonzero, unequal child budgets. -/
theorem branching_transfer_check : Combinatorics.hypergraphRamsey 3 3 ≤ 6 := by
  simpa using weighted_transfer (edgeStrategy_forces 1 2)

end Examples

end WeightedVertexOnline

#print axioms WeightedVertexOnline.weighted_transfer
#print axioms WeightedVertexOnline.simulate
#print axioms WeightedVertexOnline.Examples.edgeStrategy_forces
#print axioms WeightedVertexOnline.Examples.ramsey_three_le_three
