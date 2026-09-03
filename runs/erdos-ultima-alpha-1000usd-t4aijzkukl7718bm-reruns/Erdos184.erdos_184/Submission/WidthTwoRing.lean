import Submission.CycleRing

/-!
Explicit two-cycle decomposition of the all-crossing width-two ring.
This is auxiliary work, not a bound for arbitrary graphs.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.WidthTwoRing

lemma cycle_adj_nat {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    (cycleGraph n).Adj i j ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
      (i.val = 0 ∧ j.val + 1 = n) ∨ (j.val = 0 ∧ i.val + 1 = n) := by
  rw [cycleGraph_adj', Fin.val_sub, Fin.val_sub]
  have hi := i.isLt
  have hj := j.isLt
  by_cases hij : i.val < j.val
  · have h1 : n - j.val + i.val < n := by omega
    have h2 : n ≤ n - i.val + j.val := by omega
    have h3 : n - i.val + j.val < 2*n := by omega
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_sub_mod h2,
      Nat.mod_eq_of_lt (show n - i.val + j.val - n < n by omega)]
    omega
  · by_cases hji : j.val < i.val
    · have h1 : n - i.val + j.val < n := by omega
      have h2 : n ≤ n - j.val + i.val := by omega
      rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_sub_mod h2,
        Nat.mod_eq_of_lt (show n - j.val + i.val - n < n by omega)]
      omega
    · have hij' : i.val = j.val := by omega
      simp only [hij', Nat.sub_add_cancel (Nat.le_of_lt hj), Nat.mod_self]
      omega

abbrev Vertex (r : ℕ) := Fin (r+3) ⊕ Fin (r+3)

def interface {r : ℕ} : Vertex r → Fin (r+3) := Sum.elim id id

/-- The graph with all four cross edges between consecutive interfaces. -/
def graph (r : ℕ) : SimpleGraph (Vertex r) :=
  (cycleGraph (r+3)).comap interface

/-- The snake order: ascend along one side, descend along the other side. -/
def snake (r : ℕ) : Vertex r ≃ Fin ((r+3)+(r+3)) :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.neg _)).trans finSumFinEquiv

@[simp] lemma snake_left (r : ℕ) (i : Fin (r+3)) :
    (snake r (.inl i)).val = i.val := by simp [snake]

@[simp] lemma snake_right (r : ℕ) (i : Fin (r+3)) :
    (snake r (.inr i)).val = (r+3) + if i = 0 then 0 else r+3-i.val := by
  simp [snake, Fin.val_neg, Nat.add_comm]

/-- The first spanning cycle is a relabeled ordinary cycle graph. -/
def red (r : ℕ) : SimpleGraph (Vertex r) :=
  (cycleGraph ((r+3)+(r+3))).comap (snake r)

lemma red_connected (r : ℕ) : (red r).Connected :=
  (SimpleGraph.Iso.comap (snake r) _).connected_iff.mpr cycleGraph_connected

lemma red_regular (r : ℕ) : (red r).IsRegularOfDegree 2 := by
  intro v
  have h := (SimpleGraph.Iso.comap (snake r) (cycleGraph ((r+3)+(r+3)))).degree_eq v
  have hd : (cycleGraph ((r+3)+(r+3))).degree (snake r v) = 2 :=
    cycleGraph_degree_three_le
  simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h hd ⊢
  exact h.symm.trans hd

/-- An explicit description of the snake edges on one side. -/
lemma red_left_left (r : ℕ) (i j : Fin (r+3)) :
    (red r).Adj (.inl i) (.inl j) ↔
      i.val+1=j.val ∨ j.val+1=i.val := by
  change (cycleGraph _).Adj (snake r (.inl i)) (snake r (.inl j)) ↔ _
  rw [cycle_adj_nat (by omega), snake_left, snake_left]
  have hi := i.isLt
  have hj := j.isLt
  omega

lemma red_left_right (r : ℕ) (i j : Fin (r+3)) :
    (red r).Adj (.inl i) (.inr j) ↔
      (i.val = r+2 ∧ j = 0) ∨ (i = 0 ∧ j.val = 1) := by
  change (cycleGraph _).Adj (snake r (.inl i)) (snake r (.inr j)) ↔ _
  rw [cycle_adj_nat (by omega), snake_left, snake_right]
  have hi := i.isLt
  have hj := j.isLt
  by_cases hj0 : j = 0
  · simp only [hj0, if_pos, Fin.ext_iff, Fin.val_zero]
    norm_num at *
    omega
  · simp only [hj0, if_false, Fin.ext_iff, Fin.val_zero]
    have hjp : j.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using hj0
    norm_num at *
    omega

lemma red_right_right (r : ℕ) (i j : Fin (r+3)) :
    (red r).Adj (.inr i) (.inr j) ↔
      (i = 0 ∧ j.val = r+2) ∨ (j = 0 ∧ i.val = r+2) ∨
      (i ≠ 0 ∧ j ≠ 0 ∧ (i.val+1=j.val ∨ j.val+1=i.val)) := by
  change (cycleGraph _).Adj (snake r (.inr i)) (snake r (.inr j)) ↔ _
  rw [cycle_adj_nat (by omega), snake_right, snake_right]
  have hi := i.isLt
  have hj := j.isLt
  by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
  all_goals simp only [hi0, hj0, if_true, if_false, Fin.val_zero, ne_eq,
    not_true_eq_false, not_false_eq_true, true_and, false_and, and_false,
    false_or, or_false]
  all_goals have hi' : (i = 0 ↔ i.val = 0) := Fin.ext_iff
  all_goals have hj' : (j = 0 ↔ j.val = 0) := Fin.ext_iff
  all_goals omega

lemma red_right_left (r : ℕ) (i j : Fin (r+3)) :
    (red r).Adj (.inr i) (.inl j) ↔
      (j.val = r+2 ∧ i = 0) ∨ (j = 0 ∧ i.val = 1) := by
  rw [adj_comm, red_left_right]

/-- Reverse the two sides at interface zero and at the odd positive interfaces. -/
def swapAt {r : ℕ} (i : Fin (r+3)) : Prop := i.val = 0 ∨ i.val % 2 = 1

noncomputable def relabelFun {r : ℕ} : Vertex r → Vertex r
  | .inl i => if swapAt i then .inr i else .inl i
  | .inr i => if swapAt i then .inl i else .inr i

lemma relabelFun_involutive (r : ℕ) : Function.Involutive (relabelFun (r := r)) := by
  intro v
  cases v with
  | inl i => by_cases h : swapAt i <;> simp [relabelFun, h]
  | inr i => by_cases h : swapAt i <;> simp [relabelFun, h]

noncomputable def relabel (r : ℕ) : Equiv.Perm (Vertex r) :=
  (relabelFun_involutive r).toPerm relabelFun

lemma red_relabel (r : ℕ) (u v : Vertex r) :
    (red r).Adj (relabel r u) (relabel r v) ↔
      (graph r).Adj u v ∧ ¬ (red r).Adj u v := by
  have hh (i : Fin (r+3)) : i.val < r+3 := i.isLt
  cases u with
  | inl i =>
    cases v with
    | inl j =>
      change (red r).Adj (relabelFun (.inl i)) (relabelFun (.inl j)) ↔ _
      simp only [relabelFun, graph, comap_adj, interface, Sum.elim_inl, id_eq]
      rw [cycle_adj_nat (by omega), red_left_left]
      split_ifs <;> simp only [red_left_left, red_left_right, red_right_left, red_right_right,
        swapAt, Fin.ext_iff, Fin.val_zero] at * <;> norm_num at * <;>
        have hi0 : (i = 0 ↔ i.val = 0) := Fin.ext_iff <;>
        have hj0 : (j = 0 ↔ j.val = 0) := Fin.ext_iff <;>
        have := i.isLt <;> have := j.isLt <;> omega
    | inr j =>
      change (red r).Adj (relabelFun (.inl i)) (relabelFun (.inr j)) ↔ _
      simp only [relabelFun, graph, comap_adj, interface, Sum.elim_inl, Sum.elim_inr, id_eq]
      rw [cycle_adj_nat (by omega), red_left_right]
      split_ifs <;> simp only [red_left_left, red_left_right, red_right_left, red_right_right,
        swapAt, Fin.ext_iff, Fin.val_zero] at * <;> norm_num at * <;>
        have hi0 : (i = 0 ↔ i.val = 0) := Fin.ext_iff <;>
        have hj0 : (j = 0 ↔ j.val = 0) := Fin.ext_iff <;>
        have := i.isLt <;> have := j.isLt <;> omega
  | inr i =>
    cases v with
    | inl j =>
      change (red r).Adj (relabelFun (.inr i)) (relabelFun (.inl j)) ↔ _
      simp only [relabelFun, graph, comap_adj, interface, Sum.elim_inl, Sum.elim_inr, id_eq]
      rw [cycle_adj_nat (by omega), red_right_left]
      split_ifs <;> simp only [red_left_left, red_left_right, red_right_left, red_right_right,
        swapAt, Fin.ext_iff, Fin.val_zero] at * <;> norm_num at * <;>
        have hi0 : (i = 0 ↔ i.val = 0) := Fin.ext_iff <;>
        have hj0 : (j = 0 ↔ j.val = 0) := Fin.ext_iff <;>
        have := i.isLt <;> have := j.isLt <;> omega
    | inr j =>
      change (red r).Adj (relabelFun (.inr i)) (relabelFun (.inr j)) ↔ _
      simp only [relabelFun, graph, comap_adj, interface, Sum.elim_inr, id_eq]
      rw [cycle_adj_nat (by omega), red_right_right]
      split_ifs <;> simp only [red_left_left, red_left_right, red_right_left, red_right_right,
        swapAt, Fin.ext_iff, Fin.val_zero] at * <;> norm_num at * <;>
        have hi0 : (i = 0 ↔ i.val = 0) := Fin.ext_iff <;>
        have hj0 : (j = 0 ↔ j.val = 0) := Fin.ext_iff <;>
        have := i.isLt <;> have := j.isLt <;> omega

/-- The complementary snake. -/
noncomputable def blue (r : ℕ) : SimpleGraph (Vertex r) :=
  (red r).comap (relabel r)

lemma blue_adj (r : ℕ) (u v : Vertex r) :
    (blue r).Adj u v ↔ (graph r).Adj u v ∧ ¬ (red r).Adj u v :=
  red_relabel r u v

lemma blue_connected (r : ℕ) : (blue r).Connected :=
  (SimpleGraph.Iso.comap (relabel r) (red r)).connected_iff.mpr (red_connected r)

lemma blue_regular (r : ℕ) : (blue r).IsRegularOfDegree 2 := by
  intro v
  have h := (SimpleGraph.Iso.comap (relabel r) (red r)).degree_eq v
  have hd := red_regular r (relabel r v)
  simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h hd ⊢
  exact h.symm.trans hd

lemma interface_relabel (r : ℕ) (v : Vertex r) :
    interface (relabel r v) = interface v := by
  cases v with
  | inl i => by_cases h : swapAt i <;> simp [relabel, relabelFun, h, interface]
  | inr i => by_cases h : swapAt i <;> simp [relabel, relabelFun, h, interface]

lemma relabel_relabel (r : ℕ) (v : Vertex r) : relabel r (relabel r v) = v :=
  relabelFun_involutive r v

lemma red_le (r : ℕ) : red r ≤ graph r := by
  intro u v h
  have hh : (red r).Adj (relabel r (relabel r u)) (relabel r (relabel r v)) := by
    simpa only [relabel_relabel] using h
  have hg := ((red_relabel r (relabel r u) (relabel r v)).mp hh).1
  simpa only [graph, comap_adj, interface_relabel] using hg

lemma blue_le (r : ℕ) : blue r ≤ graph r := by
  intro u v h
  exact ((blue_adj r u v).mp h).1

lemma red_blue_disjoint (r : ℕ) : Disjoint (red r).edgeSet (blue r).edgeSet := by
  apply Set.disjoint_left.mpr
  intro e hr hb
  induction e using Sym2.ind with
  | h u v => exact ((blue_adj r u v).mp hb).2 hr

lemma red_blue_cover (r : ℕ) : (red r).edgeSet ∪ (blue r).edgeSet = (graph r).edgeSet := by
  ext e
  induction e using Sym2.ind with
  | h u v =>
    change ((red r).Adj u v ∨ (blue r).Adj u v) ↔ (graph r).Adj u v
    rw [blue_adj]
    exact ⟨fun h => h.elim (fun hr => red_le r hr) And.left, fun h => by
      by_cases hr : (red r).Adj u v
      · exact Or.inl hr
      · exact Or.inr ⟨h, hr⟩⟩

noncomputable def redPiece (r : ℕ) : (graph r).Subgraph :=
  SimpleGraph.toSubgraph (red r) (red_le r)

noncomputable def bluePiece (r : ℕ) : (graph r).Subgraph :=
  SimpleGraph.toSubgraph (blue r) (blue_le r)

lemma redPiece_cycle (r : ℕ) :
    (redPiece r).coe.Connected ∧ (redPiece r).coe.IsRegularOfDegree 2 := by
  constructor
  · apply (Subgraph.spanningCoeEquivCoeOfSpanning (redPiece r)
      (SimpleGraph.toSubgraph.isSpanning (red r) (red_le r))).connected_iff.mp
    exact red_connected r
  · intro v
    rw [Subgraph.coe_degree, ← Subgraph.degree_spanningCoe]
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using red_regular r v.val

lemma bluePiece_cycle (r : ℕ) :
    (bluePiece r).coe.Connected ∧ (bluePiece r).coe.IsRegularOfDegree 2 := by
  constructor
  · apply (Subgraph.spanningCoeEquivCoeOfSpanning (bluePiece r)
      (SimpleGraph.toSubgraph.isSpanning (blue r) (blue_le r))).connected_iff.mp
    exact blue_connected r
  · intro v
    rw [Subgraph.coe_degree, ← Subgraph.degree_spanningCoe]
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using blue_regular r v.val

noncomputable def D (r : ℕ) : Finset (graph r).Subgraph := {redPiece r, bluePiece r}

lemma pieces_ne (r : ℕ) : redPiece r ≠ bluePiece r := by
  intro heq
  have hr : (red r).Adj (.inl 0) (.inl 1) :=
    (red_left_left r 0 1).mpr (Or.inl (by simp))
  have hb : (blue r).Adj (.inl 0) (.inl 1) := by
    have hh : (redPiece r).Adj (.inl 0) (.inl 1) := hr
    rw [heq] at hh
    exact hh
  exact ((blue_adj r _ _).mp hb).2 hr

lemma D_card (r : ℕ) : (D r).card = 2 := Finset.card_pair (pieces_ne r)

lemma D_cycles (r : ℕ) : ∀ H ∈ D r,
    H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
  intro H hH
  have hh : H = redPiece r ∨ H = bluePiece r := by simpa [D] using hH
  rcases hh with rfl | rfl
  · exact redPiece_cycle r
  · exact bluePiece_cycle r

lemma D_decomposition (r : ℕ) : IsDecomposition (graph r) (D r) := by
  constructor
  · intro H hH K hK hne
    have hh : H = redPiece r ∨ H = bluePiece r := by simpa [D] using hH
    have hk : K = redPiece r ∨ K = bluePiece r := by simpa [D] using hK
    rcases hh with rfl | rfl <;> rcases hk with rfl | rfl
    · exact (hne rfl).elim
    · exact red_blue_disjoint r
    · exact (red_blue_disjoint r).symm
    · exact (hne rfl).elim
  · simpa [D, redPiece, bluePiece] using red_blue_cover r

/-- Every all-crossing width-two kernel, for arbitrary ring length at least
three, has an exact partition into two connected regular-two subgraphs. -/
theorem all_crossing_decomposition (r : ℕ) :
    ∃ E : Finset (graph r).Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (graph r) E ∧ E.card = 2 :=
  ⟨D r, D_cycles r, D_decomposition r, D_card r⟩

end Erdos184.WidthTwoRing
