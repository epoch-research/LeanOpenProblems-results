import Submission.CountCritical

/-! Balanced integral orientations of finite even graphs. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.BalancedOrientation
variable {V : Type*} {G : SimpleGraph V}
set_option maxHeartbeats 1000000

noncomputable def arcCount (x y : V) : {u v : V} → G.Walk u v → ℕ
  | _, _, .nil => 0
  | _, _, .cons (u := a) (v := b) _ p => (if x = a ∧ y = b then 1 else 0) + arcCount x y p

lemma arc_indicators {a b x y : V} (hne : a ≠ b) :
    (if x = a ∧ y = b then (1 : ℕ) else 0) + (if y = a ∧ x = b then 1 else 0) =
      if s(x,y) = s(a,b) then 1 else 0 := by
  simp only [Sym2.eq_iff]
  by_cases h : x = a ∧ y = b
  · obtain ⟨rfl,rfl⟩ := h
    simp [hne, hne.symm]
  · by_cases h' : y = a ∧ x = b
    · obtain ⟨rfl,rfl⟩ := h'
      simp [hne, hne.symm]
    · have h'' : ¬(x = b ∧ y = a) := by tauto
      simp [h,h',h'']

lemma arcCount_symm {u v : V} (p : G.Walk u v) (x y : V) :
    arcCount x y p + arcCount y x p = p.edges.count s(x,y) := by
  induction p with
  | nil => simp [arcCount]
  | @cons a b c hab p ih =>
    have hh := arc_indicators (x := x) (y := y) (G.ne_of_adj hab)
    simp only [arcCount, Walk.edges_cons, List.count_cons]
    simp only [beq_iff_eq, eq_comm (a := s(a,b))]
    omega

lemma arcCount_trail {u v : V} (p : G.Walk u v) (hp : p.IsTrail) (x y : V) :
    arcCount x y p + arcCount y x p = if s(x,y) ∈ p.edges then 1 else 0 := by
  rw [arcCount_symm]
  by_cases he : s(x,y) ∈ p.edges
  · rw [if_pos he]
    exact List.count_eq_one_of_mem hp.edges_nodup he
  · rw [if_neg he]
    exact List.count_eq_zero.mpr he

lemma arcCount_balance [Fintype V] {u v : V} (p : G.Walk u v) (x : V) :
    (∑ y, arcCount x y p) + (if x = v then 1 else 0) =
      (∑ y, arcCount y x p) + (if x = u then 1 else 0) := by
  induction p with
  | nil => simp [arcCount]
  | @cons a b c hab p ih =>
    simp only [arcCount, Finset.sum_add_distrib]
    have hr : (∑ y : V, if x = a ∧ y = b then (1 : ℕ) else 0) = if x = a then 1 else 0 := by
      by_cases h : x = a <;> simp [h]
    have hc : (∑ y : V, if y = a ∧ x = b then (1 : ℕ) else 0) = if x = b then 1 else 0 := by
      by_cases h : x = b <;> simp [h]
    rw [hr,hc]
    omega

/-- A matrix form of a balanced orientation. The symmetry equation also
forces zero diagonal and at most one of the two possible arcs per edge. -/
def IsBalanced [Fintype V] (G : SimpleGraph V) (A : V → V → ℕ) : Prop :=
  (∀ x y, A x y + A y x = if G.Adj x y then 1 else 0) ∧
  ∀ x, (∑ y, A x y) = ∑ y, A y x

lemma exists_balanced [Fintype V] (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) :
    ∃ A : V → V → ℕ, IsBalanced G A := by
  generalize hn : G.edgeSet.ncard = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hb : G = ⊥
    · subst G
      exact ⟨fun _ _ => 0, by simp [IsBalanced]⟩
    obtain ⟨v,p,hp⟩ := exists_cycle_of_even_nonempty G he hb
    have hc := cycle_subgraph_regular G hp
    have hr := CountCritical.residual_even he p.toSubgraph hc
    have hlt := CountCritical.edges_lt (G := G) sdiff_le (CountCritical.residual_proper p.toSubgraph hc)
    obtain ⟨A,hA⟩ := ih _ (by omega) (G \ p.toSubgraph.spanningCoe) (by
      intro w
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hr w) rfl
    refine ⟨fun x y => A x y + arcCount x y p, ?_, ?_⟩
    · intro x y
      have h₀ := hA.1 x y
      have h₁ := arcCount_trail p hp.isTrail x y
      have hpedge : p.toSubgraph.Adj x y ↔ s(x,y) ∈ p.edges := p.mem_edges_toSubgraph (e := s(x,y))
      change A x y + arcCount x y p + (A y x + arcCount y x p) = _
      by_cases hxy : G.Adj x y <;> by_cases hpe : s(x,y) ∈ p.edges
      · simp only [sdiff_adj, Subgraph.spanningCoe_adj, hpedge, hxy, hpe, not_true_eq_false,
          and_false, if_false] at h₀
        simp only [hpe, if_true] at h₁
        simp only [hxy, if_true]
        omega
      · simp only [sdiff_adj, Subgraph.spanningCoe_adj, hpedge, hxy, hpe, not_false_eq_true,
          and_self, if_true] at h₀
        simp only [hpe, if_false] at h₁
        simp only [hxy, if_true]
        omega
      · exact (hxy (p.edges_subset_edgeSet hpe)).elim
      · simp only [sdiff_adj, hxy, false_and, if_false] at h₀
        simp only [hpe, if_false] at h₁
        simp only [hxy, if_false]
        omega
    · intro x
      simp only [Finset.sum_add_distrib]
      have hh := arcCount_balance p x
      rw [hA.2]
      omega

lemma row_twice_degree [Fintype V] {A : V → V → ℕ} (hA : IsBalanced G A) (x : V) :
    2 * (∑ y, A x y) = G.degree x := by
  have hh := Finset.sum_congr (s₁ := (Finset.univ : Finset V)) rfl (fun y _ => hA.1 x y)
  rw [Finset.sum_add_distrib, ← hA.2] at hh
  have hd : (∑ y : V, if G.Adj x y then 1 else 0) = G.degree x := by
    rw [← Finset.card_filter]
    have heq : Finset.univ.filter (G.Adj x) = (G.neighborSet x).toFinset := by ext y; simp
    rw [heq]
    simp only [← card_neighborSet_eq_degree, Set.toFinset_card]
  rw [hd] at hh
  omega

end Erdos184.BalancedOrientation
