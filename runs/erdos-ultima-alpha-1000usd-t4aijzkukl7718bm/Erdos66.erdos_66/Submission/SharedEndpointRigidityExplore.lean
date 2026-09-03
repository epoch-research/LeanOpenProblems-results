import FormalConjecturesUtil

/-! Rigidity of endpoint positions when several prescribed sums share
vertices. These are constraints on repair templates, not on all solutions
of Erdos 66. -/
namespace Erdos66SharedEndpointRigidity
open scoped Classical
set_option maxHeartbeats 1800000

variable {V : Type*}

/-- On an edge, two realizations of the same prescribed sum have opposite
displacements at the two endpoints. -/
lemma edge_displacement (G : SimpleGraph V) (x y : V → ℤ)
    (h : ∀ u v, G.Adj u v → x u+x v = y u+y v)
    {u v : V} (huv : G.Adj u v) : y v-x v = -(y u-x u) := by
  have hh := h u v huv
  omega

lemma walk_displacement (G : SimpleGraph V) (x y : V → ℤ)
    (h : ∀ u v, G.Adj u v → x u+x v = y u+y v)
    {u v : V} (p : G.Walk u v) :
    y v-x v = (-1 : ℤ)^p.length*(y u-x u) := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    rw [SimpleGraph.Walk.length_cons, pow_succ]
    have he := edge_displacement G x y h huv
    rw [ih,he]
    ring

/-- An odd cycle removes the single translation freedom in its component. -/
lemma odd_closed_walk_fixed (G : SimpleGraph V) (x y : V → ℤ)
    (h : ∀ u v, G.Adj u v → x u+x v = y u+y v)
    {u : V} (p : G.Walk u u) (hp : Odd p.length) : y u = x u := by
  have hh := walk_displacement G x y h p
  rw [hp.neg_one_pow] at hh
  omega

lemma reachable_fixed (G : SimpleGraph V) (x y : V → ℤ)
    (h : ∀ u v, G.Adj u v → x u+x v = y u+y v)
    {u v : V} (hu : y u = x u) (huv : G.Reachable u v) : y v = x v := by
  obtain ⟨p⟩ := huv
  have hh := walk_displacement G x y h p
  rw [hu, sub_self, mul_zero] at hh
  omega

lemma odd_component_unique (G : SimpleGraph V) (x y : V → ℤ)
    (h : ∀ u v, G.Adj u v → x u+x v = y u+y v)
    {u : V} (p : G.Walk u u) (hp : Odd p.length)
    (hconn : ∀ v, G.Reachable u v) : y = x := by
  funext v
  exact reachable_fixed G x y h (odd_closed_walk_fixed G x y h p hp) (hconn v)

lemma walk_constant (G : SimpleGraph V) (f : V → ℤ)
    (h : ∀ u v, G.Adj u v → f u = f v) {u v : V} (p : G.Walk u v) : f u = f v := by
  induction p with
  | nil => rfl
  | @cons u v w huv p ih => exact (h u v huv).trans ih

/-- A connected bipartite template has only one free displacement: every
vertex on one side moves by t, and every vertex on the other side by -t. -/
theorem bipartite_one_parameter (G : SimpleGraph V) (x y : V → ℤ)
    (h : ∀ u v, G.Adj u v → x u+x v = y u+y v)
    (color : V → Bool) (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (root : V) (hconn : ∀ v, G.Reachable root v) :
    ∃ t : ℤ, ∀ v, y v = x v + if color v then t else -t := by
  let f : V → ℤ := fun v ↦ if color v then y v-x v else -(y v-x v)
  have hf : ∀ u v, G.Adj u v → f u = f v := by
    intro u v huv
    have hd := edge_displacement G x y h huv
    have hc := hcolor u v huv
    cases hu : color u <;> cases hv : color v <;> simp [f,hu,hv] at hc ⊢ <;> omega
  refine ⟨f root, ?_⟩
  intro v
  obtain ⟨p⟩ := hconn v
  have hh := walk_constant G f hf p
  cases hv : color v <;> simp only [f,hv,Bool.false_eq_true,if_false,if_true] at hh ⊢ <;> omega

/-- A fully reused rectangular family exists exactly when the prescribed
centers satisfy all the additive rectangle identities. -/
theorem rectangle_realizable_iff {ι κ : Type*} (n : ι → κ → ℤ) (i₀ : ι) (j₀ : κ) :
    (∃ x : ι → ℤ, ∃ y : κ → ℤ, ∀ i j, x i+y j = n i j) ↔
      ∀ i j, n i j+n i₀ j₀ = n i j₀+n i₀ j := by
  constructor
  · rintro ⟨x,y,h⟩ i j
    rw [← h i j, ← h i₀ j₀, ← h i j₀, ← h i₀ j]
    ring
  · intro h
    refine ⟨fun i ↦ n i j₀-n i₀ j₀, fun j ↦ n i₀ j, ?_⟩
    intro i j
    have hh := h i j
    dsimp only
    omega

lemma rectangle_parameterization {ι κ : Type*} (n : ι → κ → ℤ) (i₀ : ι) (j₀ : κ)
    (x : ι → ℤ) (y : κ → ℤ) (h : ∀ i j, x i+y j = n i j) :
    ∃ t : ℤ, (∀ i, x i = t+n i j₀-n i₀ j₀) ∧ (∀ j, y j = n i₀ j-t) := by
  refine ⟨x i₀, ?_, ?_⟩
  · intro i
    have h1 := h i j₀
    have h2 := h i₀ j₀
    omega
  · intro j
    have hh := h i₀ j
    omega

end Erdos66SharedEndpointRigidity
