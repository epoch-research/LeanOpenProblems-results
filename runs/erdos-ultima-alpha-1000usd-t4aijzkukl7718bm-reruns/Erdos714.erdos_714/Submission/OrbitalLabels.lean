import Submission.OrbitalGrids

/-! Small equivariant label spaces force complete bipartite subgraphs in
pair orbitals. This is a construction obstruction, not a resolution of the
balanced Zarankiewicz conjecture. -/
noncomputable section
open Classical Finset SimpleGraph
namespace Erdos714OrbitalLabels
open Erdos714OrbitalGrids
variable {Γ X Y Z : Type*} [Group Γ]
  [MulAction Γ X] [MulAction Γ Y] [MulAction Γ Z]

/-- The actual right neighbors of the canonical left vertex. -/
def neighbors (a : X) (b : Y) : Set Y :=
  {y | ∃ g : Γ, g • a = a ∧ g • b = y}

def neighborEquiv (a : X) (b : Y) :
    neighbors (Γ := Γ) a b ≃ (graph (Γ := Γ) a b).neighborSet (.inl a) where
  toFun y := ⟨.inr y.val, y.property⟩
  invFun y := match y with
    | ⟨.inl _, h⟩ => False.elim h
    | ⟨.inr v, h⟩ => ⟨v,h⟩
  left_inv := by intro y; rfl
  right_inv := by
    rintro ⟨y,hy⟩
    cases y with
    | inl _ => exact False.elim hy
    | inr _ => rfl

/-- Each neighbor has a transporter. Label it by the transport of `z`.
Equal labels supply the same family of common left neighbors. -/
theorem copy_of_small_labels [Fintype Y] [Fintype Z]
    (a : X) (b : Y) {r t : ℕ} (U : Z → Fin r → Γ)
    (hU : ∀ (g : Γ) z i, U (g • z) i * g = g * U z i)
    (z : Z) (hb : ∀ i, U z i • b = b)
    (ha : Function.Injective (fun i => U z i • a))
    (hcard : t * Fintype.card Z < Fintype.card (neighbors (Γ := Γ) a b)) :
    Nonempty (Copy (completeBipartiteGraph (Fin r) (Fin (t+1)))
      (graph (Γ := Γ) a b)) := by
  let N := neighbors (Γ := Γ) a b
  choose g hgA hgB using (fun y : N => y.property)
  let label : N → Z := fun y => g y • z
  obtain ⟨v, _, hv⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := (univ : Finset N)) (t := (univ : Finset Z)) (f := label)
    (fun _ _ => mem_univ _) (n := t) (by simpa [Nat.mul_comm] using hcard)
  obtain ⟨ys, hys⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin (t+1)) (s := univ.filter (label · = v)) (by simpa using hv)
  have hy (j : Fin (t+1)) : g (ys j) • z = v :=
    (mem_filter.mp (hys ⟨j,rfl⟩)).2
  have transport (j : Fin (t+1)) (i : Fin r) :
      U v i * g (ys j) = g (ys j) * U z i := by
    rw [← hy j]
    exact hU _ _ _
  have hi : Function.Injective (fun i => U v i • a) := by
    intro i k hik
    have hp (i : Fin r) : U v i • a = g (ys 0) • (U z i • a) := by
      calc
        U v i • a = U v i • (g (ys 0) • a) := by rw [hgA]
        _ = g (ys 0) • (U z i • a) := by rw [← mul_smul, transport, mul_smul]
    change U v i • a = U v k • a at hik
    rw [hp i, hp k] at hik
    exact ha (MulAction.injective (g (ys 0)) hik)
  let L : Fin r ↪ X := ⟨fun i => U v i • a, hi⟩
  let R : Fin (t+1) ↪ Y := ys.trans (Function.Embedding.subtype N)
  have he (i : Fin r) (j : Fin (t+1)) :
      ∃ h : Γ, h • a = L i ∧ h • b = R j := by
    refine ⟨U v i * g (ys j), ?_, ?_⟩
    · change (U v i * g (ys j)) • a = U v i • a
      rw [mul_smul, hgA]
    · change (U v i * g (ys j)) • b = (ys j).val
      rw [transport, mul_smul, hb, hgB]
  refine ⟨⟨⟨L.sumMap R, ?_⟩, (L.sumMap R).injective⟩⟩
  intro x y hxy
  cases x with
  | inl i =>
    cases y with
    | inl j => simp at hxy
    | inr j => exact he i j
  | inr j =>
    cases y with
    | inl i => exact he i j
    | inr k => simp at hxy

/-- The label construction is an obstruction to freeness. -/
theorem not_free_of_small_labels [Fintype Y] [Fintype Z]
    (a : X) (b : Y) {r t : ℕ} (U : Z → Fin r → Γ)
    (hU : ∀ (g : Γ) z i, U (g • z) i * g = g * U z i)
    (z : Z) (hb : ∀ i, U z i • b = b)
    (ha : Function.Injective (fun i => U z i • a))
    (hcard : t * Fintype.card Z < Fintype.card (neighbors (Γ := Γ) a b)) :
    ¬ (completeBipartiteGraph (Fin r) (Fin (t+1))).Free (graph (Γ := Γ) a b) :=
  fun hfree => hfree (copy_of_small_labels a b U hU z hb ha hcard)

/-- A free pair orbital cannot have more than `t` neighbors per label. -/
theorem degree_le_labels [Fintype X] [Fintype Y] [Fintype Z]
    (a : X) (b : Y) {r t : ℕ} (U : Z → Fin r → Γ)
    (hU : ∀ (g : Γ) z i, U (g • z) i * g = g * U z i)
    (z : Z) (hb : ∀ i, U z i • b = b)
    (ha : Function.Injective (fun i => U z i • a))
    (hfree : (completeBipartiteGraph (Fin r) (Fin (t+1))).Free
      (graph (Γ := Γ) a b)) :
    (graph (Γ := Γ) a b).degree (.inl a) ≤ t * Fintype.card Z := by
  have hcard : Fintype.card (neighbors (Γ := Γ) a b) ≤ t * Fintype.card Z := by
    by_contra! h
    exact not_free_of_small_labels a b U hU z hb ha h hfree
  rwa [Fintype.card_congr (neighborEquiv a b), card_neighborSet_eq_degree] at hcard

/-- Only the orbit of the base label is needed, not the entire label space. -/
theorem degree_le_orbit_labels [Fintype X] [Fintype Y]
    (a : X) (b : Y) {r t : ℕ} (U : Z → Fin r → Γ)
    (hU : ∀ (g : Γ) z i, U (g • z) i * g = g * U z i)
    (z : Z) [Fintype (MulAction.orbit Γ z)]
    (hb : ∀ i, U z i • b = b)
    (ha : Function.Injective (fun i => U z i • a))
    (hfree : (completeBipartiteGraph (Fin r) (Fin (t+1))).Free
      (graph (Γ := Γ) a b)) :
    (graph (Γ := Γ) a b).degree (.inl a) ≤
      t * Fintype.card (MulAction.orbit Γ z) := by
  exact degree_le_labels a b (fun w : MulAction.orbit Γ z => U w.val)
    (fun g w i => hU g w.val i) ⟨z, MulAction.mem_orbit_self z⟩ hb ha hfree

/-- Conjugation acts on the actual conjugacy class, without changing the
existing actions of `Γ` on the two vertex types. -/
instance conjugacyAction (u : Γ) : MulAction Γ (ConjClasses.mk u).carrier where
  smul g v := ⟨g * v.val * g⁻¹,
    v.property.trans (isConj_iff.mpr ⟨g,rfl⟩)⟩
  one_smul v := Subtype.ext (by
    change 1 * v.val * (1 : Γ)⁻¹ = v.val
    simp)
  mul_smul g h v := Subtype.ext (by
    change (g*h) * v.val * (g*h)⁻¹ = g * (h * v.val * h⁻¹) * g⁻¹
    simp [mul_assoc])

/-- A single nonfixed prime-order element in the opposite stabilizer
bounds a free orbital's degree by its conjugacy-class size. -/
theorem degree_le_conjugacy [Fintype Γ] [Fintype X] [Fintype Y]
    (a : X) (b : Y) {p t : ℕ} (hp : p.Prime) (u : Γ)
    (hup : u^p = 1) (hb : u • b = b) (ha : u • a ≠ a)
    (hfree : (completeBipartiteGraph (Fin p) (Fin (t+1))).Free
      (graph (Γ := Γ) a b)) :
    (graph (Γ := Γ) a b).degree (.inl a) ≤
      t * Fintype.card (ConjClasses.mk u).carrier := by
  apply degree_le_labels a b (fun w : (ConjClasses.mk u).carrier =>
    fun i : Fin p => w.val^i.val) ?_ ⟨u,ConjClasses.mem_carrier_mk⟩
      (fun i => powers_fix u b hb i.val) (prime_orbit_injective hp u hup a ha) hfree
  intro g w i
  change (g * w.val * g⁻¹)^i.val * g = g * w.val^i.val
  rw [conj_pow]
  simp [mul_assoc]

/-- The copied grid also bounds every free edge thinning, not only the
original invariant graph. -/
theorem thinning_bound_labels [Fintype X] [Fintype Y] [Fintype Z]
    (a : X) (b : Y) {r t : ℕ} (U : Z → Fin (t+1) → Γ)
    (hU : ∀ (g : Γ) z i, U (g • z) i * g = g * U z i)
    (z : Z) (hb : ∀ i, U z i • b = b)
    (ha : Function.Injective (fun i => U z i • a))
    (hcard : t * Fintype.card Z < Fintype.card (neighbors (Γ := Γ) a b))
    (H : SimpleGraph (X ⊕ Y)) (hHG : H ≤ graph (Γ := Γ) a b)
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free H) :
    (t+1)^2 * H.edgeFinset.card ≤
      extremalNumber (2*(t+1)) (completeBipartiteGraph (Fin r) (Fin r)) *
        (graph (Γ := Γ) a b).edgeFinset.card := by
  obtain ⟨c⟩ := copy_of_small_labels a b U hU z hb ha hcard
  exact Erdos714GraphAveraging.biclique_bound H _ r (t+1) c hHG hfree
    (edge_transitive a b)

end Erdos714OrbitalLabels
#print axioms Erdos714OrbitalLabels.not_free_of_small_labels
#print axioms Erdos714OrbitalLabels.degree_le_labels

#print axioms Erdos714OrbitalLabels.degree_le_orbit_labels

#print axioms Erdos714OrbitalLabels.degree_le_conjugacy

#print axioms Erdos714OrbitalLabels.copy_of_small_labels
#print axioms Erdos714OrbitalLabels.thinning_bound_labels
