import Submission.EdgeAveraging

/-!
Commuting stabilizer families force bicliques in pair-orbital graphs.
This provides an exact group-action obstruction, including arbitrary edge
thinnings, but does not settle the balanced Zarankiewicz conjecture.
-/

noncomputable section
open SimpleGraph Classical

namespace Erdos714OrbitalGrids

variable {Γ X Y : Type*} [Group Γ] [MulAction Γ X] [MulAction Γ Y]

/-- The two-part graph defined by the actual orbit of the ordered pair `(a,b)`.
The actions on the two parts need not be the same, or transitive. -/
def graph (a : X) (b : Y) : SimpleGraph (X ⊕ Y) where
  Adj x y := match x,y with
    | .inl u, .inr v => ∃ g : Γ, g • a = u ∧ g • b = v
    | .inr v, .inl u => ∃ g : Γ, g • a = u ∧ g • b = v
    | _, _ => False
  symm := by intro x y; cases x <;> cases y <;> simp_all
  loopless := by intro x; cases x <;> simp

/-- Every acting element simultaneously permutes both sides of the orbital. -/
def transform (a : X) (b : Y) (g : Γ) : graph (Γ := Γ) a b ≃g graph (Γ := Γ) a b where
  toEquiv := Equiv.sumCongr (MulAction.toPerm g) (MulAction.toPerm g)
  map_rel_iff' := by
    have hh (x : X) (y : Y) :
        (∃ h : Γ, h • a = g • x ∧ h • b = g • y) ↔
          (∃ h : Γ, h • a = x ∧ h • b = y) := by
      constructor
      · rintro ⟨h,hx,hy⟩
        exact ⟨g⁻¹*h, by rw [mul_smul, hx, inv_smul_smul],
          by rw [mul_smul, hy, inv_smul_smul]⟩
      · rintro ⟨h,hx,hy⟩
        exact ⟨g*h, by rw [mul_smul, hx], by rw [mul_smul, hy]⟩
    intro x y
    cases x <;> cases y
    · rfl
    · exact hh _ _
    · exact hh _ _
    · rfl

def canonicalEdge (a : X) (b : Y) : (graph (Γ := Γ) a b).edgeSet :=
  ⟨s(Sum.inl a,Sum.inr b), by exact ⟨1,by simp,by simp⟩⟩

lemma from_canonical (a : X) (b : Y) (e : (graph (Γ := Γ) a b).edgeSet) :
    ∃ f : graph (Γ := Γ) a b ≃g graph (Γ := Γ) a b,
      f.mapEdgeSet (canonicalEdge (Γ := Γ) a b) = e := by
  rcases e with ⟨e,he⟩
  induction e using Sym2.ind with
  | _ x y =>
    cases x with
    | inl x =>
      cases y with
      | inl y => exact False.elim he
      | inr y =>
        obtain ⟨g,hx,hy⟩ := he
        refine ⟨transform a b g, Subtype.ext ?_⟩
        change s(Sum.inl (g • a),Sum.inr (g • b)) = s(Sum.inl x,Sum.inr y)
        rw [hx,hy]
    | inr z =>
      cases y with
      | inr w => exact False.elim he
      | inl x =>
        obtain ⟨g,hx,hy⟩ := he
        refine ⟨transform a b g, Subtype.ext ?_⟩
        change s(Sum.inl (g • a),Sum.inr (g • b)) = s(Sum.inr z,Sum.inl x)
        rw [hx,hy,Sym2.eq_swap]

/-- The pair-orbital graph is edge-transitive even if the ambient actions
have further orbits, whose vertices are isolated. -/
theorem edge_transitive (a : X) (b : Y) :
    Erdos714GraphAveraging.EdgeTransitive (graph (Γ := Γ) a b) := by
  intro x y
  obtain ⟨fx,hx⟩ := from_canonical a b x
  obtain ⟨fy,hy⟩ := from_canonical a b y
  refine ⟨fy * fx⁻¹, ?_⟩
  change (Erdos714GraphAveraging.edgeAction (graph (Γ := Γ) a b)) (fy*fx⁻¹) x = y
  rw [map_mul, map_inv]
  change fy.mapEdgeSet (fx.mapEdgeSet.symm x) = y
  rw [← hx, Equiv.symm_apply_apply]
  exact hy

/-- Opposite stabilizers and cross-commutation give explicit simultaneous
transporters for every edge of a rectangular grid. -/
def commutingCopy (a : X) (b : Y) {r s : ℕ}
    (u : Fin r → Γ) (v : Fin s → Γ)
    (hu : ∀ i, u i • b = b) (hv : ∀ j, v j • a = a)
    (hc : ∀ i j, Commute (u i) (v j))
    (hi : Function.Injective (fun i => u i • a))
    (hj : Function.Injective (fun j => v j • b)) :
    Copy (completeBipartiteGraph (Fin r) (Fin s)) (graph (Γ := Γ) a b) := by
  let L : Fin r ↪ X := ⟨fun i => u i • a,hi⟩
  let R : Fin s ↪ Y := ⟨fun j => v j • b,hj⟩
  have he (i : Fin r) (j : Fin s) : ∃ g : Γ, g • a = L i ∧ g • b = R j := by
    refine ⟨u i*v j, ?_, ?_⟩
    · change (u i*v j) • a = u i • a
      rw [mul_smul, hv]
    · change (u i*v j) • b = v j • b
      rw [(hc i j).eq, mul_smul, hu]
  refine ⟨⟨L.sumMap R, ?_⟩, (L.sumMap R).injective⟩
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl k => simp at h
    | inr j => exact he i j
  | inr j =>
    cases y with
    | inr k => simp at h
    | inl i => exact he i j

lemma powers_fix (u : Γ) (a : X) (ha : u • a = a) (n : ℕ) : u^n • a = a := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_smul, ha, ih]

/-- A nonfixed point under an element whose prime power is one has a full
prime-sized orbit. This discharges the injectivity checks in cyclic grids. -/
theorem prime_orbit_injective {p : ℕ} (hp : p.Prime) (u : Γ) (hu : u^p = 1)
    (a : X) (ha : u • a ≠ a) : Function.Injective (fun i : Fin p => u^i.val • a) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hper : Function.IsPeriodicPt (fun x : X => u • x) p a := by
    change (fun x : X => u • x)^[p] a = a
    rw [smul_iterate_apply, hu, one_smul]
  have hm := Function.minimalPeriod_eq_prime hper ha
  intro i j hij
  apply Fin.ext
  apply Function.iterate_injOn_Iio_minimalPeriod (f := fun x : X => u • x) (x := a)
  · simpa only [Set.mem_Iio, hm] using i.isLt
  · simpa only [Set.mem_Iio, hm] using j.isLt
  · simpa only [smul_iterate_apply] using hij

/-- Two commuting elements of prime order, in opposite stabilizers but not
their intersection, give a complete prime-by-prime pair-orbital grid. -/
def primeCopy (a : X) (b : Y) {p : ℕ} (hp : p.Prime) (u v : Γ)
    (hup : u^p = 1) (hvp : v^p = 1) (hu : u • b = b) (hv : v • a = a)
    (hua : u • a ≠ a) (hvb : v • b ≠ b) (hc : Commute u v) :
    Copy (completeBipartiteGraph (Fin p) (Fin p)) (graph (Γ := Γ) a b) :=
  commutingCopy a b (fun i => u^i.val) (fun j => v^j.val)
    (fun i => powers_fix u b hu i.val) (fun j => powers_fix v a hv j.val)
    (fun i j => hc.pow_pow i.val j.val)
    (prime_orbit_injective hp u hup a hua) (prime_orbit_injective hp v hvp b hvb)

theorem not_free_of_prime (a : X) (b : Y) {p r : ℕ} (hp : p.Prime) (hr : r ≤ p)
    (u v : Γ) (hup : u^p = 1) (hvp : v^p = 1) (hu : u • b = b) (hv : v • a = a)
    (hua : u • a ≠ a) (hvb : v • b ≠ b) (hc : Commute u v) :
    ¬ (completeBipartiteGraph (Fin r) (Fin r)).Free (graph (Γ := Γ) a b) := by
  let e := Fin.castLEEmb hr
  let small : Copy (completeBipartiteGraph (Fin r) (Fin r))
      (completeBipartiteGraph (Fin p) (Fin p)) :=
    ⟨⟨e.sumMap e, by intro x y h; cases x <;> cases y <;> simp_all⟩,
      (e.sumMap e).injective⟩
  intro hfree
  exact hfree ⟨(primeCopy a b hp u v hup hvp hu hv hua hvb hc).comp small⟩

/-- A commuting-family grid bounds every free edge thinning of its orbital. -/
theorem thinning_bound [Fintype X] [Fintype Y]
    (a : X) (b : Y) {r t : ℕ} (u v : Fin t → Γ)
    (hu : ∀ i, u i • b = b) (hv : ∀ j, v j • a = a)
    (hc : ∀ i j, Commute (u i) (v j))
    (hi : Function.Injective (fun i => u i • a))
    (hj : Function.Injective (fun j => v j • b))
    (H : SimpleGraph (X ⊕ Y)) (hHG : H ≤ graph (Γ := Γ) a b)
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free H) :
    t^2 * H.edgeFinset.card ≤
      extremalNumber (2*t) (completeBipartiteGraph (Fin r) (Fin r)) *
        (graph (Γ := Γ) a b).edgeFinset.card := by
  exact Erdos714GraphAveraging.biclique_bound H _ r t
    (commutingCopy a b u v hu hv hc hi hj) hHG hfree (edge_transitive a b)

/-- A single orbital's canonical degree is at most the size of the left
stabilizer. This distinguishes a genuine orbital from a union of trace levels. -/
theorem canonical_degree_le_stabilizer [Fintype Γ] [Fintype X] [Fintype Y]
    (a : X) (b : Y) :
    (graph (Γ := Γ) a b).degree (.inl a) ≤ Fintype.card (MulAction.stabilizer Γ a) := by
  let f : MulAction.stabilizer Γ a → (graph (Γ := Γ) a b).neighborSet (.inl a) :=
    fun g => ⟨.inr ((g : Γ) • b), ⟨g, g.property, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨x,hx⟩
    cases x with
    | inl x => exact False.elim hx
    | inr y =>
      obtain ⟨g,hga,hgb⟩ := hx
      refine ⟨⟨g,hga⟩, Subtype.ext ?_⟩
      change Sum.inr (g • b) = Sum.inr y
      rw [hgb]
  have h := Fintype.card_le_of_surjective f hf
  simpa only [card_neighborSet_eq_degree] using h

end Erdos714OrbitalGrids

#print axioms Erdos714OrbitalGrids.edge_transitive
#print axioms Erdos714OrbitalGrids.commutingCopy
#print axioms Erdos714OrbitalGrids.prime_orbit_injective
#print axioms Erdos714OrbitalGrids.primeCopy
#print axioms Erdos714OrbitalGrids.not_free_of_prime
#print axioms Erdos714OrbitalGrids.thinning_bound

#print axioms Erdos714OrbitalGrids.canonical_degree_le_stabilizer
