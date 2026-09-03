import Submission.Work

/-!
Countable-index products of countable sets, and their quotients, cannot
supply a witness for Erdős Problem 595. This includes the usual
countable-index ultraproducts of finite graphs. No assertion about
uncountable-index ultraproducts or arbitrary saturated graphs is made.
-/

set_option autoImplicit false

open SimpleGraph Set

namespace Erdos595CountableProduct

/-- A countable product of countable sets has size at most the continuum. -/
theorem mk_pi_le_continuum {I : Type} [Countable I]
    (A : I → Type) [∀ i, Countable (A i)] :
    Cardinal.mk (∀ i, A i) ≤ Cardinal.continuum := by
  classical
  choose e he using fun i => exists_injective_nat (A i)
  have hinj : Function.Injective (fun f : (∀ i, A i) => fun i => e i (f i)) := by
    intro f g h
    exact funext (fun i => he i (congrFun h i))
  calc
    Cardinal.mk (∀ i, A i) ≤ Cardinal.mk (I → ℕ) :=
      Cardinal.mk_le_of_injective hinj
    _ = Cardinal.aleph0 ^ Cardinal.mk I := by simp
    _ ≤ Cardinal.aleph0 ^ Cardinal.aleph0 :=
      Cardinal.power_le_power_left Cardinal.aleph0_ne_zero Cardinal.mk_le_aleph0
    _ = Cardinal.continuum := Cardinal.aleph0_power_aleph0

/-- Taking an arbitrary quotient cannot evade this cardinality bound. -/
theorem mk_quotient_pi_le_continuum {I : Type} [Countable I]
    (A : I → Type) [∀ i, Countable (A i)] (s : Setoid (∀ i, A i)) :
    Cardinal.mk (Quotient s) ≤ Cardinal.continuum :=
  Cardinal.mk_quotient_le.trans (mk_pi_le_continuum A)

/-- The bound gives a cover for every graph on the quotient, not only for
`K₄`-free graphs or for graphs whose adjacency comes from an ultraproduct. -/
theorem quotient_pi_countable_cover {I : Type} [Countable I]
    (A : I → Type) [∀ i, Countable (A i)] (s : Setoid (∀ i, A i))
    (G : SimpleGraph (Quotient s)) :
    Erdos595Work.IsCountableUnionOfTriangleFree G := by
  classical
  have hcard : Cardinal.mk (Quotient s) ≤ Cardinal.mk (ℕ → Fin 2) := by
    simpa only [Cardinal.mk_arrow, Cardinal.mk_fin, Cardinal.mk_nat,
      Cardinal.lift_uzero, Nat.cast_ofNat, Cardinal.two_power_aleph0]
      using mk_quotient_pi_le_continuum A s
  let e : Quotient s ↪ (ℕ → Fin 2) :=
    (Cardinal.lift_mk_le'.mp (by simpa only [Cardinal.lift_uzero] using hcard)).some
  exact Erdos595Work.countable_union_of_binary_encoding G e e.injective

#print axioms mk_pi_le_continuum
#print axioms mk_quotient_pi_le_continuum
#print axioms quotient_pi_countable_cover

end Erdos595CountableProduct
