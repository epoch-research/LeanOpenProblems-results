import FormalConjecturesUtil

/-!
Unit orthogonality with a fixed number of positive coordinates over an
arbitrary ordered field. The positive index bounds clique size even when
the field is non-Archimedean. No edge-cover assertion is made.
-/
set_option autoImplicit false
open SimpleGraph Set
open scoped BigOperators
namespace Erdos595IndefiniteUnit

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {m n : ℕ}

abbrev Space (K : Type*) (m n : ℕ) := (Fin m → K) × (Fin n → K)

def form (x y : Space K m n) : K := x.1 ⬝ᵥ y.1 - x.2 ⬝ᵥ y.2

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma form_symm (x y : Space K m n) : form x y = form y x := by
  simp only [form, dotProduct_comm]

abbrev UnitPoint (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (m n : ℕ) := {x : Space K m n // form x x = 1}

def graph (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (m n : ℕ) : SimpleGraph (UnitPoint K m n) where
  Adj x y := form x.val y.val = 0
  symm := fun x y h => (form_symm y.val x.val).trans h
  loopless := fun x h => zero_ne_one (h.symm.trans x.property)

private lemma dot_nonneg {d : ℕ} (x : Fin d → K) : 0 ≤ x ⬝ᵥ x := by
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

/-- The positive projections of an orthonormal family are independent. -/
theorem positive_independent {I : Type*} [Fintype I]
    (x : I → UnitPoint K m n)
    (hx : ∀ i j, i ≠ j → (graph K m n).Adj (x i) (x j)) :
    LinearIndependent K (fun i => (x i).val.1) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  let neg : Fin n → K := ∑ j, g j • (x j).val.2
  have row (j : I) :
      (∑ k, g k * ((x j).val.1 ⬝ᵥ (x k).val.1)) -
        (∑ k, g k * ((x j).val.2 ⬝ᵥ (x k).val.2)) = g j := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    change (∑ k, g k * form (x j).val (x k).val) = g j
    rw [Finset.sum_eq_single j]
    · rw [(x j).property, mul_one]
    · intro k _ hkj
      rw [show form (x j).val (x k).val = 0 from hx j k hkj.symm, mul_zero]
    · simp
  have each (j : I) : -( (x j).val.2 ⬝ᵥ neg) = g j := by
    have hp := congrArg (fun z => (x j).val.1 ⬝ᵥ z) hg
    simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul, dotProduct_zero] at hp
    have hr := row j
    rw [hp, zero_sub] at hr
    simpa only [neg, dotProduct_sum, dotProduct_smul, smul_eq_mul] using hr
  have total : -(neg ⬝ᵥ neg) = ∑ j, g j * g j := by
    calc
      -(neg ⬝ᵥ neg) = ∑ j, -(g j * ((x j).val.2 ⬝ᵥ neg)) := by
        conv_lhs => rw [show neg = ∑ j, g j • (x j).val.2 from rfl]
        simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul, Finset.sum_neg_distrib]
        rfl
      _ = ∑ j, g j * g j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← mul_neg, each j]
  have hi : g i * g i ≤ ∑ j, g j * g j :=
    Finset.single_le_sum (fun j _ => mul_self_nonneg (g j)) (Finset.mem_univ i)
  have hn := dot_nonneg neg
  have hz : g i * g i = 0 := by nlinarith
  exact (mul_self_eq_zero.mp hz)

/-- The clique bound depends only on the positive index. -/
theorem cliqueFree (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (m n : ℕ) : (graph K m n).CliqueFree (m + 1) := by
  classical
  intro s hs
  have hi := positive_independent (fun a : s => a.val) (fun a b hab =>
    hs.1 a.property b.property (fun he => hab (Subtype.ext he)))
  have hc := hi.fintype_card_le_finrank
  rw [Module.finrank_pi, Fintype.card_fin, Fintype.card_coe, hs.2] at hc
  omega

/-- In particular all signatures (3,n) give K4-free graphs. -/
theorem cliqueFree_four (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (n : ℕ) : (graph K 3 n).CliqueFree 4 := cliqueFree K 3 n

#print axioms positive_independent
#print axioms cliqueFree_four
end Erdos595IndefiniteUnit
