import Submission.SquareZeroPolynomial

/-! A uniform obstruction to retaining a positive fraction of the edges in
polynomial incidence graphs modulo a square. This does not settle Erdős 714. -/

set_option maxHeartbeats 3000000
noncomputable section
open Classical SimpleGraph
namespace Erdos714SquareZeroCongruence
open Erdos714SquareZero

variable (n : ℕ) [NeZero n]

def reduction : ZMod (n^2) →+* ZMod n := ZMod.castHom (dvd_pow_self n (by decide)) (ZMod n)
def squareIdeal : Ideal (ZMod (n^2)) := RingHom.ker (reduction n)

lemma reduction_surjective : Function.Surjective (reduction n) := by
  intro a
  refine ⟨(a.val : ZMod (n^2)),?_⟩
  simp

lemma squareIdeal_mul (a b : squareIdeal n) :
    (a : ZMod (n^2))*(b : ZMod (n^2))=0 := by
  have hd (a : squareIdeal n) : n ∣ (a : ZMod (n^2)).val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    have hh : reduction n (a : ZMod (n^2))=0 := a.property
    rw [←ZMod.natCast_zmod_val (a : ZMod (n^2)),map_natCast] at hh
    exact hh
  obtain ⟨u,hu⟩ := hd a
  obtain ⟨v,hv⟩ := hd b
  have he : (a : ZMod (n^2))*(b : ZMod (n^2)) = ((n^2*(u*v) : ℕ) : ZMod (n^2)) := by
    rw [←ZMod.natCast_zmod_val (a : ZMod (n^2)),
      ←ZMod.natCast_zmod_val (b : ZMod (n^2)),hu,hv]
    push_cast
    ring
  rw [he]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_mul_right _ _)

lemma squareIdeal_card : Fintype.card (squareIdeal n)=n := by
  have hcard := Fintype.card_congr (cosetEquiv (squareIdeal n))
  have hquot : Fintype.card (ZMod (n^2) ⧸ squareIdeal n) = n := by
    simpa only [squareIdeal,Fintype.card_eq_nat_card,Nat.card_zmod] using
      Fintype.card_congr (RingHom.quotientKerEquivOfSurjective (reduction_surjective n)).toEquiv
  simp only [Fintype.card_prod,hquot,ZMod.card,pow_two] at hcard
  exact Nat.mul_left_cancel (NeZero.pos n) hcard

/-- In four variables on each side, the retained density is at most
`10368^(1/4) / n^(3/4)` over `ZMod (n^2)`, uniformly in the defining polynomial. -/
theorem four_dimensional_thinning
    (P : MvPolynomial (Fin 4 ⊕ Fin 4) (ZMod (n^2)))
    (H : SimpleGraph ((Fin 4 → ZMod (n^2)) ⊕ (Fin 4 → ZMod (n^2))))
    (hHG : H ≤ polynomialGraph P)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    n^3*H.edgeFinset.card^4 ≤ 10368*(polynomialGraph P).edgeFinset.card^4 := by
  have hh := full_polynomial_thinning (squareIdeal n) (squareIdeal_mul n) P H 3
    (by simp) (by simp) hHG hfree
  simp only [edgeFinset_card,Fintype.card_eq_nat_card] at hh ⊢
  have he := squareIdeal_card n
  simp only [Fintype.card_eq_nat_card] at he
  rwa [he] at hh

end Erdos714SquareZeroCongruence
#print axioms Erdos714SquareZeroCongruence.squareIdeal_mul
#print axioms Erdos714SquareZeroCongruence.squareIdeal_card
#print axioms Erdos714SquareZeroCongruence.four_dimensional_thinning
