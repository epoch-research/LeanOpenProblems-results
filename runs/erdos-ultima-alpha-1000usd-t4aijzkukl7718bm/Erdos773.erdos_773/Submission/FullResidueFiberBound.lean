import Submission.MatchedResidueLifting

/-!
A uniform collision inside a long full affine fiber, and a three-quarters
ceiling for full-fiber constructions with modular pair matching. These
statements do not bound the original maximum over arbitrary root subsets.
-/
namespace Erdos773.FullResidueFiberBound
open Finset MatchedResidueLifting
set_option maxHeartbeats 1000000

def indexA (q r : ℕ) := 2*r+3*q+2
def indexB (q r : ℕ) := 2*r+7*q+3
def indexC (q r : ℕ) := 4*r+9*q+2
def indexD (q r : ℕ) := 4*r+11*q+3

/-- A polynomial identity, valid uniformly in both affine parameters. -/
theorem fiber_identity (q r : ℕ) :
    (q*indexA q r+r)^2+(q*indexD q r+r)^2 =
      (q*indexB q r+r)^2+(q*indexC q r+r)^2 := by
  unfold indexA indexB indexC indexD
  ring

lemma indices_order (q r : ℕ) (hq : 0 < q) :
    indexA q r < indexB q r ∧ indexB q r < indexC q r ∧
      indexC q r < indexD q r := by
  unfold indexA indexB indexC indexD
  omega

private lemma square_mem {q H r k : ℕ} {R : Finset ℕ}
    (hr : r ∈ R) (hk : k ≤ H) :
    (q*k+r)^2 ∈ (roots q H R).image (fun n => n^2) := by
  apply mem_image.mpr
  refine ⟨q*k+r, ?_,rfl⟩
  exact mem_image.mpr ⟨(r,k),mem_product.mpr ⟨hr,mem_Icc.mpr ⟨Nat.zero_le _,hk⟩⟩,rfl⟩

/-- One full fiber already contains a nontrivial collision by this explicit index. -/
theorem long_fiber_not_sidon {q H r : ℕ} {R : Finset ℕ} (hq : 0 < q)
    (hr : r ∈ R) (hH : indexD q r ≤ H) :
    ¬ IsSidon (((roots q H R).image (fun n => n^2)) : Set ℕ) := by
  intro hs
  obtain ⟨hab,hbc,hcd⟩ := indices_order q r hq
  have ha := square_mem (q := q) hr ((hab.trans (hbc.trans hcd)).le.trans hH)
  have hb := square_mem (q := q) hr ((hbc.trans hcd).le.trans hH)
  have hc := square_mem (q := q) hr (hcd.le.trans hH)
  have hd := square_mem (q := q) hr hH
  have hAB : q*indexA q r+r < q*indexB q r+r := by nlinarith
  have hAC : q*indexA q r+r < q*indexC q r+r := by nlinarith
  have hAB2 : (q*indexA q r+r)^2 < (q*indexB q r+r)^2 :=
    Nat.pow_lt_pow_left hAB (by decide : (2 : ℕ) ≠ 0)
  have hAC2 : (q*indexA q r+r)^2 < (q*indexC q r+r)^2 :=
    Nat.pow_lt_pow_left hAC (by decide : (2 : ℕ) ≠ 0)
  rcases hs _ ha _ hb _ hd _ hc (fiber_identity q r) with h | h <;> omega

/-- For canonical residues, a nonempty union of full fibers that is Sidon
must have fewer than 15q index steps. No modular matching hypothesis is used. -/
theorem full_fiber_length_bound (q H : ℕ) (R : Finset ℕ) (hq : 0 < q)
    (hR : ∀ r ∈ R, r < q) (hne : R.Nonempty)
    (hs : IsSidon (((roots q H R).image (fun n => n^2)) : Set ℕ)) :
    H < 15*q := by
  obtain ⟨r,hr⟩ := hne
  have hrq := hR r hr
  by_contra! hh
  apply long_fiber_not_sidon hq hr (H := H) ?_ hs
  unfold indexD
  omega

/-- A weaker criterion than short-product injectivity still cannot give
near-linear full-fiber constructions: its cardinality is O(N^(3/4)), with
N=q(H+1). This is not an upper bound for arbitrary Sidon subsets of squares. -/
theorem full_fiber_card_bound (q H : ℕ) (R : Finset ℕ) (hq : 0 < q)
    (hR : ∀ r ∈ R, r < q) (hM : PairMatching q R)
    (hs : IsSidon (((roots q H R).image (fun n => n^2)) : Set ℕ)) :
    (roots q H R).card^4 ≤ 60*(q*(H+1))^3 := by
  by_cases hne : R.Nonempty
  · have hlen : H+1 ≤ 15*q := by
      have hh := full_fiber_length_bound q H R hq hR hne hs
      omega
    have hcard := pairMatching_card q R hq hM
    have hc2 := Nat.pow_le_pow_left hcard 2
    rw [roots_card q H R hq hR]
    calc
      _ = (R.card^2)^2*(H+1)^4 := by ring
      _ ≤ (2*q)^2*(H+1)^4 := Nat.mul_le_mul_right _ hc2
      _ = 4*q^2*(H+1)^3*(H+1) := by ring
      _ ≤ 4*q^2*(H+1)^3*(15*q) := Nat.mul_le_mul_left _ hlen
      _ = _ := by ring
  · have hR0 := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hR0,roots]

#print axioms fiber_identity
#print axioms indices_order
#print axioms long_fiber_not_sidon
#print axioms full_fiber_length_bound
#print axioms full_fiber_card_bound
end Erdos773.FullResidueFiberBound
