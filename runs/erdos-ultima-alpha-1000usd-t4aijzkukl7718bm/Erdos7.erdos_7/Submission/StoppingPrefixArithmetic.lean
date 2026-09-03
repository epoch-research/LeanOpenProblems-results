import Submission.StoppingPrefixClosure

/-! Actual adjacent-modulus marks in the full predictable stopping-prefix
closure. The resulting terminality condition is necessary, not a contradiction. -/
namespace Erdos7StoppingPrefixArithmetic
open scoped BigOperators
open Erdos7Digits Erdos7Compression Erdos7Reduction Erdos7AllDigits
open Erdos7StoppingDigitRestriction Erdos7StoppingPrefixClosure
set_option autoImplicit false
set_option maxHeartbeats 3000000

section Marks
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p E : ι → ℕ) (i₀ : ι) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (a : κ → ℤ)

/-- A class crossing the proposed deletion node blocks its digit if its image
is a unit, or its adjacent lower companion has a reached, unshortened prefix. -/
def Block (B : Set (Node (E i₀) (Fin (p i₀))))
    (u : Node (E i₀) (Fin (p i₀))) (r : Fin (p i₀)) : Prop :=
  ∃ k, u.1.val < e k i₀ ∧
    node (zmodDigits (p i₀) (E i₀) (a k)) u.1 = u ∧
    zmodDigits (p i₀) (E i₀) (a k) u.1 = r ∧
    ((∀ i, eraseExponent i₀ u.1.val (e k) i = 0) ∨
      ∃ l, e k i₀ = e l i₀+1 ∧ (∀ i, i ≠ i₀ → e k i = e l i) ∧
      ∃ hl : e l i₀ < E i₀,
        node (zmodDigits (p i₀) (E i₀) (a l)) ⟨e l i₀,hl⟩ ∈ B)

theorem block_mono {B C : Set (Node (E i₀) (Fin (p i₀)))} (hBC : B ⊆ C)
    {u r} : Block p E i₀ e a B u r → Block p E i₀ e a C u r := by
  rintro ⟨k,hk,hu,hr,hunit | ⟨l,hl,heq,hlt,hmem⟩⟩
  · exact ⟨k,hk,hu,hr,Or.inl hunit⟩
  · exact ⟨k,hk,hu,hr,Or.inr ⟨l,hl,heq,hlt,hBC hmem⟩⟩
end Marks

/-- In a minimum-period odd cover the least full stopping-prefix closure is
terminal. This covers all predictable deletion depths, including depth0. -/
theorem minimal_period_frozen_terminal {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p E : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i)
    (hei : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k)
    (K : ℕ) (hcard : Fintype.card κ ≤ K)
    (hmin : ∀ N, N < ∏ i, p i ^ E i → ¬ HasOddArithmeticCover N K)
    (i₀ : ι) (hE : 0 < E i₀) :
    Terminal hE (Block p E i₀ e a) (Frozen hE (Block p E i₀ e a)) := by
  classical
  let F := Frozen hE (Block p E i₀ e a)
  let A (k : κ) := zmodDigits (p i₀) (E i₀) (a k)
  by_contra hn
  obtain ⟨T,V,hT,hV,hreach,hfree⟩ := policy_of_frozen_nonterminal hE
    (Block p E i₀ e a) (fun hBC => block_mono p E i₀ e a hBC) hn
  rcases minimal_period_stopping_obstruction p E hp hpi e he hei a hc K hcard hmin
    i₀ T hT V hV with ⟨k,hk,hunit⟩ | ⟨k,l,hk,hl,hadj,hother,hshort,hlong⟩
  · have hshort : (T (A k)).val < e k i₀ := by
      by_contra! hlow
      have heq := eraseExponent_eq_self i₀ (T (A k)).val (e k) hlow
      obtain ⟨i,hi⟩ := he0 k
      apply hi
      exact (congrFun heq i).symm.trans (hunit i)
    have hval : A k (T (A k)) = V (A k) :=
      hk.resolve_left (fun h => Nat.not_le_of_gt hshort h)
    apply hfree (A k)
    exact ⟨k,hshort,rfl,hval,Or.inl hunit⟩
  · have hval : A k (T (A k)) = V (A k) :=
      hk.resolve_left (fun h => Nat.not_le_of_gt hshort h)
    have hlt : e l i₀ < E i₀ := by have := he k i₀; omega
    have hmem : node (A l) ⟨e l i₀,hlt⟩ ∈ F := hreach (A l) _ hlong
    apply hfree (A k)
    exact ⟨k,hshort,rfl,hval,Or.inr ⟨l,hadj,hother,hlt,hmem⟩⟩

#print axioms block_mono
#print axioms minimal_period_frozen_terminal
end Erdos7StoppingPrefixArithmetic
