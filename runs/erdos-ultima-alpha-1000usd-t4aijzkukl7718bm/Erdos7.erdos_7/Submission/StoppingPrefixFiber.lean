import Submission.StoppingPrefixArithmetic
import Submission.CollisionFiber

/-! The full stopping-prefix obstruction has one common top arithmetic fiber.
This is a necessary condition on minimum-period covers, not a noncoverage proof. -/
namespace Erdos7StoppingPrefixFiber
open scoped BigOperators
open Erdos7Digits Erdos7Compression Erdos7Reduction Erdos7AllDigits
open Erdos7AdaptiveDigitRestriction Erdos7CollisionFiber
open Erdos7StoppingDigitRestriction Erdos7StoppingPrefixClosure
open Erdos7StoppingPrefixArithmetic
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- All top colors can be chosen at one projected integer, with their lower
companions in the least full prefix closure and missing that same integer. -/
theorem minimal_period_frozen_fiber {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p E : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i)
    (hei : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k)
    (K : ℕ) (hcard : Fintype.card κ ≤ K)
    (hmin : ∀ N, N < ∏ i, p i ^ E i → ¬ HasOddArithmeticCover N K)
    (i₀ : ι) (hE : 2 ≤ E i₀) :
    let hE0 : 0 < E i₀ := by omega
    let t : Fin (E i₀) := ⟨E i₀-1,by omega⟩
    let F := Frozen hE0 (Block p E i₀ e a)
    ∃ x : ℤ, node (zmodDigits (p i₀) (E i₀) x) t ∈ F ∧
      ∀ r : Fin (p i₀), ∃ k l,
        e k i₀ = E i₀ ∧ e l i₀ = E i₀-1 ∧
        (∀ i, i ≠ i₀ → e k i = e l i) ∧
        node (zmodDigits (p i₀) (E i₀) (a l)) t ∈ F ∧
        zmodDigits (p i₀) (E i₀) (a k) t = r ∧
        ((∏ i, p i ^ eraseExponent i₀ t.val (e k) i : ℕ) : ℤ) ∣ x-a k ∧
        ¬ ((∏ i, p i ^ e l i : ℕ) : ℤ) ∣ x-a l := by
  classical
  dsimp only
  let hE0 : 0 < E i₀ := by omega
  let t : Fin (E i₀) := ⟨E i₀-1,by omega⟩
  let F := Frozen hE0 (Block p E i₀ e a)
  let A (k : κ) := zmodDigits (p i₀) (E i₀) (a k)
  obtain ⟨T,V,hT,hV,hreach,hfree⟩ := policy_with_terminal_fallback hE0
    (Block p E i₀ e a) F (frozen_closed hE0 (Block p E i₀ e a)
      (fun hBC => block_mono p E i₀ e a hBC))
  let S (k : κ) := T (A k)
  let Bad (k : κ) :=
    (∀ i, eraseExponent i₀ (S k).val (e k) i = 0) ∨
      ∃ l, e k i₀ = e l i₀+1 ∧ (∀ i, i ≠ i₀ → e k i = e l i) ∧
        (S k).val < e k i₀ ∧ e l i₀ ≤ (S l).val
  have hshort (k : κ) (hk : Bad k) : (S k).val < e k i₀ := by
    rcases hk with hu | ⟨l,_,_,hs,_⟩
    · by_contra! hlow
      have heq := eraseExponent_eq_self i₀ (S k).val (e k) hlow
      obtain ⟨i,hi⟩ := he0 k
      exact hi ((congrFun heq i).symm.trans (hu i))
    · exact hs
  have hblocked (k : κ) (hk : Bad k) :
      Block p E i₀ e a F (node (A k) (S k)) (A k (S k)) := by
    refine ⟨k,hshort k hk,rfl,rfl,?_⟩
    rcases hk with hu | ⟨l,hadj,hother,hs,hlong⟩
    · exact Or.inl hu
    · have hlt : e l i₀ < E i₀ := by have := he k i₀; omega
      exact Or.inr ⟨l,hadj,hother,hlt,hreach (A l) _ hlong⟩
  have hcp : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i).1 (hp j).1).mpr (fun h => hij (hpi h))
  obtain ⟨b,hb,hcover⟩ := simultaneous_stopping_restriction p E i₀ T hT
    (fun i => (hp i).1.pos) hcp e he a hc
  have hinj (k l : κ) (hk : ¬ Bad k) (hl : ¬ Bad l)
      (hkl : eraseExponent i₀ (S k).val (e k) =
        eraseExponent i₀ (S l).val (e l)) : k = l := by
    rcases erase_eq_cases i₀ (S k).val (S l).val (e k) (e l) hkl with hh | hh | hh
    · exact hei hh
    · exact (hk (Or.inr ⟨l,hh.1,hh.2.2.2,hh.2.1,hh.2.2.1⟩)).elim
    · exact (hl (Or.inr ⟨k,hh.1,hh.2.2.2,hh.2.1,hh.2.2.1⟩)).elim
  have hnot : ¬ ∀ x : ℤ, ∃ k, (¬ Bad k) ∧
      ((∏ i, p i ^ eraseExponent i₀ (S k).val (e k) i : ℕ) : ℤ) ∣ x-b k := by
    intro hcov
    have hunit (k : κ) (hk : ¬ Bad k) :
        ∃ i, eraseExponent i₀ (S k).val (e k) i ≠ 0 := by
      by_contra! hz
      exact hk (Or.inl hz)
    obtain ⟨N,hNlt,hN⟩ := individual_smaller_period p E hp hpi e he i₀ S
      (fun k => ¬ Bad k) b hcov hunit hinj
    apply hmin N hNlt
    obtain ⟨hNpos,ν,fν,n,c,hni,hn,hnc,hnN,hncard⟩ := hN
    exact ⟨hNpos,ν,fν,n,c,hni,hn,hnc,hnN,hncard.trans hcard⟩
  push_neg at hnot
  obtain ⟨x,hx⟩ := hnot
  have hfind (r : Fin (p i₀)) : ∃ k l,
      e k i₀ = E i₀ ∧ e l i₀ = E i₀-1 ∧
      (∀ i, i ≠ i₀ → e k i = e l i) ∧
      node (A k) t ∈ F ∧ node (A l) t ∈ F ∧ A k t = r ∧
      ((∏ i, p i ^ eraseExponent i₀ t.val (e k) i : ℕ) : ℤ) ∣ x-a k ∧
      ¬ ((∏ i, p i ^ e l i : ℕ) : ℤ) ∣ x-a l := by
    let Vr (y : Fin (E i₀) → Fin (p i₀)) :=
      if (T y).val = E i₀-1 then r else V y
    obtain ⟨k,hk,hdiv⟩ := hcover Vr (predictable_terminal_value hT hV r) x
    have hbad : Bad k := by by_contra hn; exact hx k hn hdiv
    have hs := hshort k hbad
    have hval : A k (S k) = Vr (A k) :=
      hk.resolve_left (fun h => Nat.not_le_of_gt hs h)
    have hlast : S k = t := by
      apply Fin.ext
      by_contra hn
      have hn' : (T (A k)).val ≠ E i₀-1 := hn
      have ht : (T (A k)).val+1 < E i₀ := by have := (S k).isLt; omega
      have hv : A k (S k) = V (A k) := by simpa only [Vr,if_neg hn'] using hval
      exact hfree (A k) ht (hv ▸ hblocked k hbad)
    have htop : e k i₀ = E i₀ := by
      rw [hlast] at hs
      have := he k i₀
      change E i₀-1 < e k i₀ at hs
      omega
    have hnunit : ¬ ∀ i, eraseExponent i₀ (S k).val (e k) i = 0 := by
      intro hz
      obtain ⟨i,hi⟩ := positive_position_nonunit i₀ (S k).val
        (by rw [hlast]; change 0 < E i₀-1; omega) (e k) (he0 k)
      exact hi (hz i)
    obtain ⟨l,hadj,hother,_,hlong⟩ := hbad.resolve_left hnunit
    have hll : e l i₀ = E i₀-1 := by omega
    have hlastl : S l = t := by
      apply Fin.ext
      have := (S l).isLt
      change (S l).val = E i₀-1
      omega
    have hsafe : ¬ Bad l := fun hh => Nat.not_lt_of_ge hlong (hshort l hh)
    have hcolor : A k t = r := by
      have hv : (T (A k)).val = E i₀-1 := congrArg Fin.val hlast
      simpa only [Vr,if_pos hv,hlast] using hval
    have hbak := low_deleted_residue p E hcp (e k) (he k) i₀ (S k)
      (a k) (b k) (hb k) (by rw [hlast]; change e k i₀ ≤ E i₀-1+1; omega)
    have hbal := low_deleted_residue p E hcp (e l) (he l) i₀ (S l)
      (a l) (b l) (hb l) (by omega)
    have hel : eraseExponent i₀ (S l).val (e l) = e l :=
      eraseExponent_eq_self i₀ (S l).val (e l) hlong
    have hxl : ¬ ((∏ i, p i ^ e l i : ℕ) : ℤ) ∣ x-a l := by
      rw [hel] at hbal
      intro hxal
      apply hx l hsafe
      rw [hel]
      convert dvd_sub hxal hbal using 1 <;> ring
    refine ⟨k,l,htop,hll,hother,?_,?_,hcolor,?_,hxl⟩
    · exact hreach (A k) t (by rw [←hlast])
    · exact hreach (A l) t (by rw [←hlastl])
    · have hxa := dvd_add hdiv hbak
      change ((∏ i, p i ^ eraseExponent i₀ (S k).val (e k) i : ℕ) : ℤ) ∣
        x-b k+(b k-a k) at hxa
      rw [hlast] at hxa
      convert hxa using 1 <;> ring
  refine ⟨x,?_,fun r => ?_⟩
  · obtain ⟨k,l,htop,_,_,hmem,_,_,hdiv,_⟩ := hfind 0
    have hnode : node (zmodDigits (p i₀) (E i₀) x) t = node (A k) t := by
      apply node_agree
      intro j hj
      apply (divisor_product_iff_digits p E (eraseExponent i₀ t.val (e k))
        (fun i => (eraseExponent_le i₀ t.val (e k) i).trans (he k i))
        hcp x (a k)).mp hdiv i₀ j
      simp only [eraseExponent_self,eraseLevel,htop]
      change j.val < if E i₀ ≤ E i₀-1 then E i₀ else E i₀-1
      split_ifs <;> omega
    rw [hnode]
    exact hmem
  · obtain ⟨k,l,htop,hll,hother,_,hmem,hcolor,hdiv,hn⟩ := hfind r
    exact ⟨k,l,htop,hll,hother,hmem,hcolor,hdiv,hn⟩

#print axioms minimal_period_frozen_fiber
end Erdos7StoppingPrefixFiber
