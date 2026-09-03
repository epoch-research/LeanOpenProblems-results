import Submission.AdaptiveTailArithmetic
import Submission.CollisionFiber

/-! The adaptive last-two-digit obstruction has a common projected arithmetic
fiber, not merely separate witnesses with incompatible cofactor residues. -/
namespace Erdos7AdaptiveTailFiber
open scoped BigOperators
open Erdos7Digits Erdos7Compression Erdos7Reduction Erdos7AllDigits
open Erdos7AdaptiveDigitRestriction Erdos7AdaptiveTailClosure
open Erdos7AdaptiveTailArithmetic Erdos7CollisionFiber
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- A single integer carries every upper digit color. Every corresponding lower
companion lies in the least closed branch set and misses that same integer. -/
theorem minimal_period_frozen_fiber {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p E : ι → ℕ) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (a : κ → ℤ) (i₀ : ι) (s : ℕ) (hE : E i₀ = s+2)
    (hp : ∀ i, (p i).Prime ∧ Odd (p i)) (hpi : Function.Injective p)
    (he : ∀ k i, e k i ≤ E i) (hei : Function.Injective e)
    (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k)
    (K : ℕ) (hcard : Fintype.card κ ≤ K)
    (hmin : ∀ N, N < ∏ i, p i ^ E i → ¬ HasOddArithmeticCover N K)
    (hs0 : 0 < s) :
    let B := Frozen (middleMark p E e a i₀ s hE) (upperMark p E e a i₀ s hE)
    ∃ x : ℤ,
      branch p E i₀ s (by omega) x ∈ B ∧
      ∀ r : Fin (p i₀), ∃ k l,
        e k i₀ = s+2 ∧ e l i₀ = s+1 ∧ sameCofactor e i₀ k l ∧
        labels p E a i₀ s hE l ∈ B ∧
        highLabel p E a i₀ s hE k = r ∧
        ((∏ i, p i ^ eraseExponent i₀ (s+1) (e k) i : ℕ) : ℤ) ∣ x-a k ∧
        ¬ ((∏ i, p i ^ e l i : ℕ) : ℤ) ∣ x-a l := by
  classical
  let M := middleMark p E e a i₀ s hE
  let A := upperMark p E e a i₀ s hE
  let B := Frozen M A
  let hs : s+1 < E i₀ := by omega
  let pos := tailPosition s hs B
  let T (k : κ) := chosenPosition p E i₀ s (by omega) pos (a k)
  have hpos (u : Branch p i₀ s) : s ≤ (pos u).val := tailPosition_ge s hs B u
  have hT (k : κ) : (T k).val =
      if labels p E a i₀ s hE k ∈ B then s+1 else s := by
    simp only [T,chosenPosition,pos,tailPosition,labels]
    split_ifs <;> rfl
  let Bad (k : κ) := ∃ l, e k i₀ = e l i₀ + 1 ∧ sameCofactor e i₀ k l ∧
    (T k).val < e k i₀ ∧ e l i₀ ≤ (T l).val
  have hcp : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i).1 (hp j).1).mpr (fun h => hij (hpi h))
  obtain ⟨b,hb,hcover⟩ := simultaneous_adaptive_restriction p E i₀ s (by omega)
    pos hpos (fun i => (hp i).1.pos) hcp e he a hc
  have hinj (k l : κ) (hk : ¬ Bad k) (hl : ¬ Bad l)
      (hkl : eraseExponent i₀ (T k).val (e k) =
        eraseExponent i₀ (T l).val (e l)) : k = l := by
    rcases erase_eq_cases i₀ (T k).val (T l).val (e k) (e l) hkl with hh | hh | hh
    · exact hei hh
    · exact (hk ⟨l,hh.1,hh.2.2.2,hh.2.1,hh.2.2.1⟩).elim
    · exact (hl ⟨k,hh.1,hh.2.2.2,hh.2.1,hh.2.2.1⟩).elim
  have hnot : ¬ ∀ x : ℤ, ∃ k, (¬ Bad k) ∧
      ((∏ i, p i ^ eraseExponent i₀ (T k).val (e k) i : ℕ) : ℤ) ∣ x-b k := by
    intro hcov
    obtain ⟨N,hNlt,hN⟩ := individual_smaller_period p E hp hpi e he i₀ T
      (fun k => ¬ Bad k) b hcov
      (fun k _ => positive_position_nonunit i₀ (T k).val
        (hs0.trans_le (hpos _)) (e k) (he0 k)) hinj
    apply hmin N hNlt
    obtain ⟨hNpos,ν,fν,n,c,hni,hn,hnc,hnN,hncard⟩ := hN
    exact ⟨hNpos,ν,fν,n,c,hni,hn,hnc,hnN,hncard.trans hcard⟩
  push_neg at hnot
  obtain ⟨x,hx⟩ := hnot
  obtain ⟨low,hlo⟩ := choices_outside_closed M A B (frozen_closed M A)
  have hfind (r : Fin (p i₀)) : ∃ k l,
      e k i₀ = s+2 ∧ e l i₀ = s+1 ∧ sameCofactor e i₀ k l ∧
      labels p E a i₀ s hE k ∈ B ∧ labels p E a i₀ s hE l ∈ B ∧
      highLabel p E a i₀ s hE k = r ∧
      ((∏ i, p i ^ eraseExponent i₀ (s+1) (e k) i : ℕ) : ℤ) ∣ x-a k ∧
      ¬ ((∏ i, p i ^ e l i : ℕ) : ℤ) ∣ x-a l := by
    let digit := tailDigit s hs B low (fun _ _ => r)
    obtain ⟨k,hk,hdiv⟩ := hcover digit x
    have hbad : Bad k := by by_contra hn; exact hx k hn hdiv
    obtain ⟨l,hkl,hother,hshort,hlong⟩ := hbad
    let uk := labels p E a i₀ s hE k
    let ul := labels p E a i₀ s hE l
    have hge : s+1 ≤ e k i₀ := by
      have hh := hpos (branch p E i₀ s (by omega) (a k))
      change s ≤ (T k).val at hh
      omega
    have hle : e k i₀ ≤ s+2 := by have := he k i₀; omega
    have hactive_early (hu : uk ∉ B) : lowLabel p E a i₀ s hE k = low uk := by
      have hh := hk.resolve_left (by rw [hT,if_neg hu]; omega)
      have hd := tailDigit_early s hs B low (fun _ _ => r) hu
        (zmodDigits (p i₀) (E i₀) (a k))
      have htpos : T k = penult E i₀ s hE := by
        apply Fin.ext
        rw [hT,if_neg hu]
      have hh' := hh.trans hd
      change zmodDigits (p i₀) (E i₀) (a k) (T k) = low uk at hh'
      simpa only [htpos,lowLabel] using hh'
    have huk : uk ∈ B := by
      by_contra hn
      apply hlo uk hn
      by_cases hmid : e k i₀ = s+1
      · exact Or.inl ⟨k,l,hmid,by omega,hother,rfl,hactive_early hn⟩
      · have htop : e k i₀ = s+2 := by omega
        have hul : ul ∈ B := by
          by_contra h
          rw [hT,if_neg h] at hlong
          omega
        exact Or.inr ⟨highLabel p E a i₀ s hE k,ul,hul,
          k,l,htop,by omega,hother,rfl,hactive_early hn,rfl,rfl⟩
    have htop : e k i₀ = s+2 := by rw [hT,if_pos huk] at hshort; omega
    have hll : e l i₀ = s+1 := by omega
    have hul : ul ∈ B := by
      by_contra h
      rw [hT,if_neg h] at hlong
      omega
    have hTk : T k = topDigit E i₀ s hE := by apply Fin.ext; rw [hT,if_pos huk]
    have hTl : T l = topDigit E i₀ s hE := by apply Fin.ext; rw [hT,if_pos hul]
    have hcolor : highLabel p E a i₀ s hE k = r := by
      have hh := hk.resolve_left (by rw [hT,if_pos huk]; omega)
      have hd := tailDigit_late s hs B low (fun _ _ => r) huk
        (zmodDigits (p i₀) (E i₀) (a k))
      have hh' := hh.trans hd
      change zmodDigits (p i₀) (E i₀) (a k) (T k) = r at hh'
      simpa only [hTk,highLabel] using hh'
    have hbak := low_deleted_residue p E hcp (e k) (he k) i₀ (T k)
      (a k) (b k) (hb k) (by rw [hTk]; change e k i₀ ≤ s+1+1; omega)
    have hxl : ¬ ((∏ i, p i ^ e l i : ℕ) : ℤ) ∣ x-a l := by
      have hsafe : ¬ Bad l := by
        rintro ⟨j,_,_,hh,_⟩
        rw [hTl] at hh
        change s+1 < e l i₀ at hh
        omega
      have hbal := low_deleted_residue p E hcp (e l) (he l) i₀ (T l)
        (a l) (b l) (hb l) (by rw [hTl]; change e l i₀ ≤ s+1+1; omega)
      have hel : eraseExponent i₀ (T l).val (e l) = e l :=
        eraseExponent_eq_self i₀ (T l).val (e l) (by rw [hTl]; exact hll.le)
      rw [hel] at hbal
      intro hxal
      apply hx l hsafe
      rw [hel]
      convert dvd_sub hxal hbal using 1 <;> ring
    refine ⟨k,l,htop,hll,hother,huk,hul,hcolor,?_,hxl⟩
    have hxa := dvd_add hdiv hbak
    change ((∏ i, p i ^ eraseExponent i₀ (T k).val (e k) i : ℕ) : ℤ) ∣
      x-b k+(b k-a k) at hxa
    rw [hTk] at hxa
    convert hxa using 1 <;> ring
  have hbranch (k : κ) (htop : e k i₀ = s+2)
      (hdiv : ((∏ i, p i ^ eraseExponent i₀ (s+1) (e k) i : ℕ) : ℤ) ∣ x-a k) :
      branch p E i₀ s (by omega) x = labels p E a i₀ s hE k := by
    apply prefix_agree
    intro j hj
    apply (divisor_product_iff_digits p E (eraseExponent i₀ (s+1) (e k))
      (fun i => (eraseExponent_le i₀ (s+1) (e k) i).trans (he k i))
      hcp x (a k)).mp hdiv i₀ j
    simp only [eraseExponent_self,eraseLevel,htop]
    split_ifs <;> omega
  refine ⟨x,?_,fun r => ?_⟩
  · obtain ⟨k,l,hk,hl,ho,huk,hul,hr,hdiv,hn⟩ := hfind 0
    rw [hbranch k hk hdiv]
    exact huk
  · obtain ⟨k,l,hk,hl,ho,huk,hul,hr,hdiv,hn⟩ := hfind r
    exact ⟨k,l,hk,hl,ho,hul,hr,hdiv,hn⟩

#print axioms minimal_period_frozen_fiber
end Erdos7AdaptiveTailFiber
