import Submission.AdaptiveDigitRestriction
import Submission.AdaptiveTailClosure

/-! The least-closed-branch obstruction is necessary in an actual minimal-period
odd arithmetic cover. This does not supply an unrestricted contradiction. -/
namespace Erdos7AdaptiveTailArithmetic
open scoped BigOperators
open Erdos7Digits Erdos7Compression Erdos7Reduction Erdos7AllDigits
open Erdos7AdaptiveDigitRestriction Erdos7AdaptiveTailClosure
set_option autoImplicit false
set_option maxHeartbeats 3000000

section Policy
variable {U α : Type*} {n : ℕ} (s : ℕ) (hs : s+1 < n)
    (B : Set U) [DecidablePred (· ∈ B)]

/-- Early branches delete position s, late branches position s+1. -/
def tailPosition (u : U) : Fin n :=
  if u ∈ B then ⟨s+1,hs⟩ else ⟨s,by omega⟩

lemma tailPosition_ge (u : U) : s ≤ (tailPosition s hs B u).val := by
  simp only [tailPosition]
  split_ifs <;> simp

variable (low : U → α) (high : U → α → α)

def tailDigit (u : U) (v : Fin (tailPosition s hs B u).val → α) : α :=
  if h : u ∈ B then high u (v ⟨s,by simp [tailPosition,h]⟩) else low u

lemma tailDigit_early {u : U} (hu : u ∉ B) (x : Fin n → α) :
    tailDigit s hs B low high u
      (shortPrefix (tailPosition s hs B u).val (tailPosition s hs B u).isLt.le x) =
      low u := by simp [tailDigit,hu]

lemma tailDigit_late {u : U} (hu : u ∈ B) (x : Fin n → α) :
    tailDigit s hs B low high u
      (shortPrefix (tailPosition s hs B u).val (tailPosition s hs B u).isLt.le x) =
      high u (x ⟨s,by omega⟩) := by simp [tailDigit,hu,shortPrefix]
end Policy

section Arithmetic
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p E : ι → ℕ) [∀ i, NeZero (p i)] (e : κ → ι → ℕ) (a : κ → ℤ)
    (i₀ : ι) (s : ℕ) (hE : E i₀ = s+2)

abbrev penult : Fin (E i₀) := ⟨s,by omega⟩
abbrev topDigit : Fin (E i₀) := ⟨s+1,by omega⟩

def labels (k : κ) : Branch p i₀ s := branch p E i₀ s (by omega) (a k)

def lowLabel (k : κ) : Fin (p i₀) := zmodDigits (p i₀) (E i₀) (a k) (penult E i₀ s hE)
def highLabel (k : κ) : Fin (p i₀) := zmodDigits (p i₀) (E i₀) (a k) (topDigit E i₀ s hE)

/-- The cofactor exponent vectors are equal. -/
def sameCofactor (k l : κ) : Prop := ∀ i, i ≠ i₀ → e k i = e l i

/-- A middle class together with its lower companion forbids an early choice. -/
def middleMark (u : Branch p i₀ s) (v : Fin (p i₀)) : Prop :=
  ∃ k l, e k i₀ = s+1 ∧ e l i₀ = s ∧ sameCofactor e i₀ k l ∧
    labels p E a i₀ s hE k = u ∧ lowLabel p E a i₀ s hE k = v

/-- An upper class records the branch of its middle companion, as well as both
of its own top digits. This is genuine residue information, not just shapes. -/
def upperMark (u : Branch p i₀ s) (v r : Fin (p i₀)) (w : Branch p i₀ s) : Prop :=
  ∃ k l, e k i₀ = s+2 ∧ e l i₀ = s+1 ∧ sameCofactor e i₀ k l ∧
    labels p E a i₀ s hE k = u ∧ lowLabel p E a i₀ s hE k = v ∧
    highLabel p E a i₀ s hE k = r ∧ labels p E a i₀ s hE l = w

/-- A period-minimal cover forces a full upper node inside the least closed set
of late branches. Both levels are linked by their actual lower companions. -/
theorem minimal_period_frozen_terminal
    (hp : ∀ i, (p i).Prime ∧ Odd (p i)) (hpi : Function.Injective p)
    (he : ∀ k i, e k i ≤ E i) (hei : Function.Injective e)
    (he0 : ∀ k, ∃ i, e k i ≠ 0)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k)
    (K : ℕ) (hcard : Fintype.card κ ≤ K)
    (hmin : ∀ N, N < ∏ i, p i ^ E i → ¬ HasOddArithmeticCover N K)
    (hs0 : 0 < s) :
    Terminal (upperMark p E e a i₀ s hE)
      (Frozen (middleMark p E e a i₀ s hE) (upperMark p E e a i₀ s hE)) := by
  classical
  let M := middleMark p E e a i₀ s hE
  let A := upperMark p E e a i₀ s hE
  let B := Frozen M A
  let hs : s+1 < E i₀ := by omega
  let pos := tailPosition s hs B
  have hpos (u : Branch p i₀ s) : s ≤ (pos u).val := tailPosition_ge s hs B u
  by_contra hn
  obtain ⟨low,high,hlo,hhi⟩ := policy_of_not_terminal M A hn
  let digit := tailDigit s hs B low high
  obtain ⟨k,l,hk,hl,hkl,hother,hshort,hlong⟩ :=
    minimal_period_adaptive_pair p E hp hpi e he hei he0 a hc K hcard hmin
      i₀ s hs0 (by omega) pos hpos digit
  let uk := labels p E a i₀ s hE k
  let ul := labels p E a i₀ s hE l
  have htk : (chosenPosition p E i₀ s (by omega) pos (a k)).val =
      if uk ∈ B then s+1 else s := by
    simp only [chosenPosition,pos,tailPosition,uk,labels]
    split_ifs <;> rfl
  have htl : (chosenPosition p E i₀ s (by omega) pos (a l)).val =
      if ul ∈ B then s+1 else s := by
    simp only [chosenPosition,pos,tailPosition,ul,labels]
    split_ifs <;> rfl
  have hge : s+1 ≤ e k i₀ := by
    have hh := hpos (branch p E i₀ s (by omega) (a k))
    change s ≤ (chosenPosition p E i₀ s (by omega) pos (a k)).val at hh
    omega
  have hle : e k i₀ ≤ s+2 := by have := he k i₀; omega
  have hactive_early (hu : uk ∉ B) : lowLabel p E a i₀ s hE k = low uk := by
    have hh : zmodDigits (p i₀) (E i₀) (a k)
        (chosenPosition p E i₀ s (by omega) pos (a k)) =
      digit uk (shortPrefix (pos uk).val (pos uk).isLt.le
        (zmodDigits (p i₀) (E i₀) (a k))) := by
      exact hk.resolve_left (by rw [htk,if_neg hu]; omega)
    have hd := tailDigit_early s hs B low high hu
      (zmodDigits (p i₀) (E i₀) (a k))
    change _ = low uk at hd
    have htpos : chosenPosition p E i₀ s (by omega) pos (a k) = penult E i₀ s hE := by
      apply Fin.ext
      rw [htk,if_neg hu]
    have hh' := hh.trans hd
    simpa only [htpos,lowLabel] using hh'
  have hactive_late (hu : uk ∈ B) (hlevel : e k i₀ = s+2) :
      highLabel p E a i₀ s hE k = high uk (lowLabel p E a i₀ s hE k) := by
    have hh : zmodDigits (p i₀) (E i₀) (a k)
        (chosenPosition p E i₀ s (by omega) pos (a k)) =
      digit uk (shortPrefix (pos uk).val (pos uk).isLt.le
        (zmodDigits (p i₀) (E i₀) (a k))) := by
      exact hk.resolve_left (by rw [htk,if_pos hu]; omega)
    have hd := tailDigit_late s hs B low high hu
      (zmodDigits (p i₀) (E i₀) (a k))
    have htpos : chosenPosition p E i₀ s (by omega) pos (a k) = topDigit E i₀ s hE := by
      apply Fin.ext
      rw [htk,if_pos hu]
    have hh' := hh.trans hd
    simpa only [htpos,lowLabel,highLabel,penult,topDigit] using hh'
  by_cases hmid : e k i₀ = s+1
  · have huk : uk ∉ B := by intro hh; rw [htk,if_pos hh] at hshort; omega
    have hll : e l i₀ = s := by omega
    apply hlo uk huk
    exact Or.inl ⟨k,l,hmid,hll,hother,rfl,hactive_early huk⟩
  · have htop : e k i₀ = s+2 := by omega
    have hll : e l i₀ = s+1 := by omega
    have hul : ul ∈ B := by
      by_contra h
      rw [htl,if_neg h] at hlong
      omega
    by_cases huk : uk ∈ B
    · apply hhi uk huk (lowLabel p E a i₀ s hE k) ul hul
      exact ⟨k,l,htop,hll,hother,rfl,rfl,hactive_late huk htop,rfl⟩
    · apply hlo uk huk
      exact Or.inr ⟨highLabel p E a i₀ s hE k,ul,hul,
        k,l,htop,hll,hother,rfl,hactive_early huk,rfl,rfl⟩
end Arithmetic

#print axioms minimal_period_frozen_terminal
end Erdos7AdaptiveTailArithmetic
