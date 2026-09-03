import Submission.ConsecutiveSquares
import Submission.QuinticNormLift

/-!
A parametric obstruction to a sheared quadratic norm plus a cubic. This file
rules out a proposed graph construction, not the extremal conjecture itself.
-/

set_option maxHeartbeats 2000000

open SimpleGraph Finset Classical

namespace Erdos714ShearedNorm

variable {F : Type*} [Field F] [CharP F 3]

private lemma two_ne_zero : (2 : F) ≠ 0 := by
  intro h
  have h3 := CharP.cast_eq_zero F 3
  apply (one_ne_zero : (1 : F) ≠ 0)
  linear_combination h3-h

/-- The inhomogeneous, balanced-fiber candidate. -/
def form (v : F × F × F) : F :=
  (v.1-v.2.2*v.2.1)^2 + v.2.1^2 + v.2.2^3

/-- Zero-weight vertices are isolated; all nonzero weights are present. -/
def graph : SimpleGraph (((F × F × F) × F) ⊕ ((F × F × F) × F)) where
  Adj u v := match u, v with
    | .inl x, .inr y => x.2 ≠ 0 ∧ y.2 ≠ 0 ∧ form (x.1+y.1) = x.2*y.2
    | .inr y, .inl x => x.2 ≠ 0 ∧ y.2 ≠ 0 ∧ form (x.1+y.1) = x.2*y.2
    | _, _ => False
  symm := by intro u v; cases u <;> cases v <;> simp_all
  loopless := by intro u; cases u <;> simp

lemma vertical_plus (r u s : F) (hu : u^2 = r^2-1)
    (hs : s^2 = r^2*(s+1)) :
    form ((0,0,s) + (-r,r,1)) = -(u^2+s^3) := by
  dsimp [form]
  linear_combination (norm := (ring_nf; reduce_mod_char!)) hu - s*hs

lemma vertical_minus (r u s : F) (hu : u^2 = r^2-1)
    (hs : s^2 = r^2*(s+1)) :
    form ((0,0,s) + (r,-r,1)) = -(u^2+s^3) := by
  dsimp [form]
  linear_combination (norm := (ring_nf; reduce_mod_char!)) hu - s*hs

/-- Four rows and two opposite pairs of columns. The hypotheses include every
nonzero weight and distinctness condition used in the actual graph copy. -/
def parametricCopy (r u p m : F) (hr : r ≠ 0) (hu0 : u ≠ 0)
    (hu : u^2 = r^2-1) (hp : p^2 = r^2*(p+1)) (hm : m^2 = r^2*(m+1))
    (hp0 : p ≠ 0) (hm0 : m ≠ 0) (hpm : p ≠ m)
    (hwp : u^2+p^3 ≠ 0) (hwm : u^2+m^3 ≠ 0) :
    Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph (F := F)) := by
  classical
  let rp : Fin 4 → F × F × F := ![(0,0,0),(0,1,0),(0,0,p),(0,0,m)]
  let rw : Fin 4 → F := ![1,r^2/u^2,(u^2+p^3)/u^2,(u^2+m^3)/u^2]
  let cp : Fin 4 → F × F × F := ![(u,0,0),(-u,0,0),(-r,r,1),(r,-r,1)]
  let cw : Fin 4 → F := ![u^2,u^2,-u^2,-u^2]
  have hu2 : u^2 ≠ 0 := pow_ne_zero _ hu0
  have hr2 : r^2 ≠ 0 := pow_ne_zero _ hr
  have huneg : u ≠ -u := by
    intro h
    have hh : (2 : F)*u = 0 := by linear_combination h
    exact mul_ne_zero two_ne_zero hu0 hh
  have hrneg : r ≠ -r := by
    intro h
    have hh : (2 : F)*r = 0 := by linear_combination h
    exact mul_ne_zero two_ne_zero hr hh
  have hrp : Function.Injective rp := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [rp, Ne.symm hp0, Ne.symm hm0, Ne.symm hpm]
  have hcp : Function.Injective cp := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [cp, Ne.symm huneg, Ne.symm hrneg]
  have hrw (i : Fin 4) : rw i ≠ 0 := by
    fin_cases i <;> simp [rw, hu2, hr2, hwp, hwm]
  have hcw (i : Fin 4) : cw i ≠ 0 := by
    fin_cases i <;> simp [cw, hu2]
  have hp3 : p^3 = r^2*(r^2+1)*p+r^4 := by
    linear_combination (p+r^2)*hp
  have hm3 : m^3 = r^2*(r^2+1)*m+r^4 := by
    linear_combination (m+r^2)*hm
  have he (i j : Fin 4) : form (rp i + cp j) = rw i * cw j := by
    fin_cases i <;> fin_cases j <;> norm_num [rp, rw, cp, cw, hu2]
    all_goals dsimp [form]
    all_goals apply sub_eq_zero.mp
    all_goals try ring_nf
    all_goals try simp only [hu, hp, hm, hp3, hm3]
    all_goals try ring_nf
    all_goals reduce_mod_char!

  let left : Fin 4 ↪ (F × F × F) × F :=
    ⟨fun i => (rp i, rw i), fun _ _ h => hrp (congrArg Prod.fst h)⟩
  let right : Fin 4 ↪ (F × F × F) × F :=
    ⟨fun i => (cp i, cw i), fun _ _ h => hcp (congrArg Prod.fst h)⟩
  refine ⟨⟨left.sumMap right, ?_⟩, (left.sumMap right).injective⟩
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl j => simp at hab
    | inr j => exact ⟨hrw i, hcw j, he i j⟩
  | inr j =>
    cases b with
    | inr i => simp at hab
    | inl i => exact ⟨hrw i, hcw j, he i j⟩

/-- The consecutive-square parameters give two distinct nonzero vertical shifts.
A fifth-root condition ensures that neither of their row weights vanishes. -/
theorem not_free_of_squares (r u h : F) (hr : r ≠ 0) (hu0 : u ≠ 0) (hh0 : h ≠ 0)
    (hu : u^2 = r^2-1) (hh : h^2 = r^2+1)
    (h5 : (r^2)^5 ≠ 1) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F)) := by
  let p := -r^2+r*h
  let m := -r^2-r*h
  have hp : p^2 = r^2*(p+1) := by
    dsimp [p]
    linear_combination (norm := (ring_nf; reduce_mod_char!)) r^2*hh
  have hm : m^2 = r^2*(m+1) := by
    dsimp [m]
    linear_combination (norm := (ring_nf; reduce_mod_char!)) r^2*hh
  have hsum : p+m = r^2 := by dsimp [p,m]; apply sub_eq_zero.mp; ring_nf; reduce_mod_char!
  have hprod : p*m = -r^2 := by
    dsimp [p,m]
    linear_combination -r^2*hh
  have hp0 : p ≠ 0 := fun he => (neg_ne_zero.mpr (pow_ne_zero 2 hr))
    (by simpa [he] using hprod.symm)
  have hm0 : m ≠ 0 := fun he => (neg_ne_zero.mpr (pow_ne_zero 2 hr))
    (by simpa [he] using hprod.symm)
  have hpm : p ≠ m := by
    intro he
    have ht : (2 : F)*(r*h) = 0 := by dsimp [p,m] at he; linear_combination he
    exact mul_ne_zero two_ne_zero (mul_ne_zero hr hh0) ht
  have hnum (s : F) (hs : s^2 = r^2*(s+1)) :
      u^2+s^3 = r^2*(r^2+1)*s + (r^4+r^2-1) := by
    linear_combination (s+r^2)*hs + hu
  have hnums : (u^2+p^3)*(u^2+m^3)*(r^2-1) = (r^2)^5-1 := by
    rw [hnum p hp, hnum m hm]
    have he : (r^2*(r^2+1)*p + (r^4+r^2-1)) *
        (r^2*(r^2+1)*m + (r^4+r^2-1)) =
        (r^2*(r^2+1))^2*(p*m) +
          (r^2*(r^2+1))*(r^4+r^2-1)*(p+m) + (r^4+r^2-1)^2 := by ring
    rw [he, hprod, hsum]
    apply sub_eq_zero.mp
    ring_nf
    reduce_mod_char!
  have hwp : u^2+p^3 ≠ 0 := by
    intro he
    have hz : (r^2)^5-1 = 0 := by simpa [he] using hnums.symm
    exact h5 (sub_eq_zero.mp hz)
  have hwm : u^2+m^3 ≠ 0 := by
    intro he
    have hz : (r^2)^5-1 = 0 := by simpa [he] using hnums.symm
    exact h5 (sub_eq_zero.mp hz)
  intro hfree
  exact hfree ⟨parametricCopy r u p m hr hu0 hu hp hm hp0 hm0 hpm hwp hwm⟩

/-- Uniformly for every field of order 3^(2k+3), the candidate contains K44. -/
theorem odd_degree_not_free [Fintype F] (k : ℕ)
    (hcard : Fintype.card F = 3^(2*k+3)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F)) := by
  have hns : ¬IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff]
    push_neg
    rw [hcard]
    norm_num [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
  have hq : 3 < Fintype.card F := by
    rw [hcard, pow_add]
    have hh : 1 ≤ 3^(2*k) := Nat.one_le_pow _ _ (by decide)
    norm_num
    omega
  obtain ⟨R,hR0,hRm,hRp,hsR,hsU,hsH⟩ :=
    Erdos714ConsecutiveSquares.exists_three_squares hns hq
  obtain ⟨r,hr⟩ := (isSquare_iff_exists_sq R).mp hsR
  obtain ⟨u,hu⟩ := (isSquare_iff_exists_sq (R-1)).mp hsU
  obtain ⟨h,hh⟩ := (isSquare_iff_exists_sq (R+1)).mp hsH
  have hr0 : r ≠ 0 := by intro he; simp [he] at hr; exact hR0 hr
  have hu0 : u ≠ 0 := by intro he; simp [he] at hu; exact hRm hu
  have hh0 : h ≠ 0 := by intro he; simp [he] at hh; exact hRp hh
  have hpow : Function.Injective (fun x : F => x^5) :=
    (Finite.injective_iff_surjective).mpr
      (Erdos714QuinticNormLift.fifth_power_surjective (k+1) (by convert hcard using 1))
  apply not_free_of_squares r u h hr0 hu0 hh0
  · rw [← hr]; exact hu.symm
  · rw [← hr]; exact hh.symm
  · intro he
    have hhR : r^2 = 1 := hpow (by simpa using he)
    exact hRm (by rw [hr, hhR]; ring)

#print axioms parametricCopy
#print axioms not_free_of_squares
#print axioms odd_degree_not_free

end Erdos714ShearedNorm
