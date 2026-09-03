import Submission.FourRepresentativeKernels

/-! Numerical consequences of the four-color classification. Five distinct
colors have no zero contact, and no color has three doubled contacts. -/
namespace Erdos184Work.AllowedFourCounts
open FourNumericalPatterns
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
local instance : Fintype (Equiv.Perm (Fin 4)) := fintypePerm
local instance : Fintype (Equiv.Perm (Fin 5)) := fintypePerm

def value (k : Fin 9) (i j : Fin 4) : ℕ := (between (representative k) i j).val

lemma zero_opposite_valid : ∀ k : Fin 9, k ∈ FourRepresentativeKernels.allowed →
    ∀ p : Equiv.Perm (Fin 4), value k (p 0) (p 1) = 0 → value k (p 2) (p 3) = 0 := by
  decide +kernel

lemma no_three_doubles_valid : ∀ k : Fin 9, k ∈ FourRepresentativeKernels.allowed →
    ∀ p : Equiv.Perm (Fin 4), ¬ (value k (p 0) (p 1) = 2 ∧
      value k (p 0) (p 2) = 2 ∧ value k (p 0) (p 3) = 2) := by
  decide +kernel

variable {I : Type*} (a : I → I → ℕ)

def Pattern (T : Fin 4 → I) : Prop :=
  ∃ k : Fin 9, k ∈ FourRepresentativeKernels.allowed ∧
    ∃ p : Equiv.Perm (Fin 4), ∀ i j, i ≠ j → a (T (p i)) (T (p j)) = value k i j

lemma zero_opposite {T : Fin 4 → I} (h : Pattern a T)
    (hz : a (T 0) (T 1) = 0) : a (T 2) (T 3) = 0 := by
  obtain ⟨k,hk,p,hp⟩ := h
  have h01 := hp (p.symm 0) (p.symm 1) (p.symm.injective.ne (by decide))
  have h23 := hp (p.symm 2) (p.symm 3) (p.symm.injective.ne (by decide))
  simp only [p.apply_symm_apply] at h01 h23
  exact h23.trans (zero_opposite_valid k hk p.symm (h01.symm.trans hz))

lemma no_three_doubles {T : Fin 4 → I} (h : Pattern a T) :
    ¬ (a (T 0) (T 1) = 2 ∧ a (T 0) (T 2) = 2 ∧ a (T 0) (T 3) = 2) := by
  obtain ⟨k,hk,p,hp⟩ := h
  rintro ⟨h1,h2,h3⟩
  have h01 := hp (p.symm 0) (p.symm 1) (p.symm.injective.ne (by decide))
  have h02 := hp (p.symm 0) (p.symm 2) (p.symm.injective.ne (by decide))
  have h03 := hp (p.symm 0) (p.symm 3) (p.symm.injective.ne (by decide))
  simp only [p.apply_symm_apply] at h01 h02 h03
  exact no_three_doubles_valid k hk p.symm
    ⟨h01.symm.trans h1,h02.symm.trans h2,h03.symm.trans h3⟩

lemma five_positive
    (hfour : ∀ T : Fin 4 → I, Function.Injective T → Pattern a T)
    (hthree : ∀ T : Fin 3 → I, Function.Injective T → 2 ≤ a (T 0) (T 1) + a (T 0) (T 2))
    (T : Fin 5 → I) (hT : Function.Injective T) : 0 < a (T 0) (T 1) := by
  by_contra hn
  have hz : a (T 0) (T 1) = 0 := by omega
  let u : Fin 4 → Fin 5 := ![0,1,2,3]
  let v : Fin 4 → Fin 5 := ![0,1,2,4]
  let w : Fin 3 → Fin 5 := ![2,3,4]
  have hu : Function.Injective u := by decide +kernel
  have hv : Function.Injective v := by decide +kernel
  have hw : Function.Injective w := by decide +kernel
  have h23 := zero_opposite a (hfour (T ∘ u) (hT.comp hu)) hz
  have h24 := zero_opposite a (hfour (T ∘ v) (hT.comp hv)) hz
  have hlow := hthree (T ∘ w) (hT.comp hw)
  change a (T 2) (T 3) = 0 at h23
  change a (T 2) (T 4) = 0 at h24
  change 2 ≤ a (T 2) (T 3) + a (T 2) (T 4) at hlow
  omega

lemma pair_permutation : ∀ i j : Fin 5, i ≠ j →
    ∃ p : Equiv.Perm (Fin 5), p 0 = i ∧ p 1 = j := by decide +kernel

lemma five_all_positive
    (hfour : ∀ T : Fin 4 → I, Function.Injective T → Pattern a T)
    (hthree : ∀ T : Fin 3 → I, Function.Injective T → 2 ≤ a (T 0) (T 1) + a (T 0) (T 2))
    (T : Fin 5 → I) (hT : Function.Injective T) (i j : Fin 5) (hij : i ≠ j) :
    0 < a (T i) (T j) := by
  obtain ⟨p,hp0,hp1⟩ := pair_permutation i j hij
  have hh := five_positive a hfour hthree (T ∘ p) (hT.comp p.injective)
  simpa only [Function.comp_apply,hp0,hp1] using hh

lemma all_positive [Fintype I] (hcard : 5 ≤ Fintype.card I)
    (hfour : ∀ T : Fin 4 → I, Function.Injective T → Pattern a T)
    (hthree : ∀ T : Fin 3 → I, Function.Injective T → 2 ≤ a (T 0) (T 1) + a (T 0) (T 2))
    (i j : I) (hij : i ≠ j) : 0 < a i j := by
  classical
  obtain ⟨A,hpair,hAuniv,hAc⟩ := Finset.exists_subsuperset_card_eq
    (show ({i,j} : Finset I) ⊆ Finset.univ from Finset.subset_univ _)
    (by simp [hij] : ({i,j} : Finset I).card ≤ 5)
    (by simpa only [Finset.card_univ] using hcard)
  let ii : A := ⟨i,hpair (by simp)⟩
  let jj : A := ⟨j,hpair (by simp)⟩
  let e : Fin 5 ≃ A := (Fintype.equivFinOfCardEq (by simpa using hAc)).symm
  let T : Fin 5 → I := fun t => (e t).val
  have hT : Function.Injective T := Subtype.val_injective.comp e.injective
  have hne : e.symm ii ≠ e.symm jj := by
    intro hh
    exact hij (congrArg Subtype.val (e.symm.injective hh))
  have hh := five_all_positive a hfour hthree T hT (e.symm ii) (e.symm jj) hne
  simpa only [T,e.apply_symm_apply,ii,jj] using hh

#print axioms all_positive
#print axioms zero_opposite
#print axioms no_three_doubles
#print axioms five_all_positive
end Erdos184Work.AllowedFourCounts
