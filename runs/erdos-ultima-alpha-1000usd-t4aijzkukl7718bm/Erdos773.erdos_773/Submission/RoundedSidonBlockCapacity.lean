import Submission.FullIntervalSquareCapacity
import Submission.RoundedSidonBlocks
import Submission.SidonModularBound

/-! A two-thirds ceiling for the FULL rounded-block construction.
This is not an upper bound for Sidon subsets chosen sparsely from the blocks. -/
namespace Erdos773.RoundedSidonBlockCapacity
open Finset RoundedSidonBlocks
set_option maxHeartbeats 2000000

lemma mark_card {L : ℕ} {A : Finset ℕ} (hbound : ∀ a∈A, a≤L) :
    A.card≤L+1 := by
  have hi : A⊆Icc 0 L := fun a ha => mem_Icc.mpr ⟨Nat.zero_le _,hbound a ha⟩
  simpa using card_le_card hi

lemma mark_card_sq {L : ℕ} {A : Finset ℕ} (hL : 0<L)
    (hbound : ∀ a∈A, a≤L) (hA : IsSidon (A : Set ℕ)) :
    A.card^2≤5*L := by
  have hh := Erdos773.sidon_modular_card_bound (C := {0}) (q := 1)
    hA hbound (by intro a ha; exact mem_singleton.mpr (Nat.mod_one a))
  simp only [card_singleton, Nat.div_one, one_mul] at hh
  have hc := mark_card hbound
  omega

/-- The close-center capacity applies to the actual rounded centers. -/
theorem squared_width_capacity {L H : ℕ} {A : Finset ℕ}
    (hL : 0<L) (hH : 10≤H) (hbound : ∀ a∈A, a≤L)
    (hS : IsSidon (A.biUnion (values L H) : Set ℕ)) :
    A.card*H^2≤78000*L*(H+1) := by
  have hheight (a : ℕ) (ha : a∈A) : center L H a+H≤65*L*(H+1) :=
    (root_height L H a _ hL (hbound a ha) (mem_Icc.mpr ⟨by omega,le_rfl⟩)).2
  have hdis (a : ℕ) (ha : a∈A) (b : ℕ) (hb : b∈A) (hab : a≠b) :
      Disjoint (FullIntervalSquareCapacity.block H (center L H) a)
        (FullIntervalSquareCapacity.block H (center L H) b) :=
    blocks_disjoint L H a b hL (hbound a ha) (hbound b hb) hab
  have hs : IsSidon (((FullIntervalSquareCapacity.roots H A (center L H)).image
      (fun n => n^2)) : Set ℕ) := by
    have he : (FullIntervalSquareCapacity.roots H A (center L H)).image (fun n => n^2) =
        A.biUnion (values L H) := by
      ext x
      simp only [FullIntervalSquareCapacity.roots, mem_image, mem_biUnion,
        values, FullIntervalSquareCapacity.block, RoundedSidonBlocks.block]
      aesop
    rw [he]
    exact hS
  have hc := FullIntervalSquareCapacity.squared_width_capacity hH hheight hdis hs
  nlinarith only [hc]

/-- For long full blocks, compatibility already limits the total root count
by a constant times the mark-height parameter. -/
theorem mass_bound {L H : ℕ} {A : Finset ℕ}
    (hL : 0<L) (hH : 10≤H) (hbound : ∀ a∈A, a≤L)
    (hS : IsSidon (A.biUnion (values L H) : Set ℕ)) :
    A.card*(H+1)≤312000*L := by
  have hc := squared_width_capacity hL hH hbound hS
  have hh : H+1≤2*H := by omega
  have hm := Nat.mul_le_mul_left (78000*L) hh
  have hAH : A.card*H≤156000*L := by
    have hx : H*(A.card*H)≤H*(156000*L) := by nlinarith only [hc,hm]
    exact Nat.le_of_mul_le_mul_left hx (by omega)
  have hh' := Nat.mul_le_mul_left A.card hh
  nlinarith only [hAH,hh']

/-- The nominal three-quarter count cannot be achieved by retaining whole
blocks: every Sidon FULL union has a two-thirds cardinality ceiling. -/
theorem full_union_cube_bound {L H : ℕ} {A : Finset ℕ}
    (hL : 0<L) (hbound : ∀ a∈A, a≤L) (hA : IsSidon (A : Set ℕ))
    (hS : IsSidon (A.biUnion (values L H) : Set ℕ)) :
    (A.biUnion (values L H)).card^3≤1560000*(L*(H+1))^2 := by
  rw [union_card L H A hL hbound]
  have ha2 := mark_card_sq hL hbound hA
  have hsq : (A.card*(H+1))^2≤5*L*(H+1)^2 := by
    have hh := Nat.mul_le_mul_right ((H+1)^2) ha2
    simpa only [mul_pow] using hh
  by_cases hH : 10≤H
  · have hm := mass_bound hL hH hbound hS
    have hh := Nat.mul_le_mul hsq hm
    nlinarith only [hh]
  · have hH1 : H+1≤10 := by omega
    have hc := mark_card hbound
    have hmass : A.card*(H+1)≤20*L := by
      have hh := Nat.mul_le_mul hc hH1
      nlinarith only [hh,hL]
    have hh := Nat.mul_le_mul hsq hmass
    nlinarith only [hh]

/-- A numerical form at the construction's actual declared root height. -/
theorem full_union_real_bound {L H : ℕ} {A : Finset ℕ}
    (hL : 0<L) (hbound : ∀ a∈A, a≤L) (hA : IsSidon (A : Set ℕ))
    (hS : IsSidon (A.biUnion (values L H) : Set ℕ)) :
    ((A.biUnion (values L H)).card : ℝ)≤
      8*(65*L*(H+1) : ℝ)^(2/3 : ℝ) := by
  have hc : ((A.biUnion (values L H)).card : ℝ)^3≤
      1560000*((L : ℝ)*(H+1))^2 := by
    exact_mod_cast full_union_cube_bound hL hbound hA hS
  have hp : ((65*L*(H+1) : ℝ)^(2/3 : ℝ))^3=(65*L*(H+1) : ℝ)^2 := by
    rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ)≤65*L*(H+1))]
    norm_num
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ)≠0) (by positivity)
  rw [mul_pow,hp]
  nlinarith only [hc,sq_nonneg ((L : ℝ)*(H+1))]

end Erdos773.RoundedSidonBlockCapacity

#print axioms Erdos773.RoundedSidonBlockCapacity.squared_width_capacity
#print axioms Erdos773.RoundedSidonBlockCapacity.mass_bound
#print axioms Erdos773.RoundedSidonBlockCapacity.full_union_cube_bound
#print axioms Erdos773.RoundedSidonBlockCapacity.full_union_real_bound
