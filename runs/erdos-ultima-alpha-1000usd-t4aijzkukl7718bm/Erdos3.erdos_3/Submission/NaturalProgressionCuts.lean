import Submission.IntervalFourUniformity

/-! An affine progression of span less than the modulus meets an initial
cyclic interval in at most two intervals of progression indices. -/
namespace Erdos3NaturalProgressionCuts
open Finset
open scoped Classical
set_option maxHeartbeats 2000000

def affineCut (A d T L : ℕ) : ℕ := min L ((T-A) ⌈/⌉ d)
lemma affineCut_le (A d T L : ℕ) : affineCut A d T L ≤ L := min_le_left _ _

lemma affineCut_lt_iff (A T L : ℕ) {d j : ℕ} (hd : 0 < d) (hj : j < L) :
    j < affineCut A d T L ↔ A+j*d < T := by
  unfold affineCut
  rw [lt_min_iff,and_iff_right hj,← not_le,ceilDiv_le_iff_le_mul hd,not_le,
    Nat.lt_sub_iff_add_lt,Nat.mul_comm,Nat.add_comm]

lemma affineCut_mono (A L : ℕ) {d T U : ℕ} (hd : 0 < d) (hTU : T ≤ U) :
    affineCut A d T L ≤ affineCut A d U L := by
  apply min_le_min le_rfl
  exact (gc_mul_ceilDiv hd).monotone_l (Nat.sub_le_sub_right hTU A)

lemma affine_below_two_moduli (A d p L : ℕ) (hA : A < p) (hspan : (L-1)*d < p)
    {j : ℕ} (hj : j < L) : A+j*d < 2*p := by
  have hmul := Nat.mul_le_mul_right d (show j ≤ L-1 by omega)
  omega

/-- Exact two-piece description; the possible wrapped piece is separated
from the initial piece by the crossing index of p. -/
theorem affine_interval_two_pieces (A d p N L : ℕ) (hA : A < p) (hd : 0 < d)
    (hspan : (L-1)*d < p) (hNp : N ≤ p) {j : ℕ} (hj : j < L) :
    (A+j*d)%p < N ↔ j < affineCut A d N L ∨
      affineCut A d p L ≤ j ∧ j < affineCut A d (p+N) L := by
  have hN := affineCut_lt_iff A N L hd hj
  have hp := affineCut_lt_iff A p L hd hj
  have hpN := affineCut_lt_iff A (p+N) L hd hj
  have hv2 := affine_below_two_moduli A d p L hA hspan hj
  by_cases hv : A+j*d < p
  · rw [Nat.mod_eq_of_lt hv]
    omega
  · have hv' : p ≤ A+j*d := by omega
    rw [Nat.mod_eq_sub_mod hv',Nat.mod_eq_of_lt (by omega : A+j*d-p < p)]
    omega

lemma affine_first_piece (A d p N L : ℕ) (hd : 0 < d) (hNp : N ≤ p)
    {j : ℕ} (hj : j < affineCut A d N L) :
    (A+j*d)%p = A+j*d ∧ A+j*d < N := by
  have hjL := hj.trans_le (affineCut_le A d N L)
  have hv := (affineCut_lt_iff A N L hd hjL).mp hj
  exact ⟨Nat.mod_eq_of_lt (hv.trans_le hNp),hv⟩

lemma affine_second_piece (A d p N L : ℕ) (hd : 0 < d) (hNp : N ≤ p)
    {j : ℕ} (hj : j < affineCut A d (p+N) L-affineCut A d p L) :
    (A+(affineCut A d p L+j)*d)%p = (A+affineCut A d p L*d-p)+j*d ∧
      (A+affineCut A d p L*d-p)+j*d < N := by
  let c := affineCut A d p L
  let e := affineCut A d (p+N) L
  have hce : c ≤ e := affineCut_mono A L hd (by omega : p ≤ p+N)
  have hje : c+j < e := by dsimp [c,e] at *; omega
  have hjL : c+j < L := hje.trans_le (affineCut_le A d (p+N) L)
  have hcL : c < L := by omega
  have hp0 := affineCut_lt_iff A p L hd hcL
  have hv : p ≤ A+c*d := by change c < c ↔ A+c*d < p at hp0; omega
  have hp1 := affineCut_lt_iff A p L hd hjL
  have hv' : p ≤ A+(c+j)*d := by change c+j < c ↔ A+(c+j)*d < p at hp1; omega
  have hvN : A+(c+j)*d < p+N := (affineCut_lt_iff A (p+N) L hd hjL).mp hje
  have he : A+(c+j)*d = (A+c*d)+j*d := by ring
  have hmod : (A+(c+j)*d)%p = (A+c*d-p)+j*d := by
    rw [Nat.mod_eq_sub_mod hv',Nat.mod_eq_of_lt (by omega : A+(c+j)*d-p < p),he,
      Nat.sub_add_comm hv]
  refine ⟨hmod,?_⟩
  have hsub : A+(c+j)*d-p < N := by omega
  rw [he,Nat.sub_add_comm hv] at hsub
  exact hsub

#print axioms affine_interval_two_pieces
#print axioms affine_second_piece
end Erdos3NaturalProgressionCuts
