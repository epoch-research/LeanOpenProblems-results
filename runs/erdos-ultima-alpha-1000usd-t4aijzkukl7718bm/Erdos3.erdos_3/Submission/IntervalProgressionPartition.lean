import Submission.AveragedPartialPartitionIncrement

/-! An interval can be partitioned into complete length-L progressions of a
fixed positive stride, with fewer than d*L exceptional points. -/
namespace Erdos3IntervalProgressionPartition
open Finset Erdos3FinitePartitionIncrement
open scoped Classical
set_option maxHeartbeats 3000000

/-- Base of the length-L progression in the d-by-L block containing k. -/
def blockBase (d L k : ℕ) : ℕ := (k/d/L*L)*d+k%d

lemma blockBase_add_offset (d L k : ℕ) :
    blockBase d L k+(k/d%L)*d = k := by
  have h₁ := Nat.mod_add_div (k/d) L
  have h₂ := Nat.mod_add_div k d
  unfold blockBase
  nlinarith

lemma blockBase_le (d L k : ℕ) : blockBase d L k ≤ k := by
  have := blockBase_add_offset d L k
  omega

noncomputable def progressionLabel (N d L : ℕ) (k : Fin N) : Option (Fin N) :=
  if k.val/d/L < N/(d*L) then
    some ⟨blockBase d L k.val,(blockBase_le d L k.val).trans_lt k.isLt⟩
  else none

lemma progressionLabel_none_iff {N d L : ℕ} (hd : 0 < d) (hL : 0 < L) (k : Fin N) :
    progressionLabel N d L k = none ↔ (N/(d*L))*(d*L) ≤ k.val := by
  simp only [progressionLabel,ite_eq_right_iff,Option.some_ne_none,imp_false,
    Nat.div_div_eq_div_mul,not_lt]
  exact ⟨fun h ↦ by
    by_contra! hh
    have := (Nat.div_lt_iff_lt_mul (Nat.mul_pos hd hL)).mpr hh
    omega,
    fun h ↦ by
      by_contra! hh
      have := (Nat.div_lt_iff_lt_mul (Nat.mul_pos hd hL)).mp hh
      omega⟩

lemma encoded_div {d L : ℕ} (hd : 0 < d) {r : ℕ} (hr : r < d) (b j : ℕ) :
    ((b*L+j)*d+r)/d = b*L+j := by
  rw [show (b*L+j)*d+r = d*(b*L+j)+r by ring,Nat.mul_add_div hd,
    Nat.div_eq_of_lt hr,add_zero]

lemma encoded_mod {d L : ℕ} {r : ℕ} (hr : r < d) (b j : ℕ) :
    ((b*L+j)*d+r)%d = r := by
  rw [show (b*L+j)*d+r = d*(b*L+j)+r by ring,Nat.mul_add_mod,Nat.mod_eq_of_lt hr]

lemma encoded_block {d L : ℕ} (hd : 0 < d) (hL : 0 < L)
    {r j : ℕ} (hr : r < d) (hj : j < L) (b : ℕ) :
    ((b*L+j)*d+r)/d/L = b := by
  rw [encoded_div hd hr,show b*L+j = L*b+j by ring,Nat.mul_add_div hL,
    Nat.div_eq_of_lt hj,add_zero]

lemma blockBase_encoded {d L : ℕ} (hd : 0 < d) (hL : 0 < L)
    {r j : ℕ} (hr : r < d) (hj : j < L) (b : ℕ) :
    blockBase d L ((b*L+j)*d+r) = b*L*d+r := by
  unfold blockBase
  rw [encoded_block hd hL hr hj,encoded_mod hr]

lemma encoded_lt {N d L b r j : ℕ} (hd : 0 < d)
    (hr : r < d) (hj : j < L) (hb : b < N/(d*L)) : (b*L+j)*d+r < N := by
  have hlocal : j*d+r < L*d := by nlinarith
  calc
    _ = b*(d*L)+(j*d+r) := by ring
    _ < b*(d*L)+L*d := Nat.add_lt_add_left hlocal _
    _ = (b+1)*(d*L) := by ring
    _ ≤ (N/(d*L))*(d*L) := Nat.mul_le_mul_right _ (by omega)
    _ ≤ N := Nat.div_mul_le_self _ _

lemma progressionLabel_some_base {N d L : ℕ} {k a : Fin N}
    (h : progressionLabel N d L k = some a) :
    k.val/d/L < N/(d*L) ∧ a.val = blockBase d L k.val := by
  unfold progressionLabel at h
  split_ifs at h with hk
  · exact ⟨hk,congrArg Fin.val (Option.some.inj h).symm⟩

/-- Every nonempty nonexceptional cell is exactly a length-L progression,
with no wraparound and with distinct natural indices. -/
theorem progressionLabel_fiber {N d L : ℕ} (hd : 0 < d) (hL : 0 < L)
    (a : Fin N) (ha : (cell (progressionLabel N d L) (some a)).Nonempty) :
    (∀ j < L, a.val+j*d < N) ∧
    (∀ k : Fin N, progressionLabel N d L k = some a ↔
      ∃ j : Fin L, k.val = a.val+j.val*d) := by
  obtain ⟨x,hx⟩ := ha
  have hxa : progressionLabel N d L x = some a := by simpa only [cell,mem_filter,mem_univ,true_and] using hx
  obtain ⟨hb,hab⟩ := progressionLabel_some_base hxa
  have hr : x.val%d < d := Nat.mod_lt _ hd
  have hbound (j : ℕ) (hj : j < L) : a.val+j*d < N := by
    rw [hab]
    convert encoded_lt hd hr hj hb using 1 <;> unfold blockBase <;> ring
  refine ⟨hbound,?_⟩
  intro k
  constructor
  · intro hk
    obtain ⟨_,hak⟩ := progressionLabel_some_base hk
    refine ⟨⟨k.val/d%L,Nat.mod_lt _ hL⟩,?_⟩
    rw [hak]
    exact (blockBase_add_offset d L k.val).symm
  · rintro ⟨j,hkj⟩
    have hkval : k.val = (x.val/d/L*L+j.val)*d+x.val%d := by
      rw [hkj,hab]
      unfold blockBase
      ring
    have hkb : k.val/d/L < N/(d*L) := by
      rw [hkval,encoded_block hd hL hr j.isLt]
      exact hb
    rw [progressionLabel,if_pos hkb]
    congr 1
    apply Fin.ext
    change blockBase d L k.val = a.val
    rw [hkval,blockBase_encoded hd hL hr j.isLt,hab]
    rfl

lemma progressionLabel_cell_card {N d L : ℕ} (hd : 0 < d) (hL : 0 < L)
    (a : Fin N) (ha : (cell (progressionLabel N d L) (some a)).Nonempty) :
    (cell (progressionLabel N d L) (some a)).card = L := by
  obtain ⟨hbound,hfiber⟩ := progressionLabel_fiber hd hL a ha
  let e : Fin L → Fin N := fun j ↦ ⟨a.val+j.val*d,hbound j j.isLt⟩
  have he : Function.Injective e := by
    intro i j hij
    have hh := congrArg Fin.val hij
    dsimp [e] at hh
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hh)
  have hset : cell (progressionLabel N d L) (some a) = univ.image e := by
    ext k
    simp only [cell,mem_filter,mem_univ,true_and,mem_image,hfiber]
    constructor
    · rintro ⟨j,hj⟩
      exact ⟨j,Fin.ext hj.symm⟩
    · rintro ⟨j,hj⟩
      exact ⟨j,(congrArg Fin.val hj).symm⟩
  rw [hset,card_image_of_injective _ he,card_fin]

lemma progressionLabel_bad_card {N d L : ℕ} (hd : 0 < d) (hL : 0 < L) :
    (cell (progressionLabel N d L) none).card = N%(d*L) := by
  let K := N/(d*L)*(d*L)
  have hset : cell (progressionLabel N d L) none =
      (Ico K N).attachFin (fun _ hm ↦ (mem_Ico.mp hm).2) := by
    ext k
    simp only [cell,mem_filter,mem_univ,true_and,mem_attachFin,mem_Ico,
      progressionLabel_none_iff hd hL]
    exact ⟨fun h ↦ ⟨h,k.isLt⟩,fun h ↦ h.1⟩
  rw [hset,card_attachFin,Nat.card_Ico]
  have hh := Nat.mod_add_div N (d*L)
  dsimp [K]
  have he : N%(d*L)+N/(d*L)*(d*L) = N := by nlinarith only [hh]
  omega

#print axioms progressionLabel_fiber
#print axioms progressionLabel_bad_card
end Erdos3IntervalProgressionPartition
