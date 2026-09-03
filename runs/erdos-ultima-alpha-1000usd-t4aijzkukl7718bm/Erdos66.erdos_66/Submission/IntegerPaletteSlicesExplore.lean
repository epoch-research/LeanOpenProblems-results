import Submission.PrefixBalancedPaletteExplore
import Submission.NatPairAlgebraExplore

/-! Exact interval slicing of a finite cyclic palette into natural numbers.
Mixed endpoint-prefix bounds transfer to actual integer mixed counts. -/
namespace Erdos66IntegerPaletteSlices
open Erdos66OuterMixedPrefix Erdos66OuterCarryProfile Erdos66SaturatingCyclicFamily
  Erdos66NatPairAlgebra
open scoped Classical
set_option maxHeartbeats 2000000

variable (M : ℕ) [NeZero M]

noncomputable def slice (C : Finset (ZMod M)) (a b : ℕ) : Finset ℕ :=
  (C.filter (fun z ↦ a ≤ z.val ∧ z.val < b)).image ZMod.val

lemma mem_slice (C : Finset (ZMod M)) (a b x : ℕ) :
    x∈slice M C a b ↔ x<M ∧ a ≤ x ∧ x<b ∧ (x : ZMod M)∈C := by
  constructor
  · intro hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hz,hza,hzb⟩ := Finset.mem_filter.mp hz
    exact ⟨ZMod.val_lt z,hza,hzb,by simpa only [ZMod.natCast_zmod_val] using hz⟩
  · rintro ⟨hxM,hax,hxb,hxC⟩
    refine Finset.mem_image.mpr ⟨(x : ZMod M),Finset.mem_filter.mpr ⟨hxC,?_⟩,?_⟩
    · simpa only [ZMod.val_natCast_of_lt hxM] using And.intro hax hxb
    · exact ZMod.val_natCast_of_lt hxM

/-- Upper endpoint of the possible first summands. -/
def cutHi (b c n : ℕ) : ℕ := min b (n+1-c)

/-- Clamp the lower endpoint to make the intersection empty rather than reversed. -/
def cutLo (a b c d n : ℕ) : ℕ := min (max a (n+1-d)) (cutHi b c n)

lemma cutLo_le_cutHi (a b c d n : ℕ) : cutLo a b c d n ≤ cutHi b c n := min_le_right _ _

lemma cutHi_le (b c n : ℕ) : cutHi b c n ≤ b := min_le_left _ _

lemma cut_bounds_iff (a b c d n x : ℕ) :
    cutLo a b c d n ≤ x ∧ x < cutHi b c n ↔
      a ≤ x ∧ x<b ∧ x ≤ n ∧ c ≤ n-x ∧ n-x<d := by
  unfold cutLo cutHi
  omega

/-- Exact mixed integer count for two sliced palette members. No carry term
is omitted: the allowed first endpoints form the displayed clamped interval. -/
theorem pairs_slice_formula (C D : Finset (ZMod M)) (a b c d n : ℕ) (hd : d ≤ M) :
    pairs (slice M C a b) (slice M D c d) n =
      intervalCount M C D (n : ZMod M) (cutLo a b c d n) (cutHi b c n) := by
  rw [pairs_eq_filter,intervalCount]
  symm
  apply Finset.card_bij (fun z _ ↦ z.val)
  · intro z hz
    obtain ⟨hzC,hzlo,hzhi,hzD⟩ := Finset.mem_filter.mp hz
    obtain ⟨hza,hzb,hzn,hzc,hzd⟩ := (cut_bounds_iff a b c d n z.val).mp ⟨hzlo,hzhi⟩
    have hyM : n-z.val<M := hzd.trans_le hd
    have hcast : ((n-z.val:ℕ):ZMod M)=(n:ZMod M)-z := by
      rw [Nat.cast_sub hzn,ZMod.natCast_zmod_val]
    exact Finset.mem_filter.mpr ⟨(mem_slice M C a b z.val).mpr
      ⟨ZMod.val_lt z,hza,hzb,by simpa only [ZMod.natCast_zmod_val] using hzC⟩,
      hzn,(mem_slice M D c d (n-z.val)).mpr ⟨hyM,hzc,hzd,by rwa [hcast]⟩⟩
  · intro z hz w hw he
    exact ZMod.val_injective M he
  · intro x hx
    obtain ⟨hx,hxn,hy⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxM,hxa,hxb,hxC⟩ := (mem_slice M C a b x).mp hx
    obtain ⟨hyM,hyc,hyd,hyD⟩ := (mem_slice M D c d (n-x)).mp hy
    refine ⟨(x:ZMod M),Finset.mem_filter.mpr ⟨hxC,?_⟩,ZMod.val_natCast_of_lt hxM⟩
    rw [ZMod.val_natCast_of_lt hxM]
    have hb := (cut_bounds_iff a b c d n x).mpr ⟨hxa,hxb,hxn,hyc,hyd⟩
    refine ⟨hb.1,hb.2,?_⟩
    rwa [Nat.cast_sub hxn] at hyD

/-- Integer mixed counts approximate the overlap-length profile. The error
is absolute relative to the full cyclic mean. -/
theorem pairs_slice_error (C D : Finset (ZMod M)) (a b c d n : ℕ)
    (hb : b ≤ M) (hd : d ≤ M) (η : ℝ)
    (hprefix : ∀ z u, u ≤ M →
      |(prefixCount M C D z u:ℝ)-(u:ℝ)/M*actualMean M C D| ≤ η*actualMean M C D) :
    |(pairs (slice M C a b) (slice M D c d) n:ℝ)-
      (((cutHi b c n:ℝ)-cutLo a b c d n)/M)*actualMean M C D| ≤
      2*η*actualMean M C D := by
  rw [pairs_slice_formula M C D a b c d n hd]
  have hhi : cutHi b c n ≤ M := (cutHi_le b c n).trans hb
  have hlo := (cutLo_le_cutHi a b c d n).trans hhi
  have hh := interval_error_of_prefix_error M C D (n:ZMod M)
    (cutLo a b c d n) (cutHi b c n) (cutLo_le_cutHi a b c d n)
    (actualMean M C D) (η*actualMean M C D)
    (hprefix _ _ hlo) (hprefix _ _ hhi)
  simpa only [mul_assoc] using hh

end Erdos66IntegerPaletteSlices
