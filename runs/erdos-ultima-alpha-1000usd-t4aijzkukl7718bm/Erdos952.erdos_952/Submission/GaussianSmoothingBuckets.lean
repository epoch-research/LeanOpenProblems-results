import Submission.GaussianHigherSmoothingLower

/-! A concrete bucket partition for higher-order Gaussian smoothing. The
number of buckets is quadratic in the number of internal factors, not
exponential. Consequently an enclosed finite set, and in particular a prime
ray segment, remains visible with a polynomial loss. -/
namespace Erdos952Investigation.GaussianSmoothingBuckets
open GaussianIdealBoxCounts GaussianIteratedSmoothing FiniteSampleSmoothing
open GaussianHigherSmoothingLower PrimePathCounting SievePeriodicDrift
open scoped BigOperators Classical
set_option maxHeartbeats 0
noncomputable section
local instance (a : GaussianInt) (R : ℕ) : Fintype (Box a R) := Fintype.ofFinite _

lemma tuple_bounds (R n : ℕ) (s : Sample (Box 0 R) n) :
    -(n : ℤ)*(R : ℤ) ≤ (tupleValue 0 R n s).re ∧ (tupleValue 0 R n s).re < R ∧
    -(n : ℤ)*(R : ℤ) ≤ (tupleValue 0 R n s).im ∧ (tupleValue 0 R n s).im < R := by
  induction n with
  | zero =>
    have h := s.property
    simpa only [tupleValue,value,InBox,Nat.cast_zero,neg_zero,zero_mul,Zsqrtd.re_zero,
      Zsqrtd.im_zero,zero_add] using h
  | succ n ih =>
    have h := ih s.1
    have hv := s.2.property
    dsimp [InBox] at hv
    change -(↑(n+1) : ℤ)*(R : ℤ) ≤ (tupleValue 0 R n s.1-s.2.val).re ∧ _
    simp only [Zsqrtd.re_sub,Nat.cast_add,Nat.cast_one]
    change _ ∧ (tupleValue 0 R n s.1).re-s.2.val.re < R ∧
      -((n : ℤ)+1)*(R : ℤ) ≤ (tupleValue 0 R n s.1).im-s.2.val.im ∧
      (tupleValue 0 R n s.1).im-s.2.val.im < R
    constructor
    · nlinarith
    constructor
    · omega
    constructor
    · nlinarith
    · omega

def cellIndex (T K : ℕ) (hT : 0 < T) (v : ℤ)
    (hv : 0 ≤ v ∧ v < (K : ℤ)*(T : ℤ)) : Fin K :=
  ⟨(v/(T : ℤ)).toNat,by
    have hTp : (0 : ℤ) < T := by exact_mod_cast hT
    have h0 : 0 ≤ v/(T : ℤ) := Int.ediv_nonneg hv.1 hTp.le
    have hlt : v/(T : ℤ) < K := (Int.ediv_lt_iff_lt_mul hTp).mpr hv.2
    omega⟩

lemma cellIndex_close (T K : ℕ) (hT : 0 < T) (v w : ℤ)
    (hv : 0 ≤ v ∧ v < (K : ℤ)*(T : ℤ))
    (hw : 0 ≤ w ∧ w < (K : ℤ)*(T : ℤ))
    (he : cellIndex T K hT v hv = cellIndex T K hT w hw) : |v-w| ≤ (T : ℤ) := by
  have hTp : (0 : ℤ) < T := by exact_mod_cast hT
  have hv0 : 0 ≤ v/(T : ℤ) := Int.ediv_nonneg hv.1 hTp.le
  have hw0 : 0 ≤ w/(T : ℤ) := Int.ediv_nonneg hw.1 hTp.le
  have hq : v/(T : ℤ) = w/(T : ℤ) := by
    have hh := congrArg Fin.val he
    dsimp [cellIndex] at hh
    omega
  have hvd := Int.mul_ediv_add_emod v (T : ℤ)
  have hwd := Int.mul_ediv_add_emod w (T : ℤ)
  have hvr := Int.emod_nonneg v hTp.ne'
  have hwr := Int.emod_nonneg w hTp.ne'
  have hvR := Int.emod_lt_of_pos v hTp
  have hwR := Int.emod_lt_of_pos w hTp
  rw [hq] at hvd
  apply abs_le.mpr
  constructor <;> omega

lemma shifted_tuple_bounds (T n : ℕ) (s : Sample (Box 0 (5*T)) n) :
    (0 ≤ (tupleValue 0 (5*T) n s).re+(n : ℤ)*(5*T : ℕ) ∧
      (tupleValue 0 (5*T) n s).re+(n : ℤ)*(5*T : ℕ) < (5*(n+1) : ℕ)*(T : ℤ)) ∧
    (0 ≤ (tupleValue 0 (5*T) n s).im+(n : ℤ)*(5*T : ℕ) ∧
      (tupleValue 0 (5*T) n s).im+(n : ℤ)*(5*T : ℕ) < (5*(n+1) : ℕ)*(T : ℤ)) := by
  have h := tuple_bounds (5*T) n s
  push_cast at h ⊢
  constructor <;> constructor <;> nlinarith

def bucket (T n : ℕ) (hT : 0 < T) (s : Sample (Box 0 (5*T)) n) :
    Fin (5*(n+1)) × Fin (5*(n+1)) :=
  (cellIndex T (5*(n+1)) hT ((tupleValue 0 (5*T) n s).re+(n : ℤ)*(5*T : ℕ))
    (shifted_tuple_bounds T n s).1,
   cellIndex T (5*(n+1)) hT ((tupleValue 0 (5*T) n s).im+(n : ℤ)*(5*T : ℕ))
    (shifted_tuple_bounds T n s).2)

lemma bucket_close (T n : ℕ) (hT : 0 < T) (s t : Sample (Box 0 (5*T)) n)
    (he : bucket T n hT s = bucket T n hT t) :
    |(tupleValue 0 (5*T) n s).re-(tupleValue 0 (5*T) n t).re| ≤ (T : ℤ) ∧
    |(tupleValue 0 (5*T) n s).im-(tupleValue 0 (5*T) n t).im| ≤ (T : ℤ) := by
  have hr := cellIndex_close T (5*(n+1)) hT _ _
    (shifted_tuple_bounds T n s).1 (shifted_tuple_bounds T n t).1 (congrArg Prod.fst he)
  have hi := cellIndex_close T (5*(n+1)) hT _ _
    (shifted_tuple_bounds T n s).2 (shifted_tuple_bounds T n t).2 (congrArg Prod.snd he)
  constructor
  · simpa only [add_sub_add_right_eq_sub] using hr
  · simpa only [add_sub_add_right_eq_sub] using hi

/-- Higher-order smoothing keeps every enclosed point with a loss of only
625*(n+1)^2. This is a concrete bound for the actual tuple-based kernel. -/
theorem enclosed_finset_le_higher_kernel (E : Finset GaussianInt) (p : GaussianInt → Prop)
    (a : GaussianInt) (T n : ℕ) (hT : 0 < T) (hp : ∀ z ∈ E, p z)
    (hbox : ∀ z ∈ E, |z.re-a.re| ≤ (T : ℤ) ∧ |z.im-a.im| ≤ (T : ℤ)) :
    (E.card : ℝ) ≤ 625*((n : ℝ)+1)^2*
      kernelCount (tupleValue 0 (5*T) n) p a (5*T) := by
  letI : Nonempty (Box 0 (5*T)) := box_nonempty 0 (5*T) (by omega)
  have hh := enclosed_finset_le_kernel (tupleValue 0 (5*T) n) (bucket T n hT)
    E p a T hT hp hbox (bucket_close T n hT)
  simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
    Nat.cast_ofNat] at hh
  convert hh using 1; ring

/-- The forced linear count survives all orders of this smoothing, with
only a quadratic loss in n+1. No contradictory upper bound is asserted. -/
theorem ray_forces_higher_smoothed_count (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x) (h : ∀ j, Prime (x j) ∧ (x (j+1)-x j).norm < C)
    (M L n : ℕ) (hM : 0 < M) :
    (M : ℝ)+1 ≤ 625*((n : ℝ)+1)^2*
      kernelCount (tupleValue 0 (5*(M*C.toNat)) n) (Starts C L) (x 0) (5*(M*C.toNat)) := by
  have hC : 0 < C := (GaussianInt.norm_nonneg _).trans_lt (h 0).2
  have hCn : 0 < C.toNat := by omega
  let T : ℕ := M*C.toNat
  let E : Finset GaussianInt := Finset.univ.image (fun i : Fin (M+1) => x i.val)
  have hE : E.card = M+1 := by
    have hi : Function.Injective (fun i : Fin (M+1) => x i.val) := hx.comp Fin.val_injective
    dsimp [E]
    rw [Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_fin]
  have hp : ∀ z ∈ E, Starts C L z := by
    intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    exact starts_of_prime_ray x C hx h i.val L
  have hb : ∀ z ∈ E, |z.re-(x 0).re| ≤ (T : ℤ) ∧ |z.im-(x 0).im| ≤ (T : ℤ) := by
    intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    have ht := taxicab_drift_le x C (fun j => (h j).2) 0 i.val
    simp only [Nat.zero_add,taxicab,Zsqrtd.re_sub,Zsqrtd.im_sub] at ht
    have hi : (i.val : ℤ) ≤ M := by exact_mod_cast (show i.val ≤ M by omega)
    have hm := mul_le_mul_of_nonneg_right hi hC.le
    have hT : (T : ℤ) = (M : ℤ)*C := by simp [T,Int.toNat_of_nonneg hC.le]
    rw [← hT] at hm
    have hr := abs_nonneg ((x i.val).re-(x 0).re)
    have him := abs_nonneg ((x i.val).im-(x 0).im)
    constructor <;> omega
  have hh := enclosed_finset_le_higher_kernel E (Starts C L) (x 0) T n
    (Nat.mul_pos hM hCn) hp hb
  rw [hE,Nat.cast_add,Nat.cast_one] at hh
  exact hh

#print axioms bucket_close
#print axioms enclosed_finset_le_higher_kernel
#print axioms ray_forces_higher_smoothed_count
end
end Erdos952Investigation.GaussianSmoothingBuckets
