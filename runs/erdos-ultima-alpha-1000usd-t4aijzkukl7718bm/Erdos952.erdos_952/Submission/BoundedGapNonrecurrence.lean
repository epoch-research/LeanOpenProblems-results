import Submission.NonrecurrentEscapeCountermodel
import Submission.BoundedAnnularSampling

/-! Bounded-gap sampling does not force recurrence. The square-root graph is
an injective bounded-step lattice path, and every bounded-gap subsequence has
no recurrent increment suffix. It is not a Gaussian-prime ray. -/
namespace Erdos952Investigation.BoundedGapNonrecurrence
open NonrecurrentEscapeCountermodel
set_option maxHeartbeats 0

def path (n : ℕ) : GaussianInt := ⟨n,Nat.sqrt n⟩

lemma path_injective : Function.Injective path := by
  intro i j he
  exact Int.natCast_inj.mp (congrArg Zsqrtd.re he)

lemma path_step_bound (n : ℕ) : (path (n+1)-path n).norm < 3 := by
  have hh := rootStep_bounds n
  have hr : (0 : ℤ) ≤ (Nat.sqrt (n+1) : ℤ)-Nat.sqrt n ∧
      (Nat.sqrt (n+1) : ℤ)-Nat.sqrt n ≤ 1 := hh
  simp only [path,gaussian_norm_sq,Zsqrtd.re_sub,Zsqrtd.im_sub]
  push_cast
  nlinarith

lemma sampling_interval_bound (f : ℕ → ℕ) (B : ℕ)
    (hgap : ∀ n, f (n+1) ≤ f n+B) (a L : ℕ) :
    f (a+L) ≤ f a+B*L := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hh := hgap (a+L)
    simp only [Nat.add_assoc,Nat.mul_add,Nat.mul_one] at *
    omega

/-- Even bounded-gap thinning cannot turn this path into a recurrent one. -/
theorem sampled_no_recurrent_suffix (f : ℕ → ℕ) (hf : StrictMono f) (B : ℕ)
    (hgap : ∀ n, f (n+1) ≤ f n+B) :
    WordUniqueBlocks.NoRecurrentSuffix (fun n => path (f (n+1))-path (f n)) := by
  intro a
  let L := (f a+2)^2
  refine ⟨L,(B*L)^2,?_⟩
  intro b hb
  by_contra! he
  have hdisp (j : ℕ) (hj : j ≤ L) :
      (Nat.sqrt (f (b+j)) : ℤ)-Nat.sqrt (f b) =
        (Nat.sqrt (f (a+j)) : ℤ)-Nat.sqrt (f a) := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hprev := ih (by omega)
      have hh := congrArg Zsqrtd.im (he j (by omega))
      simp only [path,Zsqrtd.im_sub] at hh
      simp only [Nat.add_assoc] at *
      omega
  have hbig : f a+2 ≤ Nat.sqrt (f (a+L)) := by
    apply Nat.le_sqrt'.mpr
    have hh : a+L ≤ f (a+L) := hf.id_le (a+L)
    dsimp only [L] at *
    omega
  have hsmall : Nat.sqrt (f (b+L)) ≤ Nat.sqrt (f b)+1 := by
    have hidx := sampling_interval_bound f B hgap b L
    have hroot := Nat.sqrt_le_sqrt hidx
    have hlate : (B*L)^2 ≤ f b := hb.trans (hf.id_le b)
    exact hroot.trans (sqrt_far_interval (f b) (B*L) hlate)
  have hbase := Nat.sqrt_le_self (f a)
  have hsum := hdisp L le_rfl
  omega

/-- Every position of every such sampled increment word has a unique finite
block. This property is therefore not itself a contradiction. -/
theorem sampled_unique_blocks (f : ℕ → ℕ) (hf : StrictMono f) (B : ℕ)
    (hgap : ∀ n, f (n+1) ≤ f n+B) :
    ∀ a, ∃ L, 0 < L ∧ ∀ b,
      (∀ i < L, path (f (b+i+1))-path (f (b+i)) =
        path (f (a+i+1))-path (f (a+i))) → b = a := by
  simpa only [Nat.add_assoc] using
    WordUniqueBlocks.unique_block (sampled_no_recurrent_suffix f hf B hgap)

/-- In particular, the first-exit annular construction can retain the
nonrecurrence obstruction at every radius. No primality is asserted. -/
theorem annular_samples_still_nonrecurrent (R : ℕ) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ f 0 = 0 ∧
      (∀ n, f (n+1) ≤ f n+(2*R+1)^2 ∧
        (R : ℤ)^2 < (path (f (n+1))-path (f n)).norm ∧
        (path (f (n+1))-path (f n)).norm < ((R : ℤ)+3)^2) ∧
      WordUniqueBlocks.NoRecurrentSuffix (fun n => path (f (n+1))-path (f n)) := by
  obtain ⟨f,hf,hf0,hs⟩ := BoundedAnnularSampling.bounded_gap_annular_subsequence
    path 3 R path_injective path_step_bound
  exact ⟨f,hf,hf0,hs,sampled_no_recurrent_suffix f hf ((2*R+1)^2)
    (fun n => (hs n).1)⟩

#print axioms annular_samples_still_nonrecurrent
#print axioms sampled_no_recurrent_suffix
#print axioms sampled_unique_blocks
end Erdos952Investigation.BoundedGapNonrecurrence
