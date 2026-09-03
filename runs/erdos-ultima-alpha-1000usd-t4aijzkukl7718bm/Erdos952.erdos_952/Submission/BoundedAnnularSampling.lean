import Submission.AnnularStepSampling

/-! Quantitative first-exit sampling. This supplies bounded index gaps, but
neither periodicity nor recurrence of the sampled increments. -/
namespace Erdos952Investigation.BoundedAnnularSampling
open AnnularNecessity
set_option maxHeartbeats 0

lemma norm_bound_coordinates (R : ℕ) (z : GaussianInt)
    (hz : z.norm ≤ (R : ℤ)^2) :
    -(R : ℤ) ≤ z.re ∧ z.re ≤ R ∧ -(R : ℤ) ≤ z.im ∧ z.im ≤ R := by
  rw [gaussian_norm_sq] at hz
  have hr : |z.re| ≤ (R : ℤ) := by
    simpa only [abs_of_nonneg (Int.natCast_nonneg R)] using
      (sq_le_sq.mp (show z.re^2 ≤ (R : ℤ)^2 by nlinarith [sq_nonneg z.im]))
  have hi : |z.im| ≤ (R : ℤ) := by
    simpa only [abs_of_nonneg (Int.natCast_nonneg R)] using
      (sq_le_sq.mp (show z.im^2 ≤ (R : ℤ)^2 by nlinarith [sq_nonneg z.re]))
  exact ⟨(abs_le.mp hr).1,(abs_le.mp hr).2,(abs_le.mp hi).1,(abs_le.mp hi).2⟩

/-- At most (2R+1)^2 distinct lattice points lie in a radius-R disk. -/
lemma exists_early_exit (x : ℕ → GaussianInt) (hx : Function.Injective x) (R : ℕ) :
    ∃ n ≤ (2*R+1)^2, (R : ℤ)^2 < (x n).norm := by
  by_contra! hbound
  have hcoord (i : Fin ((2*R+1)^2+1)) :=
    norm_bound_coordinates R (x i.val) (hbound i.val (by have := i.isLt; omega))
  let f : Fin ((2*R+1)^2+1) → Fin (2*R+1) × Fin (2*R+1) := fun i =>
    (⟨((x i.val).re+R).toNat,by have := hcoord i; omega⟩,
     ⟨((x i.val).im+R).toNat,by have := hcoord i; omega⟩)
  have hf : Function.Injective f := by
    intro i j he
    have hre := congrArg (fun t : Fin (2*R+1) × Fin (2*R+1) => t.1.val) he
    have him := congrArg (fun t : Fin (2*R+1) × Fin (2*R+1) => t.2.val) he
    change ((x i.val).re+R).toNat = ((x j.val).re+R).toNat at hre
    change ((x i.val).im+R).toNat = ((x j.val).im+R).toNat at him
    have hi := hcoord i
    have hj := hcoord j
    apply Fin.ext
    apply hx
    apply Zsqrtd.ext <;> omega
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin,Fintype.card_prod] at hc
  nlinarith

lemma exists_later_annular_step_bounded (x : ℕ → GaussianInt) (C : ℤ) (R : ℕ)
    (hx : Function.Injective x) (hs : ∀ n, (x (n+1)-x n).norm < C) (i : ℕ) :
    ∃ j, i < j ∧ j ≤ i+(2*R+1)^2 ∧
      (R : ℤ)^2 < (x j-x i).norm ∧ (x j-x i).norm < ((R : ℤ)+C)^2 := by
  let y (n : ℕ) : GaussianInt := x (i+n)-x i
  have hy : Function.Injective y := by
    intro m n he
    apply Nat.add_left_cancel
    apply hx
    change x (i+m)-x i = x (i+n)-x i at he
    exact sub_left_inj.mp he
  have hys (n : ℕ) : (y (n+1)-y n).norm < C := by
    simpa only [y,sub_sub_sub_cancel_right,Nat.add_assoc] using hs (i+n)
  have hC : 0 < C := (GaussianInt.norm_nonneg _).trans_lt (hs 0)
  obtain ⟨m,hm,hmexit⟩ := exists_early_exit y hy R
  have hex : ∃ n, (R : ℤ)^2 < (y n).norm := ⟨m,hmexit⟩
  let n := Nat.find hex
  have hn : (R : ℤ)^2 < (y n).norm := Nat.find_spec hex
  have hnle : n ≤ (2*R+1)^2 := (Nat.find_min' hex hmexit).trans hm
  have hn0 : n ≠ 0 := by
    intro he
    simp only [he,y,Nat.add_zero,sub_self,Zsqrtd.norm_zero] at hn
    nlinarith [sq_nonneg (R : ℤ)]
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hprev : (y j).norm ≤ (R : ℤ)^2 := by
    exact le_of_not_gt (Nat.find_min hex (show j < Nat.find hex by change j < n; omega))
  have hupper : (y n).norm < ((R : ℤ)+C)^2 := by
    rw [hj]
    exact norm_lt_square_after_step (Int.natCast_nonneg R) hC hprev (hys j)
  exact ⟨i+n,by omega,by omega,hn,hupper⟩

/-- The selected indices have uniformly bounded gaps. This is stronger than
mere existence of an annular subsequence, but does not impose recurrence. -/
theorem bounded_gap_annular_subsequence (x : ℕ → GaussianInt) (C : ℤ) (R : ℕ)
    (hx : Function.Injective x) (hs : ∀ n, (x (n+1)-x n).norm < C) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ f 0 = 0 ∧
      ∀ n, f (n+1) ≤ f n+(2*R+1)^2 ∧
        (R : ℤ)^2 < (x (f (n+1))-x (f n)).norm ∧
        (x (f (n+1))-x (f n)).norm < ((R : ℤ)+C)^2 := by
  choose next hnext hgap hlo hhi using exists_later_annular_step_bounded x C R hx hs
  let f : ℕ → ℕ := Nat.rec 0 (fun _ j => next j)
  have hsucc (n : ℕ) : f (n+1) = next (f n) := rfl
  refine ⟨f,strictMono_nat_of_lt_succ (fun n => ?_),rfl,fun n => ?_⟩
  · rw [hsucc]; exact hnext (f n)
  · rw [hsucc]; exact ⟨hgap (f n),hlo (f n),hhi (f n)⟩

#print axioms exists_early_exit
#print axioms bounded_gap_annular_subsequence
end Erdos952Investigation.BoundedAnnularSampling
