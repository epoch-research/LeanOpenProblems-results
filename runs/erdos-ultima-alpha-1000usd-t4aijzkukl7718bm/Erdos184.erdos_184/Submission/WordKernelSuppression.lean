import Submission.LabelKernelSuppression
import Submission.NormalizedKernel

/-! Every private marker in a cyclic word of at least three markers is
suppressible. Exact color-subfamily partition spectra are retained. -/
open scoped Classical
namespace Erdos184Work.WordKernel
open Erdos184Serial LabelKernel
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {K W : Type*} [DecidableEq K] [DecidableEq W] {n : K → ℕ}

noncomputable local instance : DecidableEq (Σ i, Fin (n i+2)) := Classical.decEq _

variable (place : ∀ i, Fin (n i+2) → W)

def source (e : Σ i, Fin (n i+2)) : W := place e.1 e.2

def target (e : Σ i, Fin (n i+2)) : W := place e.1 (e.2+1)

lemma prev_ne (m : ℕ) (j : Fin (m+2)) : j-1 ≠ j := by
  intro h
  have hh : j = j+1 := by simpa only [sub_add_cancel] using congrArg (fun x : Fin (m+2) => x+1) h
  have hh' := congrArg Fin.val hh
  simp only [Fin.val_add_eq_ite,Fin.val_one] at hh'
  split_ifs at hh' <;> omega

lemma next_ne (m : ℕ) (j : Fin (m+2)) : j+1 ≠ j := by
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_add_eq_ite,Fin.val_one] at hh
  split_ifs at hh <;> omega

lemma prev_ne_next {m : ℕ} (hm : 1 ≤ m) (j : Fin (m+2)) : j-1 ≠ j+1 := by
  intro h
  have hh : j = j+1+1 := by simpa only [sub_add_cancel] using congrArg (fun x : Fin (m+2) => x+1) h
  have hh' := congrArg Fin.val hh
  simp only [Fin.val_add_eq_ite,Fin.val_one] at hh'
  split_ifs at hh' <;> omega

variable (hinj : ∀ i, Function.Injective (place i))
variable (i : K) (j : Fin (n i+2))
variable (hprivate : ∀ k (r : Fin (n k+2)), place k r = place i j → k = i)

include hinj hprivate in
lemma private_label (e : Σ k, Fin (n k+2))
    (he : source place e = place i j) : e = ⟨i,j⟩ := by
  rcases e with ⟨k,r⟩
  have hk : k = i := hprivate k r he
  subst k
  exact congrArg (Sigma.mk i) (hinj i he)

noncomputable def suppression (hsize : 1 ≤ n i) : Suppression (source place) (target place) where
  left := ⟨i,j-1⟩
  right := ⟨i,j⟩
  middle := place i j
  distinct := by
    intro h
    have he : j-1 = j := by simpa only [Sigma.mk.inj_iff,heq_eq_eq,and_true,true_and] using h
    exact prev_ne (n i) j he
  left_src := fun h => prev_ne (n i) j (hinj i h)
  left_dst := by simp [target]
  right_src := rfl
  right_dst := fun h => next_ne (n i) j (hinj i h)
  outside := fun h => prev_ne_next hsize j (hinj i h)
  private_incidence e he := by
    rcases he with he | he
    · exact Or.inr (private_label place hinj i j hprivate e he)
    · rcases e with ⟨k,r⟩
      have hk : k = i := hprivate k (r+1) he
      subst k
      have hr : r+1 = j := hinj i he
      left
      apply congrArg (Sigma.mk i)
      exact eq_sub_of_add_eq hr

lemma suppressed_colors [Fintype K] (hsize : 1 ≤ n i) (A : Finset K) :
    (suppression place hinj i j hprivate hsize).transport.expand
      (Finset.univ.filter (fun e => e.val.1 ∈ A)) =
        Finset.univ.filter (fun e : Σ k, Fin (n k+2) => e.1 ∈ A) := by
  exact (suppression place hinj i j hprivate hsize).expand_colors Sigma.fst rfl A

lemma suppressed_spectrum [Fintype K] (hsize : 1 ≤ n i) (A : Finset K) (P : ℕ → Prop) :
    (∃ D, Partition (code (source place) (target place))
      (Finset.univ.filter (fun e : Σ k, Fin (n k+2) => e.1 ∈ A)) D ∧ P D.card) ↔
    (∃ D, Partition
      (code (suppression place hinj i j hprivate hsize).source
        (suppression place hinj i j hprivate hsize).target)
      (Finset.univ.filter (fun e => e.val.1 ∈ A)) D ∧ P D.card) := by
  exact (suppression place hinj i j hprivate hsize).partition_spectrum_colors_iff Sigma.fst rfl A P

#print axioms suppression
#print axioms suppressed_spectrum
end Erdos184Work.WordKernel
