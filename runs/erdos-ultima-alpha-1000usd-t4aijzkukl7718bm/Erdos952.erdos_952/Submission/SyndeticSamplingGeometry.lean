import Submission.SievePeriodicDrift
import Submission.UniformSparseEscapeCountermodel

/-! Bounded-gap subsequences preserve uniform strip escape. These geometric
facts do not establish Gaussian-prime recurrence or the moat conjecture. -/
namespace Erdos952Investigation.SyndeticSamplingGeometry
open SievePeriodicDrift
open UniformSparseEscapeCountermodel (UniformlySparse)
set_option maxHeartbeats 0

def project (a b : ℝ) (z : GaussianInt) : ℝ := a*z.re+b*z.im

def UniformEscape (x : ℕ → GaussianInt) : Prop :=
  ∀ R : ℝ, ∃ K : ℕ, ∀ N : ℕ, ∀ a b : ℝ, max |a| |b| = 1 →
    ∃ i ≤ K, R < |project a b (x (N+i)-x N)|

lemma project_sub (a b : ℝ) (z w : GaussianInt) :
    project a b (z-w) = project a b z-project a b w := by
  simp only [project,Zsqrtd.re_sub,Zsqrtd.im_sub,Int.cast_sub]
  ring

lemma project_abs_le_taxicab (a b : ℝ) (hab : max |a| |b| = 1)
    (z : GaussianInt) : |project a b z| ≤ (taxicab z : ℝ) := by
  have ha : |a| ≤ 1 := (le_max_left _ _).trans_eq hab
  have hb : |b| ≤ 1 := (le_max_right _ _).trans_eq hab
  calc
    _ ≤ |a*(z.re : ℝ)|+|b*(z.im : ℝ)| := abs_add_le _ _
    _ = |a| * |(z.re : ℝ)|+|b| * |(z.im : ℝ)| := by rw [abs_mul,abs_mul]
    _ ≤ 1* |(z.re : ℝ)|+1* |(z.im : ℝ)| := by gcongr
    _ = _ := by simp [taxicab]

lemma projection_interval_bound (x : ℕ → GaussianInt) (C : ℤ)
    (hs : ∀ n, (x (n+1)-x n).norm < C)
    (a b : ℝ) (hab : max |a| |b| = 1) (N k : ℕ) :
    |project a b (x (N+k)-x N)| ≤ (k : ℝ)*C := by
  have hh : (taxicab (x (N+k)-x N) : ℝ) ≤ (k : ℝ)*C := by
    exact_mod_cast taxicab_drift_le x C hs N k
  exact (project_abs_le_taxicab a b hab _).trans hh

lemma strictMono_interval (f : ℕ → ℕ) (hf : StrictMono f) (N i : ℕ) :
    f N+i ≤ f (N+i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h := hf (show N+i < N+(i+1) by omega)
    omega

/-- Every point of the original index interval lies within B of a sampled
point, reached in at most as many sample steps. -/
lemma sampling_cover (f : ℕ → ℕ) (hf : StrictMono f) (B : ℕ)
    (hgap : ∀ n, f (n+1) ≤ f n+B) (N i : ℕ) :
    ∃ j ≤ i, f N+i ≤ f (N+j) ∧ f (N+j) ≤ f N+i+B := by
  have hex : ∃ j, f N+i ≤ f (N+j) := ⟨i,strictMono_interval f hf N i⟩
  let j := Nat.find hex
  have hj := Nat.find_spec hex
  have hji : j ≤ i := Nat.find_min' hex (strictMono_interval f hf N i)
  refine ⟨j,hji,hj,?_⟩
  by_cases hj0 : j = 0
  · simp only [hj0,Nat.add_zero]
    omega
  · obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    have hprev : ¬ f N+i ≤ f (N+k) :=
      Nat.find_min hex (show k < Nat.find hex by change k < j; omega)
    have hh := hgap (N+k)
    rw [hk]
    simp only [Nat.succ_eq_add_one,Nat.add_assoc] at *
    omega

/-- Uniform strip escape survives every strictly increasing bounded-gap
subsequence. The jump bound controls the error between sampled points. -/
theorem uniform_escape_sampled (x : ℕ → GaussianInt) (C : ℤ)
    (hs : ∀ n, (x (n+1)-x n).norm < C) (hx : UniformEscape x)
    (f : ℕ → ℕ) (hf : StrictMono f) (B : ℕ)
    (hgap : ∀ n, f (n+1) ≤ f n+B) : UniformEscape (fun n => x (f n)) := by
  have hC : (0 : ℝ) ≤ C := by
    exact_mod_cast (GaussianInt.norm_nonneg _).trans (hs 0).le
  intro R
  obtain ⟨K,hK⟩ := hx (R+(B : ℝ)*C)
  refine ⟨K,?_⟩
  intro N a b hab
  obtain ⟨i,hi,hlarge⟩ := hK (f N) a b hab
  obtain ⟨j,hj,hl,hu⟩ := sampling_cover f hf B hgap N i
  refine ⟨j,hj.trans hi,?_⟩
  have herr : |project a b (x (f (N+j))-x (f N+i))| ≤ (B : ℝ)*C := by
    have hh := projection_interval_bound x C hs a b hab (f N+i) (f (N+j)-(f N+i))
    rw [Nat.add_sub_of_le hl] at hh
    have hsub : ((f (N+j)-(f N+i) : ℕ) : ℝ) ≤ B := by
      exact_mod_cast (show f (N+j)-(f N+i) ≤ B by omega)
    exact hh.trans (mul_le_mul_of_nonneg_right hsub hC)
  have ht : |project a b (x (f N+i)-x (f N))| ≤
      |project a b (x (f (N+j))-x (f N))|+
        |project a b (x (f (N+j))-x (f N+i))| := by
    simp only [project_sub]
    have hh := abs_sub_le (project a b (x (f N+i)))
      (project a b (x (f (N+j)))) (project a b (x (f N)))
    rw [abs_sub_comm (project a b (x (f N+i))) (project a b (x (f (N+j))))] at hh
    linarith
  dsimp only
  linarith

/-- An injective subsequence cannot increase the number of vertices in a box. -/
theorem uniformly_sparse_sampled (x : ℕ → GaussianInt) (hx : UniformlySparse x)
    (f : ℕ → ℕ) (hf : Function.Injective f) :
    UniformlySparse (fun n => x (f n)) := by
  classical
  intro ε hε
  obtain ⟨R₀,hR₀⟩ := hx ε hε
  refine ⟨R₀,?_⟩
  intro R hR z S hS
  have hh := hR₀ R hR z (S.image f) (by
    intro n hn
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hn
    exact hS i hi)
  rwa [Finset.card_image_of_injective S hf] at hh

#print axioms uniform_escape_sampled
#print axioms uniformly_sparse_sampled
end Erdos952Investigation.SyndeticSamplingGeometry
