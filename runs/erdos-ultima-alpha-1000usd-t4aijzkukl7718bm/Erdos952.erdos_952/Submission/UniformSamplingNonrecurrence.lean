import Submission.BoundedGapNonrecurrence
import Submission.SyndeticSamplingGeometry

/-! The uniform strip-escaping countermodel remains nonrecurrent under every
bounded-gap sampling. This closes a gap in the earlier geometric countermodel,
not in the proof of the Gaussian moat conjecture. No primality is asserted. -/
namespace Erdos952Investigation.UniformSamplingNonrecurrence
open NonrecurrentEscapeCountermodel
open UniformSparseEscapeCountermodel (UniformlySparse)
set_option maxHeartbeats 0

lemma no_recurrent_suffix_of_eventual_recovery {α β : Type*}
    (w : ℕ → α) (v : ℕ → β) (T : ℕ)
    (hv : WordUniqueBlocks.NoRecurrentSuffix v)
    (hrec : ∀ a ≥ T, ∀ b ≥ T, w a = w b → v a = v b) :
    WordUniqueBlocks.NoRecurrentSuffix w := by
  intro a
  obtain ⟨L,N,hN⟩ := hv (a+T)
  refine ⟨T+L,N+T,?_⟩
  intro b hb
  obtain ⟨i,hi,hne⟩ := hN (b+T) (by omega)
  refine ⟨T+i,by omega,?_⟩
  intro he
  apply hne
  apply hrec (b+T+i) (by omega) (a+T+i) (by omega)
  simpa only [Nat.add_assoc] using he

lemma sampled_root_bounds (f : ℕ → ℕ) (hf : StrictMono f) (B : ℕ)
    (hgap : ∀ n, f (n+1) ≤ f n+B) (n : ℕ) (hn : B^2 ≤ n) :
    0 ≤ root (f (n+1))-root (f n) ∧
      root (f (n+1))-root (f n) ≤ 1 := by
  have hl := Nat.sqrt_le_sqrt (hf.monotone (Nat.le_succ n))
  have hh := (Nat.sqrt_le_sqrt (hgap n)).trans
    (sqrt_far_interval (f n) B (hn.trans (hf.id_le n)))
  simp only [Nat.succ_eq_add_one] at hl
  dsimp [root]
  omega

lemma sampled_increment_recovery (f : ℕ → ℕ) (hf : StrictMono f) (B : ℕ)
    (hgap : ∀ n, f (n+1) ≤ f n+B) (a b : ℕ)
    (ha : B^2 ≤ a) (hb : B^2 ≤ b)
    (he : path (f (a+1))-path (f a) = path (f (b+1))-path (f b)) :
    BoundedGapNonrecurrence.path (f (a+1))-BoundedGapNonrecurrence.path (f a) =
      BoundedGapNonrecurrence.path (f (b+1))-BoundedGapNonrecurrence.path (f b) := by
  have hre := congrArg Zsqrtd.re he
  have him := congrArg Zsqrtd.im he
  have hA := sampled_root_bounds f hf B hgap a ha
  have hB := sampled_root_bounds f hf B hgap b hb
  simp only [path,Zsqrtd.re_sub,Zsqrtd.im_sub] at hre him
  apply Zsqrtd.ext
  · exact hre
  · change root (f (a+1))-root (f a) = root (f (b+1))-root (f b)
    omega

/-- The same nonprime path has uniform strip escape and is nonrecurrent after
EVERY strictly increasing bounded-gap sampling. -/
theorem sampled_no_recurrent_suffix (f : ℕ → ℕ) (hf : StrictMono f) (B : ℕ)
    (hgap : ∀ n, f (n+1) ≤ f n+B) :
    WordUniqueBlocks.NoRecurrentSuffix (fun n => path (f (n+1))-path (f n)) := by
  exact no_recurrent_suffix_of_eventual_recovery _ _ (B^2)
    (BoundedGapNonrecurrence.sampled_no_recurrent_suffix f hf B hgap)
    (fun a ha b hb he => sampled_increment_recovery f hf B hgap a b ha hb he)

theorem sampled_unique_blocks (f : ℕ → ℕ) (hf : StrictMono f) (B : ℕ)
    (hgap : ∀ n, f (n+1) ≤ f n+B) :
    ∀ a, ∃ L, 0 < L ∧ ∀ b,
      (∀ i < L, path (f (b+i+1))-path (f (b+i)) =
        path (f (a+i+1))-path (f (a+i))) → b = a := by
  simpa only [Nat.add_assoc] using
    WordUniqueBlocks.unique_block (sampled_no_recurrent_suffix f hf B hgap)

theorem uniform_escape_sampling_counterexample :
    ∃ x : ℕ → GaussianInt, Function.Injective x ∧
      (∀ n, (x (n+1)-x n).norm < 123) ∧ UniformlySparse x ∧
      (∀ B : ℝ, ∃ K : ℕ, ∀ N : ℕ, ∀ a b : ℝ, max |a| |b| = 1 →
        ∃ i ≤ K, B < |a*((x (N+i)-x N).re : ℝ)+b*((x (N+i)-x N).im : ℝ)|) ∧
      ∀ f : ℕ → ℕ, StrictMono f → ∀ B : ℕ,
        (∀ n, f (n+1) ≤ f n+B) →
        WordUniqueBlocks.NoRecurrentSuffix (fun n => x (f (n+1))-x (f n)) :=
  ⟨path,path_injective,path_step_bound,path_uniformly_sparse,path_uniform_escape,
    sampled_no_recurrent_suffix⟩

/-- The annular construction applied to this strip-escaping path does not
produce recurrent samples at any radius. -/
theorem annular_samples_still_nonrecurrent (R : ℕ) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ f 0 = 0 ∧
      (∀ n, f (n+1) ≤ f n+(2*R+1)^2 ∧
        (R : ℤ)^2 < (path (f (n+1))-path (f n)).norm ∧
        (path (f (n+1))-path (f n)).norm < ((R : ℤ)+123)^2) ∧
      WordUniqueBlocks.NoRecurrentSuffix (fun n => path (f (n+1))-path (f n)) := by
  obtain ⟨f,hf,hf0,hs⟩ := BoundedAnnularSampling.bounded_gap_annular_subsequence
    path 123 R path_injective path_step_bound
  exact ⟨f,hf,hf0,hs,sampled_no_recurrent_suffix f hf ((2*R+1)^2)
    (fun n => (hs n).1)⟩

theorem sampled_uniform_escape (f : ℕ → ℕ) (hf : StrictMono f) (B : ℕ)
    (hgap : ∀ n, f (n+1) ≤ f n+B) :
    SyndeticSamplingGeometry.UniformEscape (fun n => path (f n)) := by
  exact SyndeticSamplingGeometry.uniform_escape_sampled path 123 path_step_bound
    path_uniform_escape f hf B hgap

/-- The sampled counterexample retains all three properties simultaneously:
annular jumps, uniform strip escape, and no recurrent increment suffix. -/
theorem annular_samples_combined (R : ℕ) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ f 0 = 0 ∧
      (∀ n, f (n+1) ≤ f n+(2*R+1)^2 ∧
        (R : ℤ)^2 < (path (f (n+1))-path (f n)).norm ∧
        (path (f (n+1))-path (f n)).norm < ((R : ℤ)+123)^2) ∧
      UniformlySparse (fun n => path (f n)) ∧
      SyndeticSamplingGeometry.UniformEscape (fun n => path (f n)) ∧
      WordUniqueBlocks.NoRecurrentSuffix (fun n => path (f (n+1))-path (f n)) := by
  obtain ⟨f,hf,hf0,hs,hn⟩ := annular_samples_still_nonrecurrent R
  exact ⟨f,hf,hf0,hs,
    SyndeticSamplingGeometry.uniformly_sparse_sampled path path_uniformly_sparse f hf.injective,
    sampled_uniform_escape f hf ((2*R+1)^2) (fun n => (hs n).1),hn⟩

#print axioms annular_samples_combined
#print axioms uniform_escape_sampling_counterexample
#print axioms sampled_no_recurrent_suffix
#print axioms annular_samples_still_nonrecurrent
end Erdos952Investigation.UniformSamplingNonrecurrence
