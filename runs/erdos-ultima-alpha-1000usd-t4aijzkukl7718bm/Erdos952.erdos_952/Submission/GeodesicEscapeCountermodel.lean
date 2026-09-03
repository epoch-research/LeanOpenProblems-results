import Submission.GeodesicRayReduction
import Submission.AdmissibleRay
import Submission.UniformSparseEscapeCountermodel

/-! Even geodesics in the full bounded-range lattice graph can have uniform
zero planar density and escape every fixed-width strip. This nonprime example
rules out a purely geometric straightening shortcut, not the conjecture. -/
namespace Erdos952Investigation
namespace GeodesicEscapeCountermodel
open AdmissibleRay
open UniformEscapeCountermodel (height sign)
open UniformSparseEscapeCountermodel (UniformlySparse)
set_option maxHeartbeats 0

def path (K n : ℕ) : GaussianInt := ⟨(K : ℤ)*(n : ℤ),height n⟩

def stepBound (K : ℕ) : ℤ := (K : ℤ)^2+2

lemma path_zero (K : ℕ) : path K 0 = 0 := by
  apply Zsqrtd.ext <;> simp [path,height]

lemma path_injective (K : ℕ) (hK : 0 < K) : Function.Injective (path K) := by
  intro i j he
  have hr := congrArg Zsqrtd.re he
  change (K : ℤ)*(i : ℤ) = (K : ℤ)*(j : ℤ) at hr
  exact Int.natCast_inj.mp (mul_left_cancel₀ (by exact_mod_cast hK.ne') hr)

lemma path_step (K n : ℕ) : (path K (n+1)-path K n).norm = (K : ℤ)^2+1 := by
  have hs : (sign n)^2 = 1 := by
    have hh := congrArg (fun z : ℤ => z^2) (UniformEscapeCountermodel.sign_abs n)
    simpa using hh
  simp [path,gaussian_norm_sq,height,hs]
  ring

lemma path_adj (K : ℕ) (hK : 0 < K) (n : ℕ) :
    (latticeGraph (stepBound K)).Adj (path K n) (path K (n+1)) := by
  refine ⟨fun he => ?_,?_⟩
  · have := path_injective K hK he
    omega
  · rw [path_step]
    dsimp [stepBound]
    omega

lemma adjacent_real_bound (K : ℕ) (hK : 0 < K) {z w : GaussianInt}
    (h : (latticeGraph (stepBound K)).Adj z w) : |w.re-z.re| ≤ (K : ℤ) := by
  have hn := h.2
  rw [gaussian_norm_sq] at hn
  have hK' : (1 : ℤ) ≤ K := by exact_mod_cast hK
  change (w.re-z.re)^2+(w.im-z.im)^2 < (K : ℤ)^2+2 at hn
  by_contra! hh
  have hs : (K : ℤ)+1 ≤ |w.re-z.re| := by omega
  nlinarith [sq_abs (w.re-z.re),sq_nonneg (w.im-z.im)]

lemma walk_real_bound (K : ℕ) (hK : 0 < K) {z w : GaussianInt}
    (p : (latticeGraph (stepBound K)).Walk z w) :
    |w.re-z.re| ≤ (p.length : ℤ)*K := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    have hh := abs_sub_le c.re b.re a.re
    have hs := adjacent_real_bound K hK hab
    simp only [SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

/-- Every segment is shortest even when arbitrary intermediate lattice
points, not just points of the displayed path, are allowed. -/
theorem path_geodesic (K : ℕ) (hK : 0 < K) (i j : ℕ) :
    (latticeGraph (stepBound K)).dist (path K i) (path K j) = Nat.dist i j := by
  apply GeodesicRayReduction.geodesic_of_dist_from_start _ (path K) (path_adj K hK) _ i j
  intro n
  obtain ⟨p,hp⟩ := GeodesicRayReduction.segment_walk (latticeGraph (stepBound K))
    (path K) (path_adj K hK) 0 n
  have hp' : p.length = n := hp
  have hu := SimpleGraph.dist_le p
  have hr : (latticeGraph (stepBound K)).Reachable (path K 0) (path K n) := by
    simpa only [Nat.zero_add] using p.reachable
  obtain ⟨q,hq⟩ := hr.exists_walk_length_eq_dist
  have hl := walk_real_bound K hK q
  have hK' : (0 : ℤ) < K := by exact_mod_cast hK
  simp only [path,Int.natCast_zero,mul_zero,sub_zero] at hl
  rw [abs_of_nonneg (by positivity),hq] at hl
  have hn : n ≤ (latticeGraph (stepBound K)).dist (path K 0) (path K n) := by
    have hh : (n : ℤ) ≤ (latticeGraph (stepBound K)).dist (path K 0) (path K n) := by nlinarith
    exact_mod_cast hh
  simp only [Nat.zero_add] at hu
  omega

lemma path_square_card_le (K : ℕ) (hK : 0 < K) (z : GaussianInt)
    (R : ℕ) (S : Finset ℕ)
    (hS : ∀ n ∈ S, |(path K n).re-z.re| ≤ (R : ℤ) ∧
      |(path K n).im-z.im| ≤ (R : ℤ)) : S.card ≤ 2*R+1 := by
  have hsub : S.image (fun n : ℕ => (K : ℤ)*n) ⊆
      Finset.Icc (z.re-(R : ℤ)) (z.re+(R : ℤ)) := by
    intro t ht
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp ht
    have hh := abs_le.mp (hS n hn).1
    change -(R : ℤ) ≤ (K : ℤ)*n-z.re ∧ (K : ℤ)*n-z.re ≤ R at hh
    simp only [Finset.mem_Icc]
    omega
  have hcard := Finset.card_le_card hsub
  have hi : Function.Injective (fun n : ℕ => (K : ℤ)*n) := by
    intro i j he
    exact Int.natCast_inj.mp (mul_left_cancel₀ (by exact_mod_cast hK.ne') he)
  rw [Finset.card_image_of_injective S hi,Int.card_Icc] at hcard
  omega

theorem path_uniformly_sparse (K : ℕ) (hK : 0 < K) : UniformlySparse (path K) := by
  intro ε hε
  obtain ⟨R₀,hR₀⟩ := exists_nat_gt (1/ε)
  have hmul : 1 < (R₀ : ℝ)*ε := (div_lt_iff₀ hε).mp hR₀
  refine ⟨R₀,?_⟩
  intro R hR z S hS
  have hcard : (S.card : ℝ) ≤ 2*(R : ℝ)+1 := by
    exact_mod_cast path_square_card_le K hK z R S hS
  have hR' : (R₀ : ℝ) ≤ R := by exact_mod_cast hR
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hlarge : 1 ≤ ε*(2*(R : ℝ)+1) := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hlarge (by positivity : (0 : ℝ) ≤ 2*(R : ℝ)+1)
  nlinarith

/-- Horizontal stretching preserves the uniform all-direction escape
property of the original substitution path. -/
theorem path_uniform_escape (K : ℕ) (hK : 0 < K) (B : ℝ) :
    ∃ L : ℕ, ∀ N : ℕ, ∀ a b : ℝ, max |a| |b| = 1 →
      ∃ i ≤ L, B < |a*((path K (N+i)-path K N).re : ℝ)+
        b*((path K (N+i)-path K N).im : ℝ)| := by
  obtain ⟨L,hL⟩ := UniformEscapeCountermodel.path_uniform_escape (max B 0)
  refine ⟨L,?_⟩
  intro N a b hab
  let M : ℝ := max |a*(K : ℝ)| |b|
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hM1 : 1 ≤ M := by
    rw [← hab]
    apply max_le_max _ le_rfl
    rw [abs_mul,abs_of_nonneg (show (0 : ℝ) ≤ (K : ℝ) from Nat.cast_nonneg K)]
    nlinarith [abs_nonneg a]
  have hM : 0 < M := by linarith
  have hab' : max |(a*(K : ℝ))/M| |b/M| = 1 := by
    simp only [abs_div,abs_of_pos hM,max_div_div_right hM.le]
    exact div_self hM.ne'
  obtain ⟨i,hi,he⟩ := hL N ((a*(K : ℝ))/M) (b/M) hab'
  refine ⟨i,hi,?_⟩
  let E : ℝ := (a*(K : ℝ))/M*((UniformEscapeCountermodel.path (N+i)-
    UniformEscapeCountermodel.path N).re : ℝ)+b/M*((UniformEscapeCountermodel.path (N+i)-
    UniformEscapeCountermodel.path N).im : ℝ)
  have hE : max B 0 < |E| := he
  have hEq : a*((path K (N+i)-path K N).re : ℝ)+
      b*((path K (N+i)-path K N).im : ℝ) = M*E := by
    dsimp [E,path,UniformEscapeCountermodel.path]
    simp only [Int.cast_sub,Int.cast_mul,Int.cast_natCast]
    field_simp
  rw [hEq,abs_mul,abs_of_pos hM]
  have hh : |E| ≤ M*|E| := by nlinarith [abs_nonneg E]
  exact (le_max_left B 0).trans_lt (hE.trans_le hh)

/-- The extra geodesic assumption still does not repair the geometric
shortcut. The examples exist at arbitrarily large step scales. -/
theorem geodesic_sparse_escape_counterexample (K : ℕ) (hK : 0 < K) :
    ∃ x : ℕ → GaussianInt, x 0 = 0 ∧ Function.Injective x ∧
      (∀ n, (x (n+1)-x n).norm < stepBound K) ∧
      (∀ i j, (latticeGraph (stepBound K)).dist (x i) (x j) = Nat.dist i j) ∧
      UniformlySparse x ∧
      ∀ B : ℝ, ∃ L : ℕ, ∀ N : ℕ, ∀ a b : ℝ, max |a| |b| = 1 →
        ∃ i ≤ L, B < |a*((x (N+i)-x N).re : ℝ)+b*((x (N+i)-x N).im : ℝ)| := by
  exact ⟨path K,path_zero K,path_injective K hK,fun n => (path_adj K hK n).2,
    path_geodesic K hK,path_uniformly_sparse K hK,path_uniform_escape K hK⟩

#print axioms path_geodesic
#print axioms path_uniform_escape
#print axioms geodesic_sparse_escape_counterexample
end GeodesicEscapeCountermodel
end Erdos952Investigation
