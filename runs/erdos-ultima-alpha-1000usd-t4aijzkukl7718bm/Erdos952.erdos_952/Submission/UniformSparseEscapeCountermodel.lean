import Submission.UniformEscapeCountermodel

/-! Vanishing uniform planar density does not repair the geometric shortcut.
The explicit nonprime walk already has at most one vertex at each real
coordinate, while satisfying uniform escape in every direction. -/
namespace Erdos952Investigation
namespace UniformSparseEscapeCountermodel
open UniformEscapeCountermodel
set_option maxHeartbeats 0

/-- A formulation of uniform zero square density using arbitrary finite sets
of indices. For an injective walk this counts distinct vertices. -/
def UniformlySparse (x : ℕ → GaussianInt) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R ≥ R₀, ∀ z : GaussianInt, ∀ S : Finset ℕ,
    (∀ n ∈ S, |(x n).re-z.re| ≤ (R : ℤ) ∧ |(x n).im-z.im| ≤ (R : ℤ)) →
    (S.card : ℝ) ≤ ε*(2*(R : ℝ)+1)^2

lemma path_square_card_le (z : GaussianInt) (R : ℕ) (S : Finset ℕ)
    (hS : ∀ n ∈ S, |(path n).re-z.re| ≤ (R : ℤ) ∧
      |(path n).im-z.im| ≤ (R : ℤ)) : S.card ≤ 2*R+1 := by
  have hsub : S.image (fun n : ℕ => (n : ℤ)) ⊆
      Finset.Icc (z.re-(R : ℤ)) (z.re+(R : ℤ)) := by
    intro t ht
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp ht
    have hh := (abs_le.mp (hS n hn).1)
    change -(R : ℤ) ≤ (n : ℤ)-z.re ∧ (n : ℤ)-z.re ≤ R at hh
    simp only [Finset.mem_Icc]
    omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective S (by intro i j h; exact Int.natCast_inj.mp h)] at hcard
  have hIcc : (Finset.Icc (z.re-(R : ℤ)) (z.re+(R : ℤ))).card = 2*R+1 := by
    rw [Int.card_Icc]
    omega
  rwa [hIcc] at hcard

theorem path_uniformly_sparse : UniformlySparse path := by
  intro ε hε
  obtain ⟨R₀,hR₀⟩ := exists_nat_gt (1/ε)
  have hmul : 1 < (R₀ : ℝ)*ε := (div_lt_iff₀ hε).mp hR₀
  refine ⟨R₀,?_⟩
  intro R hR z S hS
  have hcard : (S.card : ℝ) ≤ 2*(R : ℝ)+1 := by
    exact_mod_cast path_square_card_le z R S hS
  have hR' : (R₀ : ℝ) ≤ R := by exact_mod_cast hR
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hlarge : 1 ≤ ε*(2*(R : ℝ)+1) := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hlarge (by positivity : (0 : ℝ) ≤ 2*(R : ℝ)+1)
  nlinarith

/-- Even uniform zero density and uniform all-direction strip escape together
are compatible with an injective bounded-step lattice ray. This is not a prime
ray, and therefore does not disprove the conjecture. -/
theorem sparse_geometric_counterexample :
    ∃ x : ℕ → GaussianInt, Function.Injective x ∧
      (∀ n, (x (n+1)-x n).norm = 2) ∧ UniformlySparse x ∧
      ∀ B : ℝ, ∃ K : ℕ, ∀ N : ℕ, ∀ a b : ℝ, max |a| |b| = 1 →
        ∃ i ≤ K, B < |a*((x (N+i)-x N).re : ℝ)+b*((x (N+i)-x N).im : ℝ)| :=
  ⟨path,path_injective,path_step,path_uniformly_sparse,path_uniform_escape⟩

#print axioms path_square_card_le
#print axioms path_uniformly_sparse
#print axioms sparse_geometric_counterexample
end UniformSparseEscapeCountermodel
end Erdos952Investigation
