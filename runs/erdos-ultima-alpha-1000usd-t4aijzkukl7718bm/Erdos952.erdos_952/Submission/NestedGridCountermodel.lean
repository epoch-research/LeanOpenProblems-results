import Submission.GraphReduction

/-! A countermodel to an abstract compactness shortcut, not to the Gaussian moat
conjecture: nested, periodic, square-symmetric sets can have rays at every level
with the same step bound, even though every fixed vertex eventually disappears. -/
namespace Erdos952Investigation
namespace NestedGridCountermodel

set_option maxHeartbeats 0

def Stripe (N : ℕ) (a : ℤ) : Prop := ∃ k : ℤ, a = 3^N * (2*k + 1)

def Grid (N : ℕ) (z : GaussianInt) : Prop := Stripe N z.re ∨ Stripe N z.im

lemma stripe_succ_subset (N : ℕ) (a : ℤ) : Stripe (N + 1) a → Stripe N a := by
  rintro ⟨k, hk⟩
  refine ⟨3*k + 1, ?_⟩
  rw [hk, pow_succ]
  ring

lemma grid_succ_subset (N : ℕ) (z : GaussianInt) : Grid (N + 1) z → Grid N z :=
  Or.imp (stripe_succ_subset N z.re) (stripe_succ_subset N z.im)

lemma grid_nested {N M : ℕ} (hNM : N ≤ M) {z : GaussianInt} : Grid M z → Grid N z := by
  induction M, hNM using Nat.le_induction with
  | base => exact id
  | succ M hNM ih => exact fun h => ih (grid_succ_subset M z h)

lemma stripe_neg (N : ℕ) (a : ℤ) : Stripe N (-a) ↔ Stripe N a := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨-k - 1, ?_⟩
    linear_combination -hk
  · rintro ⟨k, hk⟩
    refine ⟨-k - 1, ?_⟩
    linear_combination -hk

lemma stripe_period (N : ℕ) (a : ℤ) : Stripe N (a + 2 * 3^N) ↔ Stripe N a := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k - 1, ?_⟩
    linear_combination hk
  · rintro ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    linear_combination hk

lemma grid_real_period (N : ℕ) (z : GaussianInt) :
    Grid N (z + ⟨2 * 3^N, 0⟩) ↔ Grid N z := by
  simp [Grid, stripe_period]

lemma grid_imag_period (N : ℕ) (z : GaussianInt) :
    Grid N (z + ⟨0, 2 * 3^N⟩) ↔ Grid N z := by
  simp [Grid, stripe_period]

lemma grid_quarter_turn (N : ℕ) (z : GaussianInt) :
    Grid N (⟨-z.im, z.re⟩ : GaussianInt) ↔ Grid N z := by
  simp [Grid, stripe_neg, or_comm]

lemma grid_reflection (N : ℕ) (z : GaussianInt) :
    Grid N (star z) ↔ Grid N z := by
  simp [Grid, stripe_neg]

lemma stripe_lower_bound {N : ℕ} {a : ℤ} (h : Stripe N a) : (3 : ℤ)^N ≤ |a| := by
  obtain ⟨k, rfl⟩ := h
  have hodd : (1 : ℤ) ≤ |2*k + 1| := by
    have hpos := abs_pos.mpr (by omega : 2*k + 1 ≠ 0)
    omega
  have hpos : (0 : ℤ) ≤ 3^N := by positivity
  rw [abs_mul, abs_of_nonneg hpos]
  nlinarith

lemma grid_lower_bound {N : ℕ} {z : GaussianInt} (h : Grid N z) :
    (3 : ℤ)^N ≤ |z.re| + |z.im| := by
  rcases h with hr | hi
  · have := stripe_lower_bound hr
    have := abs_nonneg z.im
    omega
  · have := stripe_lower_bound hi
    have := abs_nonneg z.re
    omega

/-- No fixed lattice point survives every level. -/
theorem every_vertex_eventually_absent (z : GaussianInt) :
    ∃ N : ℕ, ∀ M ≥ N, ¬ Grid M z := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (|z.re| + |z.im|) (by decide : (1 : ℤ) < 3)
  refine ⟨N, ?_⟩
  intro M hM hz
  have := grid_lower_bound (grid_nested hM hz)
  omega

def graph (N : ℕ) : SimpleGraph GaussianInt where
  Adj z w := Grid N z ∧ Grid N w ∧ z ≠ w ∧ (w - z).norm < 2
  symm := by
    intro z w h
    exact ⟨h.2.1, h.1, h.2.2.1.symm, by rw [norm_sub_comm]; exact h.2.2.2⟩
  loopless := by intro z h; exact h.2.2.1 rfl

lemma finite_neighbors (N : ℕ) (z : GaussianInt) : ((graph N).neighborSet z).Finite := by
  have hinj : Function.Injective (fun w : GaussianInt => w - z) := by
    intro w v h
    simpa using h
  apply ((norm_sublevel_finite 2).preimage (f := fun w => w - z) hinj.injOn).subset
  intro w hw
  exact hw.2.2.2.le

noncomputable instance (N : ℕ) : (graph N).LocallyFinite :=
  fun z => (finite_neighbors N z).fintype

def ray (N : ℕ) (n : ℕ) : GaussianInt := ⟨3^N, n⟩

lemma ray_injective (N : ℕ) : Function.Injective (ray N) := by
  intro i j he
  have ht := congrArg Zsqrtd.im he
  change (i : ℤ) = (j : ℤ) at ht
  exact Int.natCast_inj.mp ht

lemma ray_grid (N n : ℕ) : Grid N (ray N n) :=
  Or.inl ⟨0, by simp [ray]⟩

lemma ray_step (N n : ℕ) : (ray N (n + 1) - ray N n).norm = 1 := by
  simp [ray, gaussian_norm_sq]

lemma ray_adj (N n : ℕ) : (graph N).Adj (ray N n) (ray N (n + 1)) := by
  refine ⟨ray_grid N n, ray_grid N (n + 1), ?_, by rw [ray_step]; norm_num⟩
  intro he
  have := ray_injective N he
  omega

/-- Every level has an infinite component, with squared steps exactly one. -/
theorem every_level_has_infinite_component (N : ℕ) :
    {w | (graph N).Reachable (ray N 0) w}.Infinite := by
  apply (RayReduction.ray_iff_infinite_component (graph N) (ray N 0)).mp
  exact ⟨ray N, rfl, ray_injective N, ray_adj N⟩

lemma component_singleton_of_absent {N : ℕ} {z : GaussianInt} (hz : ¬ Grid N z) :
    {w | (graph N).Reachable z w} = {z} := by
  ext w
  constructor
  · rintro ⟨p⟩
    cases p with
    | nil => simp
    | cons hzw p => exact (hz hzw.1).elim
  · intro hw
    rw [Set.mem_singleton_iff] at hw
    subst w
    exact SimpleGraph.Reachable.refl z

/-- Nevertheless, every fixed seed eventually has just a singleton component. -/
theorem every_seed_eventually_trapped (z : GaussianInt) :
    ∃ N : ℕ, ∀ M ≥ N, {w | (graph M).Reachable z w}.Finite := by
  obtain ⟨N, hN⟩ := every_vertex_eventually_absent z
  refine ⟨N, fun M hM => ?_⟩
  rw [component_singleton_of_absent (hN M hM)]
  exact Set.finite_singleton z

/-- The seedwise cutoff cannot be exchanged for a cutoff uniform in the seed,
even for this nested, periodic and square-symmetric family of lattice graphs. -/
theorem cutoff_quantifier_counterexample :
    (∀ z : GaussianInt, ∃ N : ℕ, {w | (graph N).Reachable z w}.Finite) ∧
      ¬ ∃ N : ℕ, ∀ z : GaussianInt, {w | (graph N).Reachable z w}.Finite := by
  constructor
  · intro z
    obtain ⟨N, hN⟩ := every_seed_eventually_trapped z
    exact ⟨N, hN N le_rfl⟩
  · rintro ⟨N, hN⟩
    exact every_level_has_infinite_component N (hN (ray N 0))

#print axioms cutoff_quantifier_counterexample
#print axioms every_vertex_eventually_absent
#print axioms grid_nested
#print axioms grid_real_period
#print axioms grid_quarter_turn

end NestedGridCountermodel
end Erdos952Investigation
