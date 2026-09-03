import Submission.NestedGridCountermodel
import Submission.PeriodicSieveEndsLogic

/-! A countermodel to a topological inference, not to the Gaussian moat
conjecture. A nested family retains the prime 3, differs from a periodic grid
at only finitely many vertices, and has a unique infinite component at every
stage. Nevertheless, 3 is eventually isolated. The vertex predicates here are
not the Gaussian prime sieve. -/
namespace Erdos952Investigation.NestedGridRetainedSeed
open NestedGridCountermodel
open PeriodicSieveEnds (reachable_int_line)
set_option maxHeartbeats 0

def Anchor (z : GaussianInt) : Prop := z.norm = 9

def Retained (N : ℕ) (z : GaussianInt) : Prop := Grid N z ∨ Anchor z

def retainedGraph (N : ℕ) : SimpleGraph GaussianInt where
  Adj z w := Retained N z ∧ Retained N w ∧ z ≠ w ∧ (w-z).norm < 2
  symm := by
    intro z w h
    exact ⟨h.2.1,h.1,h.2.2.1.symm,by rw [norm_sub_comm]; exact h.2.2.2⟩
  loopless := by intro z h; exact h.2.2.1 rfl

lemma anchor_finite : {z | Anchor z}.Finite :=
  (norm_sublevel_finite 9).subset (fun _ hz => hz.le)

lemma retains_three (N : ℕ) : Retained N (3 : GaussianInt) := by
  right
  norm_num [Anchor,gaussian_norm_sq]

lemma retained_nested {N M : ℕ} (hNM : N ≤ M) {z : GaussianInt} :
    Retained M z → Retained N z :=
  Or.imp (grid_nested hNM) id

lemma retained_diff_finite (N : ℕ) :
    {z | ¬ (Retained N z ↔ Grid N z)}.Finite := by
  apply anchor_finite.subset
  intro z hz
  by_contra ha
  change ¬ Anchor z at ha
  apply hz
  simp only [Retained,ha,or_false]

lemma retained_quarter_turn (N : ℕ) (z : GaussianInt) :
    Retained N (⟨-z.im,z.re⟩ : GaussianInt) ↔ Retained N z := by
  simp only [Retained,grid_quarter_turn,Anchor,gaussian_norm_sq]
  simp only [neg_sq,add_comm]

lemma retained_reflection (N : ℕ) (z : GaussianInt) :
    Retained N (star z) ↔ Retained N z := by
  simp [Retained,grid_reflection,Anchor,gaussian_norm_sq]

lemma grid_graph_le (N : ℕ) : graph N ≤ retainedGraph N := by
  intro z w h
  exact ⟨Or.inl h.1,Or.inl h.2.1,h.2.2⟩

lemma horizontal_reachable (N : ℕ) (b : ℤ) (hb : Stripe N b) (a c : ℤ) :
    (graph N).Reachable (⟨a,b⟩ : GaussianInt) ⟨c,b⟩ := by
  apply reachable_int_line (fun t => (⟨t,b⟩ : GaussianInt)) _ a c
  intro t
  apply SimpleGraph.Adj.reachable
  refine ⟨Or.inr hb,Or.inr hb,?_,?_⟩
  · intro h
    have hh := congrArg Zsqrtd.re h
    dsimp at hh
    omega
  · norm_num [gaussian_norm_sq]

lemma vertical_reachable (N : ℕ) (a : ℤ) (ha : Stripe N a) (b c : ℤ) :
    (graph N).Reachable (⟨a,b⟩ : GaussianInt) ⟨a,c⟩ := by
  apply reachable_int_line (fun t => (⟨a,t⟩ : GaussianInt)) _ b c
  intro t
  apply SimpleGraph.Adj.reachable
  refine ⟨Or.inl ha,Or.inl ha,?_,?_⟩
  · intro h
    have hh := congrArg Zsqrtd.im h
    dsimp at hh
    omega
  · norm_num [gaussian_norm_sq]

lemma stripe_power (N : ℕ) : Stripe N ((3 : ℤ)^N) := ⟨0,by simp⟩

lemma reachable_corner (N : ℕ) {z : GaussianInt} (hz : Grid N z) :
    (graph N).Reachable z (⟨3^N,3^N⟩ : GaussianInt) := by
  rcases hz with hr | hi
  · exact (vertical_reachable N z.re hr z.im (3^N)).trans
      (horizontal_reachable N (3^N) (stripe_power N) z.re (3^N))
  · exact (horizontal_reachable N z.im hi z.re (3^N)).trans
      (vertical_reachable N (3^N) (stripe_power N) z.im (3^N))

lemma grid_vertices_connected (N : ℕ) {z w : GaussianInt}
    (hz : Grid N z) (hw : Grid N w) : (graph N).Reachable z w :=
  (reachable_corner N hz).trans (reachable_corner N hw).symm

/-- The entire grid is one infinite component. -/
lemma grid_component_infinite (N : ℕ) {z : GaussianInt} (hz : Grid N z) :
    {w | (graph N).Reachable z w}.Infinite := by
  apply (Set.infinite_range_of_injective (ray_injective N)).mono
  rintro w ⟨n,rfl⟩
  exact grid_vertices_connected N hz (ray_grid N n)

lemma reachable_vertex_retained {N : ℕ} {z w : GaussianInt}
    (h : (retainedGraph N).Reachable z w) : w = z ∨ Retained N w := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Or.inl rfl
  | @cons a b c hab p ih =>
    rcases ih with h | h
    · exact Or.inr (h ▸ hab.2.1)
    · exact Or.inr h

lemma infinite_component_meets_grid {N : ℕ} {z : GaussianInt}
    (hz : {w | (retainedGraph N).Reachable z w}.Infinite) :
    ∃ w, (retainedGraph N).Reachable z w ∧ Grid N w := by
  obtain ⟨w,hw,hex⟩ := (hz.diff (anchor_finite.union (Set.finite_singleton z))).nonempty
  refine ⟨w,hw,?_⟩
  rcases reachable_vertex_retained hw with he | hg | ha
  · exact (hex (Or.inr he)).elim
  · exact hg
  · exact (hex (Or.inl ha)).elim

/-- Adding the finite anchor set does not create a second infinite component. -/
theorem infinite_component_unique (N : ℕ) {z w : GaussianInt}
    (hz : {v | (retainedGraph N).Reachable z v}.Infinite)
    (hw : {v | (retainedGraph N).Reachable w v}.Infinite) :
    (retainedGraph N).Reachable z w := by
  obtain ⟨a,hza,ha⟩ := infinite_component_meets_grid hz
  obtain ⟨b,hwb,hb⟩ := infinite_component_meets_grid hw
  exact hza.trans (((grid_vertices_connected N ha hb).mono (grid_graph_le N)).trans hwb.symm)

theorem every_level_infinite (N : ℕ) :
    {w | (retainedGraph N).Reachable (ray N 0) w}.Infinite :=
  (every_level_has_infinite_component N).mono (fun _ h => h.mono (grid_graph_le N))

lemma three_no_neighbors {N : ℕ} (hN : 2 ≤ N) :
    ∀ w, ¬ (retainedGraph N).Adj (3 : GaussianInt) w := by
  intro w hw
  have hn : (w.re-3)^2+w.im^2 < 2 := by
    simpa only [gaussian_norm_sq,Zsqrtd.re_sub,Zsqrtd.im_sub,Zsqrtd.re_ofNat,
      Zsqrtd.im_ofNat,sub_zero] using hw.2.2.2
  have hr : 2 ≤ w.re ∧ w.re ≤ 4 := by
    constructor <;> nlinarith [sq_nonneg w.im]
  have hi : -1 ≤ w.im ∧ w.im ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (w.re-3)]
  rcases hw.2.1 with hg | ha
  · have hgl := grid_lower_bound (grid_nested hN hg)
    norm_num at hgl
    have hrabs : |w.re| ≤ 4 := abs_le.mpr (by omega)
    have hiabs : |w.im| ≤ 1 := abs_le.mpr hi
    omega
  · have hnorm : w.re^2+w.im^2 = 9 := by simpa only [Anchor,gaussian_norm_sq] using ha
    have hre : w.re = 3 := by
      have hcases : w.re = 2 ∨ w.re = 3 ∨ w.re = 4 := by omega
      rcases hcases with h | h | h <;> nlinarith
    have him : w.im = 0 := by rw [hre] at hnorm; nlinarith [sq_nonneg w.im]
    apply hw.2.2.1
    apply Zsqrtd.ext <;> dsimp <;> omega

theorem three_component_singleton {N : ℕ} (hN : 2 ≤ N) :
    {w | (retainedGraph N).Reachable (3 : GaussianInt) w} = {(3 : GaussianInt)} := by
  ext w
  constructor
  · rintro ⟨p⟩
    cases p with
    | nil => simp
    | cons h p => exact (three_no_neighbors hN _ h).elim
  · intro h
    rw [Set.mem_singleton_iff] at h
    subst w
    exact SimpleGraph.Reachable.refl _

/-- Retention of the specified prime, nesting, finite perturbation of a
periodic symmetric grid, and uniqueness of each infinite component do not
justify exchanging the seed and cutoff quantifiers. -/
theorem retained_seed_counterexample :
    (∀ N, Retained N (3 : GaussianInt)) ∧
    (∀ N, ∃ z, {w | (retainedGraph N).Reachable z w}.Infinite) ∧
    (∀ N, ∀ z w,
      {v | (retainedGraph N).Reachable z v}.Infinite →
      {v | (retainedGraph N).Reachable w v}.Infinite →
      (retainedGraph N).Reachable z w) ∧
    ∀ N ≥ 2, {w | (retainedGraph N).Reachable (3 : GaussianInt) w}.Finite := by
  refine ⟨retains_three,fun N => ⟨_,every_level_infinite N⟩,
    fun N z w hz hw => infinite_component_unique N hz hw,?_⟩
  intro N hN
  rw [three_component_singleton hN]
  exact Set.finite_singleton _

#print axioms retained_diff_finite
#print axioms infinite_component_unique
#print axioms retained_seed_counterexample
end Erdos952Investigation.NestedGridRetainedSeed
