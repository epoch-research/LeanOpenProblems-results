import Submission.LineRecoloringIterationExplore

/-! The peak obstruction is caused by the fixed routing pattern, not by
line geometry. Arbitrary new-color-dependent graph functions still exhibit
it if every old color is copied into every new color at its assigned row. -/
namespace Erdos66RoutedGraphIteration
open Erdos66GraphRowAssembly Erdos66LineRecoloringPeaks Erdos66LineRecoloringIteration
  Erdos66OriginRepair Erdos66ParabolaRepair
open Filter
open scoped Topology
set_option maxHeartbeats 2800000
universe u
variable {G F : Type u} [AddCommGroup G] [DecidableEq G]
  [Field F] [Fintype F] [DecidableEq F]

noncomputable def routed (A : F → Finset G) (α : F) (f : F → F → F) (v : F) :
    Finset (G×(F×F)) := rowAssembly (fun x ↦ A (v-α*x)) (f v)

def routedPoint (α : F) (f : F → F → F) (v u : F) : F×F :=
  (oldRow α v u,f v (oldRow α v u))

lemma routed_mixed_dominates (A : F → Finset G) (α : F) (hα : α≠0)
    (f : F → F → F) (u t v w : F) (z : G) :
    pairCount (A u) (A t) z ≤
      pairCount (routed A α f v) (routed A α f w)
        (z,routedPoint α f v u+routedPoint α f w t) := by
  have hh := row_mixed_dominates (fun x ↦ A (v-α*x)) (fun y ↦ A (w-α*y))
    (f v) (f w) (oldRow α v u) (oldRow α w t) z
  simpa only [label_oldRow α v u hα,label_oldRow α w t hα,routed,routedPoint,Prod.mk_add_mk] using hh

lemma routed_self_dominates_twice (A : F → Finset G) (α : F) (hα : α≠0)
    (f : F → F → F) (u t : F) (hut : u≠t) (v : F) (z : G) :
    2*pairCount (A u) (A t) z ≤
      pairCount (routed A α f v) (routed A α f v)
        (z,routedPoint α f v u+routedPoint α f v t) := by
  have hh := row_self_dominates_twice (fun x ↦ A (v-α*x)) (f v)
    (oldRow α v u) (oldRow α v t) (fun he ↦ hut (oldRow_injective α v hα he)) z
  simpa only [label_oldRow α v u hα,label_oldRow α v t hα,routed,routedPoint,Prod.mk_add_mk] using hh

/-- No polynomiality, bounded-sum property, or relation between the two
graph families is assumed. The routing alone forces this amplification. -/
theorem arbitrary_graph_two_step_amplification (A : F → Finset G)
    (α β : F) (hα : α≠0) (hβ : β≠0) (f h : F → F → F) (u v : F) (z : G) :
    ∃ z' : (G×(F×F))×(F×F),
      2*pairCount (A u) (A u) z ≤
        pairCount (routed (routed A α f) β h v) (routed (routed A α f) β h v) z' := by
  let z₁ := (z,routedPoint α f 0 u+routedPoint α f 1 u)
  refine ⟨(z₁,routedPoint β h v 0+routedPoint β h v 1),?_⟩
  have hfirst := routed_mixed_dominates A α hα f u u 0 1 z
  have hsecond := routed_self_dominates_twice (routed A α f) β hβ h 0 1 zero_ne_one v z₁
  exact (Nat.mul_le_mul_left 2 hfirst).trans hsecond

lemma routed_mono {A B : F → Finset G} (hAB : ∀ u, A u⊆B u)
    (α : F) (f : F → F → F) (v : F) : routed A α f v⊆routed B α f v := by
  rintro ⟨a,x,y⟩ ha
  rw [routed,mem_rowAssembly] at ha ⊢
  exact ⟨hAB _ ha.1,ha.2⟩

/-- Arbitrary colorwise additions are allowed after each routed graph lift. -/
theorem routed_two_step_extension_peak
    (B : (n : ℕ) → F → Finset (Space G F n)) (α : ℕ → F) (f : ℕ → F → F → F)
    (hα : ∀ n, α n≠0)
    (hstep : ∀ n v, routed (B n) (α n) (f n) v⊆B (n+1) v)
    (n : ℕ) (v : F) (z : Space G F n) :
    ∃ z' : Space G F (n+2),
      2*pairCount (B n v) (B n v) z≤pairCount (B (n+2) 0) (B (n+2) 0) z' := by
  obtain ⟨z',hz⟩ := arbitrary_graph_two_step_amplification (B n) (α n) (α (n+1))
    (hα n) (hα (n+1)) (f n) (f (n+1)) v 0 z
  have hsub : routed (routed (B n) (α n) (f n)) (α (n+1)) (f (n+1)) 0⊆B (n+2) 0 :=
    (routed_mono (hstep n) _ _ _).trans (hstep (n+1) 0)
  exact ⟨z',hz.trans (pairCount_mono hsub hsub z')⟩

/-- Arbitrarily changing nonlinear graphs do not remove the exponential
peak when the old-to-new color routing is retained. -/
theorem routed_even_stage_exponential_peak
    (B : (n : ℕ) → F → Finset (Space G F n)) (α : ℕ → F) (f : ℕ → F → F → F)
    (hα : ∀ n, α n≠0)
    (hstep : ∀ n v, routed (B n) (α n) (f n) v⊆B (n+1) v)
    (v : F) (z : G) (hseed : 1≤pairCount (B 0 v) (B 0 v) z) :
    ∀ k : ℕ, ∃ w : F, ∃ z' : Space G F (2*k),
      2^k≤pairCount (B (2*k) w) (B (2*k) w) z' := by
  intro k
  induction k with
  | zero => exact ⟨v,z,hseed⟩
  | succ k ih =>
    obtain ⟨w,z',hz'⟩ := ih
    obtain ⟨z'',hz''⟩ := routed_two_step_extension_peak B α f hα hstep (2*k) w z'
    refine ⟨0,z'',?_⟩
    have hh := (Nat.mul_le_mul_left 2 hz').trans hz''
    simpa only [pow_succ,Nat.mul_comm (2^k) 2] using hh

/-- This excludes a logarithmic cap for the whole routed iteration, not
only for individual new colors. It is a finite-product-group statement. -/
theorem routed_iteration_exceeds_logarithmic_cap [Fintype G]
    (B : (n : ℕ) → F → Finset (Space G F n)) (α : ℕ → F) (f : ℕ → F → F → F)
    (hα : ∀ n, α n≠0)
    (hstep : ∀ n v, routed (B n) (α n) (f n) v⊆B (n+1) v)
    (v : F) (hB : (B 0 v).Nonempty) (K C : ℝ) :
    ∀ᶠ k : ℕ in atTop, ∃ z : Space G F (2*k),
      K+C*Real.log (Fintype.card (Space G F (2*k)) : ℝ)<
        (pairCount (Finset.univ.biUnion (B (2*k))) (Finset.univ.biUnion (B (2*k))) z : ℝ) := by
  obtain ⟨a,ha⟩ := hB
  have hp := routed_even_stage_exponential_peak B α f hα hstep v (a+a) (singleton_seed (B 0) v ha)
  filter_upwards [eventually_linear_lt_two_pow
    (K+C*Real.log (Fintype.card G : ℝ)) (4*C*Real.log (Fintype.card F : ℝ))] with k hk
  obtain ⟨w,z,hz⟩ := hp k
  have hs : B (2*k) w⊆Finset.univ.biUnion (B (2*k)) := by
    intro a ha
    exact Finset.mem_biUnion.mpr ⟨w,Finset.mem_univ _,ha⟩
  have hle : (2:ℝ)^k≤
      (pairCount (Finset.univ.biUnion (B (2*k))) (Finset.univ.biUnion (B (2*k))) z : ℝ) := by
    exact_mod_cast hz.trans (pairCount_mono hs hs z)
  refine ⟨z,lt_of_lt_of_le ?_ hle⟩
  rw [space_log_even]
  convert hk using 1; ring

/-- Replacing lines by parallel translates of an arbitrary graph is one
instance of this routing pattern. -/
lemma parallel_graph_routing (A : F → Finset G) (α : F) (g : F → F) (v : F) :
    routed A α (fun v x ↦ g x+(v-α*x)) v=
      rowAssembly (fun x ↦ A (v-α*x)) (fun x ↦ g x+(v-α*x)) := rfl

end Erdos66RoutedGraphIteration
