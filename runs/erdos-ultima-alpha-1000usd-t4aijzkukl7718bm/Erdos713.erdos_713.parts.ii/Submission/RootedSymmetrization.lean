import FormalConjecturesUtil
import Submission.CompactActualBlocksAudit

/-! Root invariance on connected forbidden graphs and encoding a rooted power
bound by gluing two copies at adjacent roots. No rationality of these bounds is
assumed or asserted. -/
open SimpleGraph Filter Asymptotics
namespace Erdos713RootPower
open Erdos713Rate Erdos713Gluing

lemma RootPowerBound.of_adj {W : Type*} {H : SimpleGraph W} {x y : W} {r : ℝ}
    (h : RootPowerBound H x r) (hxy : H.Adj x y) : RootPowerBound H y r := by
  obtain ⟨C,hC,hbound⟩ := h
  refine ⟨C,hC,?_⟩
  intro n G S hB hroot
  apply hbound n G Sᶜ (by simpa only [compl_compl] using hB.symm)
  intro f
  simpa only [Set.mem_compl_iff,not_not] using
    hB.symm.mem_of_mem_adj (hroot f) (f.toHom.map_adj hxy.symm)

lemma RootPowerBound.of_reachable {W : Type*} {H : SimpleGraph W} {x y : W} {r : ℝ}
    (h : RootPowerBound H x r) (hxy : H.Reachable x y) : RootPowerBound H y r := by
  obtain ⟨p⟩ := hxy
  have hh : ∀ {u v : W}, H.Walk u v → RootPowerBound H u r → RootPowerBound H v r := by
    intro u v p
    induction p with
    | nil => exact id
    | cons hadj p ih => exact fun hu => ih (hu.of_adj hadj)
  exact hh p h

lemma rootPowerBound_iff_of_connected {W : Type*} {H : SimpleGraph W}
    (hH : H.Connected) (x y : W) (r : ℝ) : RootPowerBound H x r ↔ RootPowerBound H y r :=
  ⟨fun h => h.of_reachable (hH x y),fun h => h.of_reachable (hH y x)⟩

/-- Opposite-shore gluing is free whenever all copies place the original root
outside the designated shore. This needs only adjacency of the two roots. -/
lemma opposite_wedge_free {W V : Type*} (H : SimpleGraph W) {x y : W}
    (hxy : H.Adj x y) (G : SimpleGraph V) (S : Set V)
    (hB : G.IsBipartiteWith S Sᶜ) (hroot : ∀ f : H.Copy G, f x ∉ S) :
    (wedge H x H y).Free G := by
  classical
  rintro ⟨f⟩
  let a : H.Copy G := f.comp (leftCopy H x H y)
  let b : H.Copy G := f.comp (rightCopy H x H y)
  have he : a x = b y := by simp [a,b,leftCopy,rightCopy,Copy.comp]
  have hby : b y ∈ Sᶜ := he ▸ hroot a
  exact hroot b (hB.symm.mem_of_mem_adj hby (b.toHom.map_adj hxy.symm))

lemma of_opposite_wedge_upper {W : Type*} (H : SimpleGraph W) {x y : W}
    (hxy : H.Adj x y) {r : ℝ} (hr : 0 ≤ r)
    (h : (fun n : ℕ => (extremalNumber n (wedge H x H y) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^r)) : RootPowerBound H x r := by
  obtain ⟨C,hC,hbound⟩ := global_free_bound_of_upper (wedge H x H y) hr h
  exact ⟨C,hC,fun n G S hB hroot => hbound n G (opposite_wedge_free H hxy G S hB hroot)⟩

/-- A rooted bound implies the ordinary bound, by retaining a bipartite
subgraph with at least half of the host's edges. -/
lemma RootPowerBound.upper {W : Type*} {H : SimpleGraph W} {x : W} {r : ℝ}
    (h : RootPowerBound H x r) :
    (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^r) := by
  classical
  obtain ⟨C,hC,hbound⟩ := h
  apply IsBigO.of_bound (2*C)
  filter_upwards with n
  rw [Real.norm_natCast,Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) r)]
  rw [← Fintype.card_fin n,extremalNumber_le_iff_of_nonneg _ (by positivity)]
  intro G _ hG
  obtain ⟨K,hKG,hKB,hhalf⟩ := Erdos713Cut.exists_bipartite_half G
  obtain ⟨χ⟩ := hKB
  let S : Set (Fin n) := {v | χ v = 0}
  have hS : K.IsBipartiteWith S Sᶜ := by
    refine ⟨disjoint_compl_right,?_⟩
    intro u v huv
    have hc := χ.valid huv
    simp only [S,Set.mem_setOf_eq,Set.mem_compl_iff]
    omega
  have hb := hbound n K S hS (fun f =>
    (hG ((show H ⊑ K from ⟨f⟩).mono_right hKG)).elim)
  have hhalf' : (G.edgeFinset.card : ℝ) ≤ 2*(K.edgeFinset.card : ℝ) := by exact_mod_cast hhalf
  simp only [edgeFinset_card,Fintype.card_eq_nat_card] at hhalf' ⊢
  simp only [Nat.card_fin]
  linarith

/-- For exponents at least one, the rooted upper-bound problem is exactly an
ordinary upper-bound problem for two copies glued at adjacent roots. -/
lemma opposite_wedge_upper_iff {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hNoIso : ∀ v, ∃ w, H.Adj v w) {x y : W} (hxy : H.Adj x y)
    {r : ℝ} (hr : 1 ≤ r) :
    ((fun n : ℕ => (extremalNumber n (wedge H x H y) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^r)) ↔ RootPowerBound H x r := by
  constructor
  · exact of_opposite_wedge_upper H hxy (by linarith)
  · intro h
    simpa only [max_self] using wedge_upper H x hNoIso H y ⟨x,hxy.symm⟩ hr h h.upper h.upper

/-- An attained threshold for the rooted problem, not necessarily equal to
an ordinary threshold for H. -/
structure HasRootRate {W : Type*} (H : SimpleGraph W) (x : W) (r : ℝ) : Prop where
  one_le : 1 ≤ r
  upper : RootPowerBound H x r
  lower : ∀ a : ℝ, 1 ≤ a → RootPowerBound H x a → r ≤ a

lemma HasRootRate.of_reachable {W : Type*} {H : SimpleGraph W} {x y : W} {r : ℝ}
    (h : HasRootRate H x r) (hxy : H.Reachable x y) : HasRootRate H y r :=
  ⟨h.one_le,h.upper.of_reachable hxy,
    fun a ha hu => h.lower a ha (hu.of_reachable hxy.symm)⟩

lemma opposite_wedge_rate_iff {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hNoIso : ∀ v, ∃ w, H.Adj v w) {x y : W} (hxy : H.Adj x y) {r : ℝ} :
    HasRate (wedge H x H y) r ↔ HasRootRate H x r := by
  constructor
  · intro h
    refine ⟨h.one_le,(opposite_wedge_upper_iff H hNoIso hxy h.one_le).mp h.upper,?_⟩
    intro a ha hu
    exact h.lower a ha ((opposite_wedge_upper_iff H hNoIso hxy ha).mpr hu)
  · intro h
    refine ⟨h.one_le,(opposite_wedge_upper_iff H hNoIso hxy h.one_le).mpr h.upper,?_⟩
    intro a ha hu
    exact h.lower a ha ((opposite_wedge_upper_iff H hNoIso hxy ha).mp hu)

#print axioms RootPowerBound.of_reachable
#print axioms opposite_wedge_free
#print axioms of_opposite_wedge_upper
#print axioms RootPowerBound.upper
#print axioms opposite_wedge_upper_iff
#print axioms opposite_wedge_rate_iff
end Erdos713RootPower

namespace Erdos713ActualBlocks
open Erdos713Rate Erdos713RootPower Erdos713Gluing

/-- For a connected graph, one attachment root suffices. -/
lemma RootedRate.of_one_root {W : Type*} {G : SimpleGraph W} (hG : G.Connected)
    (x : W) {r : ℚ} (hr : HasRate G (r : ℝ)) (hroot : RootPowerBound G x (r : ℝ)) :
    RootedRate G :=
  ⟨r,hr,fun y => hroot.of_reachable (hG x y)⟩

/-- Matching rooted data can equivalently be checked by an ordinary upper
bound for the opposite-root double of the block. -/
lemma rootedRate_iff_opposite_wedge {W : Type*} [Fintype W] (G : SimpleGraph W)
    (hG : G.Connected) (hNoIso : ∀ v, ∃ w, G.Adj v w) {x y : W} (hxy : G.Adj x y) :
    RootedRate G ↔ ∃ r : ℚ, HasRate G (r : ℝ) ∧
      (fun n : ℕ => (extremalNumber n (wedge G x G y) : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ)^(r : ℝ)) := by
  constructor
  · rintro ⟨r,hr,hroot⟩
    exact ⟨r,hr,(opposite_wedge_upper_iff G hNoIso hxy hr.one_le).mpr (hroot x)⟩
  · rintro ⟨r,hr,hu⟩
    exact RootedRate.of_one_root hG x hr
      ((opposite_wedge_upper_iff G hNoIso hxy hr.one_le).mp hu)

lemma unmatched_opposite_wedge {W : Type*} [Fintype W] {G : SimpleGraph W}
    (hG : G.Connected) (hNoIso : ∀ v, ∃ w, G.Adj v w) (h : ¬ RootedRate G)
    {x y : W} (hxy : G.Adj x y) {r : ℚ} (hr : HasRate G (r : ℝ)) :
    ¬ (fun n : ℕ => (extremalNumber n (wedge G x G y) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^(r : ℝ)) :=
  fun hu => h ((rootedRate_iff_opposite_wedge G hG hNoIso hxy).mpr ⟨r,hr,hu⟩)

#print axioms RootedRate.of_one_root
#print axioms rootedRate_iff_opposite_wedge
#print axioms unmatched_opposite_wedge
end Erdos713ActualBlocks
