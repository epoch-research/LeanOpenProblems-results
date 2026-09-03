import FormalConjecturesUtil
import Submission.CompactEdgeAttachmentsAudit
import Submission.SplitRootParity

/-! A self-copy reversing a bipartite color class converts ordinary power
bounds to rooted ones. Adjacency between a root and its image is unnecessary.
This is a symmetry criterion, not an assertion for arbitrary bipartite graphs. -/
open SimpleGraph Filter Asymptotics
namespace Erdos713RootColorReversal
open Erdos713RootPower Erdos713Rate Erdos713RootBlocks Erdos713Blocks
open Erdos713SplitRootParity
variable {W V : Type*}
set_option maxHeartbeats 2000000

/-- A bipartition with complementary shores gives its specified two-coloring. -/
noncomputable def shoreColoring (G : SimpleGraph V) (S : Set V)
    (hB : G.IsBipartiteWith S Sᶜ) : G.Coloring (Fin 2) := by
  classical
  refine ⟨fun v => if v ∈ S then 0 else 1,?_⟩
  intro v w hvw
  rcases hB.mem_of_adj hvw with ⟨hv,hw⟩ | ⟨hv,hw⟩
  · simp only [Set.mem_compl_iff] at hw
    simp [hv,hw]
  · simp only [Set.mem_compl_iff] at hv
    simp [hv,hw]

/-- Opposite source colors stay opposite under a copy, whenever the two
vertices lie in one connected component. -/
lemma copy_opposite_shores {H : SimpleGraph W} (χ : H.Coloring (Fin 2))
    {x y : W} (hp : H.Reachable x y) (hxy : χ x ≠ χ y)
    {G : SimpleGraph V} (S : Set V) (hB : G.IsBipartiteWith S Sᶜ)
    (f : H.Copy G) (hx : f x ∉ S) : f y ∈ S := by
  classical
  by_contra hy
  let ψ := shoreColoring G S hB
  have he : (ψ.comp f.toHom) x = (ψ.comp f.toHom) y := by
    change ψ (f x) = ψ (f y)
    simp [ψ,shoreColoring,hx,hy]
  exact hxy ((coloring_eq_of_reachable χ (ψ.comp f.toHom) hp).mpr he)

/-- It suffices that a self-copy reverses a root's color, not that it maps
that root to an adjacent vertex. No ordinary exponent is supplied here. -/
theorem rooted_of_upper {H : SimpleGraph W} (χ : H.Coloring (Fin 2))
    (x : W) (e : H.Copy H) (hp : H.Reachable x (e x)) (hflip : χ x ≠ χ (e x))
    {r : ℝ} (hr : 0 ≤ r)
    (hu : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^r)) : RootPowerBound H x r := by
  obtain ⟨C,hC,hbound⟩ := global_free_bound_of_upper H hr hu
  refine ⟨C,hC,?_⟩
  intro n G S hB hroot
  apply hbound n G
  rintro ⟨f⟩
  exact hroot (f.comp e) (copy_opposite_shores χ hp hflip S hB f (hroot f))

/-- For connected H, a single color-reversing self-copy gives the rooted
bound at every designated root, at the SAME supplied ordinary exponent. -/
theorem all_roots_of_upper {H : SimpleGraph W} (hH : H.Connected)
    (χ : H.Coloring (Fin 2)) (x : W) (e : H.Copy H) (hflip : χ x ≠ χ (e x))
    {r : ℝ} (hr : 0 ≤ r)
    (hu : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^r)) : ∀ y, RootPowerBound H y r := by
  intro y
  exact (rooted_of_upper χ x e (hH x (e x)) hflip hr hu).of_reachable (hH x y)

/-- A rational ordinary rate becomes matched rooted data under this explicit
symmetry criterion. Rationality of the ordinary rate is still an assumption. -/
theorem rootedRate_of_color_flip {H : SimpleGraph W} (hH : H.Connected)
    (χ : H.Coloring (Fin 2)) (x : W) (e : H.Copy H) (hflip : χ x ≠ χ (e x))
    {r : ℚ} (hr : HasRate H (r : ℝ)) : Erdos713ActualBlocks.RootedRate H := by
  exact ⟨r,hr,all_roots_of_upper hH χ x e hflip (by linarith [hr.one_le]) hr.upper⟩

/-- A strict ordinary/rooted exponent separation forces every self-copy to
preserve colors at every vertex. It does not prove such gaps impossible. -/
theorem selfcopy_preserves_colors_of_gap {H : SimpleGraph W} (hH : H.Connected)
    (χ : H.Coloring (Fin 2)) {r a : ℝ} (ha : 1 ≤ a) (har : a < r)
    (hu : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^a)) (hLower : ∀ x, RootLower H x r)
    (e : H.Copy H) (x : W) : χ (e x) = χ x := by
  by_contra hh
  have hb := rooted_of_upper χ x e (hH x (e x)) (Ne.symm hh) (by linarith) hu
  exact (not_lt_of_ge (hLower x a ha hb)) har

/-- Ordinary attained-rate localization when every cyclic block has a
color-reversing self-copy. No rationality of those rates is inferred. -/
theorem exists_block_ordinary_rate_of_color_flips [Fintype W] (G : SimpleGraph W)
    (hG : G.Connected) {r : ℝ} (hr : 1 < r) (hR : HasRate G r)
    (hFlip : ∀ S : Set W, IsBlock G S → 3 ≤ Nat.card S →
      ∃ (χ : (G.induce S).Coloring (Fin 2)) (x : S) (e : (G.induce S).Copy (G.induce S)),
        χ x ≠ χ (e x)) :
    ∃ S : Set W, IsBlock G S ∧ 3 ≤ Nat.card S ∧ HasRate (G.induce S) r := by
  obtain ⟨S,hS,hc,hLower,hAlt⟩ := ordinary_block_or_strict_root_gap G hG hr hR
  refine ⟨S,hS,hc,?_⟩
  rcases hAlt with hRate | ⟨a,ha,har,hu⟩
  · exact hRate
  · obtain ⟨χ,x,e,hflip⟩ := hFlip S hS hc
    exact (hflip (selfcopy_preserves_colors_of_gap hS.connected χ ha har hu hLower e x).symm).elim

#print axioms rooted_of_upper
#print axioms rootedRate_of_color_flip
#print axioms selfcopy_preserves_colors_of_gap
#print axioms exists_block_ordinary_rate_of_color_flips
end Erdos713RootColorReversal
