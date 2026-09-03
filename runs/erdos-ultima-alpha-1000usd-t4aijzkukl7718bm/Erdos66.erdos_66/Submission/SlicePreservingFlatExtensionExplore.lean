import Submission.FixedFirstSharedSelectionExplore
import Submission.AnchoredProductRepairExplore
import Submission.SharedParameterFlatSetExplore

/-! A genuine slice-preserving finite extension of one prescribed repaired
parabola template. Its mean stays h². This is not a growing-mean or integer
prefix extension theorem. -/
namespace Erdos66SlicePreservingFlatExtension
open Erdos66OriginRepair Erdos66ParabolaRepair Erdos66SharedParameterSet
  Erdos66AnchoredProductRepair Erdos66FixedFirstSharedSelection
  Erdos66SharedParameterKernel Erdos66SharedParameterRoot
  Erdos66SharedParameterFlatSet Erdos66PolynomialMixedEnergy
open scoped Classical
set_option maxHeartbeats 1500000

/-- Hold the entire old template, including its repair, fixed while extending
it to a second field plane. Membership and pair counts on the old slice are
exact, and all product-group counts have the same h² main term. -/
theorem exists_slice_preserving_flat_extension (p q h : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hh : 0<h) (hp : p ≠ 2) (hhp : h≤p) (hq : 4*h<q) (a : ZMod p)
    (ha : ∀ i<h, a+(i : ZMod p) ≠ 0)
    (haa : ∀ i<h, ∀ j<h, (a+(i : ZMod p))+(a+(j : ZMod p)) ≠ 0)
    (hE : labelEnergy h (fun i ↦ (quadraticChar (ZMod p) (a+i) : ℝ)) ≤ 24*(h : ℝ)^2)
    (w : ZMod p) (hw : w ≠ 0)
    (hwU : w∉(Finset.range h).image (fun i : ℕ ↦ a+(i : ZMod p)))
    (hnwU : -w∉(Finset.range h).image (fun i : ℕ ↦ a+(i : ZMod p)))
    (T : Finset (ZMod p)) (hT : (0 : ZMod p)∉T) (hTc : T.card=h^2/2) :
    let B := parabolaSet ((Finset.range h).image (fun i : ℕ ↦ a+(i : ZMod p))) ∪ repairPoints w T
    ∃ A : Finset ((ZMod p × ZMod p) × (ZMod q × ZMod q)),
      (∀ x, (x,0)∈A ↔ x∈B) ∧
      (∀ x, pairCount A A (x,0)=pairCount B B x) ∧
      ∀ z, ((pairCount A A z : ℝ)-(h : ℝ)^2)^2 ≤ 1512*(h : ℝ)^3 := by
  let u : ℕ → ZMod p := fun i ↦ a+i
  let U := (Finset.range h).image u
  let D := repairPoints w T
  have hF : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp
  have hU : ∀ x∈U, x ≠ 0 := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact ha i (Finset.mem_range.mp hi)
  have hUU : ∀ x∈U, ∀ y∈U, x+y ≠ 0 := by
    intro x hx y hy
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
    exact haa i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
  have hUne : U.Nonempty := ⟨u 0,Finset.mem_image.mpr ⟨0,Finset.mem_range.mpr hh,rfl⟩⟩
  have hdis : Disjoint (parabolaSet U) D := repairPoints_disjoint U hU w hw hwU hnwU T hT
  obtain ⟨b,hb,hbb,hroot⟩ := exists_fixed_first_root_flat p q h hh hp hq a ha haa 24 (by norm_num) hE
  let v : ℕ → ZMod q := fun i ↦ b+i
  let A := anchoredSet h u v D
  have hiu : Set.InjOn u (Finset.range h) := by
    intro i hi j hj he
    exact natCast_injOn_range p h hhp hi hj (add_left_cancel he)
  have hiv : Set.InjOn v (Finset.range h) := by
    intro i hi j hj he
    exact natCast_injOn_range q h (by omega) hi hj (add_left_cancel he)
  have hslice : ∀ x, pairCount A A (x,0)=pairCount (parabolaSet U ∪ D) (parabolaSet U ∪ D) x :=
    anchoredSet_preserves_counts h u v D hb hbb
  refine ⟨A,anchoredSet_slice h u v D,hslice,fun z ↦ ?_⟩
  by_cases hz : z=0
  · subst z
    change ((pairCount A A (0,0) : ℝ)-(h : ℝ)^2)^2 ≤ _
    rw [hslice]
    have he := (parabola_origin_repair hF U hU hUU hUne w hw hwU hnwU T hT).1
    change pairCount (parabolaSet U ∪ D) (parabolaSet U ∪ D) 0=1+2*T.card at he
    rw [he,hTc]
    have hdiv := Nat.mod_add_div (h^2) 2
    have hmod := Nat.mod_lt (h^2) (by decide : 0<2)
    have hm : 1+2*(h^2/2)=h^2 ∨ 1+2*(h^2/2)=h^2+1 := by omega
    have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
    have hpow : (1 : ℝ) ≤ (h : ℝ)^3 := one_le_pow₀ hhR
    rcases hm with hm | hm
    · rw [hm]; push_cast; nlinarith
    · rw [hm]; push_cast; nlinarith
  · obtain ⟨hlo,hhi⟩ := anchored_repair_bound h u v hF ha w hw D hdis
      (repairPoints_symmetric w T) (repairPoints_subset w T) z hz
    have hr : (sharedRootCount h u v z.1.1 z.1.2 z.2.1 z.2.2-(h : ℝ)^2)^2 ≤ 432*(h : ℝ)^3 := by
      simpa only [show (18 : ℝ)*24=432 by norm_num] using hroot z.1.1 z.1.2 z.2.1 z.2.2
    have herr := sharedSet_nonzero_error h hh u v ha hb hiu hiv z hz
    apply total_error_sq h (sharedRootCount h u v z.1.1 z.1.2 z.2.1 z.2.2)
      (pairCount (sharedSet h u v) (sharedSet h u v) z) (pairCount A A z)
      (by exact_mod_cast hh) hr herr
    · exact_mod_cast hlo
    · exact_mod_cast hhi

end Erdos66SlicePreservingFlatExtension
