import Submission.ButterflyContiguous

/-! Replacing one path interval by a path whose old vertices stay within that interval. -/
namespace Erdos583PathIntervalReplacementDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.PathIntervals
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma replace_interval_isPath {V : Type*} {G : SimpleGraph V} {a b : V}
    (P : G.Walk a b) (hP : P.IsPath) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ P.length)
    (R : G.Walk (P.getVert i) (P.getVert j)) (hR : R.IsPath)
    (hRold : ∀ x ∈ R.support, x ∈ P.support → x ∈ (interval P i j hij).support) :
    ((P.take i).append (R.append (P.drop j))).IsPath := by
  have hi : i ≤ P.length := hij.trans hj
  have hL : (P.take i).IsPath := by
    have hh : ((P.take i).append (P.drop i)).IsPath := by simpa using hP
    exact hh.of_append_left
  have hD : (P.drop j).IsPath := by
    have hh : ((P.take j).append (P.drop j)).IsPath := by simpa using hP
    exact hh.of_append_right
  have hRD : (R.append (P.drop j)).IsPath := by
    apply path_append_of_support_intersection hR hD
    intro x hxR hxD
    obtain ⟨l,hjl,hl,hxl⟩ := (drop_support P hj x).mp hxD
    have hxP : x ∈ P.support := hxl.symm ▸ P.getVert_mem_support l
    obtain ⟨m,him,hmj,hxm⟩ := (interval_support P hij hj x).mp (hRold x hxR hxP)
    have hml : m=l := hP.getVert_injOn (show m ≤ P.length by omega) hl (hxm.symm.trans hxl)
    have hlj : l=j := by omega
    exact hlj ▸ hxl
  apply path_append_of_support_intersection hL hRD
  intro x hxL hxRD
  obtain ⟨l,hli,hxl⟩ := (take_support P hi x).mp hxL
  have hxP : x ∈ P.support := hxl.symm ▸ P.getVert_mem_support l
  rcases (Walk.mem_support_append_iff R (P.drop j)).mp hxRD with hxR | hxD
  · obtain ⟨m,him,hmj,hxm⟩ := (interval_support P hij hj x).mp (hRold x hxR hxP)
    have hlm : l=m := hP.getVert_injOn (show l ≤ P.length by omega)
      (show m ≤ P.length by omega) (hxl.symm.trans hxm)
    have hli' : l=i := by omega
    exact hli' ▸ hxl
  · obtain ⟨m,hjm,hm,hxm⟩ := (drop_support P hj x).mp hxD
    have hlm : l=m := hP.getVert_injOn (show l ≤ P.length by omega) hm (hxl.symm.trans hxm)
    have hli' : l=i := by omega
    exact hli' ▸ hxl

end Erdos583PathIntervalReplacementDevelopment
