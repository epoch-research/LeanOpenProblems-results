import FormalConjecturesUtil
import Submission.Verified
import Submission.GeneralFan

/-! A minimal finite graph carrying a prescribed superlinear attained rate. -/

open Filter SimpleGraph Asymptotics

namespace Erdos713Rate
universe u

theorem exists_minimal_connected_core {W : Type u} [Fintype W] (G : SimpleGraph W)
    {r : ℝ} (hr : 1 < r) (h : HasRate G r) :
    ∃ (U : Type u) (_ : Fintype U) (H : SimpleGraph U), H ⊑ G ∧ H.Connected ∧
      (∀ v, 2 ≤ Nat.card (H.neighborSet v)) ∧ HasRate H r ∧ Fintype.card U ≤ Fintype.card W ∧
      (∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H → HasRate J r →
        Fintype.card U ≤ Fintype.card T) := by
  classical
  let P : ℕ → Prop := fun n => ∃ (U : Type u) (_ : Fintype U) (H : SimpleGraph U),
    H ⊑ G ∧ HasRate H r ∧ Fintype.card U = n
  have hP : ∃ n, P n := ⟨Fintype.card W, W, inferInstance, G, .refl _, h, rfl⟩
  obtain ⟨U, instU, H, hHG, hHR, hcard⟩ := Nat.find_spec hP
  obtain ⟨T, instT, J, hJH, hJC, hJD, hJR, hTcard⟩ := exists_connected_core H hr hHR
  have hMin (S : Type u) [Fintype S] (F : SimpleGraph S) (hFG : F ⊑ G) (hFR : HasRate F r) :
      Fintype.card U ≤ Fintype.card S := by
    rw [hcard]
    exact Nat.find_min' hP ⟨S, inferInstance, F, hFG, hFR, rfl⟩
  have hEq : Fintype.card T = Fintype.card U :=
    le_antisymm hTcard (hMin T J (hJH.trans hHG) hJR)
  refine ⟨T, instT, J, hJH.trans hHG, hJC, hJD, hJR, ?_, ?_⟩
  · exact hTcard.trans (hMin W G (.refl _) h)
  · intro S _ F hFJ hFR
    rw [hEq]
    exact hMin S F (hFJ.trans (hJH.trans hHG)) hFR

theorem minimal_fan_sandwich_card {U W : Type u} [Fintype U] [Fintype W]
    (H : SimpleGraph U) {r : ℝ} (h : HasRate H r)
    (hMin : ∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H → HasRate J r →
      Fintype.card U ≤ Fintype.card T)
    (J : SimpleGraph W) (x : W) (t : ℕ) (hlo : J ⊑ H) (hhi : H ⊑ Erdos713Fan.fan J x t) :
    Fintype.card U ≤ Fintype.card W :=
  hMin W J hlo (Erdos713Fan.rate_of_sandwich_converse J x t hlo hhi h)

#print axioms exists_minimal_connected_core
#print axioms minimal_fan_sandwich_card

end Erdos713Rate
