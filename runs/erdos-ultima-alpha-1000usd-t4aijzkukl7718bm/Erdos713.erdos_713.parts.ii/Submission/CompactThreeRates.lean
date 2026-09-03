import FormalConjecturesUtil
import Submission.CompactRate

/-! Attained rational growth thresholds for bipartite graphs with a colour
class of size at most three. No pure-power asymptotic is assumed. -/
open SimpleGraph Filter Asymptotics
namespace Erdos713ThreeSide
open Erdos713C6 Erdos713Rate
universe u

theorem rate_matrix_core {B : Type*} [Fintype B] (R : Fin 3 → B → Prop)
    (hd : ∀ v, 2 ≤ Nat.card ((bipGraph R).neighborSet v)) :
    ∃ r : ℚ, HasRate (bipGraph R) (r : ℝ) := by
  classical
  by_cases hFull : 3 ≤ Nat.card {b // ∀ i, R i b}
  · refine ⟨5/3, ?_⟩
    simpa using k3t_rate (contains_K33_of_three_full_columns R hFull) (matrix_contained_K3t R)
  by_cases hC4 : Erdos713C4.K22 ⊑ bipGraph R
  · refine ⟨3/2, ?_⟩
    simpa using two_exception_columns_rate R {b | ∀ i, R i b}
      (by change Nat.card {b // ∀ i, R i b} ≤ 2; omega)
      (fun b hb => nonfull_column_small R b hb) hC4 (.refl _)
  obtain ⟨e⟩ := matrix_iso_C6_of_no_rectangle R hd hC4
  refine ⟨4/3, ?_⟩
  simpa using c6_rate ⟨e.symm.toCopy⟩ ⟨e.toCopy⟩

theorem rate_core_of_small_bipartition {W : Type*} [Fintype W] [Nonempty W]
    (H : SimpleGraph W) (S : Set W) (hB : H.IsBipartiteWith S Sᶜ) (hS : Nat.card S ≤ 3)
    (hd : ∀ v, 2 ≤ Nat.card (H.neighborSet v)) : ∃ r : ℚ, HasRate H (r : ℝ) := by
  classical
  by_cases hS2 : Nat.card S ≤ 2
  · have hhi := Erdos713SmallCore.contained_of_small_bipartition H S hS2 hB
    have hd' : ∀ v, 2 ≤ H.degree v := by
      intro v
      simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hd v
    have hlo := Erdos713SmallCore.contains_K22_of_degree_two H hd' hhi
    refine ⟨3/2, ?_⟩
    simpa using k2t_rate hlo hhi
  obtain ⟨R,⟨e⟩⟩ := exists_matrix_iso H S hB (by omega)
  have hDeg : ∀ v, 2 ≤ Nat.card ((bipGraph R).neighborSet v) := by
    intro v
    rw [Nat.card_congr (e.symm.mapNeighborSet v)]
    exact hd (e.symm v)
  obtain ⟨r,hr⟩ := rate_matrix_core R hDeg
  exact ⟨r,iso_rate e hr⟩

theorem rate_of_small_bipartition {W : Type u} [Fintype W]
    (H : SimpleGraph W) (S : Set W) (hB : H.IsBipartiteWith S Sᶜ) (hS : Nat.card S ≤ 3) :
    ∃ r : ℚ, HasRate H (r : ℝ) := by
  classical
  suffices hP : ∀ k : ℕ, ∀ (W : Type u) [Fintype W], Fintype.card W = k →
      ∀ (G : SimpleGraph W) (S : Set W), G.IsBipartiteWith S Sᶜ → Nat.card S ≤ 3 →
        ∃ r : ℚ, HasRate G (r : ℝ) from hP _ W rfl H S hB hS
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro W _ hW G S hB hS
    by_cases hne : Nonempty W
    swap
    · letI : IsEmpty W := not_nonempty_iff.mp hne
      exact ⟨1, by simpa using forest_rate G (by intro v; exact isEmptyElim v)⟩
    letI := hne
    by_cases hd : ∀ v, 2 ≤ Nat.card (G.neighborSet v)
    · exact rate_core_of_small_bipartition G S hB hS hd
    push_neg at hd
    obtain ⟨x,hx⟩ := hd
    have hx' : G.degree x < 2 := by
      simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hx
    have hsmall : Fintype.card ↥({x}ᶜ : Set W) < k :=
      (Fintype.card_subtype_lt (x := x) (by simp)).trans_eq hW
    let T : Set ↥({x}ᶜ : Set W) := {v | v.val ∈ S}
    have hB' : (G.induce {x}ᶜ).IsBipartiteWith T Tᶜ := by
      refine ⟨disjoint_compl_right, ?_⟩
      intro u v huv
      exact hB.2 huv
    have hT : Nat.card T ≤ 3 := by
      let f : T ↪ S := ⟨fun v => ⟨v.val.val,v.prop⟩, by
        intro u v huv
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : S => z.val) huv⟩
      have hh := Fintype.card_le_of_embedding f
      simp only [Fintype.card_eq_nat_card] at hh
      exact hh.trans hS
    obtain ⟨r,hr⟩ := ih _ hsmall _ rfl (G.induce {x}ᶜ) T hB' hT
    refine ⟨r, ?_⟩
    have hx01 : G.degree x = 0 ∨ G.degree x = 1 := by omega
    rcases hx01 with hx0 | hx1
    · exact isolated_rate G hx0 hr
    · obtain ⟨y,hxy,_⟩ := degree_eq_one_iff_existsUnique_adj.mp hx1
      exact leaf_rate G hx1 hxy hr

theorem small_bipartition_of_card_le_seven {W : Type*} [Fintype W]
    (H : SimpleGraph W) (hB : H.IsBipartite) (hcard : Fintype.card W ≤ 7) :
    ∃ S : Set W, H.IsBipartiteWith S Sᶜ ∧ Nat.card S ≤ 3 := by
  classical
  obtain ⟨χ⟩ := hB
  let S : Set W := {v | χ v = 0}
  have hS : H.IsBipartiteWith S Sᶜ := by
    refine ⟨disjoint_compl_right, ?_⟩
    intro u v huv
    have hχ := χ.valid huv
    simp only [S,Set.mem_setOf_eq,Set.mem_compl_iff]
    omega
  by_cases hcS : Nat.card S ≤ 3
  · exact ⟨S,hS,hcS⟩
  have hcomp : Nat.card ↥(Sᶜ) = Fintype.card W - Nat.card S := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_compl_set]
  exact ⟨Sᶜ,by simpa only [compl_compl] using hS.symm,by omega⟩

theorem rate_of_card_le_seven {W : Type*} [Fintype W]
    (H : SimpleGraph W) (hB : H.IsBipartite) (hcard : Fintype.card W ≤ 7) :
    ∃ r : ℚ, HasRate H (r : ℝ) := by
  obtain ⟨S,hS,hcard⟩ := small_bipartition_of_card_le_seven H hB hcard
  exact rate_of_small_bipartition H S hS hcard

#print axioms rate_of_small_bipartition
#print axioms rate_of_card_le_seven
end Erdos713ThreeSide
