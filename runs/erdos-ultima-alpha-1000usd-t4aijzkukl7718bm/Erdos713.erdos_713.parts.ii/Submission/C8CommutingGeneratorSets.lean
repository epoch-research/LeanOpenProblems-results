import FormalConjecturesUtil
import Submission.C8CommutingDifferences

/-! Commuting generator differences force a commutator octagon unless the
point quadrilateral degenerates. Auxiliary construction obstruction only. -/
open SimpleGraph Finset
namespace Erdos713C8CommutingGeneratorSets
open Erdos713C8CommutingDifferences
variable {G I : Type*} [Group G]
set_option maxHeartbeats 2000000

lemma four_generator_copy (g : I → G) (hg : Function.Injective g)
    (a b c d : I) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hc : Commute (g a*(g b)⁻¹) (g c*(g d)⁻¹))
    (hne : g a*(g b)⁻¹ ≠ g c*(g d)⁻¹)
    (hprod : (g a*(g b)⁻¹)*(g c*(g d)⁻¹) ≠ 1) :
    cycleGraph 8 ⊑ graph g := by
  let X := g a*(g b)⁻¹
  let Y := g c*(g d)⁻¹
  have hXb : X*g b = g a := by simp [X]
  have hYd : Y*g d = g c := by simp [Y]
  have hXYb : (X*Y)*g b = Y*g a := by rw [hc.eq,mul_assoc Y X (g b),hXb]
  have hXYd : (X*Y)*g d = X*g c := by rw [mul_assoc X Y (g d),hYd]
  have hX1 : X ≠ 1 := by
    intro h
    apply hab
    apply hg
    calc g a = X*g b := hXb.symm
         _ = g b := by rw [h,one_mul]
  have hY1 : Y ≠ 1 := by
    intro h
    apply hcd
    apply hg
    calc g c = Y*g d := hYd.symm
         _ = g d := by rw [h,one_mul]
  have hXxy : X ≠ X*Y := by
    intro h
    apply hY1
    apply mul_left_cancel (a := X)
    rw [← h,mul_one]
  have hYxy : Y ≠ X*Y := by
    intro h
    apply hX1
    apply mul_right_cancel (b := Y)
    rw [← h,one_mul]
  let p : Fin 4 → G := ![1,X,X*Y,Y]
  let l : Fin 4 → G := ![g a,X*g c,Y*g a,g c]
  have hp : Function.Injective p := by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | (
      dsimp [p] at h
      first | exact (hX1 h).elim | exact (hX1 h.symm).elim |
        exact (hY1 h).elim | exact (hY1 h.symm).elim |
        exact (hne h).elim | exact (hne h.symm).elim |
        exact (hprod h).elim | exact (hprod h.symm).elim |
        exact (hXxy h).elim | exact (hXxy h.symm).elim |
        exact (hYxy h).elim | exact (hYxy h.symm).elim)
  have h01 : g a ≠ X*g c := by
    intro h
    exact hbc (hg (mul_left_cancel (hXb.trans h)))
  have h02 : g a ≠ Y*g a := by
    intro h
    apply hY1
    apply mul_right_cancel (b := g a)
    rw [← h,one_mul]
  have h12 : X*g c ≠ Y*g a := by
    intro h
    have he : (X*Y)*g d = (X*Y)*g b := hXYd.trans (h.trans hXYb.symm)
    exact hbd (hg (mul_left_cancel he)).symm
  have h13 : X*g c ≠ g c := by
    intro h
    apply hX1
    apply mul_right_cancel (b := g c)
    rw [h,one_mul]
  have h23 : Y*g a ≠ g c := by
    intro h
    exact had (hg (mul_left_cancel (h.trans hYd.symm)))
  have h03 : g a ≠ g c := hg.ne hac
  have hl : Function.Injective l := by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | (
      dsimp [l] at h
      first | exact (h01 h).elim | exact (h01 h.symm).elim |
        exact (h02 h).elim | exact (h02 h.symm).elim |
        exact (h03 h).elim | exact (h03 h.symm).elim |
        exact (h12 h).elim | exact (h12 h.symm).elim |
        exact (h13 h).elim | exact (h13 h.symm).elim |
        exact (h23 h).elim | exact (h23 h.symm).elim)
  apply contains_of_octagon g p l hp hl
  · intro i
    fin_cases i
    · exact ⟨a,(one_mul _).symm⟩
    · exact ⟨c,rfl⟩
    · exact ⟨b,hXYb.symm⟩
    · exact ⟨d,hYd.symm⟩
  · intro i
    fin_cases i
    · exact ⟨b,hXb.symm⟩
    · exact ⟨d,hXYd.symm⟩
    · exact ⟨a,rfl⟩
    · exact ⟨c,(one_mul _).symm⟩

lemma difference_dichotomy (g : I → G) (hg : Function.Injective g)
    (hf : (cycleGraph 8).Free (graph g))
    (a b c d : I) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hc : Commute (g a*(g b)⁻¹) (g c*(g d)⁻¹)) :
    g c*(g d)⁻¹ = g a*(g b)⁻¹ ∨ g c*(g d)⁻¹ = (g a*(g b)⁻¹)⁻¹ := by
  by_contra! hn
  apply hf
  apply four_generator_copy g hg a b c d hab hac had hbc hbd hcd hc (Ne.symm hn.1)
  intro h
  apply hn.2
  calc
    g c*(g d)⁻¹ = (g a*(g b)⁻¹)⁻¹*((g a*(g b)⁻¹)*(g c*(g d)⁻¹)) := by group
    _ = (g a*(g b)⁻¹)⁻¹ := by rw [h,mul_one]

/-- If all differences formed from one finite generator set commute, C8
exclusion bounds that set's size. The bound five is deliberately coarse. -/
lemma card_le_five (g : I → G) (hg : Function.Injective g)
    (hf : (cycleGraph 8).Free (graph g)) (S : Finset I)
    (hc : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
      Commute (g a*(g b)⁻¹) (g c*(g d)⁻¹)) : S.card ≤ 5 := by
  classical
  by_cases hs : S.card ≤ 1
  · omega
  obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp (by omega : 1 < S.card)
  let T := S \ {a,b}
  have hsplit : S.card ≤ T.card+2 := by
    change S.card ≤ (S \ {a,b}).card+2
    have hh := card_sdiff_add_card_inter S ({a,b} : Finset I)
    have hi : (S ∩ {a,b}).card ≤ 2 := (card_le_card inter_subset_right).trans card_le_two
    omega
  by_cases hT : T.Nonempty
  · obtain ⟨c,hcT⟩ := hT
    have hcS : c ∈ S := (mem_sdiff.mp hcT).1
    have hcn : c ≠ a ∧ c ≠ b := by
      simpa only [mem_insert,mem_singleton,not_or] using (mem_sdiff.mp hcT).2
    have hca := hcn.1
    have hcb := hcn.2
    let X := g a*(g b)⁻¹
    let F : I → G := fun d => g c*(g d)⁻¹
    have hFi : Function.Injective F := by
      intro d e he
      exact hg (inv_injective (mul_left_cancel he))
    have hsub : T.image F ⊆ {1,X,X⁻¹} := by
      intro y hy
      obtain ⟨d,hdT,rfl⟩ := mem_image.mp hy
      have hdS : d ∈ S := (mem_sdiff.mp hdT).1
      have hn : d ≠ a ∧ d ≠ b := by
        simpa only [mem_insert,mem_singleton,not_or] using (mem_sdiff.mp hdT).2
      by_cases hcd : c = d
      · simp [F,hcd]
      · have h := difference_dichotomy g hg hf a b c d hab hca.symm hn.1.symm
          hcb.symm hn.2.symm hcd (hc a ha b hb c hcS d hdS)
        simpa only [mem_insert,mem_singleton,F,X] using (Or.inr h :
          g c*(g d)⁻¹ = 1 ∨ g c*(g d)⁻¹ = g a*(g b)⁻¹ ∨
            g c*(g d)⁻¹ = (g a*(g b)⁻¹)⁻¹)
    have htc : T.card ≤ 3 := by
      calc
        T.card = (T.image F).card := (card_image_of_injective _ hFi).symm
        _ ≤ ({1,X,X⁻¹} : Finset G).card := card_le_card hsub
        _ ≤ 3 := by simpa using List.toFinset_card_le ([1,X,X⁻¹] : List G)
    omega
  · have ht : T.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hT)
    omega

#print axioms four_generator_copy
#print axioms difference_dichotomy
#print axioms card_le_five
end Erdos713C8CommutingGeneratorSets
