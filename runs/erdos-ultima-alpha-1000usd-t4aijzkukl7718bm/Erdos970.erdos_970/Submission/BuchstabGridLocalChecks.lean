import Submission.BuchstabGridData

/-! Small kernel checks of all local integer recurrences. Splitting the finite
check keeps kernel reduction within the memory budget. -/
namespace Erdos970.BuchstabGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def localChecks (j : ℕ) : Prop :=
  (scale ≤ (baseNodes (j)) ∧ (lowerNodes (j)) ≤ scale ∧
    scale ≤ (upperNodes (j)) ∧ (upperNodes (j)) ≤ (baseNodes (j))) ∧
  (j < 600 → mesh*(initialIntegral (j+1))+(baseNodes (j)) ≤ mesh*(initialIntegral (j))+scale) ∧
  ((lowerNodes (j)) = 0 ∨ (108 ≤ j ∧ mesh*(initialIntegral (j-mesh))+((lowerNodes (j))+10)*j ≤ scale*j)) ∧
  (j < 600 → mesh*(lowerDeficitIntegral (j+1))+scale ≤ mesh*(lowerDeficitIntegral (j))+(lowerNodes (j))) ∧
  (mesh ≤ j → (upperNodes (j)) = (baseNodes (j)) ∨
    mesh*(lowerDeficitIntegral (j-mesh))+(scale+10)*j ≤ (upperNodes (j))*j) ∧
  (j < 600 → mesh*(refinedIntegral (j+1))+(upperNodes (j)) ≤ mesh*(refinedIntegral (j))+scale)

instance (j : ℕ) : Decidable (localChecks j) := by unfold localChecks; infer_instance

private lemma block_0 : ∀ j : Fin 10, 0+j.val < 601 → localChecks (0+j.val) := by decide +kernel

private lemma block_1 : ∀ j : Fin 10, 10+j.val < 601 → localChecks (10+j.val) := by decide +kernel

private lemma block_2 : ∀ j : Fin 10, 20+j.val < 601 → localChecks (20+j.val) := by decide +kernel

private lemma block_3 : ∀ j : Fin 10, 30+j.val < 601 → localChecks (30+j.val) := by decide +kernel

private lemma block_4 : ∀ j : Fin 10, 40+j.val < 601 → localChecks (40+j.val) := by decide +kernel

private lemma block_5 : ∀ j : Fin 10, 50+j.val < 601 → localChecks (50+j.val) := by decide +kernel

private lemma block_6 : ∀ j : Fin 10, 60+j.val < 601 → localChecks (60+j.val) := by decide +kernel

private lemma block_7 : ∀ j : Fin 10, 70+j.val < 601 → localChecks (70+j.val) := by decide +kernel

private lemma block_8 : ∀ j : Fin 10, 80+j.val < 601 → localChecks (80+j.val) := by decide +kernel

private lemma block_9 : ∀ j : Fin 10, 90+j.val < 601 → localChecks (90+j.val) := by decide +kernel

private lemma block_10 : ∀ j : Fin 10, 100+j.val < 601 → localChecks (100+j.val) := by decide +kernel

private lemma block_11 : ∀ j : Fin 10, 110+j.val < 601 → localChecks (110+j.val) := by decide +kernel

private lemma block_12 : ∀ j : Fin 10, 120+j.val < 601 → localChecks (120+j.val) := by decide +kernel

private lemma block_13 : ∀ j : Fin 10, 130+j.val < 601 → localChecks (130+j.val) := by decide +kernel

private lemma block_14 : ∀ j : Fin 10, 140+j.val < 601 → localChecks (140+j.val) := by decide +kernel

private lemma block_15 : ∀ j : Fin 10, 150+j.val < 601 → localChecks (150+j.val) := by decide +kernel

private lemma block_16 : ∀ j : Fin 10, 160+j.val < 601 → localChecks (160+j.val) := by decide +kernel

private lemma block_17 : ∀ j : Fin 10, 170+j.val < 601 → localChecks (170+j.val) := by decide +kernel

private lemma block_18 : ∀ j : Fin 10, 180+j.val < 601 → localChecks (180+j.val) := by decide +kernel

private lemma block_19 : ∀ j : Fin 10, 190+j.val < 601 → localChecks (190+j.val) := by decide +kernel

private lemma block_20 : ∀ j : Fin 10, 200+j.val < 601 → localChecks (200+j.val) := by decide +kernel

private lemma block_21 : ∀ j : Fin 10, 210+j.val < 601 → localChecks (210+j.val) := by decide +kernel

private lemma block_22 : ∀ j : Fin 10, 220+j.val < 601 → localChecks (220+j.val) := by decide +kernel

private lemma block_23 : ∀ j : Fin 10, 230+j.val < 601 → localChecks (230+j.val) := by decide +kernel

private lemma block_24 : ∀ j : Fin 10, 240+j.val < 601 → localChecks (240+j.val) := by decide +kernel

private lemma block_25 : ∀ j : Fin 10, 250+j.val < 601 → localChecks (250+j.val) := by decide +kernel

private lemma block_26 : ∀ j : Fin 10, 260+j.val < 601 → localChecks (260+j.val) := by decide +kernel

private lemma block_27 : ∀ j : Fin 10, 270+j.val < 601 → localChecks (270+j.val) := by decide +kernel

private lemma block_28 : ∀ j : Fin 10, 280+j.val < 601 → localChecks (280+j.val) := by decide +kernel

private lemma block_29 : ∀ j : Fin 10, 290+j.val < 601 → localChecks (290+j.val) := by decide +kernel

private lemma block_30 : ∀ j : Fin 10, 300+j.val < 601 → localChecks (300+j.val) := by decide +kernel

private lemma block_31 : ∀ j : Fin 10, 310+j.val < 601 → localChecks (310+j.val) := by decide +kernel

private lemma block_32 : ∀ j : Fin 10, 320+j.val < 601 → localChecks (320+j.val) := by decide +kernel

private lemma block_33 : ∀ j : Fin 10, 330+j.val < 601 → localChecks (330+j.val) := by decide +kernel

private lemma block_34 : ∀ j : Fin 10, 340+j.val < 601 → localChecks (340+j.val) := by decide +kernel

private lemma block_35 : ∀ j : Fin 10, 350+j.val < 601 → localChecks (350+j.val) := by decide +kernel

private lemma block_36 : ∀ j : Fin 10, 360+j.val < 601 → localChecks (360+j.val) := by decide +kernel

private lemma block_37 : ∀ j : Fin 10, 370+j.val < 601 → localChecks (370+j.val) := by decide +kernel

private lemma block_38 : ∀ j : Fin 10, 380+j.val < 601 → localChecks (380+j.val) := by decide +kernel

private lemma block_39 : ∀ j : Fin 10, 390+j.val < 601 → localChecks (390+j.val) := by decide +kernel

private lemma block_40 : ∀ j : Fin 10, 400+j.val < 601 → localChecks (400+j.val) := by decide +kernel

private lemma block_41 : ∀ j : Fin 10, 410+j.val < 601 → localChecks (410+j.val) := by decide +kernel

private lemma block_42 : ∀ j : Fin 10, 420+j.val < 601 → localChecks (420+j.val) := by decide +kernel

private lemma block_43 : ∀ j : Fin 10, 430+j.val < 601 → localChecks (430+j.val) := by decide +kernel

private lemma block_44 : ∀ j : Fin 10, 440+j.val < 601 → localChecks (440+j.val) := by decide +kernel

private lemma block_45 : ∀ j : Fin 10, 450+j.val < 601 → localChecks (450+j.val) := by decide +kernel

private lemma block_46 : ∀ j : Fin 10, 460+j.val < 601 → localChecks (460+j.val) := by decide +kernel

private lemma block_47 : ∀ j : Fin 10, 470+j.val < 601 → localChecks (470+j.val) := by decide +kernel

private lemma block_48 : ∀ j : Fin 10, 480+j.val < 601 → localChecks (480+j.val) := by decide +kernel

private lemma block_49 : ∀ j : Fin 10, 490+j.val < 601 → localChecks (490+j.val) := by decide +kernel

private lemma block_50 : ∀ j : Fin 10, 500+j.val < 601 → localChecks (500+j.val) := by decide +kernel

private lemma block_51 : ∀ j : Fin 10, 510+j.val < 601 → localChecks (510+j.val) := by decide +kernel

private lemma block_52 : ∀ j : Fin 10, 520+j.val < 601 → localChecks (520+j.val) := by decide +kernel

private lemma block_53 : ∀ j : Fin 10, 530+j.val < 601 → localChecks (530+j.val) := by decide +kernel

private lemma block_54 : ∀ j : Fin 10, 540+j.val < 601 → localChecks (540+j.val) := by decide +kernel

private lemma block_55 : ∀ j : Fin 10, 550+j.val < 601 → localChecks (550+j.val) := by decide +kernel

private lemma block_56 : ∀ j : Fin 10, 560+j.val < 601 → localChecks (560+j.val) := by decide +kernel

private lemma block_57 : ∀ j : Fin 10, 570+j.val < 601 → localChecks (570+j.val) := by decide +kernel

private lemma block_58 : ∀ j : Fin 10, 580+j.val < 601 → localChecks (580+j.val) := by decide +kernel

private lemma block_59 : ∀ j : Fin 10, 590+j.val < 601 → localChecks (590+j.val) := by decide +kernel

private lemma block_60 : ∀ j : Fin 10, 600+j.val < 601 → localChecks (600+j.val) := by decide +kernel

private lemma all_blocks : ∀ b : Fin 61, ∀ j : Fin 10, 10*b.val+j.val < 601 → localChecks (10*b.val+j.val) := by
  intro b
  fin_cases b
  · exact block_0
  · exact block_1
  · exact block_2
  · exact block_3
  · exact block_4
  · exact block_5
  · exact block_6
  · exact block_7
  · exact block_8
  · exact block_9
  · exact block_10
  · exact block_11
  · exact block_12
  · exact block_13
  · exact block_14
  · exact block_15
  · exact block_16
  · exact block_17
  · exact block_18
  · exact block_19
  · exact block_20
  · exact block_21
  · exact block_22
  · exact block_23
  · exact block_24
  · exact block_25
  · exact block_26
  · exact block_27
  · exact block_28
  · exact block_29
  · exact block_30
  · exact block_31
  · exact block_32
  · exact block_33
  · exact block_34
  · exact block_35
  · exact block_36
  · exact block_37
  · exact block_38
  · exact block_39
  · exact block_40
  · exact block_41
  · exact block_42
  · exact block_43
  · exact block_44
  · exact block_45
  · exact block_46
  · exact block_47
  · exact block_48
  · exact block_49
  · exact block_50
  · exact block_51
  · exact block_52
  · exact block_53
  · exact block_54
  · exact block_55
  · exact block_56
  · exact block_57
  · exact block_58
  · exact block_59
  · exact block_60

lemma all_local_checks : ∀ j : Fin 601, localChecks j.val := by
  intro j
  have hj := j.isLt
  have hb : j.val/10 < 61 := by omega
  have hr : j.val%10 < 10 := Nat.mod_lt _ (by omega)
  have he : 10*(j.val/10)+j.val%10 = j.val := by omega
  have hh := all_blocks ⟨j.val/10,hb⟩ ⟨j.val%10,hr⟩
  dsimp only at hh
  rw [he] at hh
  exact hh hj

#print axioms all_local_checks
end Erdos970.BuchstabGrid
