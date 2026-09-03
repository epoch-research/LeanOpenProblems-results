import Submission.BuchstabFourGridData

/-! Kernel checks for the finite four-upper-refinement data. -/
namespace Erdos970.BuchstabFourGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def localChecks (r j : ℕ) : Prop :=
  (j < 600 → 50*upperIntegral r (j+1)+upperTable r j ≤ 50*upperIntegral r j+1000000) ∧
  (r < 3 →
    (lowerTable r j = 0 ∨ (100 ≤ j ∧ 50*upperIntegral r (j-50)+(lowerTable r j+10)*j ≤ 1000000*j)) ∧
    (j < 600 → 50*lowerIntegral r (j+1)+1000000 ≤ 50*lowerIntegral r j+lowerTable r j) ∧
    (50 ≤ j → upperTable (r+1) j = upperTable r j ∨
      50*lowerIntegral r (j-50)+(1000000+10)*j ≤ upperTable (r+1) j*j))
instance (r j : ℕ) : Decidable (localChecks r j) := by unfold localChecks; infer_instance

private lemma block_0 : ∀ r : Fin 4, ∀ j : Fin 10, 0+j.val < 601 → localChecks r.val (0+j.val) := by decide +kernel

private lemma block_1 : ∀ r : Fin 4, ∀ j : Fin 10, 10+j.val < 601 → localChecks r.val (10+j.val) := by decide +kernel

private lemma block_2 : ∀ r : Fin 4, ∀ j : Fin 10, 20+j.val < 601 → localChecks r.val (20+j.val) := by decide +kernel

private lemma block_3 : ∀ r : Fin 4, ∀ j : Fin 10, 30+j.val < 601 → localChecks r.val (30+j.val) := by decide +kernel

private lemma block_4 : ∀ r : Fin 4, ∀ j : Fin 10, 40+j.val < 601 → localChecks r.val (40+j.val) := by decide +kernel

private lemma block_5 : ∀ r : Fin 4, ∀ j : Fin 10, 50+j.val < 601 → localChecks r.val (50+j.val) := by decide +kernel

private lemma block_6 : ∀ r : Fin 4, ∀ j : Fin 10, 60+j.val < 601 → localChecks r.val (60+j.val) := by decide +kernel

private lemma block_7 : ∀ r : Fin 4, ∀ j : Fin 10, 70+j.val < 601 → localChecks r.val (70+j.val) := by decide +kernel

private lemma block_8 : ∀ r : Fin 4, ∀ j : Fin 10, 80+j.val < 601 → localChecks r.val (80+j.val) := by decide +kernel

private lemma block_9 : ∀ r : Fin 4, ∀ j : Fin 10, 90+j.val < 601 → localChecks r.val (90+j.val) := by decide +kernel

private lemma block_10 : ∀ r : Fin 4, ∀ j : Fin 10, 100+j.val < 601 → localChecks r.val (100+j.val) := by decide +kernel

private lemma block_11 : ∀ r : Fin 4, ∀ j : Fin 10, 110+j.val < 601 → localChecks r.val (110+j.val) := by decide +kernel

private lemma block_12 : ∀ r : Fin 4, ∀ j : Fin 10, 120+j.val < 601 → localChecks r.val (120+j.val) := by decide +kernel

private lemma block_13 : ∀ r : Fin 4, ∀ j : Fin 10, 130+j.val < 601 → localChecks r.val (130+j.val) := by decide +kernel

private lemma block_14 : ∀ r : Fin 4, ∀ j : Fin 10, 140+j.val < 601 → localChecks r.val (140+j.val) := by decide +kernel

private lemma block_15 : ∀ r : Fin 4, ∀ j : Fin 10, 150+j.val < 601 → localChecks r.val (150+j.val) := by decide +kernel

private lemma block_16 : ∀ r : Fin 4, ∀ j : Fin 10, 160+j.val < 601 → localChecks r.val (160+j.val) := by decide +kernel

private lemma block_17 : ∀ r : Fin 4, ∀ j : Fin 10, 170+j.val < 601 → localChecks r.val (170+j.val) := by decide +kernel

private lemma block_18 : ∀ r : Fin 4, ∀ j : Fin 10, 180+j.val < 601 → localChecks r.val (180+j.val) := by decide +kernel

private lemma block_19 : ∀ r : Fin 4, ∀ j : Fin 10, 190+j.val < 601 → localChecks r.val (190+j.val) := by decide +kernel

private lemma block_20 : ∀ r : Fin 4, ∀ j : Fin 10, 200+j.val < 601 → localChecks r.val (200+j.val) := by decide +kernel

private lemma block_21 : ∀ r : Fin 4, ∀ j : Fin 10, 210+j.val < 601 → localChecks r.val (210+j.val) := by decide +kernel

private lemma block_22 : ∀ r : Fin 4, ∀ j : Fin 10, 220+j.val < 601 → localChecks r.val (220+j.val) := by decide +kernel

private lemma block_23 : ∀ r : Fin 4, ∀ j : Fin 10, 230+j.val < 601 → localChecks r.val (230+j.val) := by decide +kernel

private lemma block_24 : ∀ r : Fin 4, ∀ j : Fin 10, 240+j.val < 601 → localChecks r.val (240+j.val) := by decide +kernel

private lemma block_25 : ∀ r : Fin 4, ∀ j : Fin 10, 250+j.val < 601 → localChecks r.val (250+j.val) := by decide +kernel

private lemma block_26 : ∀ r : Fin 4, ∀ j : Fin 10, 260+j.val < 601 → localChecks r.val (260+j.val) := by decide +kernel

private lemma block_27 : ∀ r : Fin 4, ∀ j : Fin 10, 270+j.val < 601 → localChecks r.val (270+j.val) := by decide +kernel

private lemma block_28 : ∀ r : Fin 4, ∀ j : Fin 10, 280+j.val < 601 → localChecks r.val (280+j.val) := by decide +kernel

private lemma block_29 : ∀ r : Fin 4, ∀ j : Fin 10, 290+j.val < 601 → localChecks r.val (290+j.val) := by decide +kernel

private lemma block_30 : ∀ r : Fin 4, ∀ j : Fin 10, 300+j.val < 601 → localChecks r.val (300+j.val) := by decide +kernel

private lemma block_31 : ∀ r : Fin 4, ∀ j : Fin 10, 310+j.val < 601 → localChecks r.val (310+j.val) := by decide +kernel

private lemma block_32 : ∀ r : Fin 4, ∀ j : Fin 10, 320+j.val < 601 → localChecks r.val (320+j.val) := by decide +kernel

private lemma block_33 : ∀ r : Fin 4, ∀ j : Fin 10, 330+j.val < 601 → localChecks r.val (330+j.val) := by decide +kernel

private lemma block_34 : ∀ r : Fin 4, ∀ j : Fin 10, 340+j.val < 601 → localChecks r.val (340+j.val) := by decide +kernel

private lemma block_35 : ∀ r : Fin 4, ∀ j : Fin 10, 350+j.val < 601 → localChecks r.val (350+j.val) := by decide +kernel

private lemma block_36 : ∀ r : Fin 4, ∀ j : Fin 10, 360+j.val < 601 → localChecks r.val (360+j.val) := by decide +kernel

private lemma block_37 : ∀ r : Fin 4, ∀ j : Fin 10, 370+j.val < 601 → localChecks r.val (370+j.val) := by decide +kernel

private lemma block_38 : ∀ r : Fin 4, ∀ j : Fin 10, 380+j.val < 601 → localChecks r.val (380+j.val) := by decide +kernel

private lemma block_39 : ∀ r : Fin 4, ∀ j : Fin 10, 390+j.val < 601 → localChecks r.val (390+j.val) := by decide +kernel

private lemma block_40 : ∀ r : Fin 4, ∀ j : Fin 10, 400+j.val < 601 → localChecks r.val (400+j.val) := by decide +kernel

private lemma block_41 : ∀ r : Fin 4, ∀ j : Fin 10, 410+j.val < 601 → localChecks r.val (410+j.val) := by decide +kernel

private lemma block_42 : ∀ r : Fin 4, ∀ j : Fin 10, 420+j.val < 601 → localChecks r.val (420+j.val) := by decide +kernel

private lemma block_43 : ∀ r : Fin 4, ∀ j : Fin 10, 430+j.val < 601 → localChecks r.val (430+j.val) := by decide +kernel

private lemma block_44 : ∀ r : Fin 4, ∀ j : Fin 10, 440+j.val < 601 → localChecks r.val (440+j.val) := by decide +kernel

private lemma block_45 : ∀ r : Fin 4, ∀ j : Fin 10, 450+j.val < 601 → localChecks r.val (450+j.val) := by decide +kernel

private lemma block_46 : ∀ r : Fin 4, ∀ j : Fin 10, 460+j.val < 601 → localChecks r.val (460+j.val) := by decide +kernel

private lemma block_47 : ∀ r : Fin 4, ∀ j : Fin 10, 470+j.val < 601 → localChecks r.val (470+j.val) := by decide +kernel

private lemma block_48 : ∀ r : Fin 4, ∀ j : Fin 10, 480+j.val < 601 → localChecks r.val (480+j.val) := by decide +kernel

private lemma block_49 : ∀ r : Fin 4, ∀ j : Fin 10, 490+j.val < 601 → localChecks r.val (490+j.val) := by decide +kernel

private lemma block_50 : ∀ r : Fin 4, ∀ j : Fin 10, 500+j.val < 601 → localChecks r.val (500+j.val) := by decide +kernel

private lemma block_51 : ∀ r : Fin 4, ∀ j : Fin 10, 510+j.val < 601 → localChecks r.val (510+j.val) := by decide +kernel

private lemma block_52 : ∀ r : Fin 4, ∀ j : Fin 10, 520+j.val < 601 → localChecks r.val (520+j.val) := by decide +kernel

private lemma block_53 : ∀ r : Fin 4, ∀ j : Fin 10, 530+j.val < 601 → localChecks r.val (530+j.val) := by decide +kernel

private lemma block_54 : ∀ r : Fin 4, ∀ j : Fin 10, 540+j.val < 601 → localChecks r.val (540+j.val) := by decide +kernel

private lemma block_55 : ∀ r : Fin 4, ∀ j : Fin 10, 550+j.val < 601 → localChecks r.val (550+j.val) := by decide +kernel

private lemma block_56 : ∀ r : Fin 4, ∀ j : Fin 10, 560+j.val < 601 → localChecks r.val (560+j.val) := by decide +kernel

private lemma block_57 : ∀ r : Fin 4, ∀ j : Fin 10, 570+j.val < 601 → localChecks r.val (570+j.val) := by decide +kernel

private lemma block_58 : ∀ r : Fin 4, ∀ j : Fin 10, 580+j.val < 601 → localChecks r.val (580+j.val) := by decide +kernel

private lemma block_59 : ∀ r : Fin 4, ∀ j : Fin 10, 590+j.val < 601 → localChecks r.val (590+j.val) := by decide +kernel

private lemma block_60 : ∀ r : Fin 4, ∀ j : Fin 10, 600+j.val < 601 → localChecks r.val (600+j.val) := by decide +kernel

lemma all_checks (r : Fin 4) (j : Fin 601) : localChecks r.val j.val := by
  have hb : j.val/10 < 61 := by omega
  have hj : j.val%10 < 10 := Nat.mod_lt _ (by omega)
  have he : j.val/10*10+j.val%10 = j.val := Nat.div_add_mod' _ _
  generalize hn : j.val/10 = b at *
  interval_cases b

  · have hh := block_0 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_1 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_2 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_3 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_4 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_5 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_6 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_7 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_8 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_9 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_10 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_11 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_12 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_13 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_14 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_15 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_16 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_17 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_18 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_19 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_20 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_21 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_22 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_23 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_24 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_25 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_26 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_27 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_28 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_29 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_30 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_31 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_32 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_33 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_34 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_35 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_36 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_37 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_38 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_39 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_40 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_41 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_42 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_43 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_44 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_45 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_46 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_47 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_48 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_49 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_50 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_51 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_52 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_53 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_54 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_55 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_56 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_57 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_58 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_59 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

  · have hh := block_60 r ⟨j.val%10,hj⟩ (by dsimp only; omega)
    dsimp only at hh
    convert hh using 1 <;> omega

lemma terminal_checks :
    (∀ r : Fin 4, upperIntegral r.val 600 = 4014) ∧
    (∀ r : Fin 3, lowerIntegral r.val 600 = 1962) ∧
    (upperIntegral 3 52 < 2029800) := by decide +kernel

lemma seed_checks (j : Fin 601) : 50 ≤ j.val →
    (55 ≤ j.val ∧ upperTable 0 j.val = Erdos970.BuchstabGrid.upperNodes j.val) ∨
    (j.val < 55 ∧ 50*Erdos970.BuchstabGrid.lowerDeficitIntegral (j.val-50)+
      (1000000+10)*j.val ≤ upperTable 0 j.val*j.val) := by
  intro hj
  by_cases h55 : 55 ≤ j.val
  · refine Or.inl ⟨h55, ?_⟩
    -- A separate finite equality check is supplied below.
    have hh : ∀ a : Fin 601, 55 ≤ a.val → upperTable 0 a.val = Erdos970.BuchstabGrid.upperNodes a.val := by
      decide +kernel
    exact hh j h55
  · apply Or.inr
    have hh : ∀ a : Fin 5,
        50*Erdos970.BuchstabGrid.lowerDeficitIntegral a.val+(1000000+10)*(50+a.val) ≤
          upperTable 0 (50+a.val)*(50+a.val) := by decide +kernel
    have ha : j.val-50 < 5 := by omega
    have h := hh ⟨j.val-50,ha⟩
    dsimp only at h
    rw [show 50+(j.val-50) = j.val by omega] at h
    exact ⟨by omega,h⟩
#print axioms all_checks
#print axioms seed_checks
end Erdos970.BuchstabFourGrid
