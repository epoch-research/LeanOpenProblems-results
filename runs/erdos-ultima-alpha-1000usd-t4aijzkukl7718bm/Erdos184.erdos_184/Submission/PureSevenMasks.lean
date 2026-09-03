import Submission.PureSevenMaskPull0
import Submission.PureSevenMaskPull1
import Submission.PureSevenMaskPull2
import Submission.PureSevenMaskPull3
import Submission.PureSevenMaskPull4
import Submission.PureSevenMaskPull5
import Submission.PureSevenMaskGood00
import Submission.PureSevenMaskGood01
import Submission.PureSevenMaskGood02
import Submission.PureSevenMaskGood03
import Submission.PureSevenMaskGood04
import Submission.PureSevenMaskGood05
import Submission.PureSevenMaskGood06
import Submission.PureSevenMaskGood07
import Submission.PureSevenMaskGood08
import Submission.PureSevenMaskGood09
import Submission.PureSevenMaskGood10
import Submission.PureSevenMaskGood11
import Submission.PureSevenMaskGood12
import Submission.PureSevenMaskGood13
import Submission.PureSevenMaskGood14
import Submission.PureSevenMaskGood15
import Submission.PureSevenMaskGood16
import Submission.PureSevenMaskGood17
import Submission.PureSevenMaskGood18
import Submission.PureSevenMaskGood19
import Submission.PureSevenMaskGood20
import Submission.PureSevenMaskGood21
import Submission.PureSevenMaskGood22
import Submission.PureSevenMaskGood23
import Submission.PureSevenMaskGood24
import Submission.PureSevenMaskGood25
import Submission.PureSevenMaskGood26
import Submission.PureSevenMaskGood27
import Submission.PureSevenMaskGood28
namespace Erdos184Work.PureSevenMasks
open FiniteCaseLookup PureSevenRowModel PureSevenProjectionNumbers
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false
lemma good_table : Table.Every GoodCertificate PureSixGoodLookup.table :=
  ⟨⟨⟨⟨good_block0,⟨good_block1,good_block2⟩⟩,⟨⟨good_block3,good_block4⟩,⟨good_block5,good_block6⟩⟩⟩,⟨⟨good_block7,⟨good_block8,good_block9⟩⟩,⟨⟨good_block10,good_block11⟩,⟨good_block12,good_block13⟩⟩⟩⟩,⟨⟨⟨good_block14,⟨good_block15,good_block16⟩⟩,⟨⟨good_block17,good_block18⟩,⟨good_block19,good_block20⟩⟩⟩,⟨⟨⟨good_block21,good_block22⟩,⟨good_block23,good_block24⟩⟩,⟨⟨good_block25,good_block26⟩,⟨good_block27,good_block28⟩⟩⟩⟩⟩
lemma good_bit {j : ℕ} (h : PureSixGoodLookup.Good j) :
    (smallMask (maskIndex (j / 12))).testBit (j % 12) = true := by
  obtain ⟨u,hu⟩ := Option.isSome_iff_exists.mp h
  exact Table.lookup_every GoodCertificate PureSixGoodLookup.table good_table j hu
def prefix0 (q : Rows) : ℕ := 20736 * (enc0_0 (q 1)).val + 1728 * (enc0_1 (q 2)).val + 144 * (enc0_2 (q 3)).val + 12 * (enc0_3 (q 4)).val + 1 * (enc0_4 (q 5)).val
lemma key_div0 (q : Rows) : key0 q / 12 = prefix0 q := by
  have h : (enc0_5 (q 6)).val < 12 := (enc0_5 (q 6)).isLt
  change (248832 * (enc0_0 (q 1)).val + 20736 * (enc0_1 (q 2)).val + 1728 * (enc0_2 (q 3)).val + 144 * (enc0_3 (q 4)).val + 12 * (enc0_4 (q 5)).val + 1 * (enc0_5 (q 6)).val) / 12 = 20736 * (enc0_0 (q 1)).val + 1728 * (enc0_1 (q 2)).val + 144 * (enc0_2 (q 3)).val + 12 * (enc0_3 (q 4)).val + 1 * (enc0_4 (q 5)).val
  omega
lemma key_mod0 (q : Rows) : key0 q % 12 = (enc0_5 (q 6)).val := by
  have h : (enc0_5 (q 6)).val < 12 := (enc0_5 (q 6)).isLt
  change (248832 * (enc0_0 (q 1)).val + 20736 * (enc0_1 (q 2)).val + 1728 * (enc0_2 (q 3)).val + 144 * (enc0_3 (q 4)).val + 12 * (enc0_4 (q 5)).val + 1 * (enc0_5 (q 6)).val) % 12 = _
  omega
def lastMask0 (q : Rows) : ℕ := pull0 (maskIndex (prefix0 q))
lemma good_last0 (q : Rows) (h : PureSixGoodLookup.Good (key0 q)) :
    (lastMask0 q).testBit (q 6).val = true := by
  have hh := good_bit h
  rw [key_div0,key_mod0] at hh
  unfold lastMask0
  rw [pull_valid0]
  exact hh
def prefix1 (q : Rows) : ℕ := 20736 * (enc1_0 (q 0)).val + 1728 * (enc1_1 (q 2)).val + 144 * (enc1_2 (q 3)).val + 12 * (enc1_3 (q 4)).val + 1 * (enc1_4 (q 5)).val
lemma key_div1 (q : Rows) : key1 q / 12 = prefix1 q := by
  have h : (enc1_5 (q 6)).val < 12 := (enc1_5 (q 6)).isLt
  change (248832 * (enc1_0 (q 0)).val + 20736 * (enc1_1 (q 2)).val + 1728 * (enc1_2 (q 3)).val + 144 * (enc1_3 (q 4)).val + 12 * (enc1_4 (q 5)).val + 1 * (enc1_5 (q 6)).val) / 12 = 20736 * (enc1_0 (q 0)).val + 1728 * (enc1_1 (q 2)).val + 144 * (enc1_2 (q 3)).val + 12 * (enc1_3 (q 4)).val + 1 * (enc1_4 (q 5)).val
  omega
lemma key_mod1 (q : Rows) : key1 q % 12 = (enc1_5 (q 6)).val := by
  have h : (enc1_5 (q 6)).val < 12 := (enc1_5 (q 6)).isLt
  change (248832 * (enc1_0 (q 0)).val + 20736 * (enc1_1 (q 2)).val + 1728 * (enc1_2 (q 3)).val + 144 * (enc1_3 (q 4)).val + 12 * (enc1_4 (q 5)).val + 1 * (enc1_5 (q 6)).val) % 12 = _
  omega
def lastMask1 (q : Rows) : ℕ := pull1 (maskIndex (prefix1 q))
lemma good_last1 (q : Rows) (h : PureSixGoodLookup.Good (key1 q)) :
    (lastMask1 q).testBit (q 6).val = true := by
  have hh := good_bit h
  rw [key_div1,key_mod1] at hh
  unfold lastMask1
  rw [pull_valid1]
  exact hh
def prefix2 (q : Rows) : ℕ := 20736 * (enc2_0 (q 0)).val + 1728 * (enc2_1 (q 1)).val + 144 * (enc2_2 (q 3)).val + 12 * (enc2_3 (q 4)).val + 1 * (enc2_4 (q 5)).val
lemma key_div2 (q : Rows) : key2 q / 12 = prefix2 q := by
  have h : (enc2_5 (q 6)).val < 12 := (enc2_5 (q 6)).isLt
  change (248832 * (enc2_0 (q 0)).val + 20736 * (enc2_1 (q 1)).val + 1728 * (enc2_2 (q 3)).val + 144 * (enc2_3 (q 4)).val + 12 * (enc2_4 (q 5)).val + 1 * (enc2_5 (q 6)).val) / 12 = 20736 * (enc2_0 (q 0)).val + 1728 * (enc2_1 (q 1)).val + 144 * (enc2_2 (q 3)).val + 12 * (enc2_3 (q 4)).val + 1 * (enc2_4 (q 5)).val
  omega
lemma key_mod2 (q : Rows) : key2 q % 12 = (enc2_5 (q 6)).val := by
  have h : (enc2_5 (q 6)).val < 12 := (enc2_5 (q 6)).isLt
  change (248832 * (enc2_0 (q 0)).val + 20736 * (enc2_1 (q 1)).val + 1728 * (enc2_2 (q 3)).val + 144 * (enc2_3 (q 4)).val + 12 * (enc2_4 (q 5)).val + 1 * (enc2_5 (q 6)).val) % 12 = _
  omega
def lastMask2 (q : Rows) : ℕ := pull2 (maskIndex (prefix2 q))
lemma good_last2 (q : Rows) (h : PureSixGoodLookup.Good (key2 q)) :
    (lastMask2 q).testBit (q 6).val = true := by
  have hh := good_bit h
  rw [key_div2,key_mod2] at hh
  unfold lastMask2
  rw [pull_valid2]
  exact hh
def prefix3 (q : Rows) : ℕ := 20736 * (enc3_0 (q 0)).val + 1728 * (enc3_1 (q 1)).val + 144 * (enc3_2 (q 2)).val + 12 * (enc3_3 (q 4)).val + 1 * (enc3_4 (q 5)).val
lemma key_div3 (q : Rows) : key3 q / 12 = prefix3 q := by
  have h : (enc3_5 (q 6)).val < 12 := (enc3_5 (q 6)).isLt
  change (248832 * (enc3_0 (q 0)).val + 20736 * (enc3_1 (q 1)).val + 1728 * (enc3_2 (q 2)).val + 144 * (enc3_3 (q 4)).val + 12 * (enc3_4 (q 5)).val + 1 * (enc3_5 (q 6)).val) / 12 = 20736 * (enc3_0 (q 0)).val + 1728 * (enc3_1 (q 1)).val + 144 * (enc3_2 (q 2)).val + 12 * (enc3_3 (q 4)).val + 1 * (enc3_4 (q 5)).val
  omega
lemma key_mod3 (q : Rows) : key3 q % 12 = (enc3_5 (q 6)).val := by
  have h : (enc3_5 (q 6)).val < 12 := (enc3_5 (q 6)).isLt
  change (248832 * (enc3_0 (q 0)).val + 20736 * (enc3_1 (q 1)).val + 1728 * (enc3_2 (q 2)).val + 144 * (enc3_3 (q 4)).val + 12 * (enc3_4 (q 5)).val + 1 * (enc3_5 (q 6)).val) % 12 = _
  omega
def lastMask3 (q : Rows) : ℕ := pull3 (maskIndex (prefix3 q))
lemma good_last3 (q : Rows) (h : PureSixGoodLookup.Good (key3 q)) :
    (lastMask3 q).testBit (q 6).val = true := by
  have hh := good_bit h
  rw [key_div3,key_mod3] at hh
  unfold lastMask3
  rw [pull_valid3]
  exact hh
def prefix4 (q : Rows) : ℕ := 20736 * (enc4_0 (q 0)).val + 1728 * (enc4_1 (q 1)).val + 144 * (enc4_2 (q 2)).val + 12 * (enc4_3 (q 3)).val + 1 * (enc4_4 (q 5)).val
lemma key_div4 (q : Rows) : key4 q / 12 = prefix4 q := by
  have h : (enc4_5 (q 6)).val < 12 := (enc4_5 (q 6)).isLt
  change (248832 * (enc4_0 (q 0)).val + 20736 * (enc4_1 (q 1)).val + 1728 * (enc4_2 (q 2)).val + 144 * (enc4_3 (q 3)).val + 12 * (enc4_4 (q 5)).val + 1 * (enc4_5 (q 6)).val) / 12 = 20736 * (enc4_0 (q 0)).val + 1728 * (enc4_1 (q 1)).val + 144 * (enc4_2 (q 2)).val + 12 * (enc4_3 (q 3)).val + 1 * (enc4_4 (q 5)).val
  omega
lemma key_mod4 (q : Rows) : key4 q % 12 = (enc4_5 (q 6)).val := by
  have h : (enc4_5 (q 6)).val < 12 := (enc4_5 (q 6)).isLt
  change (248832 * (enc4_0 (q 0)).val + 20736 * (enc4_1 (q 1)).val + 1728 * (enc4_2 (q 2)).val + 144 * (enc4_3 (q 3)).val + 12 * (enc4_4 (q 5)).val + 1 * (enc4_5 (q 6)).val) % 12 = _
  omega
def lastMask4 (q : Rows) : ℕ := pull4 (maskIndex (prefix4 q))
lemma good_last4 (q : Rows) (h : PureSixGoodLookup.Good (key4 q)) :
    (lastMask4 q).testBit (q 6).val = true := by
  have hh := good_bit h
  rw [key_div4,key_mod4] at hh
  unfold lastMask4
  rw [pull_valid4]
  exact hh
def prefix5 (q : Rows) : ℕ := 20736 * (enc5_0 (q 0)).val + 1728 * (enc5_1 (q 1)).val + 144 * (enc5_2 (q 2)).val + 12 * (enc5_3 (q 3)).val + 1 * (enc5_4 (q 4)).val
lemma key_div5 (q : Rows) : key5 q / 12 = prefix5 q := by
  have h : (enc5_5 (q 6)).val < 12 := (enc5_5 (q 6)).isLt
  change (248832 * (enc5_0 (q 0)).val + 20736 * (enc5_1 (q 1)).val + 1728 * (enc5_2 (q 2)).val + 144 * (enc5_3 (q 3)).val + 12 * (enc5_4 (q 4)).val + 1 * (enc5_5 (q 6)).val) / 12 = 20736 * (enc5_0 (q 0)).val + 1728 * (enc5_1 (q 1)).val + 144 * (enc5_2 (q 2)).val + 12 * (enc5_3 (q 3)).val + 1 * (enc5_4 (q 4)).val
  omega
lemma key_mod5 (q : Rows) : key5 q % 12 = (enc5_5 (q 6)).val := by
  have h : (enc5_5 (q 6)).val < 12 := (enc5_5 (q 6)).isLt
  change (248832 * (enc5_0 (q 0)).val + 20736 * (enc5_1 (q 1)).val + 1728 * (enc5_2 (q 2)).val + 144 * (enc5_3 (q 3)).val + 12 * (enc5_4 (q 4)).val + 1 * (enc5_5 (q 6)).val) % 12 = _
  omega
def lastMask5 (q : Rows) : ℕ := pull5 (maskIndex (prefix5 q))
lemma good_last5 (q : Rows) (h : PureSixGoodLookup.Good (key5 q)) :
    (lastMask5 q).testBit (q 6).val = true := by
  have hh := good_bit h
  rw [key_div5,key_mod5] at hh
  unfold lastMask5
  rw [pull_valid5]
  exact hh
def commonMask (q : Rows) : ℕ :=
  let a0 := lastMask0 q
  if a0 = 0 then 0 else
  let a1 := a0 &&& lastMask1 q
  if a1 = 0 then 0 else
  let a2 := a1 &&& lastMask2 q
  if a2 = 0 then 0 else
  let a3 := a2 &&& lastMask3 q
  if a3 = 0 then 0 else
  let a4 := a3 &&& lastMask4 q
  if a4 = 0 then 0 else
  a4 &&& lastMask5 q
lemma compatible_common (q : Rows) (h : Compatible q) :
    (commonMask q).testBit (q 6).val = true := by
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
  have hb0 := good_last0 q h0
  have hb1 := good_last1 q h1
  have hb2 := good_last2 q h2
  have hb3 := good_last3 q h3
  have hb4 := good_last4 q h4
  have hb5 := good_last5 q h5
  have hz0 : (lastMask0 q) ≠ 0 := by
    intro hz
    have hb : (lastMask0 q).testBit (q 6).val = true := by
      exact hb0
    rw [hz] at hb
    simpa using hb
  have hz1 : (lastMask0 q &&& lastMask1 q) ≠ 0 := by
    intro hz
    have hb : (lastMask0 q &&& lastMask1 q).testBit (q 6).val = true := by
      simp only [Nat.testBit_land,Bool.true_and,hb0,hb1]
    rw [hz] at hb
    simpa using hb
  have hz2 : (lastMask0 q &&& lastMask1 q &&& lastMask2 q) ≠ 0 := by
    intro hz
    have hb : (lastMask0 q &&& lastMask1 q &&& lastMask2 q).testBit (q 6).val = true := by
      simp only [Nat.testBit_land,Bool.true_and,hb0,hb1,hb2]
    rw [hz] at hb
    simpa using hb
  have hz3 : (lastMask0 q &&& lastMask1 q &&& lastMask2 q &&& lastMask3 q) ≠ 0 := by
    intro hz
    have hb : (lastMask0 q &&& lastMask1 q &&& lastMask2 q &&& lastMask3 q).testBit (q 6).val = true := by
      simp only [Nat.testBit_land,Bool.true_and,hb0,hb1,hb2,hb3]
    rw [hz] at hb
    simpa using hb
  have hz4 : (lastMask0 q &&& lastMask1 q &&& lastMask2 q &&& lastMask3 q &&& lastMask4 q) ≠ 0 := by
    intro hz
    have hb : (lastMask0 q &&& lastMask1 q &&& lastMask2 q &&& lastMask3 q &&& lastMask4 q).testBit (q 6).val = true := by
      simp only [Nat.testBit_land,Bool.true_and,hb0,hb1,hb2,hb3,hb4]
    rw [hz] at hb
    simpa using hb
  simp only [commonMask,Bool.true_and,if_neg hz0,if_neg hz1,if_neg hz2,if_neg hz3,if_neg hz4,Nat.testBit_land,hb0,hb1,hb2,hb3,hb4,hb5]
lemma commonMask_congr (p q : Rows) (h : ∀ i : Fin 6, p i.castSucc = q i.castSucc) :
    commonMask p = commonMask q := by
  have h0 : p 0 = q 0 := h 0
  have h1 : p 1 = q 1 := h 1
  have h2 : p 2 = q 2 := h 2
  have h3 : p 3 = q 3 := h 3
  have h4 : p 4 = q 4 := h 4
  have h5 : p 5 = q 5 := h 5
  simp only [commonMask,lastMask0,lastMask1,lastMask2,lastMask3,lastMask4,lastMask5,prefix0,prefix1,prefix2,prefix3,prefix4,prefix5,h0,h1,h2,h3,h4,h5]
#print axioms compatible_common
end Erdos184Work.PureSevenMasks
