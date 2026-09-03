import Submission.QuinticWeightedResultantRow0
import Submission.QuinticWeightedResultantRow1
import Submission.QuinticWeightedResultantRow2
import Submission.QuinticWeightedResultantRow3
import Submission.QuinticWeightedResultantRow4
import Submission.QuinticWeightedResultantRow5
import Submission.QuinticWeightedResultantRow6
import Submission.QuinticWeightedResultantRow7
import Submission.QuinticWeightedResultantRow8
import Submission.QuinticWeightedResultantRow9
import Submission.QuinticWeightedResultantRow10
import Submission.QuinticWeightedResultantRow11
import Submission.QuinticWeightedResultantRow12
import Submission.QuinticWeightedResultantRow13
import Submission.QuinticWeightedResultantRow14
import Submission.QuinticWeightedResultantRow15
import Submission.QuinticWeightedResultantRow16
import Submission.QuinticWeightedResultantRow17
import Submission.QuinticWeightedResultantRow18

/-! A coefficientwise certificate for a restricted quintic polynomial construction.
This module does not assert bounds for unrestricted representation counts. -/
namespace Erdos322Research.QuinticWeightedResultantCertificate
noncomputable section
open Polynomial Finset RationalPolynomialModularObstruction DensePolynomialCertificate
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
theorem certificate (V w : ℚ) (hf : f V w = 0) (hg : g V w = 0) : target w = 0 := by
  have hc : ∀ k : Fin 19, conv (avec w) (fvec w) (bvec w) (gvec w) k =
      if (k : ℕ)=0 then (-274877906944)*target w else 0 := by
    intro k
    fin_cases k

    · simp [conv, avec, fvec, bvec, gvec, Fin.sum_univ_succ, Fin.reduceSucc]
      simpa only [add_assoc, add_zero, zero_add, neg_mul] using check0 w

    · simp [conv, avec, fvec, bvec, gvec, Fin.sum_univ_succ, Fin.reduceSucc]
      simpa only [add_assoc, add_zero, zero_add, neg_mul] using check1 w

    · simp [conv, avec, fvec, bvec, gvec, Fin.sum_univ_succ, Fin.reduceSucc]
      simpa only [add_assoc, add_zero, zero_add, neg_mul] using check2 w

    · simp [conv, avec, fvec, bvec, gvec, Fin.sum_univ_succ, Fin.reduceSucc]
      simpa only [add_assoc, add_zero, zero_add, neg_mul] using check3 w

    · simp [conv, avec, fvec, bvec, gvec, Fin.sum_univ_succ, Fin.reduceSucc]
      simpa only [add_assoc, add_zero, zero_add, neg_mul] using check4 w

    · simp [conv, avec, fvec, bvec, gvec, Fin.sum_univ_succ, Fin.reduceSucc]
      simpa only [add_assoc, add_zero, zero_add, neg_mul] using check5 w

    · simp [conv, avec, fvec, bvec, gvec, Fin.sum_univ_succ, Fin.reduceSucc]
      simpa only [add_assoc, add_zero, zero_add, neg_mul] using check6 w

    · simp [conv, avec, fvec, bvec, gvec, Fin.sum_univ_succ, Fin.reduceSucc]
      simpa only [add_assoc, add_zero, zero_add, neg_mul] using check7 w

    · simp [conv, avec, fvec, bvec, gvec, Fin.sum_univ_succ, Fin.reduceSucc]
      simpa only [add_assoc, add_zero, zero_add, neg_mul] using check8 w

    · simp [conv, avec, fvec, bvec, gvec, Fin.sum_univ_succ, Fin.reduceSucc]
      simpa only [add_assoc, add_zero, zero_add, neg_mul] using check9 w

    · simp [conv, avec, fvec, bvec, gvec, Fin.sum_univ_succ, Fin.reduceSucc]
      simpa only [add_assoc, add_zero, zero_add, neg_mul] using check10 w

    · simp [conv, avec, fvec, bvec, gvec, Fin.sum_univ_succ, Fin.reduceSucc]
      simpa only [add_assoc, add_zero, zero_add, neg_mul] using check11 w

    · simp [conv, avec, fvec, bvec, gvec, Fin.sum_univ_succ, Fin.reduceSucc]
      simpa only [add_assoc, add_zero, zero_add, neg_mul] using check12 w

    · simp [conv, avec, fvec, bvec, gvec, Fin.sum_univ_succ, Fin.reduceSucc]
      simpa only [add_assoc, add_zero, zero_add, neg_mul] using check13 w

    · simp [conv, avec, fvec, bvec, gvec, Fin.sum_univ_succ, Fin.reduceSucc]
      simpa only [add_assoc, add_zero, zero_add, neg_mul] using check14 w

    · simp [conv, avec, fvec, bvec, gvec, Fin.sum_univ_succ, Fin.reduceSucc]
      simpa only [add_assoc, add_zero, zero_add, neg_mul] using check15 w

    · simp [conv, avec, fvec, bvec, gvec, Fin.sum_univ_succ, Fin.reduceSucc]
      simpa only [add_assoc, add_zero, zero_add, neg_mul] using check16 w

    · simp [conv, avec, fvec, bvec, gvec, Fin.sum_univ_succ, Fin.reduceSucc]
      simpa only [add_assoc, add_zero, zero_add, neg_mul] using check17 w

    · simp [conv, avec, fvec, bvec, gvec, Fin.sum_univ_succ, Fin.reduceSucc]
      simpa only [add_assoc, add_zero, zero_add, neg_mul] using check18 w

  have he := combine (avec w) (fvec w) (bvec w) (gvec w) ((-274877906944)*target w) V hc
  change _*f V w+_*g V w = _ at he
  rw [hf, hg, mul_zero, mul_zero, add_zero] at he
  have hK : ((-274877906944) : ℚ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp he.symm).resolve_left hK

private instance : Fact (Nat.Prime 43) := ⟨by decide⟩

private theorem mod43_no_root : ∀ w : ZMod 43, evalList rootCoeffs w ≠ 0 := by
  decide +kernel

private theorem mod43_hom_zero (a b : ZMod 43) (h : homList rootCoeffs a b = 0) :
    a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · have ha : a = 0 := by
      by_contra ha
      norm_num [homList, rootCoeffs, hb, ha] at h
      exact absurd h (by decide)
    exact ⟨ha, hb⟩
  · have he := homogenize rootCoeffs a b hb
    rw [h, mul_zero] at he
    have hz : evalList rootCoeffs (a/b) = 0 :=
      (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero _ hb)
    exact (mod43_no_root (a/b) hz).elim

theorem no_common_rational_root (V w : ℚ) : ¬ (f V w = 0 ∧ g V w = 0) := by
  rintro ⟨hf, hg⟩
  exact no_rational_root rootCoeffs mod43_hom_zero w (certificate V w hf hg)

theorem f_expansion (V w : ℚ) : f V w =
    (-125287953623040)+
      (-175901255087104)*w^1+
      (-110131040488960)*w^2+
      (-37652200846080)*w^3+
      (-7152707493120)*w^4+
      (-589428856960)*w^5+
      42361561408*w^6+
      16857936160*w^7+
      2014621880*w^8+
      128655420*w^9+
      4415450*w^10+
      64321*w^11+
      (-1374101682309120000)*V^1+
      (-1183899572128768000)*V^1*w^1+
      (-423679214781952000)*V^1*w^2+
      (-84520937420032000)*V^1*w^3+
      (-12454015420672000)*V^1*w^4+
      (-2064466375552000)*V^1*w^5+
      (-351622222016000)*V^1*w^6+
      (-39164409888000)*V^1*w^7+
      (-1703112168000)*V^1*w^8+
      120922372000*V^1*w^9+
      19762322000*V^1*w^10+
      992759000*V^1*w^11+
      18340000*V^1*w^12+
      (-2089512318949478400000)*V^2+
      (-2409581206202828800000)*V^2*w^1+
      (-1160038961626803200000)*V^2*w^2+
      (-295797634151769600000)*V^2*w^3+
      (-40280105516608000000)*V^2*w^4+
      (-2135173251641600000)*V^2*w^5+
      94117434524800000*V^2*w^6+
      1494544283200000*V^2*w^7+
      (-4284101904400000)*V^2*w^8+
      (-608242865000000)*V^2*w^9+
      (-32418425500000)*V^2*w^10+
      (-192362750000)*V^2*w^11+
      47162000000*V^2*w^12+
      1373500000*V^2*w^13+
      (-1068569310645043200000000)*V^3+
      (-1568370959127552000000000)*V^3*w^1+
      (-993566461830860800000000)*V^3*w^2+
      (-353876428022937600000000)*V^3*w^3+
      (-76551620775270400000000)*V^3*w^4+
      (-9814637676620800000000)*V^3*w^5+
      (-566856191424000000000)*V^3*w^6+
      27060141996800000000*V^3*w^7+
      6965036097600000000*V^3*w^8+
      358203922400000000*V^3*w^9+
      (-15123402000000000)*V^3*w^10+
      (-2627315000000000)*V^3*w^11+
      (-107882000000000)*V^3*w^12+
      (-626000000000)*V^3*w^13+
      42000000000*V^3*w^14+
      (-248514214758451200000000000)*V^4+
      (-433145617885209600000000000)*V^4*w^1+
      (-333442316258956800000000000)*V^4*w^2+
      (-149332131488608000000000000)*V^4*w^3+
      (-43122724841888000000000000)*V^4*w^4+
      (-8374598391235200000000000)*V^4*w^5+
      (-1090088292798400000000000)*V^4*w^6+
      (-86966545711200000000000)*V^4*w^7+
      (-2291148305000000000000)*V^4*w^8+
      348798879500000000000*V^4*w^9+
      46191449650000000000*V^4*w^10+
      2223215125000000000*V^4*w^11+
      8985000000000000*V^4*w^12+
      (-3235500000000000)*V^4*w^13+
      (-84000000000000)*V^4*w^14+
      500000000000*V^4*w^15+
      (-29388751728998400000000000000)*V^5+
      (-56317758838502400000000000000)*V^5*w^1+
      (-48061122834291200000000000000)*V^5*w^2+
      (-24181617745836800000000000000)*V^5*w^3+
      (-8051746765971200000000000000)*V^5*w^4+
      (-1904823248860800000000000000)*V^5*w^5+
      (-338586621185600000000000000)*V^5*w^6+
      (-47000841704800000000000000)*V^5*w^7+
      (-5073356082200000000000000)*V^5*w^8+
      (-390512723300000000000000)*V^5*w^9+
      (-15726810050000000000000)*V^5*w^10+
      394296625000000000000*V^5*w^11+
      87560000000000000000*V^5*w^12+
      4058500000000000000*V^5*w^13+
      37500000000000000*V^5*w^14+
      (-1500000000000000)*V^5*w^15+
      (-1901488378176000000000000000000)*V^6+
      (-3515885802528000000000000000000)*V^6*w^1+
      (-2744458012976000000000000000000)*V^6*w^2+
      (-1125478565016000000000000000000)*V^6*w^3+
      (-225322478568000000000000000000)*V^6*w^4+
      229703420000000000000000000*V^6*w^5+
      11196062050000000000000000000*V^6*w^6+
      2518084905000000000000000000*V^6*w^7+
      159411051750000000000000000*V^6*w^8+
      (-33585380625000000000000000)*V^6*w^9+
      (-9158577937500000000000000)*V^6*w^10+
      (-1022357968750000000000000)*V^6*w^11+
      (-59209500000000000000000)*V^6*w^12+
      (-1253437500000000000000)*V^6*w^13+
      37500000000000000000*V^6*w^14+
      1875000000000000000*V^6*w^15+
      (-97773426662400000000000000000000)*V^7+
      (-156263437324800000000000000000000)*V^7*w^1+
      (-83879458771200000000000000000000)*V^7*w^2+
      5264313654400000000000000000000*V^7*w^3+
      31666006160000000000000000000000*V^7*w^4+
      20444694043200000000000000000000*V^7*w^5+
      7594816314400000000000000000000*V^7*w^6+
      1934940063600000000000000000000*V^7*w^7+
      359815019300000000000000000000*V^7*w^8+
      49523754750000000000000000000*V^7*w^9+
      4870663375000000000000000000*V^7*w^10+
      302293812500000000000000000*V^7*w^11+
      6523625000000000000000000*V^7*w^12+
      (-584875000000000000000000)*V^7*w^13+
      (-50625000000000000000000)*V^7*w^14+
      (-1250000000000000000000)*V^7*w^15+
      (-7094538619200000000000000000000000)*V^8+
      (-13287706980000000000000000000000000)*V^8*w^1+
      (-11771152610800000000000000000000000)*V^8*w^2+
      (-7048500912600000000000000000000000)*V^8*w^3+
      (-3505260655400000000000000000000000)*V^8*w^4+
      (-1544652516900000000000000000000000)*V^8*w^5+
      (-561063539750000000000000000000000)*V^8*w^6+
      (-152482250975000000000000000000000)*V^8*w^7+
      (-28570030856250000000000000000000)*V^8*w^8+
      (-3219714503125000000000000000000)*V^8*w^9+
      (-95124304687500000000000000000)*V^8*w^10+
      33183550781250000000000000000*V^8*w^11+
      6161437500000000000000000000*V^8*w^12+
      527531250000000000000000000*V^8*w^13+
      24000000000000000000000000*V^8*w^14+
      468750000000000000000000*V^8*w^15+
      (-381930235200000000000000000000000000)*V^9+
      (-721533477600000000000000000000000000)*V^9*w^1+
      (-656428018800000000000000000000000000)*V^9*w^2+
      (-427011557000000000000000000000000000)*V^9*w^3+
      (-250119593000000000000000000000000000)*V^9*w^4+
      (-135751284300000000000000000000000000)*V^9*w^5+
      (-61893801950000000000000000000000000)*V^9*w^6+
      (-22143580725000000000000000000000000)*V^9*w^7+
      (-6095684406250000000000000000000000)*V^9*w^8+
      (-1289169984375000000000000000000000)*V^9*w^9+
      (-208877229687500000000000000000000)*V^9*w^10+
      (-25568160156250000000000000000000)*V^9*w^11+
      (-2289390625000000000000000000000)*V^9*w^12+
      (-141156250000000000000000000000)*V^9*w^13+
      (-5343750000000000000000000000)*V^9*w^14+
      (-93750000000000000000000000)*V^9*w^15+
      (-7682144400000000000000000000000000000)*V^10+
      (-8268839400000000000000000000000000000)*V^10*w^1+
      6438395300000000000000000000000000000*V^10*w^2+
      20613128450000000000000000000000000000*V^10*w^3+
      22184937550000000000000000000000000000*V^10*w^4+
      14993352875000000000000000000000000000*V^10*w^5+
      7249239262500000000000000000000000000*V^10*w^6+
      2626962631250000000000000000000000000*V^10*w^7+
      724617329687500000000000000000000000*V^10*w^8+
      152147455468750000000000000000000000*V^10*w^9+
      24073508203125000000000000000000000*V^10*w^10+
      2814852539062500000000000000000000*V^10*w^11+
      235617187500000000000000000000000*V^10*w^12+
      13396484375000000000000000000000*V^10*w^13+
      468750000000000000000000000000*V^10*w^14+
      7812500000000000000000000000*V^10*w^15 := by
  simp [f, fvec, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, Fin.sum_univ_succ, Fin.reduceSucc, evalList]
  norm_num
  ring

theorem g_expansion (V w : ℚ) : g V w =
    11806988544+
      5087618304*w^1+
      (-10957031936)*w^2+
      (-9955616256)*w^3+
      (-3612481376)*w^4+
      (-718589344)*w^5+
      (-85108704)*w^6+
      (-6009664)*w^7+
      (-234419)*w^8+
      (-3899)*w^9+
      7373402496000*V^1+
      18754452864000*V^1*w^1+
      52460261248000*V^1*w^2+
      32252027712000*V^1*w^3+
      9073177136000*V^1*w^4+
      1374575488000*V^1*w^5+
      109489216000*V^1*w^6+
      2803132000*V^1*w^7+
      (-224244500)*V^1*w^8+
      (-19293500)*V^1*w^9+
      (-441500)*V^1*w^10+
      544382694144000000*V^2+
      120889292544000000*V^2*w^1+
      (-83471910272000000)*V^2*w^2+
      (-43829448704000000)*V^2*w^3+
      (-8271281312000000)*V^2*w^4+
      (-573477344000000)*V^2*w^5+
      41711376000000*V^2*w^6+
      11493992000000*V^2*w^7+
      923679000000*V^2*w^8+
      30067000000*V^2*w^9+
      (-27500000)*V^2*w^10+
      (-17500000)*V^2*w^11+
      994088776320000000000*V^3+
      768203364633600000000*V^3*w^1+
      245662214566400000000*V^3*w^2+
      37384793664000000000*V^3*w^3+
      940531696000000000*V^3*w^4+
      (-694434928000000000)*V^3*w^5+
      (-137375145600000000)*V^3*w^6+
      (-12190150400000000)*V^3*w^7+
      (-439617500000000)*V^3*w^8+
      11339500000000*V^3*w^9+
      1495750000000*V^3*w^10+
      32750000000*V^3*w^11+
      (-250000000)*V^3*w^12+
      207615445344000000000000*V^4+
      204136415251200000000000*V^4*w^1+
      94209758048000000000000*V^4*w^2+
      27247115584000000000000*V^4*w^3+
      5409076124000000000000*V^4*w^4+
      729530484000000000000*V^4*w^5+
      58089388800000000000*V^4*w^6+
      855834000000000000*V^4*w^7+
      (-352415125000000000)*V^4*w^8+
      (-38109125000000000)*V^4*w^9+
      (-1556375000000000)*V^4*w^10+
      (-9375000000000)*V^4*w^11+
      750000000000*V^4*w^12+
      672573363840000000000000*V^5+
      (-3819764338560000000000000)*V^5*w^1+
      (-4068321218560000000000000)*V^5*w^2+
      (-1553114999360000000000000)*V^5*w^3+
      (-213530539760000000000000)*V^5*w^4+
      31189061600000000000000*V^5*w^5+
      18179091200000000000000*V^5*w^6+
      3480677500000000000000*V^5*w^7+
      363919112500000000000*V^5*w^8+
      20226737500000000000*V^5*w^9+
      318750000000000000*V^5*w^10+
      (-22812500000000000)*V^5*w^11+
      (-937500000000000)*V^5*w^12+
      (-1215979482240000000000000000)*V^6+
      (-2223906053760000000000000000)*V^6*w^1+
      (-1840450608960000000000000000)*V^6*w^2+
      (-914251189760000000000000000)*V^6*w^3+
      (-304180918160000000000000000)*V^6*w^4+
      (-70966596720000000000000000)*V^6*w^5+
      (-11637142600000000000000000)*V^6*w^6+
      (-1278873300000000000000000)*V^6*w^7+
      (-79638462500000000000000)*V^6*w^8+
      (-459912500000000000000)*V^6*w^9+
      346843750000000000000*V^6*w^10+
      25468750000000000000*V^6*w^11+
      625000000000000000*V^6*w^12+
      81671077440000000000000000000*V^7+
      173645714880000000000000000000*V^7*w^1+
      161962383840000000000000000000*V^7*w^2+
      86597188640000000000000000000*V^7*w^3+
      28814239480000000000000000000*V^7*w^4+
      5912220120000000000000000000*V^7*w^5+
      617143800000000000000000000*V^7*w^6+
      (-20358900000000000000000000)*V^7*w^7+
      (-17586093750000000000000000)*V^7*w^8+
      (-2838581250000000000000000)*V^7*w^9+
      (-243984375000000000000000)*V^7*w^10+
      (-11484375000000000000000)*V^7*w^11+
      (-234375000000000000000)*V^7*w^12+
      3261499560000000000000000000000*V^8+
      8642421000000000000000000000000*V^8*w^1+
      10484721120000000000000000000000*V^8*w^2+
      7696511440000000000000000000000*V^8*w^3+
      3811422945000000000000000000000*V^8*w^4+
      1343481935000000000000000000000*V^8*w^5+
      346140875000000000000000000000*V^8*w^6+
      65749525000000000000000000000*V^8*w^7+
      9142575781250000000000000000*V^8*w^8+
      907432031250000000000000000*V^8*w^9+
      60992187500000000000000000*V^8*w^10+
      2492187500000000000000000*V^8*w^11+
      46875000000000000000000*V^8*w^12+
      (-609724260000000000000000000000000)*V^9+
      (-1489431780000000000000000000000000)*V^9*w^1+
      (-1676591820000000000000000000000000)*V^9*w^2+
      (-1148060350000000000000000000000000)*V^9*w^3+
      (-531912032500000000000000000000000)*V^9*w^4+
      (-175482890000000000000000000000000)*V^9*w^5+
      (-42241550000000000000000000000000)*V^9*w^6+
      (-7474053125000000000000000000000)*V^9*w^7+
      (-965342578125000000000000000000)*V^9*w^8+
      (-88940234375000000000000000000)*V^9*w^9+
      (-5572265625000000000000000000)*V^9*w^10+
      (-214843750000000000000000000)*V^9*w^11+
      (-3906250000000000000000000)*V^9*w^12 := by
  simp [g, gvec, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, Fin.sum_univ_succ, Fin.reduceSucc, evalList]
  norm_num
  ring

end
end Erdos322Research.QuinticWeightedResultantCertificate
