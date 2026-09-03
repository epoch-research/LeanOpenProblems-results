import Submission.AxisRankObstruction
import Submission.SignedRankSix

/-! Exact, low-bit-linear encoding of the seven-point augmented Pfaffian.
No conjecture settlement or unrestricted geometric rank bound is asserted. -/
namespace Erdos213.AxisBaseCompleteness
open AxisRankObstruction
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def coeff0 (hi : ℕ) : ℤ :=
  let s0 : Bool := hi.testBit 0
  let s1 : Bool := hi.testBit 1
  let s2 : Bool := hi.testBit 2
  let s3 : Bool := hi.testBit 3
  let s4 : Bool := hi.testBit 4
  let s5 : Bool := hi.testBit 5
  let s6 : Bool := hi.testBit 6
  let s7 : Bool := hi.testBit 7
  let s8 : Bool := hi.testBit 8
  let s9 : Bool := hi.testBit 9
  let s10 : Bool := hi.testBit 10
  let s11 : Bool := hi.testBit 11
  let s12 : Bool := hi.testBit 12
  let s13 : Bool := hi.testBit 13
  let s14 : Bool := hi.testBit 14
  (if s0 ^^ s9 ^^ s14 then (-3689648) else (3689648)) +
  (if s0 ^^ s10 ^^ s13 then (4667922) else (-4667922)) +
  (if s0 ^^ s11 ^^ s12 then (-1288430) else (1288430)) +
  (if s1 ^^ s6 ^^ s14 then (6259740) else (-6259740)) +
  (if s1 ^^ s7 ^^ s13 then (-9103185) else (9103185)) +
  (if s1 ^^ s8 ^^ s12 then (3589575) else (-3589575)) +
  (if s2 ^^ s5 ^^ s14 then (-2787148) else (2787148)) +
  (if s2 ^^ s7 ^^ s11 then (6311981) else (-6311981)) +
  (if s2 ^^ s8 ^^ s10 then (-9017333) else (9017333)) +
  (if s3 ^^ s5 ^^ s13 then (4880547) else (-4880547)) +
  (if s3 ^^ s6 ^^ s11 then (-7600411) else (7600411)) +
  (if s3 ^^ s8 ^^ s9 then (12480958) else (-12480958)) +
  (if s4 ^^ s5 ^^ s12 then (-2351195) else (2351195)) +
  (if s4 ^^ s6 ^^ s10 then (13265389) else (-13265389)) +
  (if s4 ^^ s7 ^^ s9 then (-15248194) else (15248194))

def coeff1 (hi : ℕ) : ℤ :=
  let s5 : Bool := hi.testBit 5
  let s6 : Bool := hi.testBit 6
  let s7 : Bool := hi.testBit 7
  let s8 : Bool := hi.testBit 8
  let s9 : Bool := hi.testBit 9
  let s10 : Bool := hi.testBit 10
  let s11 : Bool := hi.testBit 11
  let s12 : Bool := hi.testBit 12
  let s13 : Bool := hi.testBit 13
  let s14 : Bool := hi.testBit 14
  (if s5 ^^ s12 then (-334180) else (334180)) +
  (if s5 ^^ s13 then (2296728) else (-2296728)) +
  (if s5 ^^ s14 then (-1962548) else (1962548)) +
  (if s6 ^^ s10 then (1885436) else (-1885436)) +
  (if s6 ^^ s11 then (-3576664) else (3576664)) +
  (if s6 ^^ s14 then (2306220) else (-2306220)) +
  (if s7 ^^ s9 then (-2167256) else (2167256)) +
  (if s7 ^^ s11 then (4444531) else (-4444531)) +
  (if s7 ^^ s13 then (-3353805) else (3353805)) +
  (if s8 ^^ s9 then (5873392) else (-5873392)) +
  (if s8 ^^ s10 then (-6349483) else (6349483)) +
  (if s8 ^^ s12 then (1322475) else (-1322475)) +
  (if s9 ^^ s14 then (-4142152) else (4142152)) +
  (if s10 ^^ s13 then (5240403) else (-5240403)) +
  (if s11 ^^ s12 then (-1446445) else (1446445))

def coeff2 (hi : ℕ) : ℤ :=
  let s1 : Bool := hi.testBit 1
  let s2 : Bool := hi.testBit 2
  let s3 : Bool := hi.testBit 3
  let s4 : Bool := hi.testBit 4
  let s9 : Bool := hi.testBit 9
  let s10 : Bool := hi.testBit 10
  let s11 : Bool := hi.testBit 11
  let s12 : Bool := hi.testBit 12
  let s13 : Bool := hi.testBit 13
  let s14 : Bool := hi.testBit 14
  (if s1 ^^ s12 then (940500) else (-940500)) +
  (if s1 ^^ s13 then (-6463800) else (6463800)) +
  (if s1 ^^ s14 then (5523300) else (-5523300)) +
  (if s2 ^^ s10 then (-2362620) else (2362620)) +
  (if s2 ^^ s11 then (4481880) else (-4481880)) +
  (if s2 ^^ s14 then (-2889900) else (2889900)) +
  (if s3 ^^ s9 then (3270120) else (-3270120)) +
  (if s3 ^^ s11 then (-6706245) else (6706245)) +
  (if s3 ^^ s13 then (5060475) else (-5060475)) +
  (if s4 ^^ s9 then (-10827120) else (10827120)) +
  (if s4 ^^ s10 then (11704755) else (-11704755)) +
  (if s4 ^^ s12 then (-2437875) else (2437875)) +
  (if s9 ^^ s14 then (7831800) else (-7831800)) +
  (if s10 ^^ s13 then (-9908325) else (9908325)) +
  (if s11 ^^ s12 then (2734875) else (-2734875))

def coeff4 (hi : ℕ) : ℤ :=
  let s0 : Bool := hi.testBit 0
  let s2 : Bool := hi.testBit 2
  let s3 : Bool := hi.testBit 3
  let s4 : Bool := hi.testBit 4
  let s6 : Bool := hi.testBit 6
  let s7 : Bool := hi.testBit 7
  let s8 : Bool := hi.testBit 8
  let s12 : Bool := hi.testBit 12
  let s13 : Bool := hi.testBit 13
  let s14 : Bool := hi.testBit 14
  (if s0 ^^ s12 then (-606320) else (606320)) +
  (if s0 ^^ s13 then (4167072) else (-4167072)) +
  (if s0 ^^ s14 then (-3560752) else (3560752)) +
  (if s2 ^^ s7 then (2970344) else (-2970344)) +
  (if s2 ^^ s8 then (-8049808) else (8049808)) +
  (if s2 ^^ s14 then (5677048) else (-5677048)) +
  (if s3 ^^ s6 then (-3576664) else (3576664)) +
  (if s3 ^^ s8 then (12044942) else (-12044942)) +
  (if s3 ^^ s13 then (-9941022) else (9941022)) +
  (if s4 ^^ s6 then (11842064) else (-11842064)) +
  (if s4 ^^ s7 then (-14715506) else (14715506)) +
  (if s4 ^^ s12 then (4789070) else (-4789070)) +
  (if s6 ^^ s14 then (-8565960) else (8565960)) +
  (if s7 ^^ s13 then (12456990) else (-12456990)) +
  (if s8 ^^ s12 then (-4912050) else (4912050))

def coeff8 (hi : ℕ) : ℤ :=
  let s0 : Bool := hi.testBit 0
  let s1 : Bool := hi.testBit 1
  let s3 : Bool := hi.testBit 3
  let s4 : Bool := hi.testBit 4
  let s5 : Bool := hi.testBit 5
  let s7 : Bool := hi.testBit 7
  let s8 : Bool := hi.testBit 8
  let s10 : Bool := hi.testBit 10
  let s11 : Bool := hi.testBit 11
  let s14 : Bool := hi.testBit 14
  (if s0 ^^ s10 then (790336) else (-790336)) +
  (if s0 ^^ s11 then (-1499264) else (1499264)) +
  (if s0 ^^ s14 then (966720) else (-966720)) +
  (if s1 ^^ s7 then (-1541280) else (1541280)) +
  (if s1 ^^ s8 then (4176960) else (-4176960)) +
  (if s1 ^^ s14 then (-2945760) else (2945760)) +
  (if s3 ^^ s5 then (826336) else (-826336)) +
  (if s3 ^^ s8 then (-3270120) else (3270120)) +
  (if s3 ^^ s11 then (3576664) else (-3576664)) +
  (if s4 ^^ s5 then (-2735936) else (2735936)) +
  (if s4 ^^ s7 then (3995160) else (-3995160)) +
  (if s4 ^^ s10 then (-6242536) else (6242536)) +
  (if s5 ^^ s14 then (1979040) else (-1979040)) +
  (if s7 ^^ s11 then (-4481880) else (4481880)) +
  (if s8 ^^ s10 then (6402840) else (-6402840))

def coeff16 (hi : ℕ) : ℤ :=
  let s0 : Bool := hi.testBit 0
  let s1 : Bool := hi.testBit 1
  let s2 : Bool := hi.testBit 2
  let s4 : Bool := hi.testBit 4
  let s5 : Bool := hi.testBit 5
  let s6 : Bool := hi.testBit 6
  let s8 : Bool := hi.testBit 8
  let s9 : Bool := hi.testBit 9
  let s11 : Bool := hi.testBit 11
  let s13 : Bool := hi.testBit 13
  (if s0 ^^ s9 then (-1359344) else (1359344)) +
  (if s0 ^^ s11 then (2787694) else (-2787694)) +
  (if s0 ^^ s13 then (-2103570) else (2103570)) +
  (if s1 ^^ s6 then (2306220) else (-2306220)) +
  (if s1 ^^ s8 then (-7766535) else (7766535)) +
  (if s1 ^^ s13 then (6409935) else (-6409935)) +
  (if s2 ^^ s5 then (-1026844) else (1026844)) +
  (if s2 ^^ s8 then (4063605) else (-4063605)) +
  (if s2 ^^ s11 then (-4444531) else (4444531)) +
  (if s4 ^^ s5 then (5087131) else (-5087131)) +
  (if s4 ^^ s6 then (-5977965) else (5977965)) +
  (if s4 ^^ s9 then (10736894) else (-10736894)) +
  (if s5 ^^ s13 then (-4306365) else (4306365)) +
  (if s6 ^^ s11 then (6706245) else (-6706245)) +
  (if s8 ^^ s9 then (-11012610) else (11012610))

def coeff32 (hi : ℕ) : ℤ :=
  let s0 : Bool := hi.testBit 0
  let s1 : Bool := hi.testBit 1
  let s2 : Bool := hi.testBit 2
  let s3 : Bool := hi.testBit 3
  let s5 : Bool := hi.testBit 5
  let s6 : Bool := hi.testBit 6
  let s7 : Bool := hi.testBit 7
  let s9 : Bool := hi.testBit 9
  let s10 : Bool := hi.testBit 10
  let s12 : Bool := hi.testBit 12
  (if s0 ^^ s9 then (5048992) else (-5048992)) +
  (if s0 ^^ s10 then (-5458258) else (5458258)) +
  (if s0 ^^ s12 then (1136850) else (-1136850)) +
  (if s1 ^^ s6 then (-8565960) else (8565960)) +
  (if s1 ^^ s7 then (10644465) else (-10644465)) +
  (if s1 ^^ s12 then (-3464175) else (3464175)) +
  (if s2 ^^ s5 then (3813992) else (-3813992)) +
  (if s2 ^^ s7 then (-5569395) else (5569395)) +
  (if s2 ^^ s10 then (8702317) else (-8702317)) +
  (if s3 ^^ s5 then (-5706883) else (5706883)) +
  (if s3 ^^ s6 then (6706245) else (-6706245)) +
  (if s3 ^^ s9 then (-12044942) else (12044942)) +
  (if s5 ^^ s12 then (2327325) else (-2327325)) +
  (if s6 ^^ s10 then (-13130715) else (13130715)) +
  (if s7 ^^ s9 then (15093390) else (-15093390))

def baseValue (hi lo : ℕ) : ℤ :=
  coeff0 hi +
  (if lo.testBit 0 then -coeff1 hi else coeff1 hi) +
  (if lo.testBit 1 then -coeff2 hi else coeff2 hi) +
  (if lo.testBit 2 then -coeff4 hi else coeff4 hi) +
  (if lo.testBit 3 then -coeff8 hi else coeff8 hi) +
  (if lo.testBit 4 then -coeff16 hi else coeff16 hi) +
  (if lo.testBit 5 then -coeff32 hi else coeff32 hi)

def zeroList : List ℕ := [37436,44023,53820,211705,213691,218120,306167,332453,373567,373767,374279,433506,480264,504639,556626,568311,638741,742408,782741,830455,1004552,1092599,1266696,1314410,1354743,1458410,1528840,1540525,1592512,1616887,1663645,1722872,1723384,1723584,1764698,1790984,1879031,1883460,1885446,2043331,2053128,2059715]

def checked (hi lo : ℕ) : Bool := baseValue hi lo != 0 || zeroList.contains (hi*64+lo)

def signedBase (hi lo : ℕ) : Fin 8 → Fin 8 → ℤ :=
  !![0,952*sign (lo.testBit 0),1800*sign (lo.testBit 1),3536*sign (lo.testBit 2),960*sign (lo.testBit 3),1785*sign (lo.testBit 4),6630*sign (lo.testBit 5),1;
    -(952*sign (lo.testBit 0)),0,848*sign (hi.testBit 0),2584*sign (hi.testBit 1),1352*sign (hi.testBit 2),2023*sign (hi.testBit 3),6698*sign (hi.testBit 4),1;
    -(1800*sign (lo.testBit 1)),-(848*sign (hi.testBit 0)),0,1736*sign (hi.testBit 5),2040*sign (hi.testBit 6),2535*sign (hi.testBit 7),6870*sign (hi.testBit 8),1;
    -(3536*sign (lo.testBit 2)),-(2584*sign (hi.testBit 1)),-(1736*sign (hi.testBit 5)),0,3664*sign (hi.testBit 9),3961*sign (hi.testBit 10),7514*sign (hi.testBit 11),1;
    -(960*sign (lo.testBit 3)),-(1352*sign (hi.testBit 2)),-(2040*sign (hi.testBit 6)),-(3664*sign (hi.testBit 9)),0,825*sign (hi.testBit 12),5670*sign (hi.testBit 13),1;
    -(1785*sign (lo.testBit 4)),-(2023*sign (hi.testBit 3)),-(2535*sign (hi.testBit 7)),-(3961*sign (hi.testBit 10)),-(825*sign (hi.testBit 12)),0,4845*sign (hi.testBit 14),1;
    -(6630*sign (lo.testBit 5)),-(6698*sign (hi.testBit 4)),-(6870*sign (hi.testBit 8)),-(7514*sign (hi.testBit 11)),-(5670*sign (hi.testBit 13)),-(4845*sign (hi.testBit 14)),0,1;
    -(1),-(1),-(1),-(1),-(1),-(1),-(1),0]

lemma signed_coefficient (c : ℤ) (b : Bool) :
    (if b then -c else c)=c*sign b := by
  cases b <;> simp [sign]

lemma positive_signed_coefficient (c : ℤ) (b : Bool) :
    (if b then c else -c)= -(c*sign b) := by
  cases b <;> simp [sign]

lemma sign_xor (a b : Bool) : sign (a ^^ b)=sign a*sign b := by
  cases a <;> cases b <;> rfl

/-- The computed polynomial is exactly the actual augmented Pfaffian,
with the common nonzero coefficient divisor removed. -/
theorem pfaffian_baseValue (hi lo : ℕ) :
    SignedRankSix.pf8 (signedBase hi lo)=4080*baseValue hi lo := by
  simp only [SignedRankSix.pf8, SignedRankSix.pf6, signedBase,
    Matrix.of_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
    baseValue, coeff0, coeff1, coeff2, coeff4, coeff8, coeff16, coeff32]
  simp only [signed_coefficient, positive_signed_coefficient, sign_xor]
  ring

#print axioms pfaffian_baseValue
end Erdos213.AxisBaseCompleteness
