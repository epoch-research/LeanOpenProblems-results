import Submission.ComponentEight
import Submission.OctantReduction

/-! Data for a bound-ten fixed-seed moat certificate, reduced to one octant. -/
namespace Erdos952Investigation
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def smallDivisors10 : List GaussianInt :=
  [⟨1,-1⟩, ⟨1,-2⟩, ⟨1,2⟩, ⟨3,0⟩, ⟨2,-3⟩, ⟨2,3⟩, ⟨1,-4⟩, ⟨1,4⟩, ⟨2,-5⟩, ⟨2,5⟩, ⟨1,-6⟩, ⟨1,6⟩, ⟨4,-5⟩, ⟨4,5⟩, ⟨7,0⟩, ⟨2,-7⟩, ⟨2,7⟩, ⟨5,-6⟩, ⟨5,6⟩, ⟨3,-8⟩, ⟨3,8⟩, ⟨5,-8⟩, ⟨5,8⟩]

def blocked10 (z : GaussianInt) : Prop :=
  z.norm ≤ 1 ∨ ∃ a ∈ smallDivisors10,
    1 < a.norm ∧ a.norm < z.norm ∧
    (a.re * z.re + a.im * z.im) % a.norm = 0 ∧
    (a.re * z.im - a.im * z.re) % a.norm = 0

instance (z : GaussianInt) : Decidable (blocked10 z) :=
  inferInstanceAs (Decidable (_ ∨ _))

lemma prime_not_blocked10 {z : GaussianInt} (hz : Prime z) : ¬ blocked10 z := by
  rintro (h | ⟨a, _, ha, haz, hr, hi⟩)
  · have hp : 0 < z.norm := GaussianInt.norm_pos.mpr hz.ne_zero
    have he : z.norm = 1 := by omega
    exact hz.not_unit ((Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) z).mp he)
  · exact not_prime_of_small_divisor
      (gaussian_divisor_of_congruences a z (by omega)
        (Int.dvd_of_emod_eq_zero hr) (Int.dvd_of_emod_eq_zero hi)) ha haz hz

def octantBits10 : ℕ → ℕ
  | 1 => 2
  | 2 => 2
  | 3 => 5
  | 4 => 2
  | 5 => 20
  | 6 => 34
  | 7 => 5
  | 8 => 168
  | 9 => 16
  | 10 => 650
  | 11 => 81
  | 12 => 128
  | 13 => 5380
  | 14 => 2562
  | 15 => 16404
  | 16 => 546
  | 17 => 5380
  | 18 => 131232
  | 19 => 83009
  | 20 => 534666
  | 21 => 1040
  | 22 => 172064
  | 23 => 5509377
  | 24 => 524322
  | 25 => 21057616
  | 26 => 35654178
  | 27 => 5243908
  | 28 => 33595424
  | 29 => 66640
  | 30 => 545269760
  | 31 => 1141965905
  | 32 => 142647336
  | 33 => 4564451588
  | 34 => 539003424
  | 35 => 17268277508
  | 36 => 34897133602
  | 37 => 5637406980
  | 38 => 42115208
  | 39 => 17179935744
  | 40 => 8598456330
  | 41 => 17248043024
  | 42 => 42082336
  | 43 => 5498904515841
  | 44 => 2751466078720
  | 45 => 296352825604
  | 46 => 2749352151040
  | 47 => 1078985989
  | 48 => 149705388597248
  | 49 => 89147416051792
  | 50 => 9348131195008
  | 51 => 1099512758288
  | 52 => 35364928487592
  | 53 => 1380027732992
  | 54 => 2201204295682
  | 55 => 4402408608080
  | 56 => 2748812659202
  | 57 => 4299161860
  | 58 => 137606733992
  | 59 => 17264821313
  | 60 => 140131835904
  | 61 => 18337514496
  | 62 => 8598462464
  | 63 => 1378684502016
  | 64 => 570952192
  | 65 => 361062809940
  | 66 => 2233919864834
  | 67 => 1099785568261
  | 68 => 8830461149184
  | 69 => 1099578736640
  | 70 => 2886218022912
  | 71 => 85966454784
  | 72 => 137438953472
  | 73 => 5637144576
  | 74 => 584685977600
  | 75 => 292124884992
  | 76 => 2785286291456
  | 77 => 1100585369600
  | 78 => 8830452760576
  | 79 => 1168231104512
  | 80 => 2207613190144
  | 81 => 1116691496960
  | 82 => 8967891714048
  | 84 => 2199023255552
  | _ => 0

def InOctantComponent10 (z : GaussianInt) : Prop :=
  0 ≤ z.im ∧ z.im ≤ z.re ∧ z.re ≤ 84 ∧
    (octantBits10 z.re.toNat).testBit z.im.toNat = true

instance (z : GaussianInt) : Decidable (InOctantComponent10 z) :=
  inferInstanceAs (Decidable (_ ∧ _))

def InComponent10 (z : GaussianInt) : Prop :=
  InOctantComponent10 (OctantReduction.fold z)

instance (z : GaussianInt) : Decidable (InComponent10 z) :=
  inferInstanceAs (Decidable (InOctantComponent10 _))

local instance (z : GaussianInt) : Decidable (OctantReduction.InOctant z) :=
  inferInstanceAs (Decidable (_ ∧ _))

def componentRow10 (r : Fin 85) : Prop :=
  ∀ s : Fin 85, InOctantComponent10 ⟨(r : ℤ),(s : ℤ)⟩ →
    ∀ a b : Fin 7,
    ((a : ℤ)-3)^2+((b : ℤ)-3)^2 < 10 →
    let z : GaussianInt := ⟨(r : ℤ)+((a : ℤ)-3),(s : ℤ)+((b : ℤ)-3)⟩
    OctantReduction.InOctant z → InOctantComponent10 z ∨ blocked10 z

instance (r : Fin 85) : Decidable (componentRow10 r) :=
  inferInstanceAs (Decidable (∀ s : Fin 85, _ → ∀ a b : Fin 7, _))
end Erdos952Investigation
