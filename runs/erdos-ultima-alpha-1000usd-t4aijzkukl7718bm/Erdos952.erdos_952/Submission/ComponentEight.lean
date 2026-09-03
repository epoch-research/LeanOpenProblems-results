import Submission.FiniteCertificates
import Submission.StripObstruction

/-! A kernel-checked finite certificate for the component of 3 at squared step bound 8. -/

namespace Erdos952Investigation

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

lemma gaussian_divisor_of_congruences (a z : GaussianInt) (ha : a.norm ≠ 0)
    (hr : a.norm ∣ a.re * z.re + a.im * z.im)
    (hi : a.norm ∣ a.re * z.im - a.im * z.re) : a ∣ z := by
  obtain ⟨r, hr⟩ := hr
  obtain ⟨s, hi⟩ := hi
  refine ⟨⟨r, s⟩, ?_⟩
  apply Zsqrtd.ext
  · change z.re = a.re * r + -1 * a.im * s
    apply (mul_left_cancel₀ ha)
    rw [gaussian_norm_sq] at hr hi ⊢
    nlinarith [congrArg (a.re * ·) hr, congrArg (a.im * ·) hi]
  · change z.im = a.re * s + a.im * r
    apply (mul_left_cancel₀ ha)
    rw [gaussian_norm_sq] at hr hi ⊢
    nlinarith [congrArg (a.im * ·) hr, congrArg (a.re * ·) hi]

def smallDivisors8 : List GaussianInt :=
  [⟨1,-1⟩, ⟨1,-2⟩, ⟨1,2⟩, ⟨3,0⟩, ⟨2,-3⟩, ⟨2,3⟩, ⟨1,-4⟩,
   ⟨1,4⟩, ⟨2,-5⟩, ⟨2,5⟩, ⟨1,-6⟩, ⟨1,6⟩, ⟨4,-5⟩, ⟨4,5⟩]

def blocked8 (z : GaussianInt) : Prop :=
  z.norm ≤ 1 ∨ ∃ a ∈ smallDivisors8,
    1 < a.norm ∧ a.norm < z.norm ∧
    (a.re * z.re + a.im * z.im) % a.norm = 0 ∧
    (a.re * z.im - a.im * z.re) % a.norm = 0

instance (z : GaussianInt) : Decidable (blocked8 z) :=
  inferInstanceAs (Decidable (_ ∨ _))

lemma prime_not_blocked8 {z : GaussianInt} (hz : Prime z) : ¬ blocked8 z := by
  rintro (h | ⟨a, _, ha, haz, hr, hi⟩)
  · have hp : 0 < z.norm := GaussianInt.norm_pos.mpr hz.ne_zero
    have he : z.norm = 1 := by omega
    exact hz.not_unit ((Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) z).mp he)
  · exact not_prime_of_small_divisor
      (gaussian_divisor_of_congruences a z (by omega)
        (Int.dvd_of_emod_eq_zero hr) (Int.dvd_of_emod_eq_zero hi)) ha haz hz

def componentBits8 : ℕ → ℕ
  | 0 => 576460752336977920
  | 2 => 576460752336977920
  | 3 => 288230376218820608
  | 4 => 756604738102886400
  | 5 => 1152921504623624192
  | 6 => 2305843009222082560
  | 7 => 1441151880842444800
  | 8 => 144115188210073600
  | 10 => 180143985765908480
  | 11 => 292733980141158400
  | 12 => 45035998958059520
  | 13 => 292733980141158400
  | 14 => 147754096575442452480
  | 15 => 23062933696064520192
  | 16 => 156808583636339261440
  | 17 => 1568351548635421687808
  | 18 => 149879795598898626560
  | 19 => 24229365996349030400
  | 20 => 775519855833904742400
  | 21 => 295152408783275229184
  | 22 => 627234897489396531200
  | 23 => 302305606953070275854400
  | 24 => 755616107911902231265440
  | 25 => 25387461835235403292999701
  | 26 => 2580923165087538455128200
  | 27 => 1304572187726148520658192
  | 28 => 149891065603820748800
  | 29 => 1233741325742399244227600
  | 30 => 185080493271302144000
  | 31 => 5022198488247100837888
  | 32 => 12408356583650751457280
  | 33 => 295512767397422497792
  | 34 => 613229143261184000
  | 35 => 5788274533391663104
  | 36 => 2315002080667893760
  | 37 => 1442648676945100800
  | 38 => 155526068059504640
  | 39 => 5652610753232896
  | 40 => 757355326587535360
  | 41 => 365173448579743744
  | 42 => 9605919843287040
  | 43 => 365173448579743744
  | 44 => 757355326587535360
  | 45 => 5652610753232896
  | 46 => 155526068059504640
  | 47 => 1442648676945100800
  | 48 => 2315002080667893760
  | 49 => 5788274533391663104
  | 50 => 613229143261184000
  | 51 => 295512767397422497792
  | 52 => 12408356583650751457280
  | 53 => 5022198488247100837888
  | 54 => 185080493271302144000
  | 55 => 1233741325742399244227600
  | 56 => 149891065603820748800
  | 57 => 1304572187726148520658192
  | 58 => 2580923165087538455128200
  | 59 => 25387461835235403292999701
  | 60 => 755616107911902231265440
  | 61 => 302305606953070275854400
  | 62 => 627234897489396531200
  | 63 => 295152408783275229184
  | 64 => 775519855833904742400
  | 65 => 24229365996349030400
  | 66 => 149879795598898626560
  | 67 => 1568351548635421687808
  | 68 => 156808583636339261440
  | 69 => 23062933696064520192
  | 70 => 147754096575442452480
  | 71 => 292733980141158400
  | 72 => 45035998958059520
  | 73 => 292733980141158400
  | 74 => 180143985765908480
  | 76 => 144115188210073600
  | 77 => 1441151880842444800
  | 78 => 2305843009222082560
  | 79 => 1152921504623624192
  | 80 => 756604738102886400
  | 81 => 288230376218820608
  | 82 => 576460752336977920
  | 84 => 576460752336977920
  | _ => 0

def InComponent8 (z : GaussianInt) : Prop :=
  -42 ≤ z.re ∧ z.re ≤ 42 ∧ -42 ≤ z.im ∧ z.im ≤ 42 ∧
    (componentBits8 (z.re + 42).toNat).testBit (z.im + 42).toNat = true

instance (z : GaussianInt) : Decidable (InComponent8 z) :=
  inferInstanceAs (Decidable (_ ∧ _))

def componentRow8 (r : Fin 85) : Prop :=
  ∀ s : Fin 85, InComponent8 ⟨(r : ℤ) - 42, (s : ℤ) - 42⟩ →
    ∀ a b : Fin 5,
    ((a : ℤ) - 2) ^ 2 + ((b : ℤ) - 2) ^ 2 < 8 →
    let z : GaussianInt := ⟨(r : ℤ) - 42 + ((a : ℤ) - 2), (s : ℤ) - 42 + ((b : ℤ) - 2)⟩
    InComponent8 z ∨ blocked8 z

instance (r : Fin 85) : Decidable (componentRow8 r) :=
  inferInstanceAs (Decidable (∀ s : Fin 85, _ → ∀ a b : Fin 5, _))

private lemma component_row8_0 : componentRow8 0 := by
  decide +kernel

private lemma component_row8_1 : componentRow8 1 := by
  decide +kernel

private lemma component_row8_2 : componentRow8 2 := by
  decide +kernel

private lemma component_row8_3 : componentRow8 3 := by
  decide +kernel

private lemma component_row8_4 : componentRow8 4 := by
  decide +kernel

private lemma component_row8_5 : componentRow8 5 := by
  decide +kernel

private lemma component_row8_6 : componentRow8 6 := by
  decide +kernel

private lemma component_row8_7 : componentRow8 7 := by
  decide +kernel

private lemma component_row8_8 : componentRow8 8 := by
  decide +kernel

private lemma component_row8_9 : componentRow8 9 := by
  decide +kernel

private lemma component_row8_10 : componentRow8 10 := by
  decide +kernel

private lemma component_row8_11 : componentRow8 11 := by
  decide +kernel

private lemma component_row8_12 : componentRow8 12 := by
  decide +kernel

private lemma component_row8_13 : componentRow8 13 := by
  decide +kernel

private lemma component_row8_14 : componentRow8 14 := by
  decide +kernel

private lemma component_row8_15 : componentRow8 15 := by
  decide +kernel

private lemma component_row8_16 : componentRow8 16 := by
  decide +kernel

private lemma component_row8_17 : componentRow8 17 := by
  decide +kernel

private lemma component_row8_18 : componentRow8 18 := by
  decide +kernel

private lemma component_row8_19 : componentRow8 19 := by
  decide +kernel

private lemma component_row8_20 : componentRow8 20 := by
  decide +kernel

private lemma component_row8_21 : componentRow8 21 := by
  decide +kernel

private lemma component_row8_22 : componentRow8 22 := by
  decide +kernel

private lemma component_row8_23 : componentRow8 23 := by
  decide +kernel

private lemma component_row8_24 : componentRow8 24 := by
  decide +kernel

private lemma component_row8_25 : componentRow8 25 := by
  decide +kernel

private lemma component_row8_26 : componentRow8 26 := by
  decide +kernel

private lemma component_row8_27 : componentRow8 27 := by
  decide +kernel

private lemma component_row8_28 : componentRow8 28 := by
  decide +kernel

private lemma component_row8_29 : componentRow8 29 := by
  decide +kernel

private lemma component_row8_30 : componentRow8 30 := by
  decide +kernel

private lemma component_row8_31 : componentRow8 31 := by
  decide +kernel

private lemma component_row8_32 : componentRow8 32 := by
  decide +kernel

private lemma component_row8_33 : componentRow8 33 := by
  decide +kernel

private lemma component_row8_34 : componentRow8 34 := by
  decide +kernel

private lemma component_row8_35 : componentRow8 35 := by
  decide +kernel

private lemma component_row8_36 : componentRow8 36 := by
  decide +kernel

private lemma component_row8_37 : componentRow8 37 := by
  decide +kernel

private lemma component_row8_38 : componentRow8 38 := by
  decide +kernel

private lemma component_row8_39 : componentRow8 39 := by
  decide +kernel

private lemma component_row8_40 : componentRow8 40 := by
  decide +kernel

private lemma component_row8_41 : componentRow8 41 := by
  decide +kernel

private lemma component_row8_42 : componentRow8 42 := by
  decide +kernel

private lemma component_row8_43 : componentRow8 43 := by
  decide +kernel

private lemma component_row8_44 : componentRow8 44 := by
  decide +kernel

private lemma component_row8_45 : componentRow8 45 := by
  decide +kernel

private lemma component_row8_46 : componentRow8 46 := by
  decide +kernel

private lemma component_row8_47 : componentRow8 47 := by
  decide +kernel

private lemma component_row8_48 : componentRow8 48 := by
  decide +kernel

private lemma component_row8_49 : componentRow8 49 := by
  decide +kernel

private lemma component_row8_50 : componentRow8 50 := by
  decide +kernel

private lemma component_row8_51 : componentRow8 51 := by
  decide +kernel

private lemma component_row8_52 : componentRow8 52 := by
  decide +kernel

private lemma component_row8_53 : componentRow8 53 := by
  decide +kernel

private lemma component_row8_54 : componentRow8 54 := by
  decide +kernel

private lemma component_row8_55 : componentRow8 55 := by
  decide +kernel

private lemma component_row8_56 : componentRow8 56 := by
  decide +kernel

private lemma component_row8_57 : componentRow8 57 := by
  decide +kernel

private lemma component_row8_58 : componentRow8 58 := by
  decide +kernel

private lemma component_row8_59 : componentRow8 59 := by
  decide +kernel

private lemma component_row8_60 : componentRow8 60 := by
  decide +kernel

private lemma component_row8_61 : componentRow8 61 := by
  decide +kernel

private lemma component_row8_62 : componentRow8 62 := by
  decide +kernel

private lemma component_row8_63 : componentRow8 63 := by
  decide +kernel

private lemma component_row8_64 : componentRow8 64 := by
  decide +kernel

private lemma component_row8_65 : componentRow8 65 := by
  decide +kernel

private lemma component_row8_66 : componentRow8 66 := by
  decide +kernel

private lemma component_row8_67 : componentRow8 67 := by
  decide +kernel

private lemma component_row8_68 : componentRow8 68 := by
  decide +kernel

private lemma component_row8_69 : componentRow8 69 := by
  decide +kernel

private lemma component_row8_70 : componentRow8 70 := by
  decide +kernel

private lemma component_row8_71 : componentRow8 71 := by
  decide +kernel

private lemma component_row8_72 : componentRow8 72 := by
  decide +kernel

private lemma component_row8_73 : componentRow8 73 := by
  decide +kernel

private lemma component_row8_74 : componentRow8 74 := by
  decide +kernel

private lemma component_row8_75 : componentRow8 75 := by
  decide +kernel

private lemma component_row8_76 : componentRow8 76 := by
  decide +kernel

private lemma component_row8_77 : componentRow8 77 := by
  decide +kernel

private lemma component_row8_78 : componentRow8 78 := by
  decide +kernel

private lemma component_row8_79 : componentRow8 79 := by
  decide +kernel

private lemma component_row8_80 : componentRow8 80 := by
  decide +kernel

private lemma component_row8_81 : componentRow8 81 := by
  decide +kernel

private lemma component_row8_82 : componentRow8 82 := by
  decide +kernel

private lemma component_row8_83 : componentRow8 83 := by
  decide +kernel

private lemma component_row8_84 : componentRow8 84 := by
  decide +kernel

lemma component_rows8 : ∀ r : Fin 85, componentRow8 r := by
  intro r
  fin_cases r
  · exact component_row8_0
  · exact component_row8_1
  · exact component_row8_2
  · exact component_row8_3
  · exact component_row8_4
  · exact component_row8_5
  · exact component_row8_6
  · exact component_row8_7
  · exact component_row8_8
  · exact component_row8_9
  · exact component_row8_10
  · exact component_row8_11
  · exact component_row8_12
  · exact component_row8_13
  · exact component_row8_14
  · exact component_row8_15
  · exact component_row8_16
  · exact component_row8_17
  · exact component_row8_18
  · exact component_row8_19
  · exact component_row8_20
  · exact component_row8_21
  · exact component_row8_22
  · exact component_row8_23
  · exact component_row8_24
  · exact component_row8_25
  · exact component_row8_26
  · exact component_row8_27
  · exact component_row8_28
  · exact component_row8_29
  · exact component_row8_30
  · exact component_row8_31
  · exact component_row8_32
  · exact component_row8_33
  · exact component_row8_34
  · exact component_row8_35
  · exact component_row8_36
  · exact component_row8_37
  · exact component_row8_38
  · exact component_row8_39
  · exact component_row8_40
  · exact component_row8_41
  · exact component_row8_42
  · exact component_row8_43
  · exact component_row8_44
  · exact component_row8_45
  · exact component_row8_46
  · exact component_row8_47
  · exact component_row8_48
  · exact component_row8_49
  · exact component_row8_50
  · exact component_row8_51
  · exact component_row8_52
  · exact component_row8_53
  · exact component_row8_54
  · exact component_row8_55
  · exact component_row8_56
  · exact component_row8_57
  · exact component_row8_58
  · exact component_row8_59
  · exact component_row8_60
  · exact component_row8_61
  · exact component_row8_62
  · exact component_row8_63
  · exact component_row8_64
  · exact component_row8_65
  · exact component_row8_66
  · exact component_row8_67
  · exact component_row8_68
  · exact component_row8_69
  · exact component_row8_70
  · exact component_row8_71
  · exact component_row8_72
  · exact component_row8_73
  · exact component_row8_74
  · exact component_row8_75
  · exact component_row8_76
  · exact component_row8_77
  · exact component_row8_78
  · exact component_row8_79
  · exact component_row8_80
  · exact component_row8_81
  · exact component_row8_82
  · exact component_row8_83
  · exact component_row8_84

lemma inComponent8_finite : {z | InComponent8 z}.Finite := by
  apply (norm_sublevel_finite 3528).subset
  intro z hz
  have hr0 := hz.1
  have hr1 := hz.2.1
  have hi0 := hz.2.2.1
  have hi1 := hz.2.2.2.1
  have hr : z.re ^ 2 ≤ (42 : ℤ) ^ 2 := sq_le_sq.mpr (by
    norm_num
    exact abs_le.mpr ⟨hr0, hr1⟩)
  have hi : z.im ^ 2 ≤ (42 : ℤ) ^ 2 := sq_le_sq.mpr (by
    norm_num
    exact abs_le.mpr ⟨hi0, hi1⟩)
  simp only [Set.mem_setOf_eq, gaussian_norm_sq]
  omega

lemma three_inComponent8 : InComponent8 (3 : GaussianInt) := by decide +kernel

lemma inComponent8_closed {z w : GaussianInt} (hz : InComponent8 z)
    (hw : Prime w) (hd : (w - z).norm < 8) : InComponent8 w := by
  have hd' : (w.re - z.re)^2 + (w.im - z.im)^2 < 8 := by
    simpa only [gaussian_norm_sq, Zsqrtd.re_sub, Zsqrtd.im_sub] using hd
  have hdr : -2 ≤ w.re - z.re ∧ w.re - z.re ≤ 2 := by
    constructor <;> nlinarith [sq_nonneg (w.im - z.im)]
  have hdi : -2 ≤ w.im - z.im ∧ w.im - z.im ≤ 2 := by
    constructor <;> nlinarith [sq_nonneg (w.re - z.re)]
  have hr0 := hz.1
  have hr1 := hz.2.1
  have hi0 := hz.2.2.1
  have hi1 := hz.2.2.2.1
  let r : Fin 85 := ⟨(z.re + 42).toNat, by omega⟩
  let s : Fin 85 := ⟨(z.im + 42).toNat, by omega⟩
  let a : Fin 5 := ⟨(w.re - z.re + 2).toNat, by omega⟩
  let b : Fin 5 := ⟨(w.im - z.im + 2).toNat, by omega⟩
  have hr : (r : ℤ) - 42 = z.re := by dsimp [r]; omega
  have hs : (s : ℤ) - 42 = z.im := by dsimp [s]; omega
  have ha : (a : ℤ) - 2 = w.re - z.re := by dsimp [a]; omega
  have hb : (b : ℤ) - 2 = w.im - z.im := by dsimp [b]; omega
  have hrow := component_rows8 r s
  dsimp only at hrow
  rw [hr, hs] at hrow
  have hstep := hrow hz a b
  rw [ha, hb] at hstep
  have heq : (⟨z.re + (w.re - z.re), z.im + (w.im - z.im)⟩ : GaussianInt) = w := by
    ext <;> simp
  have hrow' : InComponent8 w ∨ blocked8 w := by
    simpa only [heq] using hstep hd'
  exact hrow'.resolve_right (prime_not_blocked8 hw)

theorem component8_certificate : ∃ S : Finset GaussianInt, MoatCertificate 8 S := by
  classical
  refine ⟨inComponent8_finite.toFinset, ?_, ?_⟩
  · simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using three_inComponent8
  · intro z hz w hw
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hz ⊢
    exact inComponent8_closed hz hw.2.1 hw.2.2.2

theorem component8_finite :
    {w | (primeGraph 8).Reachable (3 : GaussianInt) w}.Finite :=
  (fixed_component_finite_iff_certificate 8).mpr component8_certificate

#print axioms component8_finite

end Erdos952Investigation
