import Submission.ComponentEight
namespace ComponentEightTest
open Erdos952Investigation
set_option maxHeartbeats 0
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

lemma inComponent8_closed (component_rows8 : ∀ r : Fin 85, componentRow8 r) {z w : GaussianInt} (hz : InComponent8 z)
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


end ComponentEightTest
