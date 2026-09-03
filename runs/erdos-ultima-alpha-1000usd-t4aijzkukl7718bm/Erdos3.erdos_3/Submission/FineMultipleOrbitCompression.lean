import Submission.MultipleLinearOrbitInverse

/-! Fine-error bootstrap for bounded-multiple linear orbit compression. A coarse
inverse-square approximation makes an integer determinant vanish exactly;
this then preserves any finer error and gains one extra length factor. -/
namespace Erdos3FineMultipleOrbitCompression
open Erdos3MultipleLinearOrbitInverse
open scoped Classical
set_option maxHeartbeats 3000000

/-- Once N dominates explicit polynomial parameter costs, errors at scale eps
for bounded multiples of every short dilate give an error O(D^2 H^2 eps/N)
for a single bounded denominator. -/
theorem fine_multiple_linear_orbit_inverse (α : ℝ) {N D H E : ℕ} {ε : ℝ}
    (hD : 0 < D) (hH : 0 < H)
    (hN : 8*(2*D*H)*(6*E+1) ≤ N)
    (hDN : 4*D ≤ N)
    (hdet : 4*(H*(256*D^2*H^2*E*(6*E+1))+(8*D*H^2)*E) ≤ N)
    (hε : 0 ≤ ε) (hεE : ε ≤ (E : ℝ)/(N : ℝ))
    (hgood : ∀ t < N/D, ∃ d : ℕ, ∃ b : ℤ, 0 < d ∧ d < H ∧
      |α*((d*t : ℕ) : ℝ)-(b : ℝ)| ≤ ε) :
    ∃ q : ℕ, ∃ b : ℤ, 0 < q ∧ q < 8*D*H^2 ∧
      |α*(q : ℝ)-(b : ℝ)| ≤ 32*(D : ℝ)^2*(H : ℝ)^2*ε/(N : ℝ) := by
  let C := 256*D^2*H^2*E*(6*E+1)
  let Q := 8*D*H^2
  have hN0 : 0 < N := (Nat.mul_pos (by decide) hD).trans_le hDN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hcoarse : ∀ t < N/D, ∃ d : ℕ, ∃ b : ℤ, 0 < d ∧ d < H ∧
      |α*((d*t : ℕ) : ℝ)-(b : ℝ)| ≤ (E : ℝ)/(N : ℝ) := by
    intro t ht
    obtain ⟨d,b,hd,hdH,he⟩ := hgood t ht
    exact ⟨d,b,hd,hdH,he.trans hεE⟩
  obtain ⟨q,b,hq,hqQ,he⟩ := multiple_linear_orbit_inverse α hD hH hN hcoarse
  let e : ℝ := α*(q : ℝ)-(b : ℝ)
  have heC : |e| ≤ (C : ℝ)/(N : ℝ)^2 := by
    simpa only [C,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using he
  let T := N/D
  let t := T-1
  have hT4 : 4 ≤ T := (Nat.le_div_iff_mul_le hD).mpr (by nlinarith only [hDN])
  have htT : t < T := by dsimp only [t]; omega
  have htN : t ≤ N := htT.le.trans (Nat.div_le_self N D)
  have hNt : N ≤ 4*D*t := by
    have hh := Nat.lt_mul_div_succ N hD
    change N < D*(T+1) at hh
    have hm := Nat.mul_le_mul_left D (show T+1 ≤ 4*t by dsimp only [t]; omega)
    nlinarith only [hh,hm]
  obtain ⟨d,c,hd,hdH,hefine⟩ := hgood t htT
  let a := d*t
  let err : ℝ := α*(a : ℝ)-(c : ℝ)
  have herr : |err| ≤ ε := hefine
  have haHN : a ≤ H*N := Nat.mul_le_mul hdH.le htN
  have hta : t ≤ a := by
    have hh := Nat.mul_le_mul_right t hd
    simpa only [Nat.one_mul] using hh
  have hNa : N ≤ 4*D*a := hNt.trans (Nat.mul_le_mul_left _ hta)
  let Δ : ℤ := (q : ℤ)*c-b*(a : ℤ)
  have hid : (Δ : ℝ) = (a : ℝ)*e-(q : ℝ)*err := by
    dsimp only [Δ,e,err]
    push_cast
    ring
  have hbudget : (H : ℝ)*(C : ℝ)+(Q : ℝ)*(E : ℝ) ≤ (N : ℝ)/4 := by
    have hh : 4*((H : ℝ)*(C : ℝ)+(Q : ℝ)*(E : ℝ)) ≤ N := by exact_mod_cast hdet
    linarith only [hh]
  have hdetbound : |(Δ : ℝ)| ≤ 1/4 := by
    rw [hid]
    calc
      _ ≤ |(a : ℝ)*e|+|(q : ℝ)*err| := abs_sub _ _
      _ = (a : ℝ)*|e|+(q : ℝ)*|err| := by
        rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg a : (0 : ℝ) ≤ a),
          abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
      _ ≤ ((H : ℝ)*(N : ℝ))*((C : ℝ)/(N : ℝ)^2)+(Q : ℝ)*((E : ℝ)/(N : ℝ)) := by
        apply add_le_add
        · exact mul_le_mul (by exact_mod_cast haHN) heC (abs_nonneg _) (by positivity)
        · exact mul_le_mul (by exact_mod_cast hqQ.le) (herr.trans hεE) (abs_nonneg _) (Nat.cast_nonneg Q)
      _ = ((H : ℝ)*(C : ℝ)+(Q : ℝ)*(E : ℝ))/(N : ℝ) := by field_simp
      _ ≤ 1/4 := (div_le_iff₀ hNr).mpr (by linarith only [hbudget])
  have hΔ : Δ = 0 := by
    apply Int.abs_lt_one_iff.mp
    have hh : |(Δ : ℝ)| < 1 := lt_of_le_of_lt hdetbound (by norm_num)
    exact_mod_cast hh
  have hae : (a : ℝ)*e = (q : ℝ)*err := by
    rw [hΔ,Int.cast_zero] at hid
    linarith only [hid]
  have hmul : (N : ℝ)*|e| ≤ 4*(D : ℝ)*(Q : ℝ)*ε := by
    calc
      _ ≤ (4*(D : ℝ)*(a : ℝ))*|e| :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hNa) (abs_nonneg _)
      _ = 4*(D : ℝ)*|(a : ℝ)*e| := by
        rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg a : (0 : ℝ) ≤ a)]; ring
      _ = 4*(D : ℝ)*((q : ℝ)*|err|) := by
        rw [hae,abs_mul,abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
      _ ≤ 4*(D : ℝ)*((Q : ℝ)*ε) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul (by exact_mod_cast hqQ.le) herr (abs_nonneg _) (Nat.cast_nonneg Q)
      _ = _ := by ring
  refine ⟨q,b,hq,hqQ,?_⟩
  calc
    _ ≤ 4*(D : ℝ)*(Q : ℝ)*ε/(N : ℝ) := (le_div_iff₀ hNr).mpr (by linarith only [hmul])
    _ = _ := by dsimp only [Q]; push_cast; ring

#print axioms fine_multiple_linear_orbit_inverse
end Erdos3FineMultipleOrbitCompression
