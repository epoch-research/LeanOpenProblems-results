import Submission.ProgressionIncrementParameters

/-! Polynomial dependence of the progression-increment threshold on the
requested progression length, using polynomial quadratic recurrence. -/
namespace Erdos3PolynomialProgressionThresholds
open Erdos3ProgressionIncrementParameters Erdos3BohrQuadraticFlattening
  Erdos3SimultaneousQuadraticRecurrence Erdos3PolynomialMixedRecurrence
  Erdos3RelativeStableBohr
open scoped Classical
set_option maxHeartbeats 3000000
set_option maxRecDepth 3000

/-- A natural-valued function is bounded by a polynomial of a specified degree.
The +1 on the left allows uniform composition and includes the zero function. -/
def HasPolyBound (f : ℕ → ℕ) (e : ℕ) : Prop :=
  ∃ C : ℕ, ∀ n, f n+1 ≤ C*(n+1)^e

lemma poly_id : HasPolyBound id 1 := by
  refine ⟨1,?_⟩
  intro n
  simp

lemma HasPolyBound.congr {f g : ℕ → ℕ} {e : ℕ}
    (hf : HasPolyBound f e) (hfg : ∀ n, f n = g n) : HasPolyBound g e := by
  obtain ⟨C,hC⟩ := hf
  exact ⟨C,fun n ↦ by rw [← hfg]; exact hC n⟩

lemma HasPolyBound.affine {f : ℕ → ℕ} {e : ℕ}
    (hf : HasPolyBound f e) (a b : ℕ) : HasPolyBound (fun n ↦ a*f n+b) e := by
  obtain ⟨C,hC⟩ := hf
  refine ⟨(a+b+1)*C,?_⟩
  intro n
  calc
    _ ≤ (a+b+1)*(f n+1) := by nlinarith only [show 0 ≤ b*f n from Nat.zero_le _]
    _ ≤ (a+b+1)*(C*(n+1)^e) := Nat.mul_le_mul_left _ (hC n)
    _ = _ := by ring

lemma HasPolyBound.mul {f g : ℕ → ℕ} {e d : ℕ}
    (hf : HasPolyBound f e) (hg : HasPolyBound g d) :
    HasPolyBound (fun n ↦ f n*g n) (e+d) := by
  obtain ⟨C,hC⟩ := hf
  obtain ⟨D,hD⟩ := hg
  refine ⟨C*D,?_⟩
  intro n
  calc
    _ ≤ (f n+1)*(g n+1) := by nlinarith only [show 0 ≤ f n+g n from Nat.zero_le _]
    _ ≤ (C*(n+1)^e)*(D*(n+1)^d) := Nat.mul_le_mul (hC n) (hD n)
    _ = _ := by rw [pow_add]; ring

lemma HasPolyBound.pow {f : ℕ → ℕ} {e : ℕ}
    (hf : HasPolyBound f e) (k : ℕ) : HasPolyBound (fun n ↦ (f n)^k) (e*k) := by
  obtain ⟨C,hC⟩ := hf
  refine ⟨2*C^k,?_⟩
  intro n
  have hp : 1 ≤ (f n+1)^k := Nat.one_le_pow _ _ (by omega)
  calc
    _ ≤ 2*(f n+1)^k := by
      have hh := Nat.pow_le_pow_left (show f n ≤ f n+1 by omega) k
      dsimp only
      omega
    _ ≤ 2*(C*(n+1)^e)^k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hC n) k)
    _ = _ := by rw [mul_pow,pow_mul]; ring

lemma HasPolyBound.comp {f g : ℕ → ℕ} {e d : ℕ}
    (hf : HasPolyBound f e) (hg : HasPolyBound g d) :
    HasPolyBound (fun n ↦ f (g n)) (d*e) := by
  obtain ⟨C,hC⟩ := hf
  obtain ⟨D,hD⟩ := hg
  refine ⟨C*D^e,?_⟩
  intro n
  calc
    _ ≤ C*(g n+1)^e := hC _
    _ ≤ C*(D*(n+1)^d)^e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hD n) e)
    _ = _ := by rw [mul_pow,pow_mul]; ring

lemma roundedScale_nat_bound (A : ℕ) (r : ℝ) :
    roundedScale (A : ℝ) r+1 ≤ (incrementPrecision r+2)*(A+1) := by
  have hs : 64/r ≤ (incrementPrecision r : ℝ) := by
    apply (Nat.le_ceil _).trans
    simp only [incrementPrecision,roundedScale,Nat.cast_add,Nat.cast_one,mul_one]
    linarith
  have hmul : 64*(A : ℝ)/r ≤ ((A*incrementPrecision r : ℕ) : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg A)
    simpa only [Nat.cast_mul] using (show 64*(A : ℝ)/r ≤ (A : ℝ)*incrementPrecision r by
      calc
        _ = (A : ℝ)*(64/r) := by ring
        _ ≤ _ := hh)
  have hc : ⌈64*(A : ℝ)/r⌉₊ ≤ A*incrementPrecision r := Nat.ceil_le.mpr hmul
  unfold roundedScale
  nlinarith only [hc,show 0 ≤ incrementPrecision r from Nat.zero_le _]

lemma HasPolyBound.rounded {f : ℕ → ℕ} {e : ℕ}
    (hf : HasPolyBound f e) (r : ℝ) :
    HasPolyBound (fun n ↦ roundedScale (f n : ℝ) r) e := by
  obtain ⟨C,hC⟩ := hf
  refine ⟨(incrementPrecision r+2)*C,?_⟩
  intro n
  exact (roundedScale_nat_bound (f n) r).trans
    (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (incrementPrecision r+2) (hC n))

lemma pow_clog_two_le (M : ℕ) : 2^(Nat.clog 2 M) ≤ 2*(M+1) := by
  by_cases hM : 1 < M
  · have hpos : 0 < Nat.clog 2 M := Nat.clog_pos (by decide) hM
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hM
    rw [show Nat.clog 2 M = (Nat.clog 2 M).pred+1 from (Nat.succ_pred_eq_of_pos hpos).symm, pow_succ]
    omega
  · interval_cases M <;> norm_num

lemma recurrence_flatten_bound (M s : ℕ) :
    recurrenceBound 1 (flattenAccuracy M s)+1 ≤
      (2^(11*s+72)+2)*(M+1)^22 := by
  have he : recurrenceBound 1 (flattenAccuracy M s)+1 =
      2^(11*s+50)*(2^(Nat.clog 2 M))^22+2 := by
    change 2^(0+11*(2*Nat.clog 2 M+s+1)+39)+1+1 = _
    rw [show 0+11*(2*Nat.clog 2 M+s+1)+39 =
      (11*s+50)+(Nat.clog 2 M)*22 by omega, pow_add, pow_mul]
  rw [he]
  have hp : 1 ≤ (M+1)^22 := Nat.one_le_pow _ _ (by omega)
  calc
    _ ≤ 2^(11*s+50)*(2*(M+1))^22+2*(M+1)^22 :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (pow_clog_two_le M) 22))
        (Nat.mul_le_mul_left 2 hp)
    _ = _ := by
      rw [mul_pow,← Nat.mul_assoc,← pow_add,
        show 11*s+50+22 = 11*s+72 by omega]
      ring

lemma recurrence_flatten_poly (s : ℕ) :
    HasPolyBound (fun M ↦ recurrenceBound 1 (flattenAccuracy M s)) 22 :=
  ⟨2^(11*s+72)+2,fun M ↦ recurrence_flatten_bound M s⟩

lemma incrementLocalLength_poly (r : ℝ) :
    HasPolyBound (fun L ↦ incrementLocalLength L r) 3 := by
  have hn : HasPolyBound (fun L ↦ incrementLinearMesh L r) 1 := poly_id.rounded r
  have hp := ((hn.affine 2 1).pow 2).mul poly_id
  exact (hp.rounded r).congr (fun L ↦ by
    simp only [incrementLocalLength,Nat.cast_mul,Function.id_def])

lemma incrementCoarseLength_poly (r : ℝ) :
    HasPolyBound (fun L ↦ incrementCoarseLength L r) 69 := by
  have hM := incrementLocalLength_poly r
  have hrec := (recurrence_flatten_poly (Nat.clog 2 (incrementPrecision r))).comp hM
  have hp := hrec.mul hM
  exact (hp.rounded r).congr (fun L ↦ by
    simp only [incrementCoarseLength,incrementAccuracy,Nat.cast_mul])

lemma incrementCoarseMesh_poly (D : ℕ) (r : ℝ) :
    HasPolyBound (fun L ↦ incrementCoarseMesh D L r) 69 := by
  apply ((incrementCoarseLength_poly r).affine
    (256*windowDenominator D (incrementPrecision r)) 1).congr
  intro L
  unfold incrementCoarseMesh
  ring

/-- With rank and desired gain fixed, the full modulus threshold has degree
69*(2*rank+1) in the requested progression length. -/
theorem incrementThreshold_poly (D : ℕ) (r : ℝ) :
    HasPolyBound (fun L ↦ incrementThreshold D L r) (69*(2*D+1)) := by
  have hn := incrementCoarseMesh_poly D r
  have hK := incrementCoarseLength_poly r
  have hT := (((hn.affine 2 1).pow (2*D)).mul hK).affine (257^(2*D)) 0
  have hT' : HasPolyBound (fun L ↦ incrementTerminalCost D L r) (69*(2*D+1)) := by
    rw [show 69*(2*D+1) = 69*(2*D)+69 by omega]
    apply hT.congr
    intro L
    unfold incrementTerminalCost
    ring
  exact hT'.rounded r

#print axioms recurrence_flatten_bound
#print axioms incrementThreshold_poly
end Erdos3PolynomialProgressionThresholds
