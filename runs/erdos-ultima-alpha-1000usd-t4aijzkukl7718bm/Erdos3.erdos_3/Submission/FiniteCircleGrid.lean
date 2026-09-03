import Submission.CircleIntegerApproximation
import Submission.QuadraticCircleBridge

/-! Quantization of unit complex phases into a finite cyclic group, with
uniform chord error and an explicit quadratic-relation defect. Quantization
is not asserted to preserve polynomial identities exactly. -/
namespace Erdos3FiniteCircleGrid
open Erdos3CircleIntegerApproximation Erdos3FiniteFourier
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 4000000

lemma ephase_dist_le (s t : ℝ) : ‖ephase s-ephase t‖ ≤ 8*|s-t| := by
  have he : ephase t*ephase (s-t) = ephase s := by
    unfold ephase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = ‖ephase t*(ephase (s-t)-1)‖ := by rw [mul_sub,he,mul_one]
    _ = ‖ephase (s-t)-1‖ := by rw [norm_mul,ephase_norm,one_mul]
    _ ≤ _ := by simpa only [Int.cast_zero,sub_zero] using ephase_near_integer (s-t) 0

noncomputable def roundPhase (N : ℕ) (v : ℂ) : ZMod N :=
  (⌊(N : ℝ)*unitAngle v⌋ : ℤ)

lemma standard_phase_int {N : ℕ} [NeZero N] (j : ℤ) :
    ZMod.stdAddChar (j : ZMod N) = ephase ((j : ℝ)/(N : ℝ)) := by
  rw [ZMod.stdAddChar_coe]
  unfold ephase
  congr 1
  push_cast
  ring

/-- A cyclic grid of size N approximates every unit phase with chord error
at most 8/N. The constant is deliberately rounded upwards. -/
theorem roundPhase_error {N : ℕ} [NeZero N] (v : ℂ) (hv : ‖v‖ = 1) :
    ‖ZMod.stdAddChar (roundPhase N v)-v‖ ≤ 8/(N : ℝ) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hfl := Int.floor_le ((N : ℝ)*unitAngle v)
  have hfu := Int.lt_floor_add_one ((N : ℝ)*unitAngle v)
  have hdist : |(⌊(N : ℝ)*unitAngle v⌋ : ℝ)/(N : ℝ)-unitAngle v| ≤ 1/(N : ℝ) := by
    rw [abs_sub_comm,abs_of_nonneg (by
      apply sub_nonneg.mpr
      exact (div_le_iff₀ hN).mpr (by nlinarith only [hfl]))]
    apply (le_div_iff₀ hN).mpr
    have he : (unitAngle v-(⌊(N : ℝ)*unitAngle v⌋ : ℝ)/(N : ℝ))*(N : ℝ) =
        (N : ℝ)*unitAngle v-(⌊(N : ℝ)*unitAngle v⌋ : ℝ) := by field_simp <;> ring
    rw [he]
    linarith
  rw [roundPhase,standard_phase_int]
  calc
    _ = ‖ephase ((⌊(N : ℝ)*unitAngle v⌋ : ℝ)/(N : ℝ))-ephase (unitAngle v)‖ := by
      rw [ephase_unitAngle v hv]
    _ ≤ 8*|(⌊(N : ℝ)*unitAngle v⌋ : ℝ)/(N : ℝ)-unitAngle v| := ephase_dist_le _ _
    _ ≤ 8*(1/(N : ℝ)) := mul_le_mul_of_nonneg_left hdist (by norm_num)
    _ = _ := by ring

lemma unit_mul_distance {a b c d : ℂ} (ha : ‖a‖ = 1) (hd : ‖d‖ = 1) :
    ‖a*b-c*d‖ ≤ ‖a-c‖+‖b-d‖ := by
  calc
    _ = ‖a*(b-d)+(a-c)*d‖ := by congr 1; ring
    _ ≤ ‖a*(b-d)‖+‖(a-c)*d‖ := norm_add_le _ _
    _ = _ := by rw [norm_mul,norm_mul,ha,hd,one_mul,mul_one]; ring

lemma unit_power_distance {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (n : ℕ) :
    ‖a^n-b^n‖ ≤ (n : ℝ)*‖a-b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,pow_succ]
    have h := (unit_mul_distance (a := a^n) (b := a) (c := b^n) (d := b)
      (by rw [norm_pow,ha,one_pow]) hb).trans (add_le_add ih le_rfl)
    simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using h

noncomputable def quadraticWord (a b c : ℂ) : ℂ := a*(conj b)^3*c^3

lemma quadraticWord_distance {a b c a' b' c' : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (ha' : ‖a'‖ = 1) (hb' : ‖b'‖ = 1) (hc' : ‖c'‖ = 1) :
    ‖quadraticWord a b c-quadraticWord a' b' c'‖ ≤
      ‖a-a'‖+3*‖b-b'‖+3*‖c-c'‖ := by
  have h₁ := unit_mul_distance (a := a*(conj b)^3) (b := c^3)
    (c := a'*(conj b')^3) (d := (c')^3)
    (by rw [norm_mul,norm_pow,Complex.norm_conj,ha,hb]; norm_num)
    (by rw [norm_pow,hc',one_pow])
  have h₂ := unit_mul_distance (a := a) (b := (conj b)^3)
    (c := a') (d := (conj b')^3) ha (by rw [norm_pow,Complex.norm_conj,hb',one_pow])
  have h₃ := unit_power_distance (by rwa [Complex.norm_conj] : ‖conj b‖ = 1)
    (by rwa [Complex.norm_conj] : ‖conj b'‖ = 1) 3
  have h₄ := unit_power_distance hc hc' 3
  simp only [← map_sub,Complex.norm_conj,Nat.cast_ofNat] at h₃ h₄
  change ‖quadraticWord a b c-quadraticWord a' b' c'‖ ≤ _ at h₁
  linarith

lemma standard_quadraticWord {N : ℕ} [NeZero N] (a b c : ZMod N) :
    ZMod.stdAddChar (a-3 • b+3 • c) =
      quadraticWord (ZMod.stdAddChar a) (ZMod.stdAddChar b) (ZMod.stdAddChar c) := by
  rw [AddChar.map_add_eq_mul,char_sub]
  simp only [AddChar.map_nsmul_eq_pow,map_pow,quadraticWord]

/-- Rounding four vertices of a quadratic configuration gives an approximate
identity, not an exact one. The coefficient sum is eight. -/
theorem roundPhase_quadratic_defect {N : ℕ} [NeZero N] (v : Fin 4 → ℂ)
    (hv : ∀ i, ‖v i‖ = 1) (hrel : v 3 = quadraticWord (v 0) (v 1) (v 2)) :
    ‖ZMod.stdAddChar (roundPhase N (v 3))-
      ZMod.stdAddChar (roundPhase N (v 0)-3 • roundPhase N (v 1)+3 • roundPhase N (v 2))‖ ≤
      64/(N : ℝ) := by
  have hq := quadraticWord_distance
    (a' := ZMod.stdAddChar (roundPhase N (v 0)))
    (b' := ZMod.stdAddChar (roundPhase N (v 1)))
    (c' := ZMod.stdAddChar (roundPhase N (v 2))) (hv 0) (hv 1) (hv 2)
    ((ZMod.stdAddChar (N := N)).norm_apply _) ((ZMod.stdAddChar (N := N)).norm_apply _)
    ((ZMod.stdAddChar (N := N)).norm_apply _)
  have h0 := roundPhase_error (N := N) (v 0) (hv 0)
  have h1 := roundPhase_error (N := N) (v 1) (hv 1)
  have h2 := roundPhase_error (N := N) (v 2) (hv 2)
  have h3 := roundPhase_error (N := N) (v 3) (hv 3)
  rw [standard_quadraticWord]
  have ht := dist_triangle (ZMod.stdAddChar (roundPhase N (v 3))) (v 3)
    (quadraticWord (ZMod.stdAddChar (roundPhase N (v 0)))
      (ZMod.stdAddChar (roundPhase N (v 1))) (ZMod.stdAddChar (roundPhase N (v 2))))
  simp only [dist_eq_norm] at ht
  rw [hrel] at ht h3 ⊢
  rw [norm_sub_rev] at h0 h1 h2
  rw [show 64/(N : ℝ) = 8*(8/(N : ℝ)) by ring]
  linarith only [ht,hq,h0,h1,h2,h3]

variable {I : Type*} [Fintype I]

noncomputable def gridVector {N : ℕ} [NeZero N] (v : I → ZMod N) : I → ℂ :=
  fun i ↦ ZMod.stdAddChar (v i)

lemma gridVector_rounding {N : ℕ} [NeZero N] (v : I → ℂ) (hv : ∀ i, ‖v i‖ = 1) :
    dist (gridVector (fun i ↦ roundPhase N (v i))) v ≤ 8/(N : ℝ) := by
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  exact roundPhase_error (v i) (hv i)

lemma gridVector_quadratic_defect {N : ℕ} [NeZero N] (v : Fin 4 → I → ℂ)
    (hv : ∀ j i, ‖v j i‖ = 1)
    (hrel : ∀ i, v 3 i = quadraticWord (v 0 i) (v 1 i) (v 2 i)) :
    dist (gridVector (fun i ↦ roundPhase N (v 3 i)))
      (gridVector (fun i ↦ roundPhase N (v 0 i)-3 • roundPhase N (v 1 i)+3 • roundPhase N (v 2 i))) ≤
      64/(N : ℝ) := by
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  exact roundPhase_quadratic_defect (fun j ↦ v j i) (fun j ↦ hv j i) (hrel i)

/-- Local quadraticity implies the word relation on every four-term AP lying
inside the domain. All repeated cube vertices are checked explicitly. -/
theorem local_quadratic_word {X : Type*} [AddCommGroup X] {R : Set X} (q : X → ℂ)
    (hq : ∀ x, ‖q x‖ = 1) (hpoly : Erdos3LocalQuadraticInverse.IsLocallyQuadratic R q)
    (x d : X) (hR : ∀ j : Fin 4, x+j.val • d ∈ R) :
    q (x+3 • d) = quadraticWord (q x) (q (x+d)) (q (x+2 • d)) := by
  have h0 : x ∈ R := by simpa using hR 0
  have h1 : x+d ∈ R := by simpa using hR 1
  have h2 : x+d+d ∈ R := by convert hR 2 using 1 <;> simp only [Fin.val_two] <;> module
  have h3 : x+d+d+d ∈ R := by
    have ht : x+3 • d ∈ R := hR 3
    convert ht using 1 <;> module
  have he := hpoly x d d d h0 h1 h1 h2 h1 h2 h2 h3
  have hn (x : X) : q x ≠ 0 := by intro hh; have h := hq x; rw [hh,norm_zero] at h; norm_num at h
  have hc (x : X) : conj (q x) = (q x)⁻¹ :=
    eq_inv_of_mul_eq_one_right (Erdos3FiniteUniformity.mul_conj_eq_one (hq x))
  simp only [Erdos3FiniteUniformity.derivative,map_mul,Complex.conj_inv,inv_inv,starRingEnd_self_apply,hc] at he
  have hs2 : x+d+d = x+2 • d := by module
  have hs3 : x+d+d+d = x+3 • d := by module
  rw [hs3,hs2] at he
  unfold quadraticWord
  rw [hc]
  field_simp [hn] at he ⊢
  linear_combination he

#print axioms local_quadratic_word

#print axioms roundPhase_error
#print axioms gridVector_quadratic_defect
end Erdos3FiniteCircleGrid
