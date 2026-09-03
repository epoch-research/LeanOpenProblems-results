import Submission.MatrixCertificates

/-! Binary matrix certificates at the critical exponential rate. A positive
Jordan correction on powers would suffice; no such instance is asserted. -/
namespace Erdos406BinaryCriticalMatrix
open Erdos406Matrix Erdos406AffineCertificate Erdos406GroupedCertificate
open scoped BigOperators Matrix

lemma good_upper (S : ℕ → ℝ)
    (hstep : ∀ n d : ℕ, d < 2 → S (3*n+d) ≤ 3*S n)
    (n : ℕ) (hg : Nat.digits 3 n ⊆ [0,1]) :
    S n ≤ (3:ℝ)^(Nat.digits 3 n).length * S 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n; simp
    have hp : 0<n := Nat.pos_of_ne_zero hn
    have hq := ih (n/3) (Nat.div_lt_self hp (by decide)) (good_div_three hg)
    have hd : n%3<2 := by
      rcases good_unit_mod_three hp hg with hd | hd <;> omega
    have hs := hstep (n/3) (n%3) hd
    have he : 3*(n/3)+n%3=n := by omega
    rw [he] at hs
    rw [Nat.digits_of_two_le_of_pos (by decide : 2≤3) hp,List.length_cons,pow_succ]
    nlinarith

/-- On positive good integers, division by their magnitude gives an even
sharper bound controlled by S(1), independently of the empty-word budget. -/
lemma good_linear_upper (S : ℕ → ℝ) (h1 : 0≤S 1)
    (hstep : ∀ n d : ℕ, d<2 → S (3*n+d)≤3*S n)
    (n : ℕ) (hn : 0<n) (hg : Nat.digits 3 n ⊆ [0,1]) : S n≤n*S 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases he : n=1
    · subst n; simp
    have hd : n%3<2 := by
      rcases good_unit_mod_three hn hg with hh | hh <;> omega
    have hqpos : 0<n/3 := by omega
    have hq := ih (n/3) (Nat.div_lt_self hn (by decide)) hqpos (good_div_three hg)
    have hs := hstep (n/3) (n%3) hd
    have hid : 3*(n/3)+n%3=n := by omega
    rw [hid] at hs
    have hle : 3*(n/3:ℕ)≤n := by omega
    have hleR : 3*(n/3:ℕ)≤(n:ℝ) := by exact_mod_cast hle
    have hm := mul_le_mul_of_nonneg_right hleR h1
    nlinarith

lemma critical_exponent_bound (S : ℕ → ℝ) (γ C : ℝ) (h1 : 0≤S 1)
    (hstep : ∀ n d : ℕ, d<2 → S (3*n+d)≤3*S n)
    (hpower : ∀ k : ℕ, γ*k*(2:ℝ)^k≤S (2^k)+C*(2:ℝ)^k)
    (k : ℕ) (hg : Nat.digits 3 (2^k) ⊆ [0,1]) : γ*k≤S 1+C := by
  have hu := good_linear_upper S h1 hstep (2^k) (by positivity) hg
  have hp := hpower k
  have hpos : (0:ℝ)<2^k := by positivity
  apply (mul_le_mul_iff_right₀ hpos).mp
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hu
  nlinarith

/-- A polynomial correction at the exact exponential rate avoids any
logarithmic approximation. The lower bound is required only on powers. -/
theorem critical_power_criterion (S : ℕ → ℝ) (γ C : ℝ)
    (hzero : 0 ≤ S 0) (hγ : 0<γ)
    (hstep : ∀ n d : ℕ, d<2 → S (3*n+d) ≤ 3*S n)
    (hpower : ∀ k : ℕ, γ*k*(2:ℝ)^k ≤ S (2^k)+C*(2:ℝ)^k) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((3*S 0+C)/γ)
  have hN' : 3*S 0+C < (N:ℝ)*γ := (div_lt_iff₀ hγ).mp hN
  have hcut (k : ℕ) (hk : N≤k) : ¬ Nat.digits 3 (2^k) ⊆ [0,1] := by
    intro hg
    have hu := good_upper S hstep (2^k) hg
    have hp := hpower k
    have hbN := Nat.base_pow_length_digits_le 3 (2^k) (by decide) (by positivity)
    have hb : (3:ℝ)^(Nat.digits 3 (2^k)).length ≤ 3*(2:ℝ)^k := by exact_mod_cast hbN
    have hm := mul_le_mul_of_nonneg_right hb hzero
    have hp0 : (0:ℝ)<2^k := by positivity
    have hbound : γ*k ≤ 3*S 0+C := by
      apply (mul_le_mul_iff_right₀ hp0).mp
      nlinarith
    have hNk : (N:ℝ)≤k := by exact_mod_cast hk
    nlinarith
  apply Set.finite_iff_bddAbove.mpr
  refine ⟨2^N,?_⟩
  rintro n ⟨⟨k,rfl⟩,hg⟩
  have hk : k<N := by by_contra h; exact hcut k (by omega) hg
  exact Nat.pow_le_pow_right (by decide) hk.le

/-- A two-level lower ladder yields the required factor of k. -/
lemma jordan_power_lower (x y : ℕ → ℝ)
    (hx : ∀ n : ℕ, 0<n → 2*x n+2*y n ≤ x (2*n))
    (hy : ∀ n : ℕ, 0<n → 2*y n ≤ y (2*n)) :
    ∀ k : ℕ, (2:ℝ)^k*x 1+k*(2:ℝ)^k*y 1 ≤ x (2^k) := by
  have hyl : ∀ k : ℕ, (2:ℝ)^k*y 1 ≤ y (2^k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hh := hy (2^k) (by positivity)
      rw [pow_succ',pow_succ']
      nlinarith
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := hx (2^k) (by positivity)
    have hh' := hyl k
    rw [pow_succ',pow_succ']
    push_cast
    nlinarith

variable {σ : Type*} [Fintype σ]

/-- Binary matrix evaluation, with the empty word at zero. -/
def evalNat (A : ℕ → Matrix σ σ ℝ) (v0 : σ → ℝ) (n : ℕ) : σ → ℝ :=
  (Nat.digits 2 n).reverse.foldl (fun v d => A d *ᵥ v) v0

@[simp] lemma evalNat_zero (A : ℕ → Matrix σ σ ℝ) (v0 : σ → ℝ) :
    evalNat A v0 0 = v0 := by simp [evalNat]

lemma evalNat_pos (A : ℕ → Matrix σ σ ℝ) (v0 : σ → ℝ) (n : ℕ) (hn : 0<n) :
    evalNat A v0 n = A (n%2) *ᵥ evalNat A v0 (n/2) := by
  rw [evalNat,Nat.digits_of_two_le_of_pos (by decide : 2≤2) hn,List.reverse_cons]
  simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
  rfl

/-- Nonnegative binary updates and signed upper carry matrices. -/
structure Dynamics (σ : Type*) [Fintype σ] where
  A : ℕ → Matrix σ σ ℝ
  v : ℕ → (σ → ℝ)
  nonneg : ∀ d<2, ∀ i j, 0 ≤ A d i j
  initial_nonneg : 0 ≤ v 0
  recurrence : ∀ n, 0<n → v n = A (n%2) *ᵥ v (n/2)
  H : ℕ → Matrix σ σ ℝ
  seed : ∀ c<3, v c ≤ H c *ᵥ v 0
  step : ∀ c d e cp, c<3 → d<2 → e<2 → cp<3 →
    3*d+c=2*cp+e → ∀ i j, (A e * H cp) i j ≤ (H c * A d) i j

namespace Dynamics
variable (D : Dynamics σ)

lemma value_nonneg (n : ℕ) : 0 ≤ D.v n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n; exact D.initial_nonneg
    have hp : 0<n := Nat.pos_of_ne_zero hn
    have hi := ih (n/2) (Nat.div_lt_self hp (by decide))
    rw [D.recurrence n hp]
    intro i
    exact dotProduct_nonneg_of_nonneg (D.nonneg _ (Nat.mod_lt _ (by decide)) i) hi

lemma simulate (n c : ℕ) (hc : c<3) : D.v (3*n+c) ≤ D.H c *ᵥ D.v n := by
  induction n using Nat.strong_induction_on generalizing c with
  | h n ih =>
    by_cases hn : n=0
    · subst n; simpa using D.seed c hc
    have hp : 0<n := Nat.pos_of_ne_zero hn
    let d := n%2
    let cp := (3*d+c)/2
    let e := (3*d+c)%2
    have hd : d<2 := Nat.mod_lt _ (by decide)
    have hcp : cp<3 := by dsimp [cp]; omega
    have he : e<2 := Nat.mod_lt _ (by decide)
    have har : 3*d+c=2*cp+e := by dsimp [cp,e]; omega
    have hi := ih (n/2) (Nat.div_lt_self hp (by decide)) cp hcp
    have hm := Erdos406Matrix.mulVec_mono_right (D.nonneg e he) hi
    have hs := Erdos406Matrix.mulVec_mono_left (D.step c d e cp hc hd he hcp har)
      (D.value_nonneg (n/2))
    have hq : (3*n+c)/2=3*(n/2)+cp := by dsimp [cp,d]; omega
    have hr : (3*n+c)%2=e := by dsimp [e,d]; omega
    rw [D.recurrence n hp,D.recurrence (3*n+c) (by omega),hq,hr]
    rw [Matrix.mulVec_mulVec] at hm ⊢
    exact hm.trans hs

lemma construction (u : σ → ℝ) (hu : 0≤u)
    (hfinish : ∀ c<2, ∀ j, Matrix.vecMul u (D.H c) j ≤ 3*u j)
    (n c : ℕ) (hc : c<2) : u ⬝ᵥ D.v (3*n+c) ≤ 3*(u ⬝ᵥ D.v n) := by
  have hh := Erdos406Matrix.dot_mono_right hu (D.simulate n c (by omega))
  have hf := Erdos406Matrix.dot_mono_left (hfinish c hc) (D.value_nonneg n)
  rw [Matrix.dotProduct_mulVec] at hh
  have he : (fun j => 3*u j) ⬝ᵥ D.v n = 3*(u ⬝ᵥ D.v n) := by
    simp only [dotProduct,Finset.mul_sum,mul_assoc]
  rw [he] at hf
  exact hh.trans hf

lemma twice (n : ℕ) (hn : 0<n) : D.v (2*n)=D.A 0 *ᵥ D.v n := by
  rw [D.recurrence (2*n) (by omega)]
  simp

lemma jordan_lower (u r s : σ → ℝ) (hr : 0≤r) (hru : r≤u)
    (hrowr : ∀ j, 2*r j+2*s j ≤ Matrix.vecMul r (D.A 0) j)
    (hrows : ∀ j, 2*s j ≤ Matrix.vecMul s (D.A 0) j)
    (k : ℕ) : (s ⬝ᵥ D.v 1)*k*(2:ℝ)^k ≤ u ⬝ᵥ D.v (2^k) := by
  have hxr (n : ℕ) (hn : 0<n) :
      2*(r ⬝ᵥ D.v n)+2*(s ⬝ᵥ D.v n) ≤ r ⬝ᵥ D.v (2*n) := by
    have hh := Erdos406Matrix.dot_mono_left hrowr (D.value_nonneg n)
    rw [D.twice n hn,Matrix.dotProduct_mulVec]
    calc
      _ = (fun j => 2*r j+2*s j) ⬝ᵥ D.v n := by
        simp [dotProduct,Finset.sum_add_distrib,Finset.mul_sum,add_mul,mul_assoc]
      _ ≤ _ := hh
  have hys (n : ℕ) (hn : 0<n) : 2*(s ⬝ᵥ D.v n) ≤ s ⬝ᵥ D.v (2*n) := by
    have hh := Erdos406Matrix.dot_mono_left hrows (D.value_nonneg n)
    rw [D.twice n hn,Matrix.dotProduct_mulVec]
    calc
      _ = (fun j => 2*s j) ⬝ᵥ D.v n := by simp [dotProduct,Finset.mul_sum,mul_assoc]
      _ ≤ _ := hh
  have hh := jordan_power_lower (fun n => r ⬝ᵥ D.v n) (fun n => s ⬝ᵥ D.v n) hxr hys k
  have hnon := dotProduct_nonneg_of_nonneg hr (D.value_nonneg 1)
  have hdom := Erdos406Matrix.dot_mono_left hru (D.value_nonneg (2^k))
  have hpow : (0:ℝ)≤2^k := by positivity
  nlinarith

/-- The exact original finiteness conclusion, CONDITIONAL on a binary matrix
instance with a genuinely positive Jordan seed. No such instance is supplied. -/
theorem finiteness (u r s : σ → ℝ) (hu : 0≤u) (hr : 0≤r) (hru : r≤u)
    (hfinish : ∀ c<2, ∀ j, Matrix.vecMul u (D.H c) j ≤ 3*u j)
    (hrowr : ∀ j, 2*r j+2*s j ≤ Matrix.vecMul r (D.A 0) j)
    (hrows : ∀ j, 2*s j ≤ Matrix.vecMul s (D.A 0) j)
    (hseed : 0<s ⬝ᵥ D.v 1) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  apply critical_power_criterion (fun n => u ⬝ᵥ D.v n) (s ⬝ᵥ D.v 1) 0
    (dotProduct_nonneg_of_nonneg hu D.initial_nonneg) hseed
    (D.construction u hu hfinish)
  intro k
  simpa using D.jordan_lower u r s hr hru hrowr hrows k

end Dynamics
end Erdos406BinaryCriticalMatrix
