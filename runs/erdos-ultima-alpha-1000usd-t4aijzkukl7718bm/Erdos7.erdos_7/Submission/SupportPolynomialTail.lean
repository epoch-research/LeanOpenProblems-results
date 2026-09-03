import Submission.SupportLaw

/-! A polynomial continuation for cofactor support at most two. The tail
bounds below use only spacing by two, not prime counting. They are auxiliary
bounds and do not settle the unrestricted odd covering conjecture. -/
namespace Erdos7SupportPolynomialTail
open scoped BigOperators
open Erdos7CompressionSieve Erdos7KilledSieve Erdos7Distortion
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Polynomial potential for the state `(e₁,e₂)`. -/
def potential (s t : ℚ) : ℚ :=
  176*s^3/27 + 80*s^2*t/9 + 736*s^2/27 + 16*s*t^2/3 +
  64*s*t/3 + 3520*s/81 + 4*t^3/3 + 52*t^2/9 + 380*t/27 + 6580/243

def drift (s t : ℚ) : ℚ := potential (s+1) (t+s)-potential s t

def linearCoeff (s t : ℚ) : ℚ :=
  80*s^3/9 + 32*s^2*t/3 + 368*s^2/9 + 4*s*t^2 + 88*s*t/3 +
  1852*s/27 + 16*t^2/3 + 64*t/3 + 3520/81

def quadraticCoeff (s t : ℚ) : ℚ :=
  16*s^3/3 + 4*s^2*t + 212*s^2/9 + 32*s*t/3 + 368*s/9 + 80*t/9 + 736/27

def cubicCoeff (s : ℚ) : ℚ := 4*s^3/3 + 16*s^2/3 + 80*s/9 + 176/27

lemma potential_nonneg (s t : ℚ) (hs : 0 ≤ s) (ht : 0 ≤ t) : 0 ≤ potential s t := by
  unfold potential
  positivity

lemma coeffs_nonneg (s t : ℚ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 ≤ linearCoeff s t ∧ 0 ≤ quadraticCoeff s t ∧ 0 ≤ cubicCoeff s := by
  unfold linearCoeff quadraticCoeff cubicCoeff
  constructor
  · positivity
  constructor <;> positivity

lemma potential_increment (s t a : ℚ) :
    potential (s+a) (t+a*s)-potential s t =
      a*linearCoeff s t+a^2*quadraticCoeff s t+a^3*cubicCoeff s := by
  unfold potential linearCoeff quadraticCoeff cubicCoeff
  ring

lemma drift_eq (s t : ℚ) :
    drift s t = linearCoeff s t+quadraticCoeff s t+cubicCoeff s := by
  simpa [drift] using potential_increment s t 1

lemma drift_nonneg (s t : ℚ) (hs : 0 ≤ s) (ht : 0 ≤ t) : 0 ≤ drift s t := by
  rw [drift_eq]
  obtain ⟨h₁,h₂,h₃⟩ := coeffs_nonneg s t hs ht
  positivity

lemma potential_resolvent (s t : ℚ) :
    potential s t-drift s t/3 = 4/3*(1+s+t)^3 := by
  unfold drift potential
  ring

lemma natural_increment_bound (s t : ℚ) (hs : 0 ≤ s) (ht : 0 ≤ t) (a : ℕ) :
    potential (s+a) (t+a*s) ≤ potential s t+(a:ℚ)^3*drift s t := by
  by_cases ha : a=0
  · subst a; simp
  have haQ : (1:ℚ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  have h₁ : 0 ≤ (a:ℚ)^3-a := by
    nlinarith [mul_nonneg (show 0 ≤ (a:ℚ)-1 by linarith) (show 0 ≤ (a:ℚ)^2+a by positivity)]
  have h₂ : 0 ≤ (a:ℚ)^3-(a:ℚ)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ (a:ℚ)-1 by linarith) (sq_nonneg (a:ℚ))]
  obtain ⟨hc₁,hc₂,hc₃⟩ := coeffs_nonneg s t hs ht
  have he := potential_increment s t (a:ℚ)
  rw [drift_eq]
  nlinarith [mul_nonneg h₁ hc₁,mul_nonneg h₂ hc₂]

/-- Finite geometric increment law, including its terminal atom. -/
def op (E : ℕ) (q : ℕ → ℚ) (f : ℕ → ℚ) : ℚ :=
  (1-q 0)*f 0+∑ g ∈ Finset.range E,(q g-q (g+1))*f (g+1)

lemma op_eq_increments (E : ℕ) (q : ℕ → ℚ) (hq : q E=0) (f : ℕ → ℚ) :
    op E q f = f 0+∑ g ∈ Finset.range E,q g*(f (g+1)-f g) := by
  have h := chain_summation_by_parts f q E
  simpa [op,hq] using h.symm

lemma op_const (E : ℕ) (q : ℕ → ℚ) (hq : q E=0) (b : ℚ) :
    op E q (fun _ => b)=b := by
  rw [op_eq_increments E q hq]
  simp

lemma op_add (E : ℕ) (q : ℕ → ℚ) (f g : ℕ → ℚ) :
    op E q (fun a => f a+g a)=op E q f+op E q g := by
  simp only [op,mul_add,Finset.sum_add_distrib]
  ring

lemma op_mul (E : ℕ) (q : ℕ → ℚ) (b : ℚ) (f : ℕ → ℚ) :
    op E q (fun a => b*f a)=b*op E q f := by
  simp only [op,Finset.mul_sum,mul_add,mul_assoc]
  ring

lemma op_mono (E : ℕ) (q : ℕ → ℚ) (hq₀ : q 0 ≤ 1)
    (hq : ∀ g, g < E → q (g+1) ≤ q g) {f g : ℕ → ℚ} (h : ∀ a, f a ≤ g a) :
    op E q f ≤ op E q g := by
  apply add_le_add (mul_le_mul_of_nonneg_left (h 0) (by linarith))
  exact Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (h (a+1))
    (sub_nonneg.mpr (hq a (Finset.mem_range.mp ha))))

lemma increment_cube_geometric (p E : ℕ) (hp : 1 < p) (c : ℚ) (hc : 0 ≤ c) :
    op E (powerTail p c E) (fun a => (a:ℚ)^3) ≤
      c*((p:ℚ)^2+4*p+1)/(p-1)^3 := by
  have hpQ : (1:ℚ) < p := by exact_mod_cast hp
  have hp0 : (0:ℚ) < p := by linarith
  have hr : (p:ℚ)⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hpQ
  have ht := cubicGeomTail_sum (p:ℚ)⁻¹ hr E
  have hn := cubicGeomTail_nonneg (p:ℚ)⁻¹ (by positivity) hr E
  have hs : (∑ a ∈ Finset.range E,(3*(a:ℚ)^2+3*a+1)*((p:ℚ)⁻¹)^a) ≤
      cubicGeomTail (p:ℚ)⁻¹ 0 := by linarith
  have he : op E (powerTail p c E) (fun a => (a:ℚ)^3) =
      c*(p:ℚ)⁻¹*(∑ a ∈ Finset.range E,(3*(a:ℚ)^2+3*a+1)*((p:ℚ)⁻¹)^a) := by
    rw [op_eq_increments E _ (powerTail_terminal p c E)]
    norm_num only [Nat.cast_zero,zero_pow (by omega : 3≠0),zero_add]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [powerTail,if_pos (Finset.mem_range.mp ha),pow_succ]
    push_cast
    ring
  rw [he]
  apply (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ c*(p:ℚ)⁻¹)).trans_eq
  unfold cubicGeomTail
  norm_num only [Nat.cast_zero,pow_zero,mul_zero,add_zero,zero_add,one_mul]
  field_simp
  <;> ring

lemma cube_moment_small (p : ℚ) (hp : 128 ≤ p) :
    (5/4)*(p^2+4*p+1)/(p-1)^3 ≤ 4/(3*p) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p-1 := by linarith
  apply (div_le_div_iff₀ (pow_pos hp1 3) (by positivity : 0 < 3*p)).mpr
  nlinarith [mul_nonneg (sq_nonneg p) (show 0 ≤ p-108 by linarith)]

lemma finite_potential_growth (p E : ℕ) (hp : 128 ≤ p) (s t : ℚ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    op E (powerTail p (5/4) E) (fun a => potential (s+a) (t+a*s)) ≤
      potential s t+4/(3*(p:ℚ))*drift s t := by
  have hp1 : 1 < p := by omega
  have hpQ : (128:ℚ) ≤ p := by exact_mod_cast hp
  have hq0 := powerTail_zero_le_one p hp1 (5/4) (by linarith) E
  have hq := powerTail_decreasing p hp1 (5/4) (by norm_num) E
  have h := op_mono E _ hq0 (fun g _ => hq g) (natural_increment_bound s t hs ht)
  have he : op E (powerTail p (5/4) E) (fun a => potential s t+(a:ℚ)^3*drift s t) =
      potential s t+drift s t*op E (powerTail p (5/4) E) (fun a => (a:ℚ)^3) := by
    rw [op_add,op_const E _ (powerTail_terminal p (5/4) E)]
    congr 1
    simpa only [mul_comm] using op_mul E (powerTail p (5/4) E) (drift s t) (fun a => (a:ℚ)^3)
  rw [he] at h
  have hm := (increment_cube_geometric p E hp1 (5/4) (by norm_num)).trans
    (cube_moment_small (p:ℚ) (by exact_mod_cast hp))
  have hd := mul_le_mul_of_nonneg_left hm (drift_nonneg s t hs ht)
  nlinarith

lemma local_drift (p s t : ℚ) (hp : 128 ≤ p) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    125/(27*(p-1)^3)*(1+s+t)^3 +
      (potential s t+4/(3*p)*drift s t)/(p+1)^2 ≤ potential s t/(p-1)^2 := by
  have hp0 : 0 < p := by linarith
  have hm : 0 < p-1 := by linarith
  have hp' : 0 < p+1 := by linarith
  have hn : 0 ≤ 19*p^2-394*p-125 := by
    nlinarith [mul_nonneg (show 0 ≤ p-128 by linarith) hp0.le]
  have hd : 0 ≤ drift s t := drift_nonneg s t hs ht
  have he : potential s t/(p-1)^2 - (125/(27*(p-1)^3)*(1+s+t)^3 +
      (potential s t+4/(3*p)*drift s t)/(p+1)^2) =
      (36*(2*p-1)*(p-1)*drift s t+p*(19*p^2-394*p-125)*(1+s+t)^3)/
        (27*p*(p-1)^3*(p+1)^2) := by
    have hres := potential_resolvent s t
    have hf : potential s t = drift s t/3+4/3*(1+s+t)^3 := by linarith
    rw [hf]
    field_simp
    <;> ring
  have hnon : 0 ≤ (36*(2*p-1)*(p-1)*drift s t+p*(19*p^2-394*p-125)*(1+s+t)^3)/
        (27*p*(p-1)^3*(p+1)^2) := by
    have : 0 ≤ 2*p-1 := by linarith
    positivity
  linarith

/-- Uniform in every finite exponent cap; the next allowed prime need only
be at least p+2. No infinite geometric sum is dropped. -/
theorem finite_tail_step (p E : ℕ) (hp : 128 ≤ p) (s t : ℚ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    residual (5/4) ((1+s+t)/((p:ℚ)-1)) +
      op E (powerTail p (5/4) E) (fun a => potential (s+a) (t+a*s))/((p:ℚ)+1)^2 ≤
      potential s t/((p:ℚ)-1)^2 := by
  have hpQ : (128:ℚ) ≤ p := by exact_mod_cast hp
  have hm : 0 < (p:ℚ)-1 := by linarith
  have hl := residual_le_cubic (c := (5:ℚ)/4) (α := (1+s+t)/((p:ℚ)-1))
    (by norm_num) (by positivity)
  have hl' : residual (5/4) ((1+s+t)/((p:ℚ)-1)) ≤
      125/(27*((p:ℚ)-1)^3)*(1+s+t)^3 := by
    apply hl.trans_eq
    field_simp
    <;> ring
  have hg := div_le_div_of_nonneg_right (finite_potential_growth p E hp s t hs ht)
    (sq_nonneg ((p:ℚ)+1))
  exact (add_le_add hl' hg).trans (local_drift (p:ℚ) s t hpQ hs ht)

#print axioms finite_tail_step
end Erdos7SupportPolynomialTail
