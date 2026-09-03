import FormalConjecturesUtil

/-!
Finite exponential moments for one event at each ternary depth. No independence
or nesting is assumed. These estimates alone do not exclude a repeated cover.
-/
namespace Erdos7TernaryExponentialMoment
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

noncomputable def hits {Ω : Type*} (A : ℕ → Ω → Prop) (n : ℕ) (x : Ω) : ℕ :=
  ∑ j ∈ Finset.range n, if A j x then 1 else 0

lemma hits_zero {Ω : Type*} (A : ℕ → Ω → Prop) (x : Ω) : hits A 0 x=0 := by
  simp [hits]

lemma hits_succ {Ω : Type*} (A : ℕ → Ω → Prop) (n : ℕ) (x : Ω) :
    hits A (n+1) x = hits A n x + if A n x then 1 else 0 := by
  classical
  simp only [hits,Finset.sum_range_succ]

lemma hits_le {Ω : Type*} (A : ℕ → Ω → Prop) (n : ℕ) (x : Ω) : hits A n x ≤ n := by
  classical
  induction n with
  | zero => simp [hits]
  | succ n ih => rw [hits_succ]; split_ifs <;> omega

lemma power_increment {Ω : Type*} (A : ℕ → Ω → Prop) (n : ℕ) (x : Ω)
    (b : ℝ) (hb : 1 ≤ b) :
    b^(hits A (n+1) x+1)-1 ≤ b^(hits A n x+1)-1 +
      if A n x then (b-1)*b^(n+1) else 0 := by
  classical
  rw [hits_succ]
  split_ifs with h
  · have hp := pow_le_pow_right₀ hb (Nat.add_le_add_right (hits_le A n x) 1)
    have he : b^(hits A n x+1+1)-1 =
        b^(hits A n x+1)-1+(b-1)*b^(hits A n x+1) := by
      rw [pow_succ]; ring
    rw [he]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hp (by linarith))
  · simp

noncomputable def moment {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (A : ℕ → Ω → Prop) (b : ℝ) (n : ℕ) : ℝ :=
  ∑ x, μ x*(b^(hits A n x+1)-1)

lemma moment_step {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (A : ℕ → Ω → Prop)
    (hμ : ∀ x,0 ≤ μ x) (b : ℝ) (hb : 1 ≤ b) (n : ℕ)
    (hA : (∑ x, if A n x then μ x else 0) ≤ (1/3 : ℝ)^(n+1)) :
    moment μ A b (n+1) ≤ moment μ A b n + (b-1)*(b/3)^(n+1) := by
  classical
  have hbm : 0 ≤ b-1 := by linarith
  have hb0 : 0 ≤ b := by linarith
  have he : (∑ x, μ x*(b^(hits A n x+1)-1 +
        if A n x then (b-1)*b^(n+1) else 0)) =
      moment μ A b n + (b-1)*b^(n+1)*(∑ x, if A n x then μ x else 0) := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  have hpow : (b-1)*b^(n+1)*(1/3 : ℝ)^(n+1) = (b-1)*(b/3)^(n+1) := by
    rw [mul_assoc,← mul_pow]
    congr 2
    ring
  calc
    moment μ A b (n+1) ≤
        ∑ x, μ x*(b^(hits A n x+1)-1 +
          if A n x then (b-1)*b^(n+1) else 0) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
        (power_increment A n x b hb) (hμ x))
    _ = _ := he
    _ ≤ moment μ A b n+(b-1)*b^(n+1)*(1/3 : ℝ)^(n+1) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hA (mul_nonneg hbm (pow_nonneg hb0 _)))
    _ = _ := by rw [hpow]

noncomputable def remainder (b : ℝ) (n : ℕ) : ℝ :=
  (b-1)*b/(3-b)*(b/3)^n

lemma remainder_step (b : ℝ) (hb : b≠3) (n : ℕ) :
    (b-1)*(b/3)^(n+1)+remainder b (n+1)=remainder b n := by
  have hd : 3-b≠0 := by intro h; apply hb; linarith
  unfold remainder
  rw [pow_succ]
  field_simp
  <;> ring

/-- The finite remainder is kept explicitly; the bound does not silently
replace a finite family by an infinite collection of independent events. -/
theorem moment_with_remainder {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (A : ℕ → Ω → Prop)
    (hμ : ∀ x,0 ≤ μ x) (hmass : (∑ x,μ x)=1)
    (b : ℝ) (hb : 1 ≤ b) (hb3 : b<3) (E : ℕ)
    (hA : ∀ j<E,(∑ x,if A j x then μ x else 0) ≤ (1/3 : ℝ)^(j+1)) :
    moment μ A b E + remainder b E ≤ 3*(b-1)/(3-b) := by
  have hd : 3-b≠0 := by linarith
  induction E with
  | zero =>
    simp only [moment,hits_zero,zero_add,pow_one,← Finset.sum_mul,hmass,one_mul]
    simp only [remainder,pow_zero,mul_one]
    apply le_of_eq
    field_simp
    <;> ring
  | succ E ih =>
    have hstep := moment_step μ A hμ b hb E (hA E (by omega))
    have hrec := remainder_step b (by linarith) E
    have hprev := ih (fun j hj => hA j (by omega))
    linarith

/-- Uniform finite bound; a strictly positive base also gives a strict
finite-cap saving via the explicit remainder. -/
theorem moment_bound {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (A : ℕ → Ω → Prop)
    (hμ : ∀ x,0 ≤ μ x) (hmass : (∑ x,μ x)=1)
    (b : ℝ) (hb : 1 ≤ b) (hb3 : b<3) (E : ℕ)
    (hA : ∀ j<E,(∑ x,if A j x then μ x else 0) ≤ (1/3 : ℝ)^(j+1)) :
    moment μ A b E ≤ 3*(b-1)/(3-b) := by
  have hh := moment_with_remainder μ A hμ hmass b hb hb3 E hA
  have hbm : 0 ≤ b-1 := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hd : 0 < 3-b := by linarith
  have hr : 0 ≤ remainder b E := by unfold remainder; positivity
  linarith

/-- Elementary weighted averaging with a retained set of mass greater than
one half. A positive baseline is not discarded on the removed points. -/
theorem exists_good_lt {Ω : Type*} [Fintype Ω] (μ f : Ω → ℝ) (G : Finset Ω)
    (hμ : ∀ x,0 ≤ μ x) (hmass : (∑ x,μ x)=1) (B T : ℝ)
    (hBT : B<T) (hbase : ∀ x,B≤f x) (hm : (∑ x,μ x*f x) ≤ T)
    (hG : (1/2 : ℝ)<∑ x ∈ G,μ x) :
    ∃ x∈G,f x<2*T-B := by
  classical
  by_contra! hn
  have hlo (x : Ω) : B+(if x∈G then 2*(T-B) else 0) ≤ f x := by
    by_cases hx : x∈G
    · rw [if_pos hx]; linarith [hn x hx]
    · rw [if_neg hx]; simpa using hbase x
  have hsum : B+2*(T-B)*(∑ x∈G,μ x) ≤ ∑ x,μ x*f x := by
    calc
      _ = ∑ x,μ x*(B+(if x∈G then 2*(T-B) else 0)) := by
        simp_rw [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hmass,one_mul]
        congr 1
        rw [Finset.mul_sum]
        simp only [mul_ite,mul_zero]
        rw [Finset.sum_ite_mem,Finset.univ_inter]
        apply Finset.sum_congr rfl
        intro x _; ring
      _ ≤ _ := Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hlo x) (hμ x))
  nlinarith

/-- The one-parameter weighted energy estimate, with the removed mass charged
at its unavoidable baseline. Families may be arbitrarily dependent. -/
theorem exists_good_energy {Ω J : Type*} [Fintype Ω] [Fintype J]
    (μ : Ω → ℝ) (A : J → ℕ → Ω → Prop) (E : J → ℕ) (w : J → ℝ)
    (hμ : ∀ x,0 ≤ μ x) (hmass : (∑ x,μ x)=1)
    (hw : ∀ j,0 ≤ w j) (hwpos : 0 < ∑ j,w j)
    (b : ℝ) (hb : 1 < b) (hb3 : b<3) (G : Finset Ω)
    (hG : (1/2 : ℝ)<∑ x∈G,μ x)
    (hA : ∀ j,∀ k<E j,(∑ x,if A j k x then μ x else 0) ≤ (1/3 : ℝ)^(k+1)) :
    ∃ x∈G, (∑ j,w j*(b^(hits (A j) (E j) x+1)-1)) <
      ((b-1)*(3+b)/(3-b))*(∑ j,w j) := by
  let S : ℝ := ∑ j,w j
  let B : ℝ := (b-1)*S
  let T : ℝ := (3*(b-1)/(3-b))*S
  let f (x : Ω) : ℝ := ∑ j,w j*(b^(hits (A j) (E j) x+1)-1)
  have hden : 0 < 3-b := by linarith
  have hsub : 0 < b-1 := by linarith
  have hb0 : 0 < b := by linarith
  have hBT : B<T := by
    have hlt : b-1 < 3*(b-1)/(3-b) := by
      apply (lt_div_iff₀ hden).mpr
      nlinarith [mul_pos hsub hb0]
    exact mul_lt_mul_of_pos_right hlt hwpos
  have hbase (x : Ω) : B ≤ f x := by
    dsimp [B,S,f]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hp := pow_le_pow_right₀ hb.le
      (show 1 ≤ hits (A j) (E j) x+1 by omega)
    simp only [pow_one] at hp
    simpa only [mul_comm (b-1)] using
      mul_le_mul_of_nonneg_left (sub_le_sub_right hp 1) (hw j)
  have hm : (∑ x,μ x*f x) ≤ T := by
    calc
      _ = ∑ j,w j*moment μ (A j) b (E j) := by
        dsimp [f,moment]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ ≤ ∑ j,w j*(3*(b-1)/(3-b)) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
          (moment_bound μ (A j) hμ hmass b hb.le hb3 (E j) (hA j)) (hw j))
      _ = T := by rw [← Finset.sum_mul]; dsimp [T,S]; ring
  obtain ⟨x,hx,hf⟩ := exists_good_lt μ f G hμ hmass B T hBT hbase hm hG
  refine ⟨x,hx,?_⟩
  have he : 2*T-B = ((b-1)*(3+b)/(3-b))*S := by
    dsimp [T,B]
    field_simp
    <;> ring
  simpa only [he,f,S] using hf

#print axioms moment_bound
#print axioms moment_with_remainder
#print axioms exists_good_lt
#print axioms exists_good_energy
end Erdos7TernaryExponentialMoment
