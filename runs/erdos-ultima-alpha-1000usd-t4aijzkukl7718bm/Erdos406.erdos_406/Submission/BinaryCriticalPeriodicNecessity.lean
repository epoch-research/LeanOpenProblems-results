import Submission.BinaryCriticalSignedDynamics
import Submission.Work

/-! Necessary growth on periodic binary predecessors of powers. These results
reject bounded normalized predecessor potentials, not the conjecture itself. -/
namespace Erdos406BinaryCriticalPeriodic
open Erdos406BinaryCriticalGuard

def predFour (h : ℕ) : ℕ := (4^h-1)/3

lemma predFour_identity (h : ℕ) : 3*predFour h+1=4^h := by
  have hm : 4^h%3=1 := by norm_num [Nat.pow_mod]
  have hp : 1≤(4:ℕ)^h := Nat.one_le_pow h 4 (by decide)
  have hd : 3 ∣ (4:ℕ)^h-1 := by omega
  dsimp [predFour]
  rw [Nat.mul_div_cancel' hd,Nat.sub_add_cancel hp]

lemma predFour_pos {h : ℕ} (hh : 0<h) : 0<predFour h := by
  have hp : 1<4^h := one_lt_pow₀ (by decide) (by omega)
  have hi := predFour_identity h
  omega

lemma predFour_periodic_residue (r j : ℕ) :
    Nat.ModEq (3^r) (predFour (1+3^r*j)) 1 := by
  have hm := ((Erdos406Work.four_pow_mod_eq_one_iff r (3^r*j)).mpr
    (dvd_mul_right _ _)).mul_left 4
  have hh : Nat.ModEq (3^(r+1)) (4^(1+3^r*j)) 4 := by
    simpa [pow_add,pow_one] using hm
  rw [← predFour_identity] at hh
  have hc : Nat.ModEq (3^(r+1)) (3*predFour (1+3^r*j)) 3 :=
    Nat.ModEq.add_right_cancel' 1 hh
  apply Nat.ModEq.mul_left_cancel' (by decide : (3:ℕ)≠0)
  simpa [pow_succ',mul_one] using hc

lemma predFour_periodic_guard (r j : ℕ) :
    Nat.digits 3 (predFour (1+3^r*j)%3^r) ⊆ [0,1] := by
  have hh : Nat.digits 3 1 ⊆ [0,1] := by norm_num [Nat.digits_of_two_le_of_pos]
  have hg := Erdos406BinaryCertificate.good_mod hh r
  rw [predFour_periodic_residue r j]
  exact hg

lemma periodic_lower (S : ℕ → ℝ) (r : ℕ) (γ B : ℝ)
    (hstep : ∀ n : ℕ, 0<n → Nat.digits 3 (n%3^r) ⊆ [0,1] →
      ∀ d : Fin 2, S (3*n+d.val)≤3*S n)
    (hpower : ∀ k : ℕ, γ*k*(2:ℝ)^k≤S (2^k)+B*(2:ℝ)^k) (j : ℕ) :
    γ*(2*(1+3^r*j):ℕ)*(4:ℝ)^(1+3^r*j) ≤
      3*S (predFour (1+3^r*j))+B*(4:ℝ)^(1+3^r*j) := by
  have hs := hstep (predFour (1+3^r*j)) (predFour_pos (by omega))
    (predFour_periodic_guard r j) 1
  change S (3*predFour (1+3^r*j)+1)≤3*S (predFour (1+3^r*j)) at hs
  rw [predFour_identity] at hs
  have hp := hpower (2*(1+3^r*j))
  norm_num only [pow_mul,Nat.reducePow] at hp
  linarith

/-- A globally sufficient critical potential cannot remain O(4^h) on the
periodic predecessor family h=1+3^r*j, even though these inputs merely pass
its fixed residue guard and need not have all ternary digits allowed. -/
theorem no_bounded_periodic_predecessors (S : ℕ → ℝ) (r : ℕ) (γ B : ℝ)
    (hγ : 0<γ)
    (hstep : ∀ n : ℕ, 0<n → Nat.digits 3 (n%3^r) ⊆ [0,1] →
      ∀ d : Fin 2, S (3*n+d.val)≤3*S n)
    (hpower : ∀ k : ℕ, γ*k*(2:ℝ)^k≤S (2^k)+B*(2:ℝ)^k) :
    ¬ ∃ C : ℝ, ∀ j : ℕ,
      S (predFour (1+3^r*j))≤C*(4:ℝ)^(1+3^r*j) := by
  rintro ⟨C,hC⟩
  obtain ⟨j,hj⟩ := exists_nat_gt ((3*C+B)/(2*γ))
  have hγ2 : 0<2*γ := by positivity
  have hj' := (div_lt_iff₀ hγ2).mp hj
  have hl := periodic_lower S r γ B hstep hpower j
  have hu := hC j
  have hp : (0:ℝ)<4^(1+3^r*j) := by positivity
  have hb : γ*(2*(1+3^r*j):ℕ)≤3*C+B := by
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith
  have hjle : j≤1+3^r*j := by
    have hh := Nat.le_mul_of_pos_left j (by positivity : 0<3^r)
    omega
  have hjR : (j:ℝ)≤(1+3^r*j:ℕ) := by exact_mod_cast hjle
  push_cast at hb
  push_cast at hjR
  nlinarith

/-- Any linear upper slope for these normalized predecessors must meet the
critical lower slope. This justifies excluding strictly subcritical periodic
behavior during discovery without claiming that the condition is sufficient. -/
theorem periodic_slope_lower (S : ℕ → ℝ) (r : ℕ) (γ B D C : ℝ)
    (hstep : ∀ n : ℕ, 0<n → Nat.digits 3 (n%3^r) ⊆ [0,1] →
      ∀ d : Fin 2, S (3*n+d.val)≤3*S n)
    (hpower : ∀ k : ℕ, γ*k*(2:ℝ)^k≤S (2^k)+B*(2:ℝ)^k)
    (hu : ∀ j : ℕ, S (predFour (1+3^r*j))≤
      (D*j+C)*(4:ℝ)^(1+3^r*j)) : 2*γ*(3:ℝ)^r≤3*D := by
  by_contra h
  have he : 0<2*γ*(3:ℝ)^r-3*D := by linarith
  obtain ⟨j,hj⟩ := exists_nat_gt ((3*C+B-2*γ)/(2*γ*(3:ℝ)^r-3*D))
  have hj' := (div_lt_iff₀ he).mp hj
  have hl := periodic_lower S r γ B hstep hpower j
  have hh := hu j
  have hp : (0:ℝ)<4^(1+3^r*j) := by positivity
  have hb : γ*(2*(1+3^r*j):ℕ)≤3*(D*j+C)+B := by
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith
  push_cast at hb
  nlinarith

#print axioms periodic_slope_lower

#print axioms predFour_periodic_residue
#print axioms periodic_lower
#print axioms no_bounded_periodic_predecessors
end Erdos406BinaryCriticalPeriodic
