import Submission.BinaryCriticalPeriodicNecessity

/-! Every ternary predecessor depth imposes a critical periodic-growth
condition. These are necessary conditions for a potential, not a sufficient
certificate and not a proof of Erdős 406. -/
namespace Erdos406BinaryCriticalTower
open Erdos406BinaryCriticalGuard

lemma guarded_zero_ladder (S : ℕ → ℝ) (r : ℕ)
    (hstep : ∀ n : ℕ, 0<n → Nat.digits 3 (n%3^r) ⊆ [0,1] →
      ∀ d : Fin 2, S (3*n+d.val)≤3*S n)
    (n : ℕ) (hn : 0<n) (hg : Nat.digits 3 (n%3^r) ⊆ [0,1]) (s : ℕ) :
    Nat.digits 3 ((3^s*n)%3^r) ⊆ [0,1] ∧ S (3^s*n)≤(3:ℝ)^s*S n := by
  induction s with
  | zero => simpa using And.intro hg (le_refl (S n))
  | succ s ih =>
    have hp : 0<3^s*n := by positivity
    have hh := hstep _ hp ih.1 0
    have hhg := good_residue_step r (3^s*n) 0 ih.1
    have he : 3^(s+1)*n=3*(3^s*n) := by rw [pow_succ']; ring
    simp only [Fin.val_zero,add_zero] at hh hhg
    rw [he]
    refine ⟨hhg,?_⟩
    rw [pow_succ']
    nlinarith [ih.2]

lemma guarded_zero_one_bound (S : ℕ → ℝ) (r : ℕ)
    (hstep : ∀ n : ℕ, 0<n → Nat.digits 3 (n%3^r) ⊆ [0,1] →
      ∀ d : Fin 2, S (3*n+d.val)≤3*S n)
    (n : ℕ) (hn : 0<n) (hg : Nat.digits 3 (n%3^r) ⊆ [0,1]) (s : ℕ) :
    Nat.digits 3 ((3^(s+1)*n+1)%3^r) ⊆ [0,1] ∧
      S (3^(s+1)*n+1)≤(3:ℝ)^(s+1)*S n := by
  have hh := guarded_zero_ladder S r hstep n hn hg s
  have hp : 0<3^s*n := by positivity
  have hs := hstep _ hp hh.1 1
  have hg' := good_residue_step r (3^s*n) 1 hh.1
  have he : 3^(s+1)*n=3*(3^s*n) := by rw [pow_succ']; ring
  simp only [Fin.val_one] at hs hg'
  rw [he]
  refine ⟨hg',?_⟩
  rw [pow_succ']
  nlinarith [hh.2]

def towerPred (s h : ℕ) : ℕ := (4^(3^s*h)-1)/3^(s+1)

lemma tower_identity (s h : ℕ) : 3^(s+1)*towerPred s h+1=4^(3^s*h) := by
  have hp : 1≤(4:ℕ)^(3^s*h) := Nat.one_le_pow _ _ (by decide)
  have hm := (Erdos406Work.four_pow_mod_eq_one_iff s (3^s*h)).mpr (dvd_mul_right _ _)
  have hd := (Nat.modEq_iff_dvd' hp).mp hm.symm
  dsimp [towerPred]
  rw [Nat.mul_div_cancel' hd,Nat.sub_add_cancel hp]

lemma tower_pos (s h : ℕ) (hh : 0<h) : 0<towerPred s h := by
  have hp : 1<(4:ℕ)^(3^s*h) := one_lt_pow₀ (by decide) (by positivity)
  have hi := tower_identity s h
  by_contra hn
  have hz : towerPred s h=0 := by omega
  rw [hz,mul_zero,zero_add] at hi
  omega

lemma tower_guard_zero (s r j : ℕ) : towerPred s (3^r*j)%3^r=0 := by
  have hp : 1≤(4:ℕ)^(3^(s+r)*j) := Nat.one_le_pow _ _ (by decide)
  have hm := (Erdos406Work.four_pow_mod_eq_one_iff (s+r) (3^(s+r)*j)).mpr
    (dvd_mul_right _ _)
  have hd := (Nat.modEq_iff_dvd' hp).mp hm.symm
  have hi := tower_identity s (3^r*j)
  have hexp : 3^s*(3^r*j)=3^(s+r)*j := by rw [pow_add]; ring
  rw [hexp] at hi
  have hsub : 4^(3^(s+r)*j)-1=3^(s+1)*towerPred s (3^r*j) := by omega
  have hden : 3^(s+r+1)=3^(s+1)*3^r := by rw [← pow_add]; congr 1; omega
  rw [hden,hsub] at hd
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mul_dvd_mul_left (by positivity) hd)

/-- A depth-(s+1) predecessor is guarded when its repetition count is a
multiple of 3^r. Appending s zero ternary digits and then one reaches a power. -/
lemma tower_lower (S : ℕ → ℝ) (r s : ℕ) (γ B : ℝ)
    (hstep : ∀ n : ℕ, 0<n → Nat.digits 3 (n%3^r) ⊆ [0,1] →
      ∀ d : Fin 2, S (3*n+d.val)≤3*S n)
    (hpower : ∀ k : ℕ, Nat.digits 3 (2^k%3^r) ⊆ [0,1] →
      γ*k*(2:ℝ)^k≤S (2^k)+B*(2:ℝ)^k)
    (j : ℕ) (hj : 0<j) :
    γ*(2*(3^(s+r)*j):ℕ)*(4:ℝ)^(3^(s+r)*j)≤
      (3:ℝ)^(s+1)*S (towerPred s (3^r*j))+B*(4:ℝ)^(3^(s+r)*j) := by
  have hn := tower_pos s (3^r*j) (by positivity)
  have hg : Nat.digits 3 (towerPred s (3^r*j)%3^r) ⊆ [0,1] := by
    rw [tower_guard_zero]; simp
  have hs := guarded_zero_one_bound S r hstep _ hn hg s
  rw [tower_identity] at hs
  have he : 3^s*(3^r*j)=3^(s+r)*j := by rw [pow_add]; ring
  rw [he] at hs
  have hpow : (2:ℕ)^(2*(3^(s+r)*j))=4^(3^(s+r)*j) := by
    norm_num only [pow_mul,Nat.reducePow]
  have hp := hpower (2*(3^(s+r)*j)) (by simpa only [hpow] using hs.1)
  have hpowR : (2:ℝ)^(2*(3^(s+r)*j))=4^(3^(s+r)*j) := by
    rw [pow_mul]; norm_num
  rw [hpow,hpowR] at hp
  linarith [hs.2]

/-- There is one necessary critical slope for every denominator 3^(s+1),
not just for the first alternating-binary predecessor family. -/
theorem tower_slope_lower (S : ℕ → ℝ) (r s : ℕ) (γ B D C : ℝ)
    (hstep : ∀ n : ℕ, 0<n → Nat.digits 3 (n%3^r) ⊆ [0,1] →
      ∀ d : Fin 2, S (3*n+d.val)≤3*S n)
    (hpower : ∀ k : ℕ, Nat.digits 3 (2^k%3^r) ⊆ [0,1] →
      γ*k*(2:ℝ)^k≤S (2^k)+B*(2:ℝ)^k)
    (hu : ∀ j : ℕ, 0<j → S (towerPred s (3^r*j))≤
      (D*j+C)*(4:ℝ)^(3^(s+r)*j)) :
    2*γ*(3:ℝ)^(s+r)≤(3:ℝ)^(s+1)*D := by
  by_contra h
  have he : 0<2*γ*(3:ℝ)^(s+r)-(3:ℝ)^(s+1)*D := by linarith
  obtain ⟨j,hj⟩ := exists_nat_gt (((3:ℝ)^(s+1)*C+B)/
    (2*γ*(3:ℝ)^(s+r)-(3:ℝ)^(s+1)*D))
  have hj' := (div_lt_iff₀ he).mp hj
  have hl := tower_lower S r s γ B hstep hpower (j+1) (by omega)
  have hh := hu (j+1) (by omega)
  norm_num only [Nat.cast_add,Nat.cast_one] at hh
  have hp : (0:ℝ)<4^(3^(s+r)*(j+1)) := by positivity
  have hb : γ*(2*(3^(s+r)*(j+1)):ℕ)≤(3:ℝ)^(s+1)*(D*(j+1)+C)+B := by
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith [mul_le_mul_of_nonneg_left hh (show (0:ℝ)≤3^(s+1) by positivity)]
  push_cast at hb
  nlinarith

/-- Uniformly bounded normalized values along even one level of this tower
are incompatible with a positive critical seed and the construction law. -/
theorem no_bounded_tower_predecessors (S : ℕ → ℝ) (r s : ℕ) (γ B : ℝ)
    (hγ : 0<γ)
    (hstep : ∀ n : ℕ, 0<n → Nat.digits 3 (n%3^r) ⊆ [0,1] →
      ∀ d : Fin 2, S (3*n+d.val)≤3*S n)
    (hpower : ∀ k : ℕ, Nat.digits 3 (2^k%3^r) ⊆ [0,1] →
      γ*k*(2:ℝ)^k≤S (2^k)+B*(2:ℝ)^k) :
    ¬ ∃ C : ℝ, ∀ j : ℕ, 0<j →
      S (towerPred s (3^r*j))≤C*(4:ℝ)^(3^(s+r)*j) := by
  rintro ⟨C,hC⟩
  have hh := tower_slope_lower S r s γ B 0 C hstep hpower (by simpa using hC)
  have hp : 0<2*γ*(3:ℝ)^(s+r) := by positivity
  simp only [mul_zero] at hh
  linarith

#print axioms tower_identity
#print axioms tower_guard_zero
#print axioms tower_lower
#print axioms tower_slope_lower
#print axioms no_bounded_tower_predecessors
end Erdos406BinaryCriticalTower
