import Submission.BohrCovering

/-! Fixed-tolerance stable scales for finite Bohr sets.
This is a quantitative local-averaging ingredient, not the original conjecture. -/
namespace Erdos3BohrStableScale
open Finset Erdos3FiniteBohr Erdos3BohrCovering
open scoped BigOperators Classical
set_option maxHeartbeats 1500000

lemma exists_slow_step (v : ℕ → ℝ) {n : ℕ} {c K : ℝ}
    (hc : 0 ≤ c) (hv : 0 < v 0) (hend : v n ≤ K*v 0) (hgrowth : K < c^n) :
    ∃ j < n, v (j+1) ≤ c*v j := by
  by_contra! h
  have hpow (j : ℕ) (hj : j ≤ n) : c^j*v 0 ≤ v j := by
    induction j with
    | zero => simp
    | succ j ih =>
      calc
        c^(j+1)*v 0 = c*(c^j*v 0) := by rw [pow_succ]; ring
        _ ≤ c*v j := mul_le_mul_of_nonneg_left (ih (by omega)) hc
        _ ≤ v (j+1) := (h j (by omega)).le
  have hstrict := mul_lt_mul_of_pos_right hgrowth hv
  linarith [hpow n le_rfl]

lemma stability_growth {q : ℕ} (hq : 0 < q) (d : ℕ) :
    (81 : ℝ)^d < (1+1/(q : ℝ))^(q*(7*d+1)) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hb : (2 : ℝ) ≤ (1+1/(q : ℝ))^q := by
    have h := one_add_mul_le_pow (a := 1/(q : ℝ)) (le_trans (by norm_num : (-2 : ℝ) ≤ 0) (by positivity)) q
    simpa only [mul_one_div_cancel hqR, show (1 : ℝ)+1 = 2 by norm_num] using h
  calc
    (81 : ℝ)^d ≤ (128 : ℝ)^d := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = (2 : ℝ)^(7*d) := by rw [pow_mul]; norm_num
    _ < (2 : ℝ)^(7*d+1) := pow_lt_pow_right₀ (by norm_num) (by omega)
    _ ≤ ((1+1/(q : ℝ))^q)^(7*d+1) := pow_le_pow_left₀ (by norm_num) hb _
    _ = _ := (pow_mul _ _ _).symm

variable {G : Type*} [AddCommGroup G] [Fintype G]

def stabilitySteps (D : Finset (AddChar G ℂ)) (q : ℕ) : ℕ := q*(7*D.card+1)
noncomputable def stabilityWidth (D : Finset (AddChar G ℂ)) (q : ℕ) (R : ℝ) : ℝ :=
  R/(2*(stabilitySteps D q : ℝ))

lemma stabilitySteps_pos (D : Finset (AddChar G ℂ)) {q : ℕ} (hq : 0 < q) :
    0 < stabilitySteps D q := by unfold stabilitySteps; positivity

lemma stabilityWidth_pos (D : Finset (AddChar G ℂ)) {q : ℕ} (hq : 0 < q)
    {R : ℝ} (hR : 0 < R) : 0 < stabilityWidth D q R := by
  unfold stabilityWidth
  exact div_pos hR (mul_pos (by norm_num) (by exact_mod_cast stabilitySteps_pos D hq))

/-- For each fixed tolerance 1/q there is a stable radius between R and 2R,
with stability window R/(2q(7d+1)). No all-tolerances regularity is asserted. -/
theorem exists_stable_radius (D : Finset (AddChar G ℂ)) {R : ℝ} (hR : 0 < R)
    {q : ℕ} (hq : 0 < q) :
    ∃ s : ℝ, R ≤ s-stabilityWidth D q R ∧ s+stabilityWidth D q R ≤ 2*R ∧
      ((bohr D (s+stabilityWidth D q R)).card : ℝ) ≤
        (1+1/(q : ℝ))*((bohr D (s-stabilityWidth D q R)).card : ℝ) := by
  let n := stabilitySteps D q
  have hn : 0 < n := stabilitySteps_pos D hq
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let r : ℕ → ℝ := fun j ↦ R+(j : ℝ)*R/n
  let v : ℕ → ℝ := fun j ↦ (bohr D (r j)).card
  have hr0 : r 0 = R := by simp [r]
  have hrn : r n = 2*R := by dsimp [r]; field_simp; ring
  have hv0 : 0 < v 0 := by
    dsimp only [v]
    rw [hr0]
    exact_mod_cast (show (bohr D R).Nonempty from ⟨0,bohr_zero D hR.le⟩).card_pos
  have hend : v n ≤ (81 : ℝ)^D.card*v 0 := by
    dsimp only [v]
    rw [hr0, hrn]
    exact_mod_cast card_double_le D hR
  obtain ⟨j,hj,hslow⟩ := exists_slow_step v (by positivity : (0 : ℝ) ≤ 1+1/(q : ℝ))
    hv0 hend (stability_growth hq D.card)
  let s := r j+stabilityWidth D q R
  have hminus : s-stabilityWidth D q R = r j := by dsimp [s]; ring
  have hplus : s+stabilityWidth D q R = r (j+1) := by
    dsimp [s, r, stabilityWidth, n]
    push_cast
    ring
  refine ⟨s,?_,?_,?_⟩
  · rw [hminus]
    dsimp [r]
    exact le_add_of_nonneg_right (by positivity)
  · rw [hplus]
    have hjR : ((j+1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (show j+1 ≤ n by omega)
    dsimp [r]
    have hd : ((j+1 : ℕ) : ℝ)*R/n ≤ R := by
      apply (div_le_iff₀ hnR).mpr
      nlinarith
    linarith
  · rw [hplus, hminus]
    exact hslow

#print axioms exists_stable_radius
end Erdos3BohrStableScale
