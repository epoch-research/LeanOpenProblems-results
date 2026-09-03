import Submission.PresentCylinderArithmetic

/-! Coverage pressure on every prime-adic shell about an actual private point.
These are necessary conditions for a cover, not a settlement of Erdős 7. -/
namespace Erdos7PrivateShellPressure
open scoped BigOperators
open Erdos7PresentCylinderArithmetic
set_option maxHeartbeats 2000000

lemma coprime_lift (P M : ℕ) (hcop : P.Coprime M) (x y : ℤ) :
    ∃ z : ℤ, (M : ℤ) ∣ z-x ∧ (P : ℤ) ∣ z-y := by
  obtain ⟨u,v,h⟩ := (hcop.isCoprime : IsCoprime (P : ℤ) (M : ℤ))
  refine ⟨x+(y-x)*v*M, ⟨(y-x)*v, by ring⟩, u*(x-y), ?_⟩
  linear_combination -(x-y)*h

/-- A shell consists of points agreeing through t digits and disagreeing at
exactly the next digit. -/
def shell (p E t : ℕ) [NeZero p] (x : ℤ) : Finset (ZMod (p^E)) :=
  cylinder p E t x \ cylinder p E (t+1) x

lemma cylinder_subset (p E u v : ℕ) [NeZero p] (huv : u ≤ v) (x : ℤ) :
    cylinder p E v x ⊆ cylinder p E u x := by
  intro y hy
  apply (mem_cylinder _ _ _ _ _).mpr
  have hd : ((p^u : ℕ) : ℤ) ∣ ((p^v : ℕ) : ℤ) := by
    exact_mod_cast pow_dvd_pow p huv
  exact hd.trans ((mem_cylinder _ _ _ _ _).mp hy)

lemma shell_card (p E t : ℕ) [NeZero p] (ht : t < E) (x : ℤ) :
    ((shell p E t x).card : ℚ) =
      Fintype.card (ZMod (p^E))*(((p : ℚ)⁻¹)^t-((p : ℚ)⁻¹)^(t+1)) := by
  have hcard := Finset.card_sdiff_add_card_eq_card
    (cylinder_subset p E t (t+1) (by omega) x)
  have hq : ((shell p E t x).card : ℚ) + (cylinder p E (t+1) x).card =
      (cylinder p E t x).card := by exact_mod_cast hcard
  rw [cylinder_card p E (t+1) (by omega), cylinder_card p E t (by omega)] at hq
  linarith

/-- A class is eligible for this shell only if all its non-p coordinates
match the private point, and its first p-adic mismatch has depth exactly t. -/
def Eligible {I : Type*} (p t : ℕ) (e d : I → ℕ) (a : I → ℤ) (x : ℤ)
    (j : I) : Prop :=
  t < e j ∧ (d j : ℤ) ∣ x-a j ∧
    ((p^t : ℕ) : ℤ) ∣ x-a j ∧ ¬ ((p^(t+1) : ℕ) : ℤ) ∣ x-a j

instance {I : Type*} (p t : ℕ) (e d : I → ℕ) (a : I → ℤ) (x : ℤ)
    (j : I) : Decidable (Eligible p t e d a x j) := by
  unfold Eligible
  infer_instance

lemma eligible_not_private {I : Type*} (p t : ℕ) (e d : I → ℕ)
    (a : I → ℤ) (x : ℤ) (i : I)
    (hxi : ((p^(e i)*d i : ℕ) : ℤ) ∣ x-a i) :
    ¬ Eligible p t e d a x i := by
  rintro ⟨hti, _, _, hn⟩
  have hd : ((p^(t+1) : ℕ) : ℤ) ∣ ((p^(e i)*d i : ℕ) : ℤ) := by
    exact_mod_cast (pow_dvd_pow p (show t+1 ≤ e i by omega)).trans (dvd_mul_right _ _)
  exact hn (hd.trans hxi)

lemma eligible_disjoint_depths {I : Type*} (p : ℕ) (e d : I → ℕ)
    (a : I → ℤ) (x : ℤ) (s t : ℕ) (hst : s < t) (j : I) :
    ¬ (Eligible p s e d a x j ∧ Eligible p t e d a x j) := by
  rintro ⟨hs,ht⟩
  have hd : ((p^(s+1) : ℕ) : ℤ) ∣ ((p^t : ℕ) : ℤ) := by
    exact_mod_cast pow_dvd_pow p (show s+1 ≤ t by omega)
  exact hs.2.2.2 (hd.trans ht.2.2.1)

/-- Full arithmetic coverage gives a cylinder cover of every such shell.
Only private membership at x and the modulus factorization are used. -/
theorem shell_covered {I : Type*} (p E M : ℕ) [NeZero p]
    (hcop : (p^E).Coprime M) (e d : I → ℕ) (a : I → ℤ)
    (he : ∀ j, e j ≤ E) (hd : ∀ j, d j ∣ M)
    (hc : ∀ z : ℤ, ∃ j, ((p^(e j)*d j : ℕ) : ℤ) ∣ z-a j)
    (i : I) (x : ℤ)
    (hpriv : ∀ j, ((p^(e j)*d j : ℕ) : ℤ) ∣ x-a j ↔ j=i)
    (t : ℕ) (hti : t < e i) :
    ∀ y ∈ shell p E t x, ∃ j, Eligible p t e d a x j ∧
      y ∈ cylinder p E (e j) (a j) := by
  intro y hy
  obtain ⟨hy0,hy1⟩ := Finset.mem_sdiff.mp hy
  have hyt := (mem_cylinder p E t x y).mp hy0
  have hyt1 : ¬ ((p^(t+1) : ℕ) : ℤ) ∣ (y.val : ℤ)-x :=
    fun h => hy1 ((mem_cylinder p E (t+1) x y).mpr h)
  obtain ⟨z,hzM,hzP⟩ := coprime_lift (p^E) M hcop x y.val
  obtain ⟨j,hj⟩ := hc z
  have hdj : (d j : ℤ) ∣ (M : ℤ) := by exact_mod_cast hd j
  have hdprod : (d j : ℤ) ∣ ((p^(e j)*d j : ℕ) : ℤ) := by
    exact_mod_cast dvd_mul_left (d j) (p^(e j))
  have hpj : ((p^(e j) : ℕ) : ℤ) ∣ ((p^(e j)*d j : ℕ) : ℤ) := by
    exact_mod_cast dvd_mul_right (p^(e j)) (d j)
  have hpe : ((p^(e j) : ℕ) : ℤ) ∣ ((p^E : ℕ) : ℤ) := by
    exact_mod_cast pow_dvd_pow p (he j)
  have hdmatch : (d j : ℤ) ∣ x-a j := by
    convert dvd_sub (hdprod.trans hj) (hdj.trans hzM) using 1; ring
  have hpy : ((p^(e j) : ℕ) : ℤ) ∣ (y.val : ℤ)-a j := by
    convert dvd_sub (hpj.trans hj) (hpe.trans hzP) using 1; ring
  have htj : t < e j := by
    by_contra hn
    have hjt : e j ≤ t := by omega
    have hpt : ((p^(e j) : ℕ) : ℤ) ∣ ((p^t : ℕ) : ℤ) := by
      exact_mod_cast pow_dvd_pow p hjt
    have hpx : ((p^(e j) : ℕ) : ℤ) ∣ x-a j := by
      convert dvd_sub hpy (hpt.trans hyt) using 1; ring
    have hcp : (p^(e j)).Coprime (d j) := hcop.of_dvd (pow_dvd_pow p (he j)) (hd j)
    have hmx : ((p^(e j)*d j : ℕ) : ℤ) ∣ x-a j := by
      simpa only [Nat.cast_mul] using hcp.isCoprime.mul_dvd hpx hdmatch
    have hji := (hpriv j).mp hmx
    subst j
    omega
  have hpt : ((p^t : ℕ) : ℤ) ∣ ((p^(e j) : ℕ) : ℤ) := by
    exact_mod_cast pow_dvd_pow p (show t ≤ e j by omega)
  have hpt1 : ((p^(t+1) : ℕ) : ℤ) ∣ ((p^(e j) : ℕ) : ℤ) := by
    exact_mod_cast pow_dvd_pow p (show t+1 ≤ e j by omega)
  have hx0 : ((p^t : ℕ) : ℤ) ∣ x-a j := by
    convert dvd_sub (hpt.trans hpy) hyt using 1; ring
  have hx1 : ¬ ((p^(t+1) : ℕ) : ℤ) ∣ x-a j := by
    intro hx1
    apply hyt1
    convert dvd_sub (hpt1.trans hpy) hx1 using 1; ring
  exact ⟨j, ⟨htj,hdmatch,hx0,hx1⟩, (mem_cylinder _ _ _ _ _).mpr hpy⟩

/-- The separate rational pressure inequality at EVERY shell of EVERY private
point of an actual cover. No numerical certificate or minimum-period assumption
is used. Distinctness and oddness can subsequently constrain the eligible sum. -/
theorem shell_pressure {I : Type*} [Fintype I] (p E M : ℕ) [NeZero p]
    (hcop : (p^E).Coprime M) (e d : I → ℕ) (a : I → ℤ)
    (he : ∀ j, e j ≤ E) (hd : ∀ j, d j ∣ M)
    (hc : ∀ z : ℤ, ∃ j, ((p^(e j)*d j : ℕ) : ℤ) ∣ z-a j)
    (i : I) (x : ℤ)
    (hpriv : ∀ j, ((p^(e j)*d j : ℕ) : ℤ) ∣ x-a j ↔ j=i)
    (t : ℕ) (hti : t < e i) :
    ((p : ℚ)⁻¹)^t-((p : ℚ)⁻¹)^(t+1) ≤
      ∑ j, if Eligible p t e d a x j then ((p : ℚ)⁻¹)^(e j) else 0 := by
  classical
  let B (j : I) := if Eligible p t e d a x j then cylinder p E (e j) (a j) else ∅
  have hsub : shell p E t x ⊆ Finset.univ.biUnion B := by
    intro y hy
    obtain ⟨j,hj,hyj⟩ := shell_covered p E M hcop e d a he hd hc i x hpriv t hti y hy
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,by simpa [B,hj] using hyj⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hq : ((shell p E t x).card : ℚ) ≤ ∑ j, ((B j).card : ℚ) := by
    exact_mod_cast hcard
  rw [shell_card p E t (hti.trans_le (he i)) x] at hq
  have hB (j : I) : ((B j).card : ℚ) = Fintype.card (ZMod (p^E)) *
      (if Eligible p t e d a x j then ((p : ℚ)⁻¹)^(e j) else 0) := by
    dsimp only [B]
    split_ifs
    · exact cylinder_card p E (e j) (he j) (a j)
    · simp
  simp_rw [hB] at hq
  rw [← Finset.mul_sum] at hq
  exact (mul_le_mul_iff_right₀ (show (0 : ℚ) < Fintype.card (ZMod (p^E)) by
    exact_mod_cast Fintype.card_pos)).mp hq



/-- A depth-sensitive form: a class with exponent e_j contributes only
p^(-(e_j-t-1)) to the p-1 sibling branches required by shell t. -/
theorem shell_depth_pressure {I : Type*} [Fintype I]
    (p E M : ℕ) [NeZero p] (hcop : (p^E).Coprime M)
    (e d : I → ℕ) (a : I → ℤ) (he : ∀ j, e j ≤ E) (hd : ∀ j, d j ∣ M)
    (hc : ∀ z : ℤ, ∃ j, ((p^(e j)*d j : ℕ) : ℤ) ∣ z-a j)
    (i : I) (x : ℤ)
    (hpriv : ∀ j, ((p^(e j)*d j : ℕ) : ℤ) ∣ x-a j ↔ j=i)
    (t : ℕ) (hti : t < e i) :
    (p : ℚ)-1 ≤ ∑ j, if Eligible p t e d a x j then
      ((p : ℚ)⁻¹)^(e j-t-1) else 0 := by
  have hp : (0 : ℚ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hq := shell_pressure p E M hcop e d a he hd hc i x hpriv t hti
  have hleft : ((p : ℚ)⁻¹)^t-((p : ℚ)⁻¹)^(t+1) =
      ((p : ℚ)⁻¹)^(t+1)*((p : ℚ)-1) := by
    rw [pow_succ]
    field_simp
  have hterm (j : I) :
      (if Eligible p t e d a x j then ((p : ℚ)⁻¹)^(e j) else 0) =
      ((p : ℚ)⁻¹)^(t+1)*(if Eligible p t e d a x j then
        ((p : ℚ)⁻¹)^(e j-t-1) else 0) := by
    by_cases hj : Eligible p t e d a x j
    · simp only [if_pos hj]
      have heq : e j = (t+1)+(e j-t-1) := by have := hj.1; omega
      conv_lhs => rw [heq, pow_add]
    · simp only [if_neg hj, mul_zero]
  rw [hleft] at hq
  simp_rw [hterm] at hq
  rw [← Finset.mul_sum] at hq
  exact (mul_le_mul_iff_right₀ (pow_pos (inv_pos.mpr hp) (t+1))).mp hq

/-- A strict deficit in one private shell rules out full coverage. -/
theorem not_cover_of_shell_deficit {I : Type*} [Fintype I]
    (p E M : ℕ) [NeZero p] (hcop : (p^E).Coprime M)
    (e d : I → ℕ) (a : I → ℤ) (he : ∀ j, e j ≤ E) (hd : ∀ j, d j ∣ M)
    (i : I) (x : ℤ)
    (hpriv : ∀ j, ((p^(e j)*d j : ℕ) : ℤ) ∣ x-a j ↔ j=i)
    (t : ℕ) (hti : t < e i)
    (hdef : (∑ j, if Eligible p t e d a x j then ((p : ℚ)⁻¹)^(e j) else 0) <
      ((p : ℚ)⁻¹)^t-((p : ℚ)⁻¹)^(t+1)) :
    ¬ (∀ z : ℤ, ∃ j, ((p^(e j)*d j : ℕ) : ℤ) ∣ z-a j) := by
  intro hc
  exact (not_lt_of_ge (shell_pressure p E M hcop e d a he hd hc i x hpriv t hti)) hdef

#print axioms coprime_lift
#print axioms shell_covered
#print axioms shell_pressure
#print axioms shell_depth_pressure
#print axioms not_cover_of_shell_deficit
end Erdos7PrivateShellPressure
