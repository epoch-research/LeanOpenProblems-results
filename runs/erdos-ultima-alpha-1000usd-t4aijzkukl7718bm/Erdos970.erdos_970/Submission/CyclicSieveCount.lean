import Submission.ParityDiscrepancyInterval
import Submission.SoftEndpointReduction
import Submission.CompetingCoverVariance

/-! Exact cumulative inclusion-exclusion and cyclic-to-normalized phase
transport. These formulas assert no new bound on Jacobsthal's function. -/
namespace Erdos970.GapAverages.CyclicSieve
open Finset Real ParityDiscrepancy

set_option maxHeartbeats 1000000

/-- Count on the integer interval (a,a+m]. -/
def natCount (P : Finset ℕ) (m a : ℕ) : ℕ :=
  ((range m).filter (fun x => ∀ p ∈ P, ¬p ∣ a+x+1)).card

def fullPrefix (P : Finset ℕ) (x : ℕ) : ℤ :=
  ∑ Q ∈ P.powerset, (-1 : ℤ)^Q.card * ((x / primeProduct Q : ℕ) : ℤ)

lemma indicator_inclusion (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : ℕ) :
    (if ∀ p ∈ P, ¬p ∣ x then (1 : ℤ) else 0) =
      ∑ Q ∈ P.powerset, (-1 : ℤ)^Q.card * (if primeProduct Q ∣ x then 1 else 0) := by
  have hh := survivorIndicator_inclusion P hP x
  dsimp only [survivorIndicator] at hh
  exact_mod_cast hh

lemma fullPrefix_sum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : ℕ) :
    (∑ j ∈ range x, if ∀ p ∈ P, ¬p ∣ j+1 then (1 : ℤ) else 0) = fullPrefix P x := by
  simp_rw [indicator_inclusion P hP]
  rw [sum_comm]
  apply sum_congr rfl
  intro Q hQ
  rw [← mul_sum]
  congr 1
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, mul_one, Nat.card_multiples]

lemma fullPrefix_diff (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m a : ℕ) :
    fullPrefix P (a+m)-fullPrefix P a = (natCount P m a : ℤ) := by
  rw [← fullPrefix_sum P hP, sum_range_add, ← fullPrefix_sum P hP]
  simp only [add_sub_cancel_left, sum_boole, natCount]

lemma fullPrefix_diff_toNat (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m a : ℕ) :
    (fullPrefix P (a+m)-fullPrefix P a).toNat = natCount P m a := by
  rw [fullPrefix_diff P hP, Int.toNat_natCast]

lemma product_modEq (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a b : ℕ)
    (h : ∀ p ∈ P, a ≡ b [MOD p]) : a ≡ b [MOD primeProduct P] := by
  have hforward (a b : ℕ) (hab : a ≤ b) (h : ∀ p ∈ P, a ≡ b [MOD p]) :
      a ≡ b [MOD primeProduct P] := by
    apply (Nat.modEq_iff_dvd' hab).mpr
    apply (primeProduct_dvd_iff P hP _).mpr
    intro p hp
    exact (Nat.modEq_iff_dvd' hab).mp (h p hp)
  rcases le_total a b with hab | hba
  · exact hforward a b hab h
  · exact (hforward b a hba (fun p hp => (h p hp).symm)).symm

def cyclicPhase (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (a : Fin (primeProduct P)) : Phase P := fun p =>
  ⟨(primeProduct P-(a.val+1)) % p.val, Nat.mod_lt _ (hP p.val p.property).pos⟩

lemma cyclicPhase_injective (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Function.Injective (cyclicPhase P hP) := by
  intro a b he
  have hc : primeProduct P-(a.val+1) ≡ primeProduct P-(b.val+1) [MOD primeProduct P] := by
    apply product_modEq P hP
    intro p hp
    exact congrArg (fun r : Phase P => (r ⟨p,hp⟩).val) he
  have hn := primeProduct_pos P (fun p hp => (hP p hp).pos)
  have heq := hc.eq_of_lt_of_lt (by omega) (by omega)
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  omega

lemma phase_card (P : Finset ℕ) : Fintype.card (Phase P) = primeProduct P := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  exact prod_coe_sort P (fun p : ℕ => p)

noncomputable def cyclicPhaseEquiv (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Fin (primeProduct P) ≃ Phase P :=
  Equiv.ofBijective (cyclicPhase P hP) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨cyclicPhase_injective P hP, by rw [Fintype.card_fin, phase_card]⟩)

lemma cyclic_hit (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (a : Fin (primeProduct P)) (x : ℕ) (p : P) :
    x % p.val = ((cyclicPhase P hP a) p).val ↔ p.val ∣ a.val+x+1 := by
  have hn : p.val ∣ primeProduct P := dvd_prod_of_mem id p.property
  have hz : primeProduct P ≡ 0 [MOD p.val] := Nat.modEq_zero_iff_dvd.mpr hn
  have hc : a.val+1+(primeProduct P-(a.val+1)) = primeProduct P := by
    have := a.isLt
    omega
  change x ≡ primeProduct P-(a.val+1) [MOD p.val] ↔ _
  constructor
  · intro hh
    have hh' := hh.add_left (a.val+1)
    rw [hc] at hh'
    have hd := Nat.modEq_zero_iff_dvd.mp (hh'.trans hz)
    convert hd using 1 <;> omega
  · intro hd
    have hh : a.val+1+x ≡ 0 [MOD p.val] :=
      Nat.modEq_zero_iff_dvd.mpr (by convert hd using 1 <;> omega)
    have he := hh.trans hz.symm
    have he' : a.val+1+x ≡ a.val+1+(primeProduct P-(a.val+1)) [MOD p.val] :=
      he.trans (by rw [hc])
    exact Nat.ModEq.add_left_cancel' (a.val+1) he'

lemma cyclic_count (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (m : ℕ) (a : Fin (primeProduct P)) :
    intervalCount P m (cyclicPhase P hP a) = (natCount P m a.val : ℝ) := by
  simp only [intervalCount, CoverFibers.point_eq_avoidance_indicator]
  have he (x : ℕ) : (∀ p : P, x % p.val ≠ ((cyclicPhase P hP a) p).val) ↔
      ∀ p ∈ P, ¬p ∣ a.val+x+1 := by
    constructor
    · intro h p hp hd
      exact h ⟨p,hp⟩ ((cyclic_hit P hP a x ⟨p,hp⟩).mpr hd)
    · intro h p hh
      exact h p.val p.property ((cyclic_hit P hP a x p).mp hh)
  simp only [he, sum_boole, natCount]

lemma cyclic_laplace (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (t : ℝ) (m : ℕ) :
    countLaplace P t m =
      (∑ a ∈ range (primeProduct P), exp (-t*(natCount P m a : ℝ))) / primeProduct P := by
  unfold countLaplace phaseMean
  rw [← (cyclicPhaseEquiv P hP).sum_comp (fun r => exp (-t*intervalCount P m r))]
  change (∑ a : Fin (primeProduct P), exp (-t*intervalCount P m (cyclicPhase P hP a))) / _ = _
  simp_rw [cyclic_count]
  rw [Fin.sum_univ_eq_sum_range (fun a => exp (-t*(natCount P m a : ℝ))) (primeProduct P)]
  congr 1
  rw [prod_coe_sort P (fun p : ℕ => (p : ℝ))]
  simp only [primeProduct, Nat.cast_prod]

#print axioms fullPrefix_diff_toNat
#print axioms cyclic_laplace
end Erdos970.GapAverages.CyclicSieve
