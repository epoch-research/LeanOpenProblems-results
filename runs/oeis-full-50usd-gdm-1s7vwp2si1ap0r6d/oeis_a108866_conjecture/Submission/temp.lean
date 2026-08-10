import FormalConjectures.Util.ProblemImports
import Submission.Spec

lemma term_harmonic_sub_eq_choose {p : ℕ} (hp : p.Prime) (i : ℕ) (hi : i < p - 1) :
    (-1 : ZMod (p^2))^i * (p : ZMod (p^2)) * Finset.sum (Finset.range i) (fun j => (j + 1 : ZMod (p^2))⁻¹) * (i + 1 : ZMod (p^2))⁻¹ =
    (-1 : ZMod (p^2))^i * (i + 1 : ZMod (p^2))⁻¹ - ((p - 1).choose i : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹ := by
  have h_choose := choose_p_sub_one_eq_harmonic hp i (by omega)
  have h_mul : ((p - 1).choose i : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹ = (-1 : ZMod (p^2))^i * (1 - (p : ZMod (p^2)) * Finset.sum (Finset.range i) (fun j => (j + 1 : ZMod (p^2))⁻¹)) * (i + 1 : ZMod (p^2))⁻¹ := by
    rw [h_choose]
  rw [h_mul]
  ring

lemma p_mul_S2_eq_sub {p : ℕ} (hp : p.Prime) (hp3 : p > 3) :
    (p : ZMod (p^2)) * Finset.sum (Finset.range (p - 1)) (fun i => (-1 : ZMod (p^2))^i * Finset.sum (Finset.range i) (fun j => (j + 1 : ZMod (p^2))⁻¹) * (i + 1 : ZMod (p^2))⁻¹) =
    Finset.sum (Finset.range (p - 1)) (fun i => (-1 : ZMod (p^2))^i * (i + 1 : ZMod (p^2))⁻¹) -
    Finset.sum (Finset.range (p - 1)) (fun i => ((p - 1).choose i : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹) := by
  haveI : NeZero (p^2) := ⟨Nat.ne_of_gt (Nat.pow_pos hp.pos)⟩
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  have h := term_harmonic_sub_eq_choose hp i hi
  rw [← h]
  ring

