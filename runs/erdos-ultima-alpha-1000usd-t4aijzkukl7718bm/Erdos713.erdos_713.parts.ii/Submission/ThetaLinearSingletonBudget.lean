import FormalConjecturesUtil
import Submission.ThetaSingletonDegree

/-! A linear-in-incidences singleton budget suffices for a square-degree
bound on almost-regular all-links-theta-free hosts. The singleton budget
is an explicit additional hypothesis, not a consequence proved here. -/
open Finset
open scoped Classical
namespace Erdos713ThetaLinearSingletonBudget
open Erdos713ThetaGram Erdos713ThetaZeroLinks Erdos713ThetaSingletonDegree
set_option maxHeartbeats 2000000

lemma square_of_ninth {n d A : ℕ} (h : d^9 ≤ A*n^4*d) : d^2 ≤ (A+1)*n := by
  by_cases hd : d=0
  · simp [hd]
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  have h₈ : d^8 ≤ A*n^4 := Nat.le_of_mul_le_mul_right
    (by simpa only [show 9=8+1 from rfl,pow_succ] using h) hdpos
  have hA : A ≤ (A+1)^4 := (Nat.le_succ A).trans (Nat.le_self_pow (by decide) (A+1))
  apply (Nat.pow_le_pow_iff_left (by decide : 4 ≠ 0)).mp
  calc
    (d^2)^4 = d^8 := by ring
    _ ≤ A*n^4 := h₈
    _ ≤ (A+1)^4*n^4 := Nat.mul_le_mul_right _ hA
    _ = ((A+1)*n)^4 := by ring

def bound (K C : ℕ) : ℕ := 2560*(K+1)^2+251658240000*K^4*C+1

lemma incidence_le {n d D K : ℕ} (R : Fin n → Fin n → Prop)
    (hColMax : ∀ b, Nat.card {a // R a b} ≤ D) (hRatio : D ≤ K*d) :
    Nat.card {p : Fin n × Fin n // R p.1 p.2} ≤ K*n*d := by
  rw [Erdos713ThetaSplit.edge_card_eq_cols]
  calc
    _ ≤ ∑ _b : Fin n, K*d := sum_le_sum (fun b _ => (hColMax b).trans hRatio)
    _ = _ := by simp; ring

/-- The extra hypothesis is Z<=C*E, not Z=0. All conditions concern the
same relation, and the cap ratio K and budget coefficient C are fixed. -/
theorem degree_square {n d D K C : ℕ} (hn : 0 < n)
    (R : Fin n → Fin n → Prop)
    (hFree : ∀ a, ¬ HasTheta (link R a))
    (hrows : ∀ a, d ≤ Nat.card {b // R a b})
    (hcols : ∀ b, d ≤ Nat.card {a // R a b})
    (hRowMax : ∀ a, Nat.card {b // R a b} ≤ D)
    (hColMax : ∀ b, Nat.card {a // R a b} ≤ D) (hRatio : D ≤ K*d)
    (hSingleton : (singleSet R).card ≤ C*Nat.card {p : Fin n × Fin n // R p.1 p.2}) :
    d^2 ≤ bound K C*n := by
  have hE := incidence_le R hColMax hRatio
  rcases degree_alternative hn R hFree hrows hcols hRowMax hColMax hRatio with h | h
  · exact h.trans (Nat.mul_le_mul_right n (by unfold bound; omega))
  · have hZ : (singleSet R).card ≤ C*(K*n*d) :=
      hSingleton.trans (Nat.mul_le_mul_left C hE)
    have h₉ : d^9 ≤ (251658240000*K^4*C)*n^4*d := by
      calc
        _ ≤ 251658240000*K^3*n^3*(singleSet R).card := h
        _ ≤ 251658240000*K^3*n^3*(C*(K*n*d)) := Nat.mul_le_mul_left _ hZ
        _ = _ := by ring
    exact (square_of_ninth h₉).trans (Nat.mul_le_mul_right n (by unfold bound; omega))

/-- A direct conditional O(n^(3/2)) incidence estimate in squared form. -/
theorem incidence_square {n d D K C : ℕ} (hn : 0 < n)
    (R : Fin n → Fin n → Prop)
    (hFree : ∀ a, ¬ HasTheta (link R a))
    (hrows : ∀ a, d ≤ Nat.card {b // R a b})
    (hcols : ∀ b, d ≤ Nat.card {a // R a b})
    (hRowMax : ∀ a, Nat.card {b // R a b} ≤ D)
    (hColMax : ∀ b, Nat.card {a // R a b} ≤ D) (hRatio : D ≤ K*d)
    (hSingleton : (singleSet R).card ≤ C*Nat.card {p : Fin n × Fin n // R p.1 p.2}) :
    (Nat.card {p : Fin n × Fin n // R p.1 p.2})^2 ≤ K^2*bound K C*n^3 := by
  have hd := degree_square hn R hFree hrows hcols hRowMax hColMax hRatio hSingleton
  calc
    _ ≤ (K*n*d)^2 := Nat.pow_le_pow_left (incidence_le R hColMax hRatio) 2
    _ = K^2*n^2*d^2 := by ring
    _ ≤ K^2*n^2*(bound K C*n) := Nat.mul_le_mul_left _ hd
    _ = _ := by ring

/-- Dense all-links-free witnesses must have a superlinear singleton
budget relative to their incidence count, in this precise finite sense. -/
theorem many_singletons {n d D K C : ℕ} (hn : 0 < n)
    (R : Fin n → Fin n → Prop)
    (hFree : ∀ a, ¬ HasTheta (link R a))
    (hrows : ∀ a, d ≤ Nat.card {b // R a b})
    (hcols : ∀ b, d ≤ Nat.card {a // R a b})
    (hRowMax : ∀ a, Nat.card {b // R a b} ≤ D)
    (hColMax : ∀ b, Nat.card {a // R a b} ≤ D) (hRatio : D ≤ K*d)
    (hDense : K^2*bound K C*n^3 < (Nat.card {p : Fin n × Fin n // R p.1 p.2})^2) :
    C*Nat.card {p : Fin n × Fin n // R p.1 p.2} < (singleSet R).card := by
  by_contra hh
  have hS := Nat.le_of_not_gt hh
  exact (not_lt_of_ge (incidence_square hn R hFree hrows hcols hRowMax hColMax hRatio hS)) hDense

#print axioms square_of_ninth
#print axioms degree_square
#print axioms incidence_square
#print axioms many_singletons
end Erdos713ThetaLinearSingletonBudget
