import FormalConjecturesUtil

/-!
Mixed product-degenerate four-cycles can be confined to narrow multiplicative
intervals. The polynomial family is unconditional; its identification with
largest-prime labels is conditional on four explicit primality assumptions.
A concrete instance below verifies those assumptions. This is an obstruction
to a cycle-exclusion argument, NOT a disproof of the density conjecture.
-/
namespace Erdos371.NarrowMixedPrimeCycle

set_option autoImplicit false

def rLabel (t h : ℕ) : ℕ := 4*(t+1)*h+1
def sLabel (t h : ℕ) : ℕ := 4*t*h+1
def vLabel (t h : ℕ) : ℕ := 2*(2*t+1)*h+1
def qLabel (t h : ℕ) : ℕ := 8*t*(t+1)*h+2*t+1

def first (t h : ℕ) : ℕ := 2*t*rLabel t h
def second (t h : ℕ) : ℕ := qLabel t h
def third (t h : ℕ) : ℕ := 2*t*vLabel t h
def fourth (t h : ℕ) : ℕ := (2*t+1)*rLabel t h

lemma consecutive_factorizations (t h : ℕ) :
    first t h+1 = qLabel t h ∧
    second t h+1 = 2*(t+1)*sLabel t h ∧
    third t h+1 = (2*t+1)*sLabel t h ∧
    fourth t h+1 = 2*(t+1)*vLabel t h := by
  simp only [first, second, third, fourth, rLabel, sLabel, vLabel, qLabel]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- Two forward and two backward edges have exactly equal endpoint products. -/
theorem endpoint_product_equality (t h : ℕ) :
    first t h * second t h * (third t h+1) * (fourth t h+1) =
      (first t h+1) * (second t h+1) * third t h * fourth t h := by
  simp only [first, second, third, fourth, rLabel, vLabel, qLabel]
  ring

lemma indices_ordered (t h : ℕ) (ht : 1 ≤ t) (hh : 1 ≤ h) :
    0 < third t h ∧ third t h < first t h ∧
      first t h < second t h ∧ second t h < fourth t h := by
  have hth : 0 < t*h := Nat.mul_pos (by omega) (by omega)
  have hr : 1 < rLabel t h := by dsimp [rLabel]; nlinarith
  have hv : 0 < vLabel t h := by dsimp [vLabel]; omega
  have hdelta : first t h = third t h+4*t*h := by
    simp only [first, third, rLabel, vLabel]
    ring
  have he := (consecutive_factorizations t h).1
  have he' : fourth t h = first t h+rLabel t h := by
    simp only [fourth, first]
    ring
  change _ ∧ _ ∧ first t h < qLabel t h ∧ qLabel t h < fourth t h
  refine ⟨Nat.mul_pos (by omega) hv, ?_, ?_, ?_⟩
  · nlinarith [hdelta]
  · omega
  · omega

/-- All four indices lie in a relative interval shorter than 1/t. -/
theorem narrow_interval (t h : ℕ) (ht : 1 ≤ t) (hh : 1 ≤ h) :
    0 < third t h ∧
      (∀ n ∈ ({first t h, second t h, third t h, fourth t h} : Finset ℕ),
        third t h ≤ n ∧ n ≤ fourth t h) ∧
      t*fourth t h < (t+1)*third t h := by
  obtain ⟨hp, h31, h12, h24⟩ := indices_ordered t h ht hh
  have he : t*fourth t h+t = (t+1)*third t h := by
    simp only [fourth, third, rLabel, vLabel]
    ring
  refine ⟨hp, ?_, by omega⟩
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> omega

private lemma maxPrimeFac_small_cofactor (k p : ℕ) (hk : 0 < k)
    (hp : p.Prime) (hkp : k ≤ p) : Nat.maxPrimeFac (k*p) = p := by
  rw [Nat.maxPrimeFac_mul hk.ne' hp.ne_zero, hp.maxPrimeFac_eq_self]
  exact max_eq_right (Nat.maxPrimeFac_le.trans hkp)

/-- When the four explicit labels are prime, they give an actual mixed
four-cycle of the largest-prime-factor sequence. -/
theorem actual_labels (t h : ℕ) (ht : 1 ≤ t) (hh : 1 ≤ h)
    (hr : (rLabel t h).Prime) (hs : (sLabel t h).Prime)
    (hv : (vLabel t h).Prime) (hq : (qLabel t h).Prime) :
    Nat.maxPrimeFac (first t h) = rLabel t h ∧
    Nat.maxPrimeFac (first t h+1) = qLabel t h ∧
    Nat.maxPrimeFac (second t h) = qLabel t h ∧
    Nat.maxPrimeFac (second t h+1) = sLabel t h ∧
    Nat.maxPrimeFac (third t h) = vLabel t h ∧
    Nat.maxPrimeFac (third t h+1) = sLabel t h ∧
    Nat.maxPrimeFac (fourth t h) = rLabel t h ∧
    Nat.maxPrimeFac (fourth t h+1) = vLabel t h := by
  have hmul := Nat.mul_le_mul_left (4*t) hh
  have hS : 2*(t+1) ≤ sLabel t h := by dsimp [sLabel]; nlinarith
  have hSV : sLabel t h ≤ vLabel t h := by
    dsimp [sLabel, vLabel]
    nlinarith
  have hVR : vLabel t h ≤ rLabel t h := by
    dsimp [vLabel, rLabel]
    nlinarith
  have hR := hS.trans (hSV.trans hVR)
  have hV := hS.trans hSV
  obtain ⟨h1, h2, h3, h4⟩ := consecutive_factorizations t h
  refine ⟨?_, ?_, hq.maxPrimeFac_eq_self, ?_, ?_, ?_, ?_, ?_⟩
  · exact maxPrimeFac_small_cofactor _ _ (by omega) hr (by omega)
  · rw [h1, hq.maxPrimeFac_eq_self]
  · rw [h2]
    exact maxPrimeFac_small_cofactor _ _ (by omega) hs hS
  · exact maxPrimeFac_small_cofactor _ _ (by omega) hv (by omega)
  · rw [h3]
    exact maxPrimeFac_small_cofactor _ _ (by omega) hs (by omega)
  · exact maxPrimeFac_small_cofactor _ _ (by omega) hr (by omega)
  · rw [h4]
    exact maxPrimeFac_small_cofactor _ _ (by omega) hv hV

/-- A concrete prime specialization; each primality assertion is checked
by the kernel through `norm_num`, not by external numerical evaluation. -/
theorem concrete_labels :
    Nat.maxPrimeFac 54394762 = 269281 ∧
    Nat.maxPrimeFac 54394763 = 54394763 ∧
    Nat.maxPrimeFac 54394763 = 54394763 ∧
    Nat.maxPrimeFac 54394764 = 266641 ∧
    Nat.maxPrimeFac 54128122 = 267961 ∧
    Nat.maxPrimeFac 54128123 = 266641 ∧
    Nat.maxPrimeFac 54664043 = 269281 ∧
    Nat.maxPrimeFac 54664044 = 267961 := by
  have hr : (rLabel 101 660).Prime := by norm_num [rLabel]
  have hs : (sLabel 101 660).Prime := by norm_num [sLabel]
  have hv : (vLabel 101 660).Prime := by norm_num [vLabel]
  have hq : (qLabel 101 660).Prime := by norm_num [qLabel]
  have hl := actual_labels 101 660 (by norm_num) (by norm_num) hr hs hv hq
  norm_num only [first, second, third, fourth, rLabel, sLabel, vLabel, qLabel] at hl
  exact hl

/-- The four actual indices lie inside a one-percent interval, all labels
exceed its square root, and the mixed endpoint product is degenerate even
though the label product exceeds the directed four-cycle bound. -/
theorem narrow_actual_cycle_obstruction :
    (∀ n ∈ ({54394762, 54394763, 54128122, 54664043} : Finset ℕ),
      54128122 ≤ n ∧ n ≤ 54664043) ∧
    100*54664043 < 101*54128122 ∧
    (∀ p ∈ ({269281, 54394763, 266641, 267961} : Finset ℕ), 54664043 < p^2) ∧
    Nat.maxPrimeFac 54394762 = Nat.maxPrimeFac 54664043 ∧
    Nat.maxPrimeFac 54394764 = Nat.maxPrimeFac 54128123 ∧
    Nat.maxPrimeFac 54128122 = Nat.maxPrimeFac 54664044 ∧
    (54394762 : ℕ)*54394763*54128123*54664044 =
      54394763*54394764*54128122*54664043 ∧
    4*(54664043+1)^3 <
      Nat.maxPrimeFac 54394762 * Nat.maxPrimeFac 54394763 *
        Nat.maxPrimeFac 54394764 * Nat.maxPrimeFac 54128122 := by
  obtain ⟨h1, h2, _, h3, h4, h5, h6, h7⟩ := concrete_labels
  rw [h1, h2, h3, h4, h5, h6, h7]
  norm_num [Finset.mem_insert, Finset.mem_singleton]

/-- Balanced traversal orientation does not make the actual comparison
signs balance, even in this narrow interval: one edge rises and three fall. -/
theorem narrow_cycle_comparisons :
    Nat.maxPrimeFac 54394762 < Nat.maxPrimeFac 54394763 ∧
    Nat.maxPrimeFac 54394764 < Nat.maxPrimeFac 54394763 ∧
    Nat.maxPrimeFac 54128123 < Nat.maxPrimeFac 54128122 ∧
    Nat.maxPrimeFac 54664044 < Nat.maxPrimeFac 54664043 := by
  obtain ⟨h1, h2, _, h3, h4, h5, h6, h7⟩ := concrete_labels
  rw [h1, h2, h3, h4, h5, h6, h7]
  norm_num

#print axioms endpoint_product_equality
#print axioms narrow_interval
#print axioms actual_labels
#print axioms concrete_labels
#print axioms narrow_actual_cycle_obstruction
#print axioms narrow_cycle_comparisons
end Erdos371.NarrowMixedPrimeCycle
