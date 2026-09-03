import FormalConjecturesUtil

/-! Exact primal and dual certificates for a finite, concrete comb mean model.
This is not a covering obstruction and makes no claim about other current
families, arbitrary ternary exponents, or the unrestricted conjecture. -/
namespace Erdos7CombMeanCertificate
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000

abbrev Point := Fin 14 × Fin 3

def points : Fin 14 → ℕ := ![2,5,7,8,11,13,14,16,17,20,22,23,25,26]

def allowed (z : Point) : Prop :=
  if z.2.val = 0 then ¬ (points z.1 % 3 = 2 ∨ points z.1 = 13)
  else if z.2.val = 1 then points z.1 % 9 ≠ 2 else True

instance (z : Point) : Decidable (allowed z) := by unfold allowed; infer_instance

def indicator (u r : ℕ) (c : Option (Fin 3)) (z : Point) : ℚ :=
  if points z.1 % 3^u = r ∧ (c = none ∨ c = some z.2) then 1 else 0

def mass (μ : Point → ℚ) (u r : ℕ) (c : Option (Fin 3)) : ℚ :=
  ∑ z, μ z * indicator u r c z

structure Row where
  exponent : ℕ
  residue : ℕ
  column : Option (Fin 3)
  group : Fin 7

def rows : Fin 16 → Row := ![
  ⟨1,1,none,0⟩, ⟨1,2,none,0⟩,
  ⟨2,4,none,1⟩, ⟨2,7,none,1⟩,
  ⟨3,13,none,2⟩, ⟨3,22,none,2⟩,
  ⟨0,0,some 1,3⟩, ⟨0,0,some 2,3⟩,
  ⟨1,2,some 1,4⟩, ⟨1,2,some 2,4⟩,
  ⟨2,5,some 1,5⟩, ⟨2,7,some 0,5⟩, ⟨2,8,some 1,5⟩,
  ⟨3,13,some 1,6⟩, ⟨3,13,some 2,6⟩, ⟨3,22,some 0,6⟩]

def numerators : Fin 16 → ℕ := ![13,19,6,26,12,20,16,16,12,20,8,16,8,8,8,16]
def weight (i : Fin 16) : ℚ := numerators i / 32

theorem weight_nonneg : ∀ i, 0 ≤ weight i := by decide +kernel

theorem point_identity : ∀ z : Point, allowed z →
    (∑ i, weight i * indicator (rows i).exponent (rows i).residue (rows i).column z) = 55/32 := by
  decide +kernel

theorem group_identity (v : Fin 7 → ℚ) :
    (∑ i, weight i * v (rows i).group) = ∑ j, v j := by
  have hv : v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6] := by
    funext j
    fin_cases j <;> rfl
  rw [hv]
  norm_num [Fin.sum_univ_succ, rows, weight, numerators]
  ring_nf
  rfl

/-- A sixteen-row dual certificate. No floating solver is trusted. -/
theorem lower_bound (μ : Point → ℚ) (v : Fin 7 → ℚ)
    (hs : ∀ z, ¬ allowed z → μ z = 0) (hm : (∑ z, μ z) = 1)
    (hrow : ∀ i, mass μ (rows i).exponent (rows i).residue (rows i).column ≤ v (rows i).group) :
    87/32 ≤ 1 + ∑ j, v j := by
  have hlin := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (hrow i) (weight_nonneg i))
  rw [group_identity] at hlin
  have he : (∑ i, weight i * mass μ (rows i).exponent (rows i).residue (rows i).column) = 55/32 := by
    simp only [mass, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ z, μ z * (55/32) := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : allowed z
        · rw [← point_identity z hz, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        · simp only [hs z hz, mul_zero, zero_mul, Finset.sum_const_zero]
      _ = 55/32 := by rw [← Finset.sum_mul, hm, one_mul]
  rw [he] at hlin
  linarith

def Feasible (μ : Point → ℚ) (v : Fin 7 → ℚ) : Prop :=
  (∀ z, 0 ≤ μ z) ∧ (∀ z, ¬ allowed z → μ z = 0) ∧ (∑ z, μ z) = 1 ∧
  (∀ u : Fin 3, ∀ r : Fin 27,
    mass μ (u.val+1) r.val none ≤ v ⟨u.val, by omega⟩) ∧
  (∀ u : Fin 4, ∀ r : Fin 27, ∀ c : Fin 3,
    mass μ u.val r.val (some c) ≤ v ⟨3+u.val, by omega⟩) ∧
  (∀ u : Fin 4, ∀ r : Fin 27,
    mass μ u.val r.val none ≤ 4 * v ⟨3+u.val, by omega⟩)

instance (μ : Point → ℚ) (v : Fin 7 → ℚ) : Decidable (Feasible μ v) := by
  unfold Feasible
  infer_instance

theorem feasible_lower_bound (μ : Point → ℚ) (v : Fin 7 → ℚ) (hf : Feasible μ v) :
    87/32 ≤ 1 + ∑ j, v j := by
  obtain ⟨_, hs, hm, hA, hB, _⟩ := hf
  apply lower_bound μ v hs hm
  intro i
  fin_cases i
  · exact hA 0 1
  · exact hA 0 2
  · exact hA 1 4
  · exact hA 1 7
  · exact hA 2 13
  · exact hA 2 22
  · exact hB 0 0 1
  · exact hB 0 0 2
  · exact hB 1 2 1
  · exact hB 1 2 2
  · exact hB 2 5 1
  · exact hB 2 7 0
  · exact hB 2 8 1
  · exact hB 3 13 1
  · exact hB 3 13 2
  · exact hB 3 22 0

def primalNumerators : Fin 14 → Fin 3 → ℕ := ![
  ![0,0,2], ![0,2,0], ![2,0,2], ![0,2,0], ![0,0,2], ![0,2,2], ![0,2,2],
  ![0,0,0], ![0,2,0], ![0,0,0], ![2,1,1], ![0,0,0], ![2,2,0], ![0,0,2]]
def primal (z : Point) : ℚ := primalNumerators z.1 z.2 / 32

def primalCaps (j : Fin 7) : ℚ := (![16,8,4,13,8,4,2] : Fin 7 → ℚ) j / 32

theorem primal_feasible : Feasible primal primalCaps := by decide +kernel

theorem primal_value : 1 + (∑ j, primalCaps j) = 87/32 := by decide +kernel

/-- Exact finite LP optimum. Its objective is the model's mean, not a density
bound excluding arbitrary odd covering systems. -/
theorem exact_optimum :
    (∃ μ v, Feasible μ v ∧ 1 + (∑ j, v j) = 87/32) ∧
    (∀ μ v, Feasible μ v → 87/32 ≤ 1 + ∑ j, v j) :=
  ⟨⟨primal, primalCaps, primal_feasible, primal_value⟩, feasible_lower_bound⟩


lemma mass_sum {D : Type*} [Fintype D] (μ : D → Point → ℚ)
    (u r : ℕ) (c : Option (Fin 3)) :
    mass (fun z => ∑ d, μ d z) u r c = ∑ d, mass (μ d) u r c := by
  simp only [mass, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The same dual identity gives a lower bound for arbitrary supported
exit-depth weights, not only weights with one common coarse profile. The
hypotheses here include all probability mass in the specified exit layers. -/
theorem exit_depth_lower_bound {D : Type*} [Fintype D]
    (μ : D → Point → ℚ) (A : Fin 3 → ℚ) (B : D → Fin 4 → ℚ)
    (hs : ∀ d z, ¬ allowed z → μ d z = 0)
    (hm : (∑ z, ∑ d, μ d z) = 1)
    (hA : ∀ u : Fin 3, ∀ r : Fin 27,
      mass (fun z => ∑ d, μ d z) (u.val+1) r.val none ≤ A u)
    (hB : ∀ d, ∀ u : Fin 4, ∀ r : Fin 27, ∀ c : Fin 3,
      mass (μ d) u.val r.val (some c) ≤ B d u) :
    87/32 ≤ 1 + (∑ u, A u) + ∑ d, ∑ u, B d u := by
  let v : Fin 7 → ℚ := ![A 0, A 1, A 2,
    ∑ d, B d 0, ∑ d, B d 1, ∑ d, B d 2, ∑ d, B d 3]
  have hb (u : Fin 4) (r : Fin 27) (c : Fin 3) :
      mass (fun z => ∑ d, μ d z) u.val r.val (some c) ≤ ∑ d, B d u := by
    rw [mass_sum]
    exact Finset.sum_le_sum (fun d _ => hB d u r c)
  have hr : ∀ i, mass (fun z => ∑ d, μ d z)
      (rows i).exponent (rows i).residue (rows i).column ≤ v (rows i).group := by
    intro i
    fin_cases i
    · exact hA 0 1
    · exact hA 0 2
    · exact hA 1 4
    · exact hA 1 7
    · exact hA 2 13
    · exact hA 2 22
    · exact hb 0 0 1
    · exact hb 0 0 2
    · exact hb 1 2 1
    · exact hb 1 2 2
    · exact hb 2 5 1
    · exact hb 2 7 0
    · exact hb 2 8 1
    · exact hb 3 13 1
    · exact hb 3 13 2
    · exact hb 3 22 0
  have hh := lower_bound (fun z => ∑ d, μ d z) v
    (fun z hz => Finset.sum_eq_zero (fun d _ => hs d z hz)) hm hr
  have hv : (∑ j, v j) = (∑ u, A u) + ∑ d, ∑ u, B d u := by
    simp only [Fin.sum_univ_three, Fin.sum_univ_four]
    simp [v, Fin.sum_univ_succ, Finset.sum_add_distrib]
    ring
  rw [hv] at hh
  linarith

#print axioms exact_optimum
#print axioms exit_depth_lower_bound
end Erdos7CombMeanCertificate
