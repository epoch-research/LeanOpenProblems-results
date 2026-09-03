import FormalConjecturesUtil

/-! Established Kővári–Sós–Turán upper bounds, separated for development use. -/

open SimpleGraph

namespace Erdos714Upper

open Finset

variable {V : Type*} [Fintype V] {r : ℕ}

noncomputable def common (G : SimpleGraph V) (f : Fin r ↪ V) : Finset V := by
  classical
  exact univ.filter (fun v => ∀ i, G.Adj (f i) v)

@[simp] lemma mem_common (G : SimpleGraph V) (f : Fin r ↪ V) (v : V) :
    v ∈ common G f ↔ ∀ i, G.Adj (f i) v := by
  classical
  simp [common]

lemma common_card_le (G : SimpleGraph V)
    (hG : (completeBipartiteGraph (Fin r) (Fin r)).Free G)
    (f : Fin r ↪ V) : (common G f).card ≤ r - 1 := by
  classical
  by_contra! h
  have hr : r ≤ (common G f).card := by omega
  obtain ⟨s, hs, hcard⟩ := exists_subset_card_eq hr
  apply hG
  refine ⟨Copy.completeBipartiteGraph (univ.map f) s (by simp) (by simpa using hcard) ?_⟩
  intro v hv w hw
  change v ∈ univ.map f at hv
  obtain ⟨i, _, rfl⟩ := mem_map.mp hv
  exact (mem_common G f w).mp (hs hw) i

noncomputable def starEquiv (G : SimpleGraph V) (r : ℕ) :
    (Σ v : V, (Fin r ↪ G.neighborSet v)) ≃
      (Σ f : Fin r ↪ V, {v // v ∈ common G f}) where
  toFun x := ⟨⟨fun i => (x.2 i).val, fun i j h => x.2.injective (Subtype.ext h)⟩,
    ⟨x.1, (mem_common _ _ _).mpr (fun i => (x.2 i).property.symm)⟩⟩
  invFun x := ⟨x.2.val, ⟨fun i => ⟨x.1 i,
    ((mem_common _ _ _).mp x.2.property i).symm⟩,
      fun i j h => x.1.injective (congrArg Subtype.val h)⟩⟩
  left_inv := by rintro ⟨v, f⟩; rfl
  right_inv := by rintro ⟨f, v, hv⟩; rfl

lemma count_stars (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v : V, (G.degree v).descFactorial r =
      ∑ f : Fin r ↪ V, (common G f).card := by
  classical
  have h := Fintype.card_congr (starEquiv G r)
  simpa only [Fintype.card_sigma, Fintype.card_embedding_eq, Fintype.card_fin,
    card_neighborSet_eq_degree, Fintype.card_coe] using h

/-- The exact ordered-star counting inequality for a balanced biclique-free graph. -/
theorem star_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : (completeBipartiteGraph (Fin r) (Fin r)).Free G) :
    ∑ v : V, (G.degree v).descFactorial r ≤
      (r - 1) * (Fintype.card V).descFactorial r := by
  classical
  rw [count_stars]
  calc
    _ ≤ ∑ _f : Fin r ↪ V, (r - 1) := sum_le_sum fun f _ => common_card_le G hG f
    _ = _ := by simp [Nat.mul_comm]

/-- A power-moment version of the star bound. -/
theorem truncated_degree_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : (completeBipartiteGraph (Fin r) (Fin r)).Free G) :
    ∑ v : V, (G.degree v + 1 - r) ^ r ≤
      (r - 1) * (Fintype.card V) ^ r := by
  classical
  calc
    _ ≤ ∑ v : V, (G.degree v).descFactorial r :=
      sum_le_sum fun v _ => Nat.pow_sub_le_descFactorial _ _
    _ ≤ (r - 1) * (Fintype.card V).descFactorial r := star_bound G hG
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow _ _)

/-- A version of the Kővári–Sós–Turán inequality involving natural powers only. -/
theorem edge_power_bound (hr : 1 ≤ r) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : (completeBipartiteGraph (Fin r) (Fin r)).Free G) :
    (2 * G.edgeFinset.card - (r - 1) * Fintype.card V) ^ r ≤
      (r - 1) * (Fintype.card V) ^ (2 * r - 1) := by
  classical
  have hs : 2 * G.edgeFinset.card ≤
      (∑ v : V, (G.degree v + 1 - r)) + (r - 1) * Fintype.card V := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    calc
      _ ≤ ∑ v : V, (G.degree v + 1 - r + (r - 1)) := sum_le_sum fun v _ => by omega
      _ = _ := by rw [sum_add_distrib]; simp [Nat.mul_comm]
  have hs' : 2 * G.edgeFinset.card - (r - 1) * Fintype.card V ≤
      ∑ v : V, (G.degree v + 1 - r) := by omega
  have hp := pow_sum_le_card_mul_sum_pow
    (s := (univ : Finset V)) (f := fun v => G.degree v + 1 - r) (by intros; omega) (r - 1)
  rw [Nat.sub_add_cancel hr, card_univ] at hp
  calc
    _ ≤ (∑ v : V, (G.degree v + 1 - r)) ^ r := Nat.pow_le_pow_left hs' r
    _ ≤ (Fintype.card V) ^ (r - 1) * ∑ v : V, (G.degree v + 1 - r) ^ r := hp
    _ ≤ (Fintype.card V) ^ (r - 1) * ((r - 1) * (Fintype.card V) ^ r) :=
      Nat.mul_le_mul_left _ (truncated_degree_bound G hG)
    _ = _ := by rw [← mul_assoc, mul_comm ((Fintype.card V) ^ (r - 1)),
      mul_assoc, ← pow_add, show r - 1 + r = 2 * r - 1 by omega]

/-- The usual Kővári–Sós–Turán upper bound, including its leading constant. -/
theorem edge_real_bound (hr : 1 ≤ r) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : (completeBipartiteGraph (Fin r) (Fin r)).Free G) :
    (G.edgeFinset.card : ℝ) ≤
      ((r : ℝ) - 1) ^ (1 / (r : ℝ)) / 2 *
        (Fintype.card V : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) +
      ((r : ℝ) - 1) / 2 * (Fintype.card V : ℝ) := by
  classical
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrsub : 0 ≤ (r : ℝ) - 1 := sub_nonneg.mpr hr1
  let t := 2 * G.edgeFinset.card - (r - 1) * Fintype.card V
  have ht : (t : ℝ) ^ r ≤ ((r : ℝ) - 1) * (Fintype.card V : ℝ) ^ (2 * r - 1) := by
    exact_mod_cast edge_power_bound hr G hG
  have hroot := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (t : ℝ) ^ r) ht
    (by positivity : (0 : ℝ) ≤ 1 / (r : ℝ))
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    mul_one_div_cancel hr0.ne', Real.rpow_one] at hroot
  rw [Real.mul_rpow (by linarith) (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)] at hroot
  have hexp : ((2 * r - 1 : ℕ) : ℝ) * (1 / (r : ℝ)) = (2 : ℝ) - 1 / (r : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    field_simp
  rw [hexp] at hroot
  have ht' : 2 * G.edgeFinset.card ≤ (r - 1) * Fintype.card V + t := by
    dsimp [t]
    omega
  have ht'' : (2 : ℝ) * G.edgeFinset.card ≤
      ((r : ℝ) - 1) * Fintype.card V + (t : ℝ) := by exact_mod_cast ht'
  linarith

/-- The same upper bound for the extremal number. -/
theorem extremal_real_bound (hr : 1 ≤ r) (n : ℕ) :
    (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ) ≤
      ((r : ℝ) - 1) ^ (1 / (r : ℝ)) / 2 *
        (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) + ((r : ℝ) - 1) / 2 * n := by
  classical
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrsub : 0 ≤ (r : ℝ) - 1 := sub_nonneg.mpr hr1
  rw [← Fintype.card_fin n]
  apply (extremalNumber_le_iff_of_nonneg _ (by positivity)).mpr
  intro G _ hG
  exact edge_real_bound hr G hG

end Erdos714Upper

#print axioms Erdos714Upper.extremal_real_bound
