import FormalConjecturesUtil

/-! An integer-power criterion for the remaining construction. -/

open Filter SimpleGraph

namespace Erdos714Reduction

/-- Adding isolated vertices does not create a copy of a graph without isolated vertices. -/
theorem free_map_of_no_isolated {A B W : Type*} {H : SimpleGraph W}
    {G : SimpleGraph A} (hH : ∀ v, ∃ w, H.Adj v w) (e : A ↪ B)
    (hG : H.Free G) : H.Free (G.map e) := by
  classical
  rintro ⟨f⟩
  have hrange : ∀ v, ∃ x, e x = f v := by
    intro v
    obtain ⟨w, hw⟩ := hH v
    obtain ⟨x, y, hxy, hx, hy⟩ := f.toHom.map_adj hw
    exact ⟨x, hx⟩
  choose g hg using hrange
  apply hG
  refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
  · intro v w hvw
    have h := f.toHom.map_adj hvw
    change (G.map e).Adj (f v) (f w) at h
    rw [← hg v, ← hg w, map_adj_apply] at h
    exact h
  · intro v w hvw
    apply f.injective
    change f v = f w
    change g v = g w at hvw
    rw [← hg v, ← hg w, hvw]

set_option maxHeartbeats 1000000 in
/-- The extremal number of a graph without isolated vertices is monotone in its order. -/
theorem extremalNumber_monotone_of_no_isolated {W : Type*} (H : SimpleGraph W)
    (hH : ∀ v, ∃ w, H.Adj v w) : Monotone (fun n => extremalNumber n H) := by
  classical
  intro n m hnm
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro G _ hG
  have hmap := free_map_of_no_isolated hH (Fin.castLEEmb hnm) hG
  have he := card_edgeFinset_le_extremalNumber hmap
  simp only [Fintype.card_fin] at he
  convert he using 1
  symm
  convert card_edgeFinset_map (Fin.castLEEmb hnm) G using 1
  congr 1
  ext a
  simp [edgeSet_map, Set.mem_image]

/-- Interpolate lower bounds between successive members of a geometric sequence. -/
theorem lower_bound_from_scaled_sizes (f : ℕ → ℝ) (hf : Monotone f)
    (p : ℝ) (hp : 0 ≤ p) (a b : ℕ) (ha : 0 < a) (hb : 2 ≤ b)
    (c : ℝ) (hc : 0 < c)
    (h : ∀ k : ℕ, c * ((a * b ^ k : ℕ) : ℝ) ^ p ≤ f (a * b ^ k)) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ᶠ n : ℕ in atTop, c' * (n : ℝ) ^ p ≤ f n := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  refine ⟨c / (b : ℝ) ^ p, div_pos hc (Real.rpow_pos_of_pos hb0 p), ?_⟩
  filter_upwards [eventually_ge_atTop a] with n hn
  have hn' : (1 : ℝ) ≤ (n : ℝ) / a := by
    rw [le_div_iff₀ ha0, one_mul]
    exact_mod_cast hn
  obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near hn' (show (1 : ℝ) < b by exact_mod_cast hb)
  have hkn : a * b ^ k ≤ n := by
    have hkn' := (le_div_iff₀ ha0).mp hk
    have hkn'' : (a : ℝ) * (b : ℝ) ^ k ≤ (n : ℝ) := by simpa only [mul_comm] using hkn'
    exact_mod_cast hkn''
  have hnb : (n : ℝ) ≤ (b : ℝ) * ((a * b ^ k : ℕ) : ℝ) := by
    have hnup := (div_le_iff₀ ha0).mp hk'.le
    calc
      (n : ℝ) ≤ (b : ℝ) ^ (k + 1) * (a : ℝ) := hnup
      _ = (b : ℝ) * ((a * b ^ k : ℕ) : ℝ) := by
        push_cast
        ring
  have hpw := Real.rpow_le_rpow (show (0 : ℝ) ≤ n by positivity) hnb hp
  rw [Real.mul_rpow (le_of_lt hb0) (by positivity)] at hpw
  calc
    c / (b : ℝ) ^ p * (n : ℝ) ^ p ≤
        c / (b : ℝ) ^ p * ((b : ℝ) ^ p * ((a * b ^ k : ℕ) : ℝ) ^ p) :=
      mul_le_mul_of_nonneg_left hpw (by positivity)
    _ = c * ((a * b ^ k : ℕ) : ℝ) ^ p := by field_simp
    _ ≤ f (a * b ^ k) := h k
    _ ≤ f n := hf hkn

end Erdos714Reduction

namespace Erdos714Criterion

/-- Eventual geometric lower bounds suffice; the finitely many initial sizes do not matter. -/
theorem lower_bound_from_eventual_scaled_sizes (f : ℕ → ℝ) (hf : Monotone f)
    (p : ℝ) (hp : 0 ≤ p) (a b : ℕ) (ha : 0 < a) (hb : 2 ≤ b)
    (c : ℝ) (hc : 0 < c)
    (h : ∀ᶠ k : ℕ in atTop, c * ((a * b ^ k : ℕ) : ℝ) ^ p ≤ f (a * b ^ k)) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ᶠ n : ℕ in atTop, c' * (n : ℝ) ^ p ≤ f n := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp h
  apply Erdos714Reduction.lower_bound_from_scaled_sizes f hf p hp (a * b ^ K) b
    (by positivity) hb c hc
  intro j
  simpa only [pow_add, mul_assoc] using hK (K + j) (by omega)

lemma power_exponent (r : ℕ) (hr : 1 ≤ r) (q : ℕ) :
    (((q ^ r : ℕ) : ℝ)) ^ ((2 : ℝ) - 1 / (r : ℝ)) = (q : ℝ) ^ (2 * r - 1) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity)]
  have h : (r : ℝ) * ((2 : ℝ) - 1 / (r : ℝ)) = ((2 * r - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    field_simp
  rw [h, Real.rpow_natCast]

lemma growing_sizes (r k : ℕ) (hr : 1 ≤ r) : k ≤ (2 ^ k) ^ r := by
  have hk : k ≤ 2 ^ k := (show k < 2 ^ k from Nat.lt_two_pow_self).le
  have hp : 2 ^ k ≤ (2 ^ k) ^ r := by
    simpa only [pow_one] using pow_le_pow_right' (Nat.one_le_pow _ _ (by omega)) hr
  exact hk.trans hp

/-- The desired real lower bound is equivalent to a natural-number bound on geometric sizes. -/
theorem integer_criterion (f : ℕ → ℕ) (hf : Monotone f) (r : ℕ) (hr : 1 ≤ r) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) ≤ (f n : ℝ)) ↔
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      (2 ^ k) ^ (2 * r - 1) ≤ C * f ((2 ^ k) ^ r)) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  constructor
  · rintro ⟨c, hc, h⟩
    obtain ⟨C, hC⟩ := exists_nat_ge (1 / c)
    have hC0 : 0 < C := by
      have : (0 : ℝ) < C := lt_of_lt_of_le (by positivity) hC
      exact_mod_cast this
    have hcC : 1 ≤ (C : ℝ) * c := (div_le_iff₀ hc).mp hC
    obtain ⟨N, hN⟩ := eventually_atTop.mp h
    refine ⟨C, hC0, ?_⟩
    filter_upwards [eventually_ge_atTop N] with k hk
    have hg := hN ((2 ^ k) ^ r) (hk.trans (growing_sizes r k hr))
    rw [power_exponent r hr] at hg
    have hp : (0 : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) ^ (2 * r - 1) := by positivity
    have hm := mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ C)
    have h1 := mul_le_mul_of_nonneg_right hcC hp
    have h1' : ((2 ^ k : ℕ) : ℝ) ^ (2 * r - 1) ≤
        (C : ℝ) * (c * ((2 ^ k : ℕ) : ℝ) ^ (2 * r - 1)) := by
      simpa only [one_mul, mul_assoc] using h1
    exact_mod_cast h1'.trans hm
  · rintro ⟨C, hC, h⟩
    have hC0 : (0 : ℝ) < C := by exact_mod_cast hC
    have hm : Monotone (fun n : ℕ => (f n : ℝ)) := fun a b hab => Nat.cast_le.mpr (hf hab)
    have hp : (0 : ℝ) ≤ (2 : ℝ) - 1 / (r : ℝ) := by
      have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
      have : 1 / (r : ℝ) ≤ 1 := (div_le_one hr0).mpr hr1
      linarith
    have hb : 2 ≤ (2 : ℕ) ^ r := by
      simpa only [pow_one] using pow_le_pow_right' (by omega : (1 : ℕ) ≤ 2) hr
    apply lower_bound_from_eventual_scaled_sizes (fun n => (f n : ℝ)) hm
      ((2 : ℝ) - 1 / (r : ℝ)) hp 1 (2 ^ r) (by omega) hb (1 / C) (by positivity)
    filter_upwards [h] with k hk
    have heq : (2 ^ r) ^ k = (2 ^ k) ^ r := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    simp only [one_mul, heq, power_exponent r hr]
    have hk' : ((2 ^ k : ℕ) : ℝ) ^ (2 * r - 1) ≤ (C : ℝ) * f ((2 ^ k) ^ r) := by
      exact_mod_cast hk
    apply (mul_le_mul_iff_right₀ hC0).mp
    calc
      _ = ((2 ^ k : ℕ) : ℝ) ^ (2 * r - 1) := by field_simp
      _ ≤ _ := by simpa only [mul_comm] using hk'

/-- Exact integer formulation of a single instance of the original conjecture. -/
theorem erdos_integer_criterion (r : ℕ) (hr : 2 ≤ r) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ)) ↔
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      (2 ^ k) ^ (2 * r - 1) ≤
        C * extremalNumber ((2 ^ k) ^ r) (completeBipartiteGraph (Fin r) (Fin r))) := by
  apply integer_criterion _ _ r (by omega)
  apply Erdos714Reduction.extremalNumber_monotone_of_no_isolated
  intro v
  have i : Fin r := ⟨0, by omega⟩
  cases v with
  | inl v => exact ⟨Sum.inr i, by simp⟩
  | inr v => exact ⟨Sum.inl i, by simp⟩

/-- The conjecture at `r` is equivalent to constructing finite graphs at geometric sizes. -/
theorem finite_graph_criterion (r : ℕ) (hr : 2 ≤ r) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ)) ↔
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∃ G : SimpleGraph (Fin ((2 ^ k) ^ r)), ∃ _ : DecidableRel G.Adj,
        (completeBipartiteGraph (Fin r) (Fin r)).Free G ∧
          (2 ^ k) ^ (2 * r - 1) ≤ C * G.edgeFinset.card) := by
  classical
  rw [erdos_integer_criterion r hr]
  have hH : completeBipartiteGraph (Fin r) (Fin r) ≠ ⊥ := by
    intro h
    let i : Fin r := ⟨0, by omega⟩
    have he : (completeBipartiteGraph (Fin r) (Fin r)).Adj (Sum.inl i) (Sum.inr i) := by simp
    rw [h] at he
    exact he
  constructor
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, ?_⟩
    filter_upwards [h] with k hk
    obtain ⟨G, inst, hG⟩ := exists_isExtremal_free (V := Fin ((2 ^ k) ^ r)) hH
    refine ⟨G, inst, hG.prop, ?_⟩
    rw [card_edgeFinset_of_isExtremal_free hG]
    simpa only [Fintype.card_fin] using hk
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, ?_⟩
    filter_upwards [h] with k hk
    obtain ⟨G, inst, hG, hbound⟩ := hk
    have he := card_edgeFinset_le_extremalNumber hG
    simp only [Fintype.card_fin] at he
    exact hbound.trans (Nat.mul_le_mul_left C he)

end Erdos714Criterion

#print axioms Erdos714Criterion.integer_criterion
#print axioms Erdos714Criterion.finite_graph_criterion
