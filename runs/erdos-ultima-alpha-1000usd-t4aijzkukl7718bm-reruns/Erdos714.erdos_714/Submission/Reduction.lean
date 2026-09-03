import FormalConjecturesUtil

open Filter SimpleGraph

namespace Erdos714Reduction

/-- The fourth instance of the conjecture has exponent exactly seven quarters. -/
theorem fourth_instance
    (h : ∀ r : ℕ, 2 ≤ r → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((7 : ℝ) / 4) ≤
        (extremalNumber n (completeBipartiteGraph (Fin 4) (Fin 4)) : ℝ) := by
  convert h 4 (by norm_num) using 1 <;> norm_num

/-- The complete bipartite graph in the conjecture has edges. -/
theorem completeBipartite_ne_bot {r : ℕ} (hr : 2 ≤ r) :
    completeBipartiteGraph (Fin r) (Fin r) ≠ ⊥ := by
  let v : Fin r := ⟨0, by omega⟩
  intro h
  have he : (completeBipartiteGraph (Fin r) (Fin r)).Adj (Sum.inl v) (Sum.inr v) := by
    simp
  rw [h] at he
  exact he

open Classical in
/-- Lower bounds on the extremal number require actual free graphs of that size. -/
theorem lower_bound_iff_graphs {W : Type*} (H : SimpleGraph W) (hH : H ≠ ⊥)
    (p : ℝ) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ p ≤ (extremalNumber n H : ℝ)) ↔
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∃ G : SimpleGraph (Fin n), H.Free G ∧
        c * (n : ℝ) ^ p ≤ (G.edgeFinset.card : ℝ)) := by
  classical
  constructor
  · rintro ⟨c, hc, hn⟩
    refine ⟨c, hc, hn.mono ?_⟩
    intro n hn
    obtain ⟨G, _, hG⟩ := exists_isExtremal_free (V := Fin n) hH
    refine ⟨G, hG.prop, ?_⟩
    have he := card_edgeFinset_of_isExtremal_free hG
    simp only [Fintype.card_fin] at he
    convert hn using 1 <;> congr 1
    convert he using 1
    congr 1
    ext e
    simp
  · rintro ⟨c, hc, hn⟩
    refine ⟨c, hc, hn.mono ?_⟩
    rintro n ⟨G, hG, hn⟩
    apply hn.trans
    exact_mod_cast (by simpa only [Fintype.card_fin] using card_edgeFinset_le_extremalNumber hG)

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

/-- A power lower bound at powers of a fixed integer suffices for a monotone function. -/
theorem lower_bound_from_geometric_sizes (f : ℕ → ℝ) (hf : Monotone f)
    (p : ℝ) (hp : 0 ≤ p) (b : ℕ) (hb : 2 ≤ b)
    (c : ℝ) (hc : 0 < c)
    (h : ∀ k : ℕ, c * ((b ^ k : ℕ) : ℝ) ^ p ≤ f (b ^ k)) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ᶠ n : ℕ in atTop, c' * (n : ℝ) ^ p ≤ f n := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  refine ⟨c / (b : ℝ) ^ p, div_pos hc (Real.rpow_pos_of_pos hb0 p), ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near hn (show 1 < b by omega)
  have hbn : (n : ℝ) ≤ (b : ℝ) * ((b ^ k : ℕ) : ℝ) := by
    exact_mod_cast (by simpa only [pow_succ, mul_comm] using hk'.le)
  have hpw := Real.rpow_le_rpow (show (0 : ℝ) ≤ n by positivity) hbn hp
  rw [Real.mul_rpow (le_of_lt hb0) (by positivity)] at hpw
  calc
    c / (b : ℝ) ^ p * (n : ℝ) ^ p ≤
        c / (b : ℝ) ^ p * ((b : ℝ) ^ p * ((b ^ k : ℕ) : ℝ) ^ p) :=
      mul_le_mul_of_nonneg_left hpw (by positivity)
    _ = c * ((b ^ k : ℕ) : ℝ) ^ p := by
      field_simp
    _ ≤ f (b ^ k) := h k
    _ ≤ f n := hf hk

end Erdos714Reduction
