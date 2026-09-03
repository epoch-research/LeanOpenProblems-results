import FormalConjecturesUtil

/-! Finite-field incidence graphs for the second instance of Erdős Problem 714. -/

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

namespace Erdos714Finite

variable (F : Type*) [Field F]

/-- Two copies of the affine plane, with point-line incidence written symmetrically. -/
def incidenceGraph : SimpleGraph (Bool × (F × F)) where
  Adj u v := u.1 ≠ v.1 ∧ u.2.1 + v.2.1 = u.2.2 * v.2.2
  symm := by
    intro u v h
    exact ⟨h.1.symm, by simpa only [add_comm, mul_comm] using h.2⟩
  loopless := by
    intro v h
    exact h.1 rfl

lemma bool_eq_of_ne {a b c : Bool} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- Any two distinct vertices have at most one common neighbor. -/
theorem common_neighbors_unique
    {a b c d : Bool × (F × F)}
    (hac : (incidenceGraph F).Adj a c) (had : (incidenceGraph F).Adj a d)
    (hbc : (incidenceGraph F).Adj b c) (hbd : (incidenceGraph F).Adj b d) :
    a = b ∨ c = d := by
  have habs : a.1 = b.1 := bool_eq_of_ne hac.1 hbc.1
  have hcds : c.1 = d.1 := bool_eq_of_ne hac.1.symm had.1.symm
  have hmul : (a.2.2 - b.2.2) * (c.2.2 - d.2.2) = 0 := by
    linear_combination -hac.2 + had.2 + hbc.2 - hbd.2
  rcases mul_eq_zero.mp hmul with hab | hcd
  · left
    have hab2 : a.2.2 = b.2.2 := sub_eq_zero.mp hab
    have hab1 : a.2.1 = b.2.1 := by
      have h1 := hac.2
      have h2 := hbc.2
      rw [hab2] at h1
      exact add_right_cancel (h1.trans h2.symm)
    exact Prod.ext habs (Prod.ext hab1 hab2)
  · right
    have hcd2 : c.2.2 = d.2.2 := sub_eq_zero.mp hcd
    have hcd1 : c.2.1 = d.2.1 := by
      have h1 := hac.2
      have h2 := had.2
      rw [hcd2] at h1
      exact add_left_cancel (h1.trans h2.symm)
    exact Prod.ext hcds (Prod.ext hcd1 hcd2)

theorem incidenceGraph_free :
    (completeBipartiteGraph (Fin 2) (Fin 2)).Free (incidenceGraph F) := by
  rintro ⟨f⟩
  have h00 := f.toHom.map_adj (show
    (completeBipartiteGraph (Fin 2) (Fin 2)).Adj (Sum.inl 0) (Sum.inr 0) by simp)
  have h01 := f.toHom.map_adj (show
    (completeBipartiteGraph (Fin 2) (Fin 2)).Adj (Sum.inl 0) (Sum.inr 1) by simp)
  have h10 := f.toHom.map_adj (show
    (completeBipartiteGraph (Fin 2) (Fin 2)).Adj (Sum.inl 1) (Sum.inr 0) by simp)
  have h11 := f.toHom.map_adj (show
    (completeBipartiteGraph (Fin 2) (Fin 2)).Adj (Sum.inl 1) (Sum.inr 1) by simp)
  rcases common_neighbors_unique F h00 h01 h10 h11 with h | h
  · have := f.injective h
    simp at this
  · have := f.injective h
    simp at this

/-- Neighbors are parameterized by one field coordinate. -/
def neighborEquiv (v : Bool × (F × F)) : (incidenceGraph F).neighborSet v ≃ F where
  toFun w := w.val.2.2
  invFun t := ⟨(!v.1, (v.2.2 * t - v.2.1, t)), by
    change v.1 ≠ !v.1 ∧ v.2.1 + (v.2.2 * t - v.2.1) = v.2.2 * t
    constructor
    · cases v.1 <;> decide
    · ring⟩
  left_inv := by
    rintro ⟨⟨s, x, y⟩, hw⟩
    apply Subtype.ext
    apply Prod.ext
    · change (!v.1) = s
      have hs := hw.1
      cases hv : v.1 <;> cases s <;> simp_all
    · apply Prod.ext
      · change v.2.2 * y - v.2.1 = x
        have hx := hw.2
        change v.2.1 + x = v.2.2 * y at hx
        linear_combination -hx
      · rfl
  right_inv t := rfl

open Classical in
theorem incidenceGraph_degree [Fintype F] (v : Bool × (F × F)) :
    (incidenceGraph F).degree v = Fintype.card F := by
  rw [← card_neighborSet_eq_degree]
  exact Fintype.card_congr (neighborEquiv F v)

open Classical in
theorem incidenceGraph_edges [Fintype F] :
    (incidenceGraph F).edgeFinset.card = (Fintype.card F) ^ 3 := by
  have h := (incidenceGraph F).sum_degrees_eq_twice_card_edges
  simp only [incidenceGraph_degree, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_bool, smul_eq_mul] at h
  nlinarith

open Classical in
theorem incidence_lower_bound [Fintype F] :
    (Fintype.card F) ^ 3 ≤ extremalNumber (2 * (Fintype.card F) ^ 2)
      (completeBipartiteGraph (Fin 2) (Fin 2)) := by
  have h := card_edgeFinset_le_extremalNumber (incidenceGraph_free F)
  rw [incidenceGraph_edges] at h
  simpa only [Fintype.card_prod, Fintype.card_bool, pow_two] using h

theorem dyadic_lower_bound (k : ℕ) (hk : k ≠ 0) :
    (2 ^ k) ^ 3 ≤ extremalNumber (2 * (2 ^ k) ^ 2)
      (completeBipartiteGraph (Fin 2) (Fin 2)) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype (GaloisField 2 k) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 k) = 2 ^ k := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 k hk]
  simpa only [hcard] using incidence_lower_bound (GaloisField 2 k)

lemma square_rpow_three_halves (x : ℝ) (hx : 0 ≤ x) :
    (x ^ 2) ^ ((3 : ℝ) / 2) = x ^ 3 := by
  rw [← Real.rpow_natCast_mul hx]
  norm_num

lemma two_square_rpow_le (x : ℝ) (hx : 0 ≤ x) :
    (2 * x ^ 2) ^ ((3 : ℝ) / 2) ≤ 4 * x ^ 3 := by
  rw [Real.mul_rpow (by norm_num) (by positivity), square_rpow_three_halves x hx]
  have h2 : (2 : ℝ) ^ ((3 : ℝ) / 2) ≤ 4 := by
    calc
      _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by norm_num
  exact mul_le_mul_of_nonneg_right h2 (by positivity)

theorem geometric_lower_bound (k : ℕ) :
    (1 / 4 : ℝ) * ((8 * 4 ^ k : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
      (extremalNumber (8 * 4 ^ k) (completeBipartiteGraph (Fin 2) (Fin 2)) : ℝ) := by
  have htw : (2 ^ k) ^ 2 = (4 : ℕ) ^ k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
    norm_num
  have hsize : 2 * (2 ^ (k + 1)) ^ 2 = 8 * 4 ^ k := by
    rw [pow_succ 2 k, mul_pow, htw]
    ring
  have h := dyadic_lower_bound (k + 1) (by omega)
  have hr := two_square_rpow_le (↑(2 ^ (k + 1) : ℕ)) (by positivity)
  rw [← hsize]
  have hr' : ((2 * (2 ^ (k + 1)) ^ 2 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
      4 * ((2 ^ (k + 1) : ℕ) : ℝ) ^ 3 := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hr
  have he : (((2 ^ (k + 1)) ^ 3 : ℕ) : ℝ) ≤
      (extremalNumber (2 * (2 ^ (k + 1)) ^ 2)
        (completeBipartiteGraph (Fin 2) (Fin 2)) : ℝ) := by exact_mod_cast h
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hr' he ⊢
  nlinarith

/-- The conjectured exponent is attained for `r = 2`. -/
theorem second_instance :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (2 : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2)) : ℝ) := by
  have hH : ∀ v : Fin 2 ⊕ Fin 2, ∃ w,
      (completeBipartiteGraph (Fin 2) (Fin 2)).Adj v w := by
    intro v
    cases v with
    | inl v => exact ⟨Sum.inr 0, by simp⟩
    | inr v => exact ⟨Sum.inl 0, by simp⟩
  have hm := Erdos714Reduction.extremalNumber_monotone_of_no_isolated _ hH
  have hm' : Monotone (fun n : ℕ =>
      (extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2)) : ℝ)) := by
    intro a b hab
    exact Nat.cast_le.mpr (hm hab)
  convert Erdos714Reduction.lower_bound_from_scaled_sizes _ hm' ((3 : ℝ) / 2)
    (by norm_num) 8 4 (by norm_num) (by norm_num) (1 / 4) (by norm_num)
    geometric_lower_bound using 1 <;> norm_num

theorem completeBipartite_mono {s r : ℕ} (hsr : s ≤ r) :
    completeBipartiteGraph (Fin s) (Fin s) ⊑ completeBipartiteGraph (Fin r) (Fin r) := by
  let e := Fin.castLEEmb hsr
  refine ⟨⟨⟨Sum.map e e, ?_⟩, ?_⟩⟩
  · intro v w hvw
    cases v <;> cases w <;> simpa using hvw
  · exact Sum.map_injective.mpr ⟨e.injective, e.injective⟩

/-- A uniform weaker lower bound, with exponent `3/2`, for every `r ≥ 2`. -/
theorem all_r_three_halves :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 2 ≤ r → ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((3 : ℝ) / 2) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ) := by
  obtain ⟨c, hc, hn⟩ := second_instance
  refine ⟨c, hc, ?_⟩
  intro r hr
  filter_upwards [hn] with n hn
  have hle := (completeBipartite_mono hr).extremalNumber_le (n := n)
  have hn' : c * (n : ℝ) ^ ((3 : ℝ) / 2) ≤
      (extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2)) : ℝ) := by
    convert hn using 1 <;> norm_num
  exact hn'.trans (Nat.cast_le.mpr hle)

end Erdos714Finite
