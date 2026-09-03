import FormalConjecturesUtil

/-!
# Erdős Problem 714

*References:*
- [erdosproblems.com/714](https://www.erdosproblems.com/714)
-/

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

namespace Erdos714Norm

variable {F : Type*} [Field F]

def Q (ν : F) (x : F × F) : F := x.1 ^ 2 - ν * x.2 ^ 2

def B (ν : F) (x y : F × F) : F := x.1 * y.1 - ν * x.2 * y.2

lemma Q_add (ν : F) (x y : F × F) :
    Q ν (x + y) = Q ν x + Q ν y + 2 * B ν x y := by
  dsimp [Q, B]
  ring

lemma Q_smul (ν t : F) (x : F × F) : Q ν (t • x) = t ^ 2 * Q ν x := by
  dsimp [Q]
  ring

lemma B_smul_left (ν t : F) (x y : F × F) : B ν (t • x) y = t * B ν x y := by
  dsimp [B]
  ring

lemma B_smul_right (ν t : F) (x y : F × F) : B ν x (t • y) = t * B ν x y := by
  dsimp [B]
  ring

lemma Q_zero_iff (ν : F) (hν : ¬IsSquare ν) (x : F × F) : Q ν x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_cases hx : x.2 = 0
    · have h1 : x.1 ^ 2 = 0 := by simpa [Q, hx] using h
      exact Prod.ext (sq_eq_zero_iff.mp h1) hx
    · exfalso
      apply hν
      refine ⟨x.1 / x.2, ?_⟩
      dsimp [Q] at h
      field_simp
      linear_combination -h
  · rintro rfl
    simp [Q]

lemma Q_ne_zero (ν : F) (hν : ¬IsSquare ν) {x : F × F} (hx : x ≠ 0) : Q ν x ≠ 0 :=
  mt (Q_zero_iff ν hν x).mp hx

def inversion (ν : F) (x : F × F) : F × F := (Q ν x)⁻¹ • x

lemma Q_inversion (ν : F) (x : F × F) : Q ν (inversion ν x) = (Q ν x)⁻¹ := by
  rw [inversion, Q_smul]
  by_cases h : Q ν x = 0
  · simp [h]
  · field_simp

lemma inversion_involutive (ν : F) (hν : ¬IsSquare ν) : Function.Involutive (inversion ν) := by
  intro x
  by_cases hx : x = 0
  · subst x
    simp [inversion, Q]
  · have hq := Q_ne_zero ν hν hx
    rw [inversion, Q_inversion, inv_inv, inversion, smul_smul, mul_inv_cancel₀ hq, one_smul]

lemma inversion_injective (ν : F) (hν : ¬IsSquare ν) : Function.Injective (inversion ν) :=
  (inversion_involutive ν hν).injective

/-- Three collinear points on a circle cannot all be distinct when the norm is anisotropic. -/
theorem circle_collinear (ν : F) (hν : ¬IsSquare ν) (u v w : F × F) (A B C : F)
    (hu : Q ν u + A * u.1 + B * u.2 = C)
    (hv : Q ν v + A * v.1 + B * v.2 = C)
    (hw : Q ν w + A * w.1 + B * w.2 = C)
    (hcol : (v.1 - u.1) * (w.2 - u.2) - (v.2 - u.2) * (w.1 - u.1) = 0) :
    u = v ∨ u = w ∨ v = w := by
  by_cases huv : u = v
  · exact Or.inl huv
  have hd : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  have hq := Q_ne_zero ν hν hd
  have hparam : ∃ t : F, w = u + t • (v - u) := by
    by_cases h1 : v.1 - u.1 = 0
    · have h2 : v.2 - u.2 ≠ 0 := by
        intro h2
        apply huv
        exact Prod.ext (sub_eq_zero.mp h1).symm (sub_eq_zero.mp h2).symm
      refine ⟨(w.2 - u.2) / (v.2 - u.2), ?_⟩
      apply Prod.ext
      · dsimp
        have hw1 : w.1 - u.1 = 0 := by
          apply (mul_eq_zero.mp (show (v.2 - u.2) * (w.1 - u.1) = 0 by
            linear_combination -hcol + (w.2 - u.2) * h1)).resolve_left h2
        rw [h1, mul_zero, add_zero]
        exact sub_eq_zero.mp hw1
      · dsimp
        field_simp
        ring
    · refine ⟨(w.1 - u.1) / (v.1 - u.1), ?_⟩
      apply Prod.ext
      · dsimp
        field_simp
        ring
      · dsimp
        field_simp
        linear_combination hcol
  obtain ⟨t, rfl⟩ := hparam
  have ht : t * (t - 1) * Q ν (v - u) = 0 := by
    dsimp [Q] at hu hv hw ⊢
    linear_combination hw - t * hv - (1 - t) * hu
  have ht' : t = 0 ∨ t = 1 := by
    have := (mul_eq_zero.mp ht).resolve_right hq
    simpa only [mul_eq_zero, sub_eq_zero] using this
  rcases ht' with rfl | rfl
  · exact Or.inr (Or.inl (by simp))
  · exact Or.inr (Or.inr (by simp))

/-- A line intersects an anisotropic circle in at most two points. -/
theorem circle_line (ν : F) (hν : ¬IsSquare ν) (u v w : F × F) (A B C D E K : F)
    (hu : Q ν u + A * u.1 + B * u.2 = C)
    (hv : Q ν v + A * v.1 + B * v.2 = C)
    (hw : Q ν w + A * w.1 + B * w.2 = C)
    (lu : D * u.1 + E * u.2 = K)
    (lv : D * v.1 + E * v.2 = K)
    (lw : D * w.1 + E * w.2 = K)
    (hDE : D ≠ 0 ∨ E ≠ 0) : u = v ∨ u = w ∨ v = w := by
  apply circle_collinear ν hν u v w A B C hu hv hw
  rcases hDE with hD | hE
  · apply (mul_eq_zero.mp (show D *
      ((v.1 - u.1) * (w.2 - u.2) - (v.2 - u.2) * (w.1 - u.1)) = 0 by
        linear_combination (w.2 - u.2) * (lv - lu) - (v.2 - u.2) * (lw - lu))).resolve_left hD
  · apply (mul_eq_zero.mp (show E *
      ((v.1 - u.1) * (w.2 - u.2) - (v.2 - u.2) * (w.1 - u.1)) = 0 by
        linear_combination (v.1 - u.1) * (lw - lu) - (w.1 - u.1) * (lv - lu))).resolve_left hE

/-- Radial inversion changes the common-neighbor equations into circle equations. -/
lemma transformed_equation (ν : F) (d t : F × F) (a₀ a b : F)
    (hd : Q ν d ≠ 0) (ht : Q ν t ≠ 0) (ha : a₀ ≠ 0)
    (h₀ : Q ν t = a₀ * b) (h : Q ν (d + t) = a * b) :
    Q ν (inversion ν t) + 2 * B ν (inversion ν d) (inversion ν t) =
      (a - a₀) / (a₀ * Q ν d) := by
  rw [Q_add] at h
  have h' : Q ν d + 2 * B ν d t = (a - a₀) * b := by
    linear_combination h - h₀
  rw [Q_inversion, inversion, inversion, B_smul_left, B_smul_right]
  field_simp
  linear_combination a₀ * h' + (a₀ - a) * h₀

/-- The quadratic-norm incidence relation has no three-by-three rectangle. -/
theorem no_three_by_three (ν : F) (hν : ¬IsSquare ν) (h₂ : (2 : F) ≠ 0)
    (x y : Fin 3 → F × F) (a b : Fin 3 → F)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (he : ∀ i j, Q ν (x i + y j) = a i * b j) : False := by
  let d₁ := x 1 - x 0
  let d₂ := x 2 - x 0
  have hd₁ : d₁ ≠ 0 := by
    intro h
    have := hx (sub_eq_zero.mp h)
    norm_num [Fin.ext_iff] at this
  have hd₂ : d₂ ≠ 0 := by
    intro h
    have := hx (sub_eq_zero.mp h)
    norm_num [Fin.ext_iff] at this
  have hd₁₂ : d₁ ≠ d₂ := by
    intro h
    have := hx (sub_left_injective h)
    norm_num [Fin.ext_iff] at this
  let z : Fin 3 → F × F := fun j => inversion ν (x 0 + y j)
  have hz : Function.Injective z := by
    intro i j h
    apply hy
    exact add_left_cancel (inversion_injective ν hν h)
  have ht : ∀ j, Q ν (x 0 + y j) ≠ 0 := by
    intro j
    rw [he]
    exact mul_ne_zero (ha 0) (hb j)
  let u₁ := inversion ν d₁
  let u₂ := inversion ν d₂
  let C₁ := (a 1 - a 0) / (a 0 * Q ν d₁)
  let C₂ := (a 2 - a 0) / (a 0 * Q ν d₂)
  have hc₁ : ∀ j, Q ν (z j) + (2 * u₁.1) * (z j).1 + (-2 * ν * u₁.2) * (z j).2 = C₁ := by
    intro j
    have ht' : Q ν (d₁ + (x 0 + y j)) = a 1 * b j := by
      convert he 1 j using 2 <;> dsimp [d₁] <;> abel
    have h := transformed_equation ν d₁ (x 0 + y j) (a 0) (a 1) (b j)
      (Q_ne_zero ν hν hd₁) (ht j) (ha 0) (he 0 j) ht'
    change Q ν (z j) + 2 * B ν u₁ (z j) = C₁ at h
    dsimp only [B] at h
    linear_combination h
  have hc₂ : ∀ j, Q ν (z j) + (2 * u₂.1) * (z j).1 + (-2 * ν * u₂.2) * (z j).2 = C₂ := by
    intro j
    have ht' : Q ν (d₂ + (x 0 + y j)) = a 2 * b j := by
      convert he 2 j using 2 <;> dsimp [d₂] <;> abel
    have h := transformed_equation ν d₂ (x 0 + y j) (a 0) (a 2) (b j)
      (Q_ne_zero ν hν hd₂) (ht j) (ha 0) (he 0 j) ht'
    change Q ν (z j) + 2 * B ν u₂ (z j) = C₂ at h
    dsimp only [B] at h
    linear_combination h
  have hl : ∀ j, (2 * (u₁.1 - u₂.1)) * (z j).1 + (-2 * ν * (u₁.2 - u₂.2)) * (z j).2 = C₁ - C₂ := by
    intro j
    linear_combination hc₁ j - hc₂ j
  have hu₁₂ : u₁ ≠ u₂ := fun h => hd₁₂ (inversion_injective ν hν h)
  have hν₀ : ν ≠ 0 := by
    rintro rfl
    exact hν ⟨0, by ring⟩
  have hDE : 2 * (u₁.1 - u₂.1) ≠ 0 ∨ -2 * ν * (u₁.2 - u₂.2) ≠ 0 := by
    by_cases h₁ : u₁.1 = u₂.1
    · right
      apply mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h₂) hν₀)
      apply sub_ne_zero.mpr
      intro h₂'
      exact hu₁₂ (Prod.ext h₁ h₂')
    · exact Or.inl (mul_ne_zero h₂ (sub_ne_zero.mpr h₁))
  have h := circle_line ν hν (z 0) (z 1) (z 2) (2 * u₁.1) (-2 * ν * u₁.2) C₁
    (2 * (u₁.1 - u₂.1)) (-2 * ν * (u₁.2 - u₂.2)) (C₁ - C₂)
    (hc₁ 0) (hc₁ 1) (hc₁ 2) (hl 0) (hl 1) (hl 2) hDE
  rcases h with h | h | h
  all_goals have := hz h; norm_num [Fin.ext_iff] at this

/-- The bipartite quadratic norm graph, with nonzero field weights. -/
def normGraph (ν : F) : SimpleGraph (Bool × ((F × F) × Fˣ)) where
  Adj u v := u.1 ≠ v.1 ∧ Q ν (u.2.1 + v.2.1) = (u.2.2 : F) * (v.2.2 : F)
  symm := by
    intro u v h
    exact ⟨h.1.symm, by simpa only [add_comm, mul_comm] using h.2⟩
  loopless := by
    intro v h
    exact h.1 rfl

lemma same_side_of_common_neighbor {s t u : Bool} (h : s ≠ u) (h' : t ≠ u) : s = t := by
  cases s <;> cases t <;> cases u <;> simp_all

lemma point_injective_on_neighbors (ν : F) {u v w : Bool × ((F × F) × Fˣ)}
    (hu : (normGraph ν).Adj u w) (hv : (normGraph ν).Adj v w)
    (hpoint : u.2.1 = v.2.1) : u = v := by
  have hs := same_side_of_common_neighbor hu.1 hv.1
  have hp : (u.2.2 : F) * (w.2.2 : F) = (v.2.2 : F) * (w.2.2 : F) := by
    rw [← hu.2, ← hv.2, hpoint]
  have hw : u.2.2 = v.2.2 := Units.ext (mul_right_cancel₀ w.2.2.ne_zero hp)
  exact Prod.ext hs (Prod.ext hpoint hw)

theorem normGraph_free (ν : F) (hν : ¬IsSquare ν) (h₂ : (2 : F) ≠ 0) :
    (completeBipartiteGraph (Fin 3) (Fin 3)).Free (normGraph ν) := by
  rintro ⟨f⟩
  have he : ∀ i j : Fin 3, (normGraph ν).Adj (f (Sum.inl i)) (f (Sum.inr j)) := by
    intro i j
    exact f.toHom.map_adj (by simp)
  have hx : Function.Injective (fun i : Fin 3 => (f (Sum.inl i)).2.1) := by
    intro i j h
    apply Sum.inl_injective
    apply f.injective
    exact point_injective_on_neighbors ν (he i 0) (he j 0) h
  have hy : Function.Injective (fun i : Fin 3 => (f (Sum.inr i)).2.1) := by
    intro i j h
    apply Sum.inr_injective
    apply f.injective
    exact point_injective_on_neighbors ν (he 0 i).symm (he 0 j).symm h
  exact no_three_by_three ν hν h₂
    (fun i => (f (Sum.inl i)).2.1) (fun j => (f (Sum.inr j)).2.1)
    (fun i => ((f (Sum.inl i)).2.2 : F)) (fun j => ((f (Sum.inr j)).2.2 : F))
    (fun i => (f (Sum.inl i)).2.2.ne_zero) (fun j => (f (Sum.inr j)).2.2.ne_zero)
    hx hy (fun i j => (he i j).2)

/-- A neighbor is uniquely specified by a nonzero translated plane coordinate. -/
def neighborEquiv (ν : F) (hν : ¬IsSquare ν) (v : Bool × ((F × F) × Fˣ)) :
    (normGraph ν).neighborSet v ≃ {z : F × F // z ≠ 0} where
  toFun w := ⟨v.2.1 + w.val.2.1, by
    intro hz
    have hq := (Q_zero_iff ν hν _).mpr hz
    rw [w.property.2] at hq
    exact mul_ne_zero v.2.2.ne_zero w.val.2.2.ne_zero hq⟩
  invFun z := ⟨(!v.1, (z.val - v.2.1,
    Units.mk0 (Q ν z.val / (v.2.2 : F))
      (div_ne_zero (Q_ne_zero ν hν z.property) v.2.2.ne_zero))), by
    constructor
    · change v.1 ≠ (!v.1)
      cases v.1 <;> decide
    · change Q ν (v.2.1 + (z.val - v.2.1)) = (v.2.2 : F) * (Q ν z.val / (v.2.2 : F))
      have hz : v.2.1 + (z.val - v.2.1) = z.val := by abel
      rw [hz]
      field_simp⟩
  left_inv := by
    intro w
    apply Subtype.ext
    apply Prod.ext
    · change (!v.1) = w.val.1
      have hs := w.property.1
      cases hv : v.1 <;> cases hw : w.val.1 <;> simp_all
    · apply Prod.ext
      · change v.2.1 + w.val.2.1 - v.2.1 = w.val.2.1
        abel
      · apply Units.ext
        change Q ν (v.2.1 + w.val.2.1) / (v.2.2 : F) = (w.val.2.2 : F)
        rw [w.property.2]
        field_simp
  right_inv := by
    intro z
    apply Subtype.ext
    change v.2.1 + (z.val - v.2.1) = z.val
    abel

open Classical in
theorem normGraph_degree [Fintype F] (ν : F) (hν : ¬IsSquare ν)
    (v : Bool × ((F × F) × Fˣ)) :
    (normGraph ν).degree v = (Fintype.card F) ^ 2 - 1 := by
  rw [← card_neighborSet_eq_degree, Fintype.card_congr (neighborEquiv ν hν v)]
  rw [Fintype.card_subtype_compl]
  simp [Fintype.card_prod, pow_two]

open Classical in
theorem normGraph_edges [Fintype F] (ν : F) (hν : ¬IsSquare ν) :
    (normGraph ν).edgeFinset.card =
      (Fintype.card F) ^ 2 * (Fintype.card F - 1) * ((Fintype.card F) ^ 2 - 1) := by
  have h := (normGraph ν).sum_degrees_eq_twice_card_edges
  simp only [normGraph_degree ν hν, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_bool, Fintype.card_units, smul_eq_mul] at h
  nlinarith

open Classical in
theorem normGraph_lower_bound [Fintype F] (ν : F) (hν : ¬IsSquare ν) (h₂ : (2 : F) ≠ 0) :
    (Fintype.card F) ^ 2 * (Fintype.card F - 1) * ((Fintype.card F) ^ 2 - 1) ≤
      extremalNumber (2 * ((Fintype.card F) ^ 2 * (Fintype.card F - 1)))
        (completeBipartiteGraph (Fin 3) (Fin 3)) := by
  have h := card_edgeFinset_le_extremalNumber (normGraph_free ν hν h₂)
  rw [normGraph_edges ν hν] at h
  simpa only [Fintype.card_prod, Fintype.card_bool, Fintype.card_units, pow_two] using h

theorem cubic_power_lower_bound (k : ℕ) (hk : k ≠ 0) :
    (3 ^ k) ^ 2 * (3 ^ k - 1) * ((3 ^ k) ^ 2 - 1) ≤
      extremalNumber (2 * ((3 ^ k) ^ 2 * (3 ^ k - 1)))
        (completeBipartiteGraph (Fin 3) (Fin 3)) := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Fintype (GaloisField 3 k) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 k) = 3 ^ k := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 3 k hk]
  have hchar : ringChar (GaloisField 3 k) ≠ 2 := by
    rw [ringChar.eq (GaloisField 3 k) 3]
    decide
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hchar
  have h₂ : (2 : GaloisField 3 k) ≠ 0 := by
    intro h
    have h' := (CharP.cast_eq_zero_iff (GaloisField 3 k) 3 2).mp h
    norm_num at h'
  simpa only [hcard] using normGraph_lower_bound ν hν h₂

theorem k33_mono :
    Monotone (fun n => extremalNumber n (completeBipartiteGraph (Fin 3) (Fin 3))) := by
  apply Erdos714Reduction.extremalNumber_monotone_of_no_isolated
  intro v
  cases v with
  | inl v => exact ⟨Sum.inr 0, by simp⟩
  | inr v => exact ⟨Sum.inl 0, by simp⟩

lemma cube_rpow_five_thirds (x : ℝ) (hx : 0 ≤ x) :
    (x ^ 3) ^ ((5 : ℝ) / 3) = x ^ 5 := by
  rw [← Real.rpow_natCast_mul hx]
  norm_num

lemma two_cube_rpow_le (x : ℝ) (hx : 0 ≤ x) :
    (2 * x ^ 3) ^ ((5 : ℝ) / 3) ≤ 4 * x ^ 5 := by
  rw [Real.mul_rpow (by norm_num) (by positivity), cube_rpow_five_thirds x hx]
  have h2 : (2 : ℝ) ^ ((5 : ℝ) / 3) ≤ 4 := by
    calc
      _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by norm_num
  exact mul_le_mul_of_nonneg_right h2 (by positivity)

lemma edge_count_lower_real (q : ℕ) (hq : 2 ≤ q) :
    (q : ℝ) ^ 5 / 4 ≤ ((q ^ 2 * (q - 1) * (q ^ 2 - 1) : ℕ) : ℝ) := by
  have hq1 : 1 ≤ q := by omega
  have hq2 : 1 ≤ q ^ 2 := by nlinarith
  have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
  norm_num only [Nat.cast_mul, Nat.cast_sub hq1, Nat.cast_sub hq2, Nat.cast_pow, Nat.cast_one]
  have h1 : (q : ℝ) / 2 ≤ (q : ℝ) - 1 := by linarith
  have h2 : (q : ℝ) ^ 2 / 2 ≤ (q : ℝ) ^ 2 - 1 := by nlinarith
  have hmul := mul_le_mul h1 h2 (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ 2 / 2)
    (by linarith : (0 : ℝ) ≤ (q : ℝ) - 1)
  have hmul' := mul_le_mul_of_nonneg_left hmul (sq_nonneg (q : ℝ))
  nlinarith only [hmul']

theorem cubic_geometric_lower_bound (k : ℕ) :
    (1 / 16 : ℝ) * ((54 * 27 ^ k : ℕ) : ℝ) ^ ((5 : ℝ) / 3) ≤
      (extremalNumber (54 * 27 ^ k) (completeBipartiteGraph (Fin 3) (Fin 3)) : ℝ) := by
  let q := 3 ^ (k + 1)
  have hq : 2 ≤ q := by
    dsimp [q]
    have : 1 ≤ (3 : ℕ) ^ k := Nat.one_le_pow k 3 (by norm_num)
    rw [pow_succ]
    omega
  have hth : (3 ^ k) ^ 3 = (27 : ℕ) ^ k := by
    rw [← pow_mul, Nat.mul_comm k 3, pow_mul]
    norm_num
  have hsize : 2 * q ^ 3 = 54 * 27 ^ k := by
    dsimp [q]
    rw [pow_succ 3 k, mul_pow, hth]
    ring
  have hsmall : 2 * (q ^ 2 * (q - 1)) ≤ 2 * q ^ 3 := by
    calc
      _ ≤ 2 * (q ^ 2 * q) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le q 1))
      _ = _ := by ring
  have hn := (cubic_power_lower_bound (k + 1) (by omega)).trans (k33_mono hsmall)
  have he : ((q ^ 2 * (q - 1) * (q ^ 2 - 1) : ℕ) : ℝ) ≤
      (extremalNumber (2 * q ^ 3) (completeBipartiteGraph (Fin 3) (Fin 3)) : ℝ) := by
    exact_mod_cast hn
  have hl := (edge_count_lower_real q hq).trans he
  have hr := two_cube_rpow_le (q : ℝ) (by positivity)
  rw [← hsize]
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  nlinarith only [hr, hl]

/-- The conjectured exponent is attained for `r = 3`. -/
theorem third_instance :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (3 : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin 3) (Fin 3)) : ℝ) := by
  have hm : Monotone (fun n : ℕ =>
      (extremalNumber n (completeBipartiteGraph (Fin 3) (Fin 3)) : ℝ)) := by
    intro a b hab
    exact Nat.cast_le.mpr (k33_mono hab)
  convert Erdos714Reduction.lower_bound_from_scaled_sizes _ hm ((5 : ℝ) / 3)
    (by norm_num) 54 27 (by norm_num) (by norm_num) (1 / 16) (by norm_num)
    cubic_geometric_lower_bound using 1 <;> norm_num

end Erdos714Norm

namespace Erdos714Alteration

open Finset

variable {E : Type*} [DecidableEq E]

/-- Delete at most one element for each forbidden set present in the original set. -/
theorem delete_forbidden (s : Finset E) (A : Finset (Finset E))
    (hA : ∀ a ∈ A, a.Nonempty) :
    ∃ t : Finset E, t ⊆ s ∧ (∀ a ∈ A, ¬a ⊆ t) ∧
      s.card ≤ t.card + (A.filter (· ⊆ s)).card := by
  induction A using Finset.induction_on generalizing s with
  | empty => exact ⟨s, Subset.refl _, by simp, by simp⟩
  | @insert a A ha ih =>
    by_cases has : a ⊆ s
    · obtain ⟨e, hea⟩ := hA a (mem_insert_self _ _)
      have hes : e ∈ s := has hea
      obtain ⟨t, hts, ht, hc⟩ := ih (s.erase e) (by
        intro b hb
        exact hA b (mem_insert_of_mem hb))
      refine ⟨t, hts.trans (erase_subset _ _), ?_, ?_⟩
      · intro b hb
        rcases mem_insert.mp hb with rfl | hb
        · intro hat
          exact (mem_erase.mp (hts (hat hea))).1 rfl
        · exact ht b hb
      · have hfilter : (A.filter (· ⊆ s.erase e)).card ≤ (A.filter (· ⊆ s)).card := by
          apply card_le_card
          intro b hb
          exact mem_filter.mpr ⟨(mem_filter.mp hb).1, (mem_filter.mp hb).2.trans (erase_subset _ _)⟩
        have hcard : s.card = (s.erase e).card + 1 := by
          exact (card_erase_add_one hes).symm
        rw [filter_insert, if_pos has, card_insert_of_notMem (by intro h; exact ha (mem_filter.mp h).1)]
        omega
    · obtain ⟨t, hts, ht, hc⟩ := ih s (by
        intro b hb
        exact hA b (mem_insert_of_mem hb))
      refine ⟨t, hts, ?_, ?_⟩
      · intro b hb
        rcases mem_insert.mp hb with rfl | hb
        · exact fun h => has (h.trans hts)
        · exact ht b hb
      · simpa only [filter_insert, if_neg has] using hc

variable [Fintype E] (k : ℕ) [NeZero k]

/-- Coloring outside a fixed set freely is equivalent to coloring it zero on that set. -/
def coloringEquiv (s : Finset E) :
    {f : E → Fin k // ∀ e ∈ s, f e = 0} ≃ ({e : E // e ∉ s} → Fin k) where
  toFun f e := f.val e.val
  invFun g := ⟨fun e => if h : e ∈ s then 0 else g ⟨e, h⟩, by
    intro e he
    simp [he]⟩
  left_inv := by
    intro f
    apply Subtype.ext
    funext e
    by_cases he : e ∈ s
    · simp [he, f.property e he]
    · simp [he]
  right_inv := by
    intro g
    funext e
    simp [e.property]

lemma count_colorings (s : Finset E) :
    Fintype.card {f : E → Fin k // ∀ e ∈ s, f e = 0} = k ^ (Fintype.card E - s.card) := by
  rw [Fintype.card_congr (coloringEquiv k s), Fintype.card_fun,
    Fintype.card_fin, Fintype.card_subtype_compl]
  simp

lemma indicator_sum (s : Finset E) :
    (∑ f : E → Fin k, if ∀ e ∈ s, f e = 0 then (1 : ℝ) else 0) =
      (k : ℝ) ^ (Fintype.card E - s.card) := by
  have h := count_colorings k s
  rw [Fintype.card_subtype] at h
  exact_mod_cast (by simpa only [Finset.sum_boole] using h)

lemma indicator_average (s : Finset E) :
    (∑ f : E → Fin k, if ∀ e ∈ s, f e = 0 then (1 : ℝ) else 0) /
        (Fintype.card (E → Fin k) : ℝ) = 1 / (k : ℝ) ^ s.card := by
  rw [indicator_sum, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne k)
  have hs : Fintype.card E = (Fintype.card E - s.card) + s.card := by
    exact (Nat.sub_add_cancel (s.card_le_univ)).symm
  conv_lhs => rhs; rw [hs, pow_add]
  field_simp

/-- The sampled subset is the zero color class. -/
def sample (f : E → Fin k) : Finset E := univ.filter (fun e => f e = 0)

lemma subset_sample (s : Finset E) (f : E → Fin k) :
    s ⊆ sample k f ↔ ∀ e ∈ s, f e = 0 := by
  simp [sample, Finset.subset_iff]

lemma sample_average :
    (∑ f : E → Fin k, ((sample k f).card : ℝ)) /
      (Fintype.card (E → Fin k) : ℝ) = (Fintype.card E : ℝ) / k := by
  simp only [sample, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [sum_comm, sum_div]
  have he (e : E) :
      (∑ f : E → Fin k, if f e = 0 then (1 : ℝ) else 0) /
        (Fintype.card (E → Fin k) : ℝ) = 1 / k := by
    simpa using indicator_average k {e}
  simp only [he, sum_const, card_univ, nsmul_eq_mul, mul_one_div]

lemma forbidden_average (A : Finset (Finset E)) (m : ℕ)
    (hA : ∀ a ∈ A, a.card = m) :
    (∑ f : E → Fin k, ((A.filter (· ⊆ sample k f)).card : ℝ)) /
      (Fintype.card (E → Fin k) : ℝ) = (A.card : ℝ) / (k : ℝ) ^ m := by
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, subset_sample]
  rw [sum_comm, sum_div]
  have ha (a : Finset E) (ha : a ∈ A) :
      (∑ f : E → Fin k, if ∀ e ∈ a, f e = 0 then (1 : ℝ) else 0) /
        (Fintype.card (E → Fin k) : ℝ) = 1 / (k : ℝ) ^ m := by
    simpa only [hA a ha] using indicator_average k a
  rw [Finset.sum_congr rfl ha]
  simp only [sum_const, nsmul_eq_mul, mul_one_div]

/-- The elementary alteration lower bound for an `m`-uniform hypergraph. -/
theorem independent_lower_bound (A : Finset (Finset E)) (m : ℕ) (hm : 0 < m)
    (hA : ∀ a ∈ A, a.card = m) :
    ∃ t : Finset E, (∀ a ∈ A, ¬a ⊆ t) ∧
      (Fintype.card E : ℝ) / k - (A.card : ℝ) / (k : ℝ) ^ m ≤ (t.card : ℝ) := by
  let score (f : E → Fin k) : ℝ := (sample k f).card - (A.filter (· ⊆ sample k f)).card
  let v : ℝ := (Fintype.card E : ℝ) / k - (A.card : ℝ) / (k : ℝ) ^ m
  have havg : (∑ f : E → Fin k, score f) / (Fintype.card (E → Fin k) : ℝ) = v := by
    dsimp [score, v]
    rw [sum_sub_distrib, sub_div, sample_average, forbidden_average k A m hA]
  have hN : (Fintype.card (E → Fin k) : ℝ) ≠ 0 := by positivity
  have hsum : ∑ f : E → Fin k, v ≤ ∑ f : E → Fin k, score f := by
    rw [sum_const, card_univ, nsmul_eq_mul, (div_eq_iff hN).mp havg]
    exact le_of_eq (mul_comm _ _)
  obtain ⟨f, _, hf⟩ := Finset.exists_le_of_sum_le (Finset.univ_nonempty : (univ : Finset (E → Fin k)).Nonempty) hsum
  obtain ⟨t, ht, htA, htc⟩ := delete_forbidden (sample k f) A (by
    intro a ha
    rw [← card_pos, hA a ha]
    exact hm)
  refine ⟨t, htA, hf.trans ?_⟩
  have htc' : ((sample k f).card : ℝ) ≤ (t.card : ℝ) + (A.filter (· ⊆ sample k f)).card := by
    exact_mod_cast htc
  dsimp [score]
  linarith

end Erdos714Alteration

namespace Erdos714Random

open Finset

open SimpleGraph

variable (n r : ℕ)

/-- A bipartite graph with edge set given as an ordered-pair set. -/
def bipGraph (T : Finset (Fin n × Fin n)) : SimpleGraph (Fin n ⊕ Fin n) where
  Adj
    | Sum.inl x, Sum.inr y => (x, y) ∈ T
    | Sum.inr y, Sum.inl x => (x, y) ∈ T
    | _, _ => False
  symm := by
    intro x y
    cases x <;> cases y <;> simp
  loopless := by
    intro x
    cases x <;> simp

lemma edgePair_injective : Function.Injective
    (fun p : Fin n × Fin n => s(Sum.inl p.1, Sum.inr p.2) : Fin n × Fin n → Sym2 (Fin n ⊕ Fin n)) := by
  intro x y h
  rcases Sym2.eq_iff.mp h with h | h
  · exact Prod.ext (Sum.inl.inj h.1) (Sum.inr.inj h.2)
  · cases h.1

open Classical in
lemma bipGraph_edges (T : Finset (Fin n × Fin n)) : (bipGraph n T).edgeFinset.card = T.card := by
  have he : (bipGraph n T).edgeFinset = T.image (fun p => s(Sum.inl p.1, Sum.inr p.2)) := by
    ext e
    refine Sym2.inductionOn e ?_
    intro x y
    cases x <;> cases y <;> simp [SimpleGraph.mem_edgeFinset, bipGraph, Sym2.eq_iff, Prod.exists]
  rw [he, Finset.card_image_of_injective _ (edgePair_injective n)]

/-- All potential copies of an `r` by `r` rectangle in the pair universe. -/
def rectangles : Finset (Finset (Fin n × Fin n)) :=
  ((univ.powersetCard r).product (univ.powersetCard r)).image (fun p => p.1 ×ˢ p.2)

lemma mem_rectangles_iff (T : Finset (Fin n × Fin n)) :
    T ∈ rectangles n r ↔ ∃ L R : Finset (Fin n), L.card = r ∧ R.card = r ∧ T = L ×ˢ R := by
  simp [rectangles, Finset.mem_powersetCard, Prod.exists, eq_comm]
  aesop

lemma rectangle_card (T : Finset (Fin n × Fin n)) (hT : T ∈ rectangles n r) : T.card = r ^ 2 := by
  obtain ⟨L, R, hL, hR, rfl⟩ := (mem_rectangles_iff n r T).mp hT
  simp [hL, hR, pow_two]

lemma rectangles_card_le : (rectangles n r).card ≤ n ^ (2 * r) := by
  calc
    (rectangles n r).card ≤ ((univ.powersetCard r : Finset (Finset (Fin n))).product
      (univ.powersetCard r)).card := card_image_le
    _ = (n.choose r) ^ 2 := by simp [pow_two]
    _ ≤ (n ^ r) ^ 2 := Nat.pow_le_pow_left (Nat.choose_le_pow n r) 2
    _ = n ^ (2 * r) := by rw [← pow_mul, Nat.mul_comm]

/-- A copy of the complete bipartite graph in a bipartite graph gives a rectangle. -/
lemma copy_gives_rectangle (hr : 0 < r) (T : Finset (Fin n × Fin n))
    (f : (completeBipartiteGraph (Fin r) (Fin r)).Copy (bipGraph n T)) :
    ∃ L R : Finset (Fin n), L.card = r ∧ R.card = r ∧ L ×ˢ R ⊆ T := by
  let i₀ : Fin r := ⟨0, hr⟩
  have he (i j : Fin r) : (bipGraph n T).Adj (f (Sum.inl i)) (f (Sum.inr j)) :=
    f.toHom.map_adj (by simp)
  cases hf₀ : f (Sum.inl i₀) with
  | inl x₀ =>
    have hright : ∀ j : Fin r, ∃ y : Fin n, f (Sum.inr j) = Sum.inr y := by
      intro j
      have h := he i₀ j
      cases hfj : f (Sum.inr j) with
      | inl y => simp [hf₀, hfj, bipGraph] at h
      | inr y => exact ⟨y, rfl⟩
    choose y hy using hright
    have hleft : ∀ i : Fin r, ∃ x : Fin n, f (Sum.inl i) = Sum.inl x := by
      intro i
      have h := he i i₀
      cases hfi : f (Sum.inl i) with
      | inl x => exact ⟨x, rfl⟩
      | inr x => simp [hfi, hy i₀, bipGraph] at h
    choose x hx using hleft
    have hxi : Function.Injective x := by
      intro i j h
      apply Sum.inl_injective
      apply f.injective
      change f (Sum.inl i) = f (Sum.inl j)
      rw [hx i, hx j, h]
    have hyi : Function.Injective y := by
      intro i j h
      apply Sum.inr_injective
      apply f.injective
      change f (Sum.inr i) = f (Sum.inr j)
      rw [hy i, hy j, h]
    refine ⟨univ.image x, univ.image y, ?_, ?_, ?_⟩
    · simp [card_image_of_injective _ hxi]
    · simp [card_image_of_injective _ hyi]
    · rintro ⟨u, v⟩ h
      obtain ⟨hu, hv⟩ := mem_product.mp h
      obtain ⟨i, _, rfl⟩ := mem_image.mp hu
      obtain ⟨j, _, rfl⟩ := mem_image.mp hv
      simpa only [hx i, hy j, bipGraph] using he i j
  | inr y₀ =>
    have hright : ∀ j : Fin r, ∃ x : Fin n, f (Sum.inr j) = Sum.inl x := by
      intro j
      have h := he i₀ j
      cases hfj : f (Sum.inr j) with
      | inl x => exact ⟨x, rfl⟩
      | inr x => simp [hf₀, hfj, bipGraph] at h
    choose x hx using hright
    have hleft : ∀ i : Fin r, ∃ y : Fin n, f (Sum.inl i) = Sum.inr y := by
      intro i
      have h := he i i₀
      cases hfi : f (Sum.inl i) with
      | inl y => simp [hfi, hx i₀, bipGraph] at h
      | inr y => exact ⟨y, rfl⟩
    choose y hy using hleft
    have hxi : Function.Injective x := by
      intro i j h
      apply Sum.inr_injective
      apply f.injective
      change f (Sum.inr i) = f (Sum.inr j)
      rw [hx i, hx j, h]
    have hyi : Function.Injective y := by
      intro i j h
      apply Sum.inl_injective
      apply f.injective
      change f (Sum.inl i) = f (Sum.inl j)
      rw [hy i, hy j, h]
    refine ⟨univ.image x, univ.image y, ?_, ?_, ?_⟩
    · simp [card_image_of_injective _ hxi]
    · simp [card_image_of_injective _ hyi]
    · rintro ⟨u, v⟩ h
      obtain ⟨hu, hv⟩ := mem_product.mp h
      obtain ⟨j, _, rfl⟩ := mem_image.mp hu
      obtain ⟨i, _, rfl⟩ := mem_image.mp hv
      simpa only [hy i, hx j, bipGraph] using he i j

/-- The finite probabilistic lower bound for a forbidden balanced biclique. -/
theorem finite_lower_bound (hr : 0 < r) (k : ℕ) [NeZero k] :
    (n : ℝ) ^ 2 / k - (n : ℝ) ^ (2 * r) / (k : ℝ) ^ (r ^ 2) ≤
      (extremalNumber (2 * n) (completeBipartiteGraph (Fin r) (Fin r)) : ℝ) := by
  classical
  obtain ⟨T, hT, hsize⟩ := Erdos714Alteration.independent_lower_bound k
    (rectangles n r) (r ^ 2) (by positivity) (rectangle_card n r)
  have hG : (completeBipartiteGraph (Fin r) (Fin r)).Free (bipGraph n T) := by
    rintro ⟨f⟩
    obtain ⟨L, R, hL, hR, hLR⟩ := copy_gives_rectangle n r hr T f
    exact hT (L ×ˢ R) ((mem_rectangles_iff n r _).mpr ⟨L, R, hL, hR, rfl⟩) hLR
  have he := card_edgeFinset_le_extremalNumber hG
  rw [bipGraph_edges] at he
  have he' : T.card ≤ extremalNumber (2 * n) (completeBipartiteGraph (Fin r) (Fin r)) := by
    simpa only [Fintype.card_sum, Fintype.card_fin, two_mul] using he
  have hcount : ((rectangles n r).card : ℝ) ≤ (n : ℝ) ^ (2 * r) := by
    exact_mod_cast rectangles_card_le n r
  have hcount' := div_le_div_of_nonneg_right hcount (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ (r ^ 2))
  calc
    _ ≤ (n : ℝ) ^ 2 / k - ((rectangles n r).card : ℝ) / (k : ℝ) ^ (r ^ 2) := sub_le_sub_left hcount' _
    _ ≤ (T.card : ℝ) := by
      simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two] using hsize
    _ ≤ _ := Nat.cast_le.mpr he'

/-- Parameter sizes that balance the edge term and the deletion term. -/
theorem power_sizes_lower_bound (hr : 2 ≤ r) (q : ℕ) (hq : 0 < q) :
    (q : ℝ) ^ (2 * r) / 4 ≤
      (extremalNumber (2 * q ^ (r + 1)) (completeBipartiteGraph (Fin r) (Fin r)) : ℝ) := by
  letI : NeZero (2 * q ^ 2) := ⟨by positivity⟩
  have h := finite_lower_bound (q ^ (r + 1)) r (by omega) (2 * q ^ 2)
  have hq' : (q : ℝ) ≠ 0 := by positivity
  norm_num only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at h
  have hfirst : ((q : ℝ) ^ (r + 1)) ^ 2 / (2 * (q : ℝ) ^ 2) = (q : ℝ) ^ (2 * r) / 2 := by
    rw [← pow_mul, show (r + 1) * 2 = 2 * r + 2 by omega, pow_add]
    field_simp
  have hbad : ((q : ℝ) ^ (r + 1)) ^ (2 * r) / (2 * (q : ℝ) ^ 2) ^ (r ^ 2) =
      (q : ℝ) ^ (2 * r) / (2 : ℝ) ^ (r ^ 2) := by
    rw [← pow_mul, mul_pow, ← pow_mul,
      show (r + 1) * (2 * r) = 2 * r ^ 2 + 2 * r by ring, pow_add]
    field_simp
  rw [hfirst, hbad] at h
  have hpow : (4 : ℝ) ≤ (2 : ℝ) ^ (r ^ 2) := by
    calc
      _ = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by nlinarith : 2 ≤ r ^ 2)
  have hd := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ (2 * r))
    (by norm_num : (0 : ℝ) < 4) hpow
  linarith

/-- Convert the finite bound to a power of the number of vertices. -/
theorem power_sizes_rpow_lower_bound (hr : 2 ≤ r) (q : ℕ) (hq : 0 < q) :
    (1 / 16 : ℝ) * ((2 * q ^ (r + 1) : ℕ) : ℝ) ^ ((2 : ℝ) * r / (r + 1)) ≤
      (extremalNumber (2 * q ^ (r + 1)) (completeBipartiteGraph (Fin r) (Fin r)) : ℝ) := by
  let p : ℝ := 2 * r / (r + 1)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hp2 : p ≤ 2 := by
    dsimp [p]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < r + 1)]
    linarith
  have he : ((r + 1 : ℕ) : ℝ) * p = ((2 * r : ℕ) : ℝ) := by
    dsimp [p]
    push_cast
    field_simp
  have hcancel : ((q : ℝ) ^ (r + 1)) ^ p = (q : ℝ) ^ (2 * r) := by
    rw [← Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ q), he, Real.rpow_natCast]
  have h2 : (2 : ℝ) ^ p ≤ 4 := by
    calc
      _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp2
      _ = 4 := by norm_num
  have hsize : ((2 * q ^ (r + 1) : ℕ) : ℝ) ^ p ≤ 4 * (q : ℝ) ^ (2 * r) := by
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [Real.mul_rpow (by norm_num) (by positivity), hcancel]
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have h := power_sizes_lower_bound r hr q hq
  change (1 / 16 : ℝ) * ((2 * q ^ (r + 1) : ℕ) : ℝ) ^ p ≤ _
  linarith

/-- The standard alteration exponent, proved here for every balanced biclique. -/
theorem all_r_alteration :
    ∀ r : ℕ, 2 ≤ r → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 2 / (r + 1 : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ) := by
  intro r hr
  have hH : ∀ v : Fin r ⊕ Fin r, ∃ w,
      (completeBipartiteGraph (Fin r) (Fin r)).Adj v w := by
    let i : Fin r := ⟨0, by omega⟩
    intro v
    cases v with
    | inl v => exact ⟨Sum.inr i, by simp⟩
    | inr v => exact ⟨Sum.inl i, by simp⟩
  have hmN := Erdos714Reduction.extremalNumber_monotone_of_no_isolated _ hH
  have hm : Monotone (fun n : ℕ =>
      (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ)) := by
    intro a b hab
    exact Nat.cast_le.mpr (hmN hab)
  have hg (k : ℕ) :
      (1 / 16 : ℝ) * ((2 * (2 ^ (r + 1)) ^ k : ℕ) : ℝ) ^ ((2 : ℝ) * r / (r + 1)) ≤
        (extremalNumber (2 * (2 ^ (r + 1)) ^ k) (completeBipartiteGraph (Fin r) (Fin r)) : ℝ) := by
    have hpow : (2 ^ k) ^ (r + 1) = (2 ^ (r + 1)) ^ k := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    simpa only [hpow] using power_sizes_rpow_lower_bound r hr (2 ^ k) (by positivity)
  have hb : 2 ≤ 2 ^ (r + 1) := by
    have h : 1 ≤ (2 : ℕ) ^ r := Nat.one_le_pow r 2 (by norm_num)
    rw [pow_succ]
    omega
  have hexp : (2 : ℝ) - 2 / (r + 1) = (2 : ℝ) * r / (r + 1) := by
    field_simp
    ring
  simpa only [hexp] using Erdos714Reduction.lower_bound_from_scaled_sizes _ hm
    ((2 : ℝ) * r / (r + 1)) (by positivity) 2 (2 ^ (r + 1)) (by norm_num) hb
    (1 / 16) (by norm_num) hg

lemma sub_power_le_one (t : ℝ) (ht : 0 ≤ t) (m : ℕ) (hm : 1 ≤ m) :
    t - t ^ m ≤ 1 := by
  by_cases ht1 : t ≤ 1
  · have := pow_nonneg ht m
    linarith
  · have hpow : t ≤ t ^ m := by
      simpa only [pow_one] using pow_le_pow_right₀ (le_of_not_ge ht1) hm
    linarith

/-- Optimizing the first-moment alteration estimate alone cannot improve its exponent. -/
theorem first_moment_upper (hr : 1 ≤ r) (q k : ℝ) (hq : 0 ≤ q) (hk : 0 ≤ k) :
    (q ^ (r + 1)) ^ 2 / k - (q ^ (r + 1)) ^ (2 * r) / k ^ (r ^ 2) ≤ q ^ (2 * r) := by
  have hfirst : (q ^ (r + 1)) ^ 2 = q ^ (2 * r) * q ^ 2 := by
    rw [← pow_mul, show (r + 1) * 2 = 2 * r + 2 by omega, pow_add]
  have hsecond : (q ^ (r + 1)) ^ (2 * r) = q ^ (2 * r) * (q ^ 2) ^ (r ^ 2) := by
    calc
      _ = q ^ ((r + 1) * (2 * r)) := (pow_mul q (r + 1) (2 * r)).symm
      _ = q ^ (2 * r + 2 * r ^ 2) := by congr 1; ring
      _ = _ := by rw [pow_add, pow_mul q 2 (r ^ 2)]
  have hfactor : (q ^ (r + 1)) ^ 2 / k - (q ^ (r + 1)) ^ (2 * r) / k ^ (r ^ 2) =
      q ^ (2 * r) * (q ^ 2 / k - (q ^ 2 / k) ^ (r ^ 2)) := by
    rw [hfirst, hsecond, div_pow]
    ring
  rw [hfactor]
  have h := sub_power_le_one (q ^ 2 / k) (div_nonneg (sq_nonneg _) hk) (r ^ 2) (by nlinarith)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h (pow_nonneg hq (2 * r))

end Erdos714Random


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


namespace Erdos714Progress

/-- With the second and third cases proved, the exact remaining problem begins at four. -/
theorem conjecture_iff_large_cases :
    (∀ r : ℕ, 2 ≤ r → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ)) ↔
    (∀ r : ℕ, 4 ≤ r → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ)) := by
  constructor
  · intro h r hr
    exact h r (by omega)
  · intro h r hr
    by_cases h₂ : r = 2
    · subst r
      exact Erdos714Finite.second_instance
    by_cases h₃ : r = 3
    · subst r
      exact Erdos714Norm.third_instance
    exact h r (by omega)

end Erdos714Progress

namespace Erdos714

/--
Is it true that\[\mathrm{ex}(n; K_{r,r}) \gg n^{2-1/r}?\]
-/
theorem erdos_714 :
    (∀ r : ℕ, 2 ≤ r → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ)) := by
  intro r hr
  by_cases h₂ : r = 2
  · subst r
    exact Erdos714Finite.second_instance
  by_cases h₃ : r = 3
  · subst r
    exact Erdos714Norm.third_instance
  have hr4 : 4 ≤ r := by omega
  -- The remaining mathematical conjecture is the range `r ≥ 4`.
  sorry

end Erdos714

#print axioms Erdos714Upper.star_bound
#print axioms Erdos714Upper.edge_power_bound
#print axioms Erdos714Upper.extremal_real_bound
#print axioms Erdos714Finite.second_instance
#print axioms Erdos714Norm.third_instance
#print axioms Erdos714Random.all_r_alteration
