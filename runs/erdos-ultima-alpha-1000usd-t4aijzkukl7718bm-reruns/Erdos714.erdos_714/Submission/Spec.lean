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



/- Verified cubic norm construction: a 7/4 lower exponent for r >= 5. -/

/- Self-contained cubic norm graph K55 construction. Not a solution of Erdős714. -/

noncomputable section

/-
Linear-algebraic ingredients for the cubic norm variety. These results do
not yet give a construction settling Erdős 714.
-/
open Classical Finset
set_option maxHeartbeats 2000000
namespace Erdos714CubicSegre
variable {E : Type*} [Field E]

/-- Affine coordinates on the product of three projective lines. -/
def segre (x y z : E) : Fin 8 → E := ![1,x,y,z,x*y,x*z,y*z,x*y*z]

def point (σ : E →+* E) (x : E) : Fin 8 → E := segre x (σ x) (σ (σ x))

/-- Every product of three affine factors is a linear functional in Segre coordinates. -/
def functional (a b c d e f : E) : (Fin 8 → E) →ₗ[E] E where
  toFun v := b*d*f*v 0+a*d*f*v 1+b*c*f*v 2+b*d*e*v 3+
    a*c*f*v 4+a*d*e*v 5+b*c*e*v 6+a*c*e*v 7
  map_add' := by intro v w; simp only [Pi.add_apply]; ring
  map_smul' := by intro k v; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma functional_segre (a b c d e f x y z : E) :
    functional a b c d e f (segre x y z) = (a*x+b)*(c*y+d)*(e*z+f) := by
  simp [functional,segre]
  ring

lemma functional_relation {I : Type*} [Fintype I] (σ : E →+* E)
    (x coeff : I → E) (h : ∑ i, coeff i • point σ (x i) = 0)
    (a b c d e f : E) :
    ∑ i, coeff i*((a*x i+b)*(c*σ (x i)+d)*(e*σ (σ (x i))+f)) = 0 := by
  have he := congrArg (functional a b c d e f) h
  simpa only [map_sum,map_smul,map_zero,point,functional_segre,smul_eq_mul] using he

/-- A product of three coordinate factors isolates one of four distinct points. -/
theorem four_relation (σ : E →+* E) (x : Fin 4 → E) (hx : Function.Injective x)
    (coeff : Fin 4 → E) (h : ∑ i, coeff i • point σ (x i) = 0) : ∀ i, coeff i = 0 := by
  have hn (i j : Fin 4) (hij : i ≠ j) : x i-x j ≠ 0 := sub_ne_zero.mpr (hx.ne hij)
  have hn₁ (i j : Fin 4) (hij : i ≠ j) : σ (x i)-σ (x j) ≠ 0 :=
    sub_ne_zero.mpr (σ.injective.ne (hx.ne hij))
  have hn₂ (i j : Fin 4) (hij : i ≠ j) : σ (σ (x i))-σ (σ (x j)) ≠ 0 :=
    sub_ne_zero.mpr (σ.injective.ne (σ.injective.ne (hx.ne hij)))
  intro i
  fin_cases i
  · have he := functional_relation σ x coeff h 1 (-x 1) 1 (-σ (x 2)) 1 (-σ (σ (x 3)))
    simp only [Fin.sum_univ_four,one_mul,← sub_eq_add_neg,sub_self,zero_mul,mul_zero,
      add_zero] at he
    exact (mul_eq_zero.mp he).resolve_right
      (mul_ne_zero (mul_ne_zero (hn 0 1 (by decide)) (hn₁ 0 2 (by decide))) (hn₂ 0 3 (by decide)))
  · have he := functional_relation σ x coeff h 1 (-x 0) 1 (-σ (x 2)) 1 (-σ (σ (x 3)))
    simp only [Fin.sum_univ_four,one_mul,← sub_eq_add_neg,sub_self,zero_mul,mul_zero,
      zero_add,add_zero] at he
    exact (mul_eq_zero.mp he).resolve_right
      (mul_ne_zero (mul_ne_zero (hn 1 0 (by decide)) (hn₁ 1 2 (by decide))) (hn₂ 1 3 (by decide)))
  · have he := functional_relation σ x coeff h 1 (-x 0) 1 (-σ (x 1)) 1 (-σ (σ (x 3)))
    simp only [Fin.sum_univ_four,one_mul,← sub_eq_add_neg,sub_self,zero_mul,mul_zero,
      zero_add,add_zero] at he
    exact (mul_eq_zero.mp he).resolve_right
      (mul_ne_zero (mul_ne_zero (hn 2 0 (by decide)) (hn₁ 2 1 (by decide))) (hn₂ 2 3 (by decide)))
  · have he := functional_relation σ x coeff h 1 (-x 0) 1 (-σ (x 1)) 1 (-σ (σ (x 2)))
    simp only [Fin.sum_univ_four,one_mul,← sub_eq_add_neg,sub_self,zero_mul,mul_zero,
      zero_add,add_zero] at he
    exact (mul_eq_zero.mp he).resolve_right
      (mul_ne_zero (mul_ne_zero (hn 3 0 (by decide)) (hn₁ 3 1 (by decide))) (hn₂ 3 2 (by decide)))

/-- The cubic norm variety has four-point linear independence over the extension field. -/
theorem four_independent (σ : E →+* E) (x : Fin 4 → E) (hx : Function.Injective x) :
    LinearIndependent E (fun i => point σ (x i)) := by
  rw [Fintype.linearIndependent_iff]
  exact four_relation σ x hx

/-- Eliminate the second coordinate from singleton and pair moment relations. -/
lemma pair_eliminate (a b c z w u v : E)
    (h₁ : a+b*z+c*w = 0) (h₂ : a+b*u+c*v = 0)
    (h₁₂ : a+b*z*u+c*w*v = 0) :
    b*(b+c)*z*u+a*b*(z+u)+a*(a+c) = 0 := by
  linear_combination c*h₁₂+(a+b*u)*h₁-c*w*h₂

/-- Three conjugates are either all equal or pairwise distinct. -/
lemma orbit_distinct (σ : E →+* E) (hσ : ∀ x, σ (σ (σ x)) = x)
    (z : E) (hz : σ z ≠ z) :
    z ≠ σ z ∧ σ z ≠ σ (σ z) ∧ z ≠ σ (σ z) := by
  refine ⟨Ne.symm hz,?_,?_⟩
  · intro he
    exact hz (σ.injective he).symm
  · intro he
    have hh := congrArg σ he
    rw [hσ] at hh
    exact hz hh

/-- After normalizing three projective points to infinity, zero, and one,
a nontrivial five-point dependence forces the other two parameters to be fixed.
No assumption that the dependence coefficients lie in the fixed field is needed. -/
theorem normalized_five_dependence (σ : E →+* E) (hσ : ∀ x, σ (σ (σ x)) = x)
    (a b c z w : E) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h₀ : a+b*z+c*w = 0)
    (h₁ : a+b*σ z+c*σ w = 0)
    (h₂ : a+b*σ (σ z)+c*σ (σ w) = 0)
    (h₀₁ : a+b*z*σ z+c*w*σ w = 0)
    (h₀₂ : a+b*z*σ (σ z)+c*w*σ (σ w) = 0)
    (h₁₂ : a+b*σ z*σ (σ z)+c*σ w*σ (σ w) = 0) :
    σ z = z ∧ σ w = w := by
  have hz : σ z = z := by
    by_contra hn
    obtain ⟨hne₀₁,hne₁₂,hne₀₂⟩ := orbit_distinct σ hσ z hn
    have e₀₁ := pair_eliminate a b c z w (σ z) (σ w) h₀ h₁ h₀₁
    have e₀₂ := pair_eliminate a b c z w (σ (σ z)) (σ (σ w)) h₀ h₂ h₀₂
    have e₁₂ := pair_eliminate a b c (σ z) (σ w) (σ (σ z)) (σ (σ w)) h₁ h₂ h₁₂
    have hp : b*(b+c)*z+a*b = 0 := by
      apply (mul_eq_zero.mp (show (σ z-σ (σ z))*(b*(b+c)*z+a*b) = 0 by
        linear_combination e₀₁-e₀₂)).resolve_left (sub_ne_zero.mpr hne₁₂)
    have hq : b*(b+c)*σ z+a*b = 0 := by
      apply (mul_eq_zero.mp (show (z-σ (σ z))*(b*(b+c)*σ z+a*b) = 0 by
        linear_combination e₀₁-e₁₂)).resolve_left (sub_ne_zero.mpr hne₀₂)
    have hA : b*(b+c) = 0 := by
      apply (mul_eq_zero.mp (show b*(b+c)*(z-σ z) = 0 by
        linear_combination hp-hq)).resolve_right (sub_ne_zero.mpr hne₀₁)
    rw [hA,zero_mul,zero_add] at hp
    exact mul_ne_zero ha hb hp
  refine ⟨hz,?_⟩
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp (show c*(σ w-w) = 0 by
    rw [hz] at h₁
    linear_combination h₁-h₀)).resolve_left hc

end Erdos714CubicSegre


/-
Five-point dependence in the cubic norm variety: after a projective change
of parameter, all five points lie on a line over the fixed field. This is
an ingredient for a larger-biclique bound, not a solution of Erdős 714.
-/
open Classical Finset
set_option maxHeartbeats 4000000
namespace Erdos714CubicSegre
variable {E : Type*} [Field E]

/-- The product of three conjugates, valued in the extension field. -/
def norm (σ : E →+* E) (x : E) : E := x*σ x*σ (σ x)

lemma norm_ne_zero (σ : E →+* E) {x : E} (hx : x ≠ 0) : norm σ x ≠ 0 :=
  mul_ne_zero (mul_ne_zero hx ((map_ne_zero σ).mpr hx))
    ((map_ne_zero σ).mpr ((map_ne_zero σ).mpr hx))

lemma norm_mul (σ : E →+* E) (x y : E) : norm σ (x*y) = norm σ x*norm σ y := by
  simp only [norm,map_mul]
  ring

lemma norm_div (σ : E →+* E) (x y : E) : norm σ (x/y) = norm σ x/norm σ y := by
  simp only [norm,map_div₀]
  ring

/-- Homogeneous coordinates, including the point at infinity. -/
def homogeneous (σ : E →+* E) (u v : E) : Fin 8 → E :=
  ![norm σ v, u*σ v*σ (σ v), v*σ u*σ (σ v), v*σ v*σ (σ u),
    u*σ u*σ (σ v), u*σ v*σ (σ u), v*σ u*σ (σ u), norm σ u]

lemma homogeneous_div (σ : E →+* E) (u v : E) (hv : v ≠ 0) :
    homogeneous σ u v = norm σ v • point σ (u/v) := by
  have hv₁ : σ v ≠ 0 := (map_ne_zero σ).mpr hv
  have hv₂ : σ (σ v) ≠ 0 := (map_ne_zero σ).mpr hv₁
  ext i
  fin_cases i <;> simp [homogeneous,point,segre,norm,map_div₀] <;> field_simp

/-- Tensoring the three conjugate two-dimensional changes of coordinates. -/
def transform (σ : E →+* E) (a b c d : E) : (Fin 8 → E) →ₗ[E] (Fin 8 → E) where
  toFun v := ![
    functional c d (σ c) (σ d) (σ (σ c)) (σ (σ d)) v,
    functional a b (σ c) (σ d) (σ (σ c)) (σ (σ d)) v,
    functional c d (σ a) (σ b) (σ (σ c)) (σ (σ d)) v,
    functional c d (σ c) (σ d) (σ (σ a)) (σ (σ b)) v,
    functional a b (σ a) (σ b) (σ (σ c)) (σ (σ d)) v,
    functional a b (σ c) (σ d) (σ (σ a)) (σ (σ b)) v,
    functional c d (σ a) (σ b) (σ (σ a)) (σ (σ b)) v,
    functional a b (σ a) (σ b) (σ (σ a)) (σ (σ b)) v]
  map_add' := by intro v w; ext i; fin_cases i <;> simp
  map_smul' := by intro k v; ext i; fin_cases i <;> simp

lemma transform_point (σ : E →+* E) (a b c d x : E) :
    transform σ a b c d (point σ x) = homogeneous σ (a*x+b) (c*x+d) := by
  ext i
  fin_cases i <;> simp [transform,point,functional_segre,homogeneous,norm,map_add,map_mul]

/-- Every coefficient in a nonzero relation on five distinct points is nonzero. -/
theorem five_relation_nonzero (σ : E →+* E) (x : Fin 5 → E) (hx : Function.Injective x)
    (coeff : Fin 5 → E) (h : ∑ i, coeff i • point σ (x i) = 0)
    (hn : ∃ i, coeff i ≠ 0) : ∀ i, coeff i ≠ 0 := by
  intro j hj
  have he := h
  rw [Fin.sum_univ_succAbove _ j,hj,zero_smul,zero_add] at he
  have hh := four_relation σ (fun i => x (j.succAbove i))
    (hx.comp Fin.succAbove_right_injective) (fun i => coeff (j.succAbove i)) he
  obtain ⟨i,hi⟩ := hn
  rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨k,rfl⟩
  · exact hi hj
  · exact hi (hh k)

/-- The cross-ratio parameter sending the first three points to infinity, zero, one. -/
def parameter (x : Fin 5 → E) (i : Fin 5) : E :=
  ((x 2-x 0)/(x 2-x 1))*(x i-x 1)/(x i-x 0)

/-- The nontrivial remaining parameters in a five-point dependence are fixed. -/
theorem dependent_parameters_fixed (σ : E →+* E) (hσ : ∀ z, σ (σ (σ z)) = z)
    (x : Fin 5 → E) (hx : Function.Injective x)
    (hdep : ¬ LinearIndependent E (fun i => point σ (x i))) :
    σ (parameter x 3) = parameter x 3 ∧ σ (parameter x 4) = parameter x 4 := by
  obtain ⟨coeff,hrel,hn⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hc := five_relation_nonzero σ x hx coeff hrel hn
  let k := (x 2-x 0)/(x 2-x 1)
  let U (i : Fin 5) := k*x i-k*x 1
  let V (i : Fin 5) := x i-x 0
  have hv (i : Fin 5) (hi : i ≠ 0) : V i ≠ 0 := sub_ne_zero.mpr (hx.ne hi)
  have hu₁ : U 1 = 0 := by dsimp [U]; ring
  have hu₂ : U 2 = V 2 := by
    dsimp [U,V,k]
    have hh : x 2-x 1 ≠ 0 := sub_ne_zero.mpr (hx.ne (by decide))
    field_simp
  have hv₀ : V 0 = 0 := by simp [V]
  have hp (i : Fin 5) : U i/V i = parameter x i := by dsimp [U,V,k,parameter]; ring
  have htr : ∑ i, coeff i • homogeneous σ (U i) (V i) = 0 := by
    have he := congrArg (transform σ k (-k*x 1) 1 (-x 0)) hrel
    simpa only [map_sum,map_smul,map_zero,transform_point,one_mul,neg_mul,
      ← sub_eq_add_neg,U,V] using he
  have hform (i : Fin 5) (hi : i ≠ 0) :
      homogeneous σ (U i) (V i) = norm σ (V i) • point σ (parameter x i) := by
    rw [homogeneous_div σ _ _ (hv i hi),hp]
  have hp₁ : parameter x 1 = 0 := by simp [parameter]
  have hp₂ : parameter x 2 = 1 := by
    rw [← hp 2,hu₂,div_self (hv 2 (by decide))]
  have hcoord (j : Fin 8) (hj₀ : j ≠ 0) (hj₇ : j ≠ 7) :
      (coeff 2*norm σ (V 2))+
      (coeff 3*norm σ (V 3))*point σ (parameter x 3) j+
      (coeff 4*norm σ (V 4))*point σ (parameter x 4) j = 0 := by
    have he := congrArg (fun v : Fin 8 → E => v j) htr
    simp only [Fin.sum_univ_five,Pi.add_apply,Pi.zero_apply,Pi.smul_apply,smul_eq_mul] at he
    rw [hform 1 (by decide),hform 2 (by decide),hform 3 (by decide),hform 4 (by decide),
      hp₁,hp₂] at he
    fin_cases j <;> simp_all [homogeneous,point,segre,norm,mul_assoc]
  apply normalized_five_dependence σ hσ
    (coeff 2*norm σ (V 2)) (coeff 3*norm σ (V 3)) (coeff 4*norm σ (V 4))
    (parameter x 3) (parameter x 4)
    (mul_ne_zero (hc 2) (norm_ne_zero σ (hv 2 (by decide))))
    (mul_ne_zero (hc 3) (norm_ne_zero σ (hv 3 (by decide))))
    (mul_ne_zero (hc 4) (norm_ne_zero σ (hv 4 (by decide))))
  all_goals first
    | simpa [point,segre,mul_assoc] using hcoord 1 (by decide) (by decide)
    | simpa [point,segre,mul_assoc] using hcoord 2 (by decide) (by decide)
    | simpa [point,segre,mul_assoc] using hcoord 3 (by decide) (by decide)
    | simpa [point,segre,mul_assoc] using hcoord 4 (by decide) (by decide)
    | simpa [point,segre,mul_assoc] using hcoord 5 (by decide) (by decide)
    | simpa [point,segre,mul_assoc] using hcoord 6 (by decide) (by decide)

end Erdos714CubicSegre


/-
Common-neighbor bounds for dependent rows of a cubic norm graph.
This is not a resolution of Erdős 714.
-/
open Classical Finset Polynomial
set_option maxHeartbeats 4000000
namespace Erdos714CubicSegre
variable {E : Type*} [Field E]

/-- The cubic norm polynomial on shifts fixed by the automorphism. -/
def shift (σ : E →+* E) (z : E) : E[X] :=
  (X+C z)*(X+C (σ z))*(X+C (σ (σ z)))

lemma shift_degree (σ : E →+* E) (z : E) : (shift σ z).natDegree ≤ 3 := by
  unfold shift
  compute_degree!

lemma shift_monic (σ : E →+* E) (z : E) : (shift σ z).Monic :=
  ((monic_X_add_C _).mul (monic_X_add_C _)).mul (monic_X_add_C _)

lemma shift_eval (σ : E →+* E) (z t : E) (ht : σ t = t) :
    (shift σ z).eval t = norm σ (z+t) := by
  simp only [shift,eval_mul,eval_add,eval_X,eval_C,norm,map_add,ht]
  ring

lemma shift_root (σ : E →+* E) (z : E) : (shift σ z).eval (-z) = 0 := by
  simp [shift]

/-- Four distinct fixed scalar shifts recover the complete cubic polynomial. -/
lemma shift_recovery (σ : E →+* E) (z w : E) (t : Fin 4 → E)
    (ht : Function.Injective t) (hfix : ∀ i, σ (t i) = t i)
    (h : ∀ i, norm σ (z+t i) = norm σ (w+t i)) : shift σ z = shift σ w := by
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ ht
  · intro i
    simp only [eval_sub,shift_eval σ _ _ (hfix i),h i,sub_self]
  · have hd := (natDegree_sub_le (shift σ z) (shift σ w)).trans
      (max_le (shift_degree σ z) (shift_degree σ w))
    simpa using (show (shift σ z-shift σ w).natDegree < 4 by omega)

/-- Four norm spheres centered on a fixed-field affine line have at most
three common points. The five-point contradiction is enough for K55. -/
theorem no_five_sphere_points (σ : E →+* E) (A B : E) (hA : A ≠ 0)
    (t : Fin 4 → E) (ht : Function.Injective t) (hfix : ∀ i, σ (t i) = t i)
    (y : Fin 5 → E) (hy : Function.Injective y) (c : Fin 4 → E)
    (h : ∀ i j, norm σ (A*t i+B+y j) = c i) : False := by
  let z (j : Fin 5) := (B+y j)/A
  have hz : Function.Injective z := by
    intro i j hij
    apply hy
    apply add_left_cancel (a := B)
    exact (div_left_inj' hA).mp hij
  have he (i : Fin 4) (j : Fin 5) : A*(z j+t i) = A*t i+B+y j := by
    dsimp [z]
    field_simp
    ring
  have hsame (j : Fin 5) : shift σ (z j) = shift σ (z 0) := by
    apply shift_recovery σ _ _ t ht hfix
    intro i
    apply mul_left_cancel₀ (norm_ne_zero σ hA)
    rw [← norm_mul,← norm_mul,he,he,h i j,h i 0]
  have hzero : shift σ (z 0) = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
      (neg_injective.comp hz)
    · intro j
      rw [← hsame j]
      exact shift_root σ (z j)
    · have hd := shift_degree σ (z 0)
      simpa using (show (shift σ (z 0)).natDegree < 5 by omega)
  exact (shift_monic σ (z 0)).ne_zero hzero

/-- Reciprocal coordinates turn the dependent five-point set into four
centers on a fixed-field affine line. -/
theorem dependent_reciprocal_line (σ : E →+* E) (hσ : ∀ z, σ (σ (σ z)) = z)
    (x : Fin 5 → E) (hx : Function.Injective x)
    (hdep : ¬ LinearIndependent E (fun i => point σ (x i))) :
    ∃ A B : E, A ≠ 0 ∧ ∃ t : Fin 4 → E, Function.Injective t ∧
      (∀ i, σ (t i) = t i) ∧ ∀ i, (x i.succ-x 0)⁻¹ = A*t i+B := by
  let k := (x 2-x 0)/(x 2-x 1)
  let A := (k*(x 0-x 1))⁻¹
  let B := -(x 0-x 1)⁻¹
  let t (i : Fin 4) := parameter x i.succ
  have h₂₀ : x 2-x 0 ≠ 0 := sub_ne_zero.mpr (hx.ne (by decide))
  have h₂₁ : x 2-x 1 ≠ 0 := sub_ne_zero.mpr (hx.ne (by decide))
  have h₀₁ : x 0-x 1 ≠ 0 := sub_ne_zero.mpr (hx.ne (by decide))
  have hk : k ≠ 0 := div_ne_zero h₂₀ h₂₁
  have ha : A ≠ 0 := inv_ne_zero (mul_ne_zero hk h₀₁)
  have hform (i : Fin 4) : (x i.succ-x 0)⁻¹ = A*t i+B := by
    have hi : x i.succ-x 0 ≠ 0 := sub_ne_zero.mpr (hx.ne (Fin.succ_ne_zero i))
    dsimp [A,B,t,parameter,k]
    field_simp
    ring
  refine ⟨A,B,ha,t,?_,?_,hform⟩
  · intro i j hij
    have hv : (x i.succ-x 0)⁻¹ = (x j.succ-x 0)⁻¹ := by rw [hform,hform,hij]
    exact Fin.succ_injective 4 (hx (sub_left_injective (inv_injective hv)))
  · obtain ⟨h₃,h₄⟩ := dependent_parameters_fixed σ hσ x hx hdep
    have hp₁ : parameter x 1 = 0 := by simp [parameter]
    have hp₂ : parameter x 2 = 1 := by
      dsimp [parameter]
      field_simp
    intro i
    fin_cases i
    · simp [t,hp₁]
    · simp [t,hp₂]
    · exact h₃
    · exact h₄

/-- Dependent five rows cannot have five distinct common column points.
Both nonzero weights needed in the reciprocal normalization are explicit. -/
theorem dependent_no_rectangle (σ : E →+* E) (hσ : ∀ z, σ (σ (σ z)) = z)
    (x y : Fin 5 → E) (hx : Function.Injective x) (hy : Function.Injective y)
    (a b : Fin 5 → E) (ha : a 0 ≠ 0) (hb : ∀ j, b j ≠ 0)
    (h : ∀ i j, norm σ (x i+y j) = a i*b j)
    (hdep : ¬ LinearIndependent E (fun i => point σ (x i))) : False := by
  obtain ⟨A,B,hA,t,ht,hfix,hform⟩ := dependent_reciprocal_line σ hσ x hx hdep
  have hsum (j : Fin 5) : x 0+y j ≠ 0 := by
    intro he
    have hn := h 0 j
    rw [he] at hn
    have hz : norm σ (0 : E) = 0 := by simp [norm]
    rw [hz] at hn
    exact mul_ne_zero ha (hb j) hn.symm
  let w (j : Fin 5) := (x 0+y j)⁻¹
  have hw : Function.Injective w := by
    intro i j hij
    exact hy (add_left_cancel (inv_injective hij))
  let c (i : Fin 4) := a i.succ/(a 0*norm σ (x i.succ-x 0))
  apply no_five_sphere_points σ A B hA t ht hfix w hw c
  intro i j
  rw [← hform]
  have hd : x i.succ-x 0 ≠ 0 := sub_ne_zero.mpr (hx.ne (Fin.succ_ne_zero i))
  have he : (x i.succ-x 0)⁻¹+w j =
      (x i.succ+y j)/((x i.succ-x 0)*(x 0+y j)) := by
    dsimp [w]
    field_simp [hsum j]
    ring
  rw [he,norm_div,norm_mul,h i.succ j,h 0 j]
  dsimp [c]
  field_simp [hb j,norm_ne_zero σ hd]

end Erdos714CubicSegre

open SimpleGraph
namespace Erdos714CubicSegre
variable {E : Type*} [Field E]

/-- The norm of a sum is the pairing of complementary Segre coordinates. -/
lemma complement_pairing (σ : E →+* E) (x y : E) :
    ∑ i : Fin 8, point σ x i*point σ y i.rev = norm σ (x+y) := by
  simp [Fin.sum_univ_succ,point,segre,norm,map_add]
  ring

/-- Independent rows on both sides cannot be orthogonal in dimension nine. -/
theorem independent_no_rectangle (σ : E →+* E)
    (x y a b : Fin 5 → E)
    (hx : LinearIndependent E (fun i => point σ (x i)))
    (hy : LinearIndependent E (fun j => point σ (y j)))
    (h : ∀ i j, norm σ (x i+y j) = a i*b j) : False := by
  let A : Matrix (Fin 5) (Fin 9) E := fun i => Fin.snoc (point σ (x i)) (a i)
  let B : Matrix (Fin 9) (Fin 5) E := fun k j =>
    (Fin.snoc (fun l : Fin 8 => point σ (y j) l.rev) (-b j) : Fin 9 → E) k
  have hA : LinearIndependent E A.row := by
    apply LinearIndependent.of_comp (LinearMap.funLeft E E (fun i : Fin 8 => i.castSucc))
    simpa [A,Function.comp_def,Matrix.row,LinearMap.funLeft] using hx
  have hB : LinearIndependent E B.transpose.row := by
    apply LinearIndependent.of_comp
      (LinearMap.funLeft E E (fun i : Fin 8 => i.rev.castSucc))
    simpa [B,Function.comp_def,Matrix.row,Matrix.transpose_apply,LinearMap.funLeft] using hy
  have hAB : A*B = 0 := by
    ext i j
    change ∑ k : Fin 9, A i k*B k j = 0
    rw [Fin.sum_univ_castSucc]
    simp only [A,B,Fin.snoc_castSucc,Fin.snoc_last]
    rw [complement_pairing,h i j]
    ring
  have hr := Matrix.rank_add_rank_le_card_of_mul_eq_zero hAB
  rw [hA.rank_matrix,← Matrix.rank_transpose B,hB.rank_matrix] at hr
  norm_num at hr

/-- All row configurations, including the linearly dependent ones, are handled. -/
theorem no_five_rectangle (σ : E →+* E) (hσ : ∀ z, σ (σ (σ z)) = z)
    (x y : Fin 5 → E) (hx : Function.Injective x) (hy : Function.Injective y)
    (a b : Fin 5 → E) (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0)
    (h : ∀ i j, norm σ (x i+y j) = a i*b j) : False := by
  by_cases hi : LinearIndependent E (fun i => point σ (x i))
  · by_cases hj : LinearIndependent E (fun j => point σ (y j))
    · exact independent_no_rectangle σ x y a b hi hj h
    · exact dependent_no_rectangle σ hσ y x hy hx b a (hb 0) ha
        (fun j i => by simpa [add_comm,mul_comm] using h i j) hj
  · exact dependent_no_rectangle σ hσ x y hx hy a b (ha 0) hb h hi


end Erdos714CubicSegre

namespace Erdos714CubicSegre
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]

/-- Two copies of the ordinary weighted cubic norm graph. -/
def normGraph : SimpleGraph (Bool × (E × Fˣ)) where
  Adj p q := p.1 ≠ q.1 ∧ Algebra.norm F (p.2.1+q.2.1) = (p.2.2 : F)*(q.2.2 : F)
  symm := by intro p q h; exact ⟨h.1.symm,by simpa [add_comm,mul_comm] using h.2⟩
  loopless := by intro p h; exact h.1 rfl

private lemma same_side {a b c : Bool} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

omit [Fintype F] [Fintype E] in
/-- The conjugate formula is sufficient for freeness of the actual field-norm graph. -/
theorem graph_free_of_norm_formula (σ : E →+* E) (hσ : ∀ z, σ (σ (σ z)) = z)
    (hN : ∀ z, algebraMap F E (Algebra.norm F z) = norm σ z) :
    (completeBipartiteGraph (Fin 5) (Fin 5)).Free (normGraph (F := F) (E := E)) := by
  rintro ⟨f⟩
  let L (i : Fin 5) := f (Sum.inl i)
  let R (j : Fin 5) := f (Sum.inr j)
  have he (i j : Fin 5) : (normGraph (F := F) (E := E)).Adj (L i) (R j) :=
    f.toHom.map_adj (by simp)
  have hx : Function.Injective (fun i => (L i).2.1) := by
    intro i j hij
    change (L i).2.1 = (L j).2.1 at hij
    have hw : ((L i).2.2 : F) = ((L j).2.2 : F) := by
      apply mul_right_cancel₀ (R 0).2.2.ne_zero
      rw [← (he i 0).2,← (he j 0).2,hij]
    have hv : L i = L j := Prod.ext (same_side (he i 0).1 (he j 0).1)
      (Prod.ext hij (Units.ext hw))
    exact Sum.inl.inj (f.injective hv)
  have hy : Function.Injective (fun j => (R j).2.1) := by
    intro i j hij
    change (R i).2.1 = (R j).2.1 at hij
    have hw : ((R i).2.2 : F) = ((R j).2.2 : F) := by
      apply mul_left_cancel₀ (L 0).2.2.ne_zero
      rw [← (he 0 i).2,← (he 0 j).2,hij]
    have hv : R i = R j := Prod.ext (same_side (he 0 i).1.symm (he 0 j).1.symm)
      (Prod.ext hij (Units.ext hw))
    exact Sum.inr.inj (f.injective hv)
  apply no_five_rectangle σ hσ (fun i => (L i).2.1) (fun j => (R j).2.1) hx hy
    (fun i => algebraMap F E ((L i).2.2 : F)) (fun j => algebraMap F E ((R j).2.2 : F))
    (fun i => (_root_.map_ne_zero _).mpr (L i).2.2.ne_zero)
    (fun j => (_root_.map_ne_zero _).mpr (R j).2.2.ne_zero)
  intro i j
  rw [← hN,(he i j).2,map_mul]

/-- Uniform K55-freeness in every finite cubic extension, all characteristics. -/
theorem normGraph_free (hdim : Module.finrank F E = 3) :
    (completeBipartiteGraph (Fin 5) (Fin 5)).Free (normGraph (F := F) (E := E)) := by
  let σ : E →+* E := (FiniteField.frobeniusAlgHom F E).toRingHom
  have hcard : Fintype.card E = Fintype.card F^3 := by
    rw [Module.card_eq_pow_finrank (K := F) (V := E),hdim]
  have hσ : ∀ z, σ (σ (σ z)) = z := by
    intro z
    change ((z^Fintype.card F)^Fintype.card F)^Fintype.card F = z
    rw [← pow_mul,← pow_mul,show Fintype.card F*(Fintype.card F*Fintype.card F) =
      Fintype.card F^3 by ring,← hcard]
    exact FiniteField.pow_card z
  apply graph_free_of_norm_formula σ hσ
  intro z
  change algebraMap F E (Algebra.norm F z) =
    z*(z^Fintype.card F)*((z^Fintype.card F)^Fintype.card F)
  rw [FiniteField.algebraMap_norm_eq_prod_pow F E z,hdim]
  simp only [Finset.prod_range_succ,Finset.prod_range_zero,pow_zero,pow_one,one_mul,
    Nat.card_eq_fintype_card,← pow_mul,pow_two]

/-- A neighbor is uniquely determined by its nonzero sum coordinate. -/
def normNeighborEquiv (p : Bool × (E × Fˣ)) :
    (normGraph (F := F) (E := E)).neighborSet p ≃ Eˣ where
  toFun q := Units.mk0 (p.2.1+q.val.2.1) (by
    have hn : Algebra.norm F (p.2.1+q.val.2.1) ≠ 0 := by
      rw [q.property.2]
      exact mul_ne_zero p.2.2.ne_zero q.val.2.2.ne_zero
    exact Algebra.norm_ne_zero_iff.mp hn)
  invFun z := ⟨(!p.1,((z : E)-p.2.1,Units.map (Algebra.norm F (S := E)) z/p.2.2)),by
    constructor
    · cases p.1 <;> simp
    · simp only [Units.val_div_eq_div_val]
      change Algebra.norm F (p.2.1+((z : E)-p.2.1)) =
        (p.2.2 : F)*(Algebra.norm F (z : E)/(p.2.2 : F))
      rw [show p.2.1+((z : E)-p.2.1) = (z : E) by ring]
      field_simp⟩
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · change (!p.1) = q.val.1
      have hs := q.property.1
      cases hp : p.1 <;> cases hq : q.val.1 <;> simp_all
    · apply Prod.ext
      · change p.2.1+q.val.2.1-p.2.1 = q.val.2.1
        ring
      · apply Units.ext
        simp only [Units.val_div_eq_div_val]
        change Algebra.norm F (p.2.1+q.val.2.1)/(p.2.2 : F) = (q.val.2.2 : F)
        rw [q.property.2]
        field_simp
  right_inv z := by
    apply Units.ext
    change p.2.1+((z : E)-p.2.1) = (z : E)
    ring

lemma normGraph_degree (p : Bool × (E × Fˣ)) :
    (normGraph (F := F) (E := E)).degree p = Fintype.card E-1 := by
  rw [← card_neighborSet_eq_degree,← Fintype.card_units]
  exact Fintype.card_congr (normNeighborEquiv p)

/-- Exact number of unordered edges. -/
theorem normGraph_edges (hdim : Module.finrank F E = 3) :
    (normGraph (F := F) (E := E)).edgeFinset.card =
      Fintype.card F^3*(Fintype.card F-1)*(Fintype.card F^3-1) := by
  have h := (normGraph (F := F) (E := E)).sum_degrees_eq_twice_card_edges
  simp only [normGraph_degree,Finset.sum_const,Finset.card_univ,Fintype.card_prod,
    Fintype.card_bool,Fintype.card_units,nsmul_eq_mul,Nat.cast_id,
    Module.card_eq_pow_finrank (K := F) (V := E),hdim] at h
  nlinarith

end Erdos714CubicSegre
end


/-
A genuine7/4 lower exponent for K55 and all larger balanced bicliques,
obtained from cubic norm graphs. This remains below the conjectured exponent.
-/
noncomputable section
open Classical SimpleGraph Filter
namespace Erdos714CubicNormLower

abbrev Forbidden := completeBipartiteGraph (Fin 5) (Fin 5)

theorem extremal_mono : Monotone (fun n => extremalNumber n Forbidden) := by
  apply Erdos714Reduction.extremalNumber_monotone_of_no_isolated
  intro v
  cases v with
  | inl v => exact ⟨Sum.inr 0,by simp [Forbidden]⟩
  | inr v => exact ⟨Sum.inl 0,by simp [Forbidden]⟩

/-- The precise finite graph construction bound. -/
theorem finite_lower (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Fintype F] [Fintype E] (hdim : Module.finrank F E = 3) :
    Fintype.card F^3*(Fintype.card F-1)*(Fintype.card F^3-1) ≤
      extremalNumber (2*(Fintype.card F^3*(Fintype.card F-1))) Forbidden := by
  have h := card_edgeFinset_le_extremalNumber (Erdos714CubicSegre.normGraph_free hdim)
  rw [Erdos714CubicSegre.normGraph_edges hdim] at h
  simpa only [Fintype.card_prod,Fintype.card_bool,Fintype.card_units,
    Module.card_eq_pow_finrank (K := F) (V := E),hdim] using h

/-- Cubic extensions over fields of order2^k exist at every positive k. -/
theorem dyadic_lower (k : ℕ) (hk : k ≠ 0) :
    (2^k)^3*(2^k-1)*((2^k)^3-1) ≤
      extremalNumber (2*((2^k)^3*(2^k-1))) Forbidden := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 k
  let E := FiniteField.Extension F 2 3
  letI : Fintype F := Fintype.ofFinite F
  letI : Fintype E := Fintype.ofFinite E
  have hc : Fintype.card F = 2^k := by
    rw [Fintype.card_eq_nat_card,GaloisField.card 2 k hk]
  have hd : Module.finrank F E = 3 := FiniteField.finrank_extension F 2 3
  simpa only [hc] using finite_lower F E hd

lemma count_lower (q : ℕ) (hq : 2 ≤ q) :
    (q : ℝ)^7/4 ≤ ((q^3*(q-1)*(q^3-1) : ℕ) : ℝ) := by
  have hq₁ : 1 ≤ q := by omega
  have hq₃ : 1 ≤ q^3 := Nat.one_le_pow 3 q hq₁
  have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hc : (2 : ℝ) ≤ (q : ℝ)^3 := by
    calc
      _ ≤ (2 : ℝ)^3 := by norm_num
      _ ≤ (q : ℝ)^3 := by gcongr
  norm_num only [Nat.cast_mul,Nat.cast_sub hq₁,Nat.cast_sub hq₃,Nat.cast_pow,Nat.cast_one]
  have h₁ : (q : ℝ)/2 ≤ (q : ℝ)-1 := by linarith
  have h₂ : (q : ℝ)^3/2 ≤ (q : ℝ)^3-1 := by linarith
  have hh := mul_le_mul h₁ h₂ (by positivity : (0 : ℝ) ≤ (q : ℝ)^3/2)
    (by linarith : (0 : ℝ) ≤ (q : ℝ)-1)
  have hh' := mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ (q : ℝ)^3)
  nlinarith only [hh']

lemma fourth_power_rpow (q : ℝ) (hq : 0 ≤ q) :
    (2*q^4)^((7 : ℝ)/4) ≤ 4*q^7 := by
  rw [Real.mul_rpow (by norm_num) (by positivity),← Real.rpow_natCast_mul hq]
  norm_num
  have h : (2 : ℝ)^((7 : ℝ)/4) ≤ 4 := by
    calc
      _ ≤ (2 : ℝ)^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by norm_num
  exact mul_le_mul_of_nonneg_right h (by positivity)

/-- A bound at a geometric sequence with a constant independent of k. -/
theorem geometric_lower (k : ℕ) :
    (1/16 : ℝ)*((32*16^k : ℕ) : ℝ)^((7 : ℝ)/4) ≤
      (extremalNumber (32*16^k) Forbidden : ℝ) := by
  let q := 2^(k+1)
  have hq : 2 ≤ q := by
    have h : 1 ≤ (2 : ℕ)^k := Nat.one_le_pow k 2 (by norm_num)
    dsimp [q]
    rw [pow_succ]
    omega
  have hp : ((2 : ℕ)^k)^4 = 16^k := by
    rw [← pow_mul,Nat.mul_comm k 4,pow_mul]
    norm_num
  have hsize : 2*q^4 = 32*16^k := by
    dsimp [q]
    rw [pow_succ 2 k,mul_pow,hp]
    ring
  have hsmall : 2*(q^3*(q-1)) ≤ 2*q^4 := by
    calc
      _ ≤ 2*(q^3*q) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le q 1))
      _ = _ := by ring
  have hn := (dyadic_lower (k+1) (by omega)).trans (extremal_mono hsmall)
  have he : ((q^3*(q-1)*(q^3-1) : ℕ) : ℝ) ≤
      (extremalNumber (2*q^4) Forbidden : ℝ) := by exact_mod_cast hn
  have hlo := (count_lower q hq).trans he
  have hup := fourth_power_rpow (q : ℝ) (by positivity)
  rw [← hsize]
  norm_num only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  nlinarith only [hlo,hup]

/-- Positive eventual7/4 exponent for K55. This is weaker than9/5. -/
theorem fifth_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c*(n : ℝ)^((7 : ℝ)/4) ≤ (extremalNumber n Forbidden : ℝ) := by
  have hm : Monotone (fun n : ℕ => (extremalNumber n Forbidden : ℝ)) := by
    intro n m hnm
    exact Nat.cast_le.mpr (extremal_mono hnm)
  exact Erdos714Reduction.lower_bound_from_scaled_sizes _ hm ((7 : ℝ)/4)
    (by norm_num) 32 16 (by norm_num) (by norm_num) (1/16) (by norm_num) geometric_lower

/-- The same7/4 exponent holds for every r at least five. -/
theorem larger_lower (r : ℕ) (hr : 5 ≤ r) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c*(n : ℝ)^((7 : ℝ)/4) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ) := by
  let e : Fin 5 ↪ Fin r := Fin.castLEEmb hr
  have hc : Forbidden ⊑ completeBipartiteGraph (Fin r) (Fin r) := by
    refine ⟨⟨⟨Sum.map e e,?_⟩,Sum.map_injective.mpr ⟨e.injective,e.injective⟩⟩⟩
    intro x y hxy
    cases x <;> cases y <;> simp_all [Forbidden]
  obtain ⟨c,hc₀,hn⟩ := fifth_lower
  refine ⟨c,hc₀,?_⟩
  filter_upwards [hn] with n hn
  exact hn.trans (Nat.cast_le.mpr hc.extremalNumber_le)

end Erdos714CubicNormLower
end



/- ## A refined upper bound in the fourth case

The upper bound below does not supply the positive lower-bound constant
required by the conjecture. Its leading coefficient is one half.
-/

noncomputable section
open Finset Classical
set_option maxHeartbeats 2000000
namespace Erdos714Packing

variable {A B : Type*}

/-- The incidence graph of an indexed set system. Repeated blocks are allowed. -/
def incidence (S : A → Finset B) : SimpleGraph (A ⊕ B) where
  Adj x y := match x, y with
    | .inl a, .inr b => b ∈ S a
    | .inr b, .inl a => b ∈ S a
    | _, _ => False
  symm := by intro x y; cases x <;> cases y <;> simp_all
  loopless := by intro x; cases x <;> simp

@[simp] theorem incidence_inl_inr (S : A → Finset B) (a : A) (b : B) :
    (incidence S).Adj (.inl a) (.inr b) ↔ b ∈ S a := Iff.rfl
@[simp] theorem incidence_inr_inl (S : A → Finset B) (a : A) (b : B) :
    (incidence S).Adj (.inr b) (.inl a) ↔ b ∈ S a := Iff.rfl
@[simp] theorem incidence_inl_inl (S : A → Finset B) (a a' : A) :
    ¬ (incidence S).Adj (.inl a) (.inl a') := not_false
@[simp] theorem incidence_inr_inr (S : A → Finset B) (b b' : B) :
    ¬ (incidence S).Adj (.inr b) (.inr b') := not_false

private theorem extract_rectangle (S : A → Finset B) {r : ℕ} (hr : 0 < r)
    (l t : Fin r ↪ A ⊕ B)
    (h : ∀ i j, (incidence S).Adj (l i) (t j))
    (hl : ∃ a, l ⟨0, hr⟩ = .inl a) :
    ∃ f : Fin r ↪ A, ∃ g : Fin r ↪ B, ∀ i j, g j ∈ S (f i) := by
  obtain ⟨a₀, ha₀⟩ := hl
  have ht : ∀ j, ∃ b, t j = .inr b := by
    intro j
    have hj := h ⟨0, hr⟩ j
    rw [ha₀] at hj
    cases he : t j with
    | inl a => simp [he] at hj
    | inr b => exact ⟨b, rfl⟩
  choose g hg using ht
  have hl' : ∀ i, ∃ a, l i = .inl a := by
    intro i
    have hi := h i ⟨0, hr⟩
    rw [hg] at hi
    cases he : l i with
    | inl a => exact ⟨a, rfl⟩
    | inr b => simp [he] at hi
  choose f hf using hl'
  have hfi : Function.Injective f := by
    intro i j hij
    apply l.injective
    rw [hf, hf, hij]
  have hgi : Function.Injective g := by
    intro i j hij
    apply t.injective
    rw [hg, hg, hij]
  refine ⟨⟨f, hfi⟩, ⟨g, hgi⟩, ?_⟩
  intro i j
  have hij := h i j
  simpa [hf, hg] using hij

/-- Incidence graphs contain a balanced biclique exactly when the set system contains
an all-incidence rectangle with distinct row and column indices. -/
theorem free_iff_no_rectangle (S : A → Finset B) {r : ℕ} (hr : 0 < r) :
    (completeBipartiteGraph (Fin r) (Fin r)).Free (incidence S) ↔
      ∀ f : Fin r ↪ A, ∀ g : Fin r ↪ B, ¬ ∀ i j, g j ∈ S (f i) := by
  constructor
  · intro h f g hfg
    apply h
    refine ⟨⟨⟨f.sumMap g, ?_⟩, (f.sumMap g).injective⟩⟩
    intro x y hxy
    cases x <;> cases y <;> simp_all
  · intro h ⟨c⟩
    let l : Fin r ↪ A ⊕ B :=
      ⟨fun i => c (.inl i), fun i j hij => Sum.inl_injective (c.injective hij)⟩
    let t : Fin r ↪ A ⊕ B :=
      ⟨fun i => c (.inr i), fun i j hij => Sum.inr_injective (c.injective hij)⟩
    have hlt : ∀ i j, (incidence S).Adj (l i) (t j) := by
      intro i j
      exact c.toHom.map_adj (by simp)
    have hex : ∃ f : Fin r ↪ A, ∃ g : Fin r ↪ B, ∀ i j, g j ∈ S (f i) := by
      cases he : l ⟨0, hr⟩ with
      | inl a => exact extract_rectangle S hr l t hlt ⟨a, he⟩
      | inr b =>
        have hright : ∃ a, t ⟨0, hr⟩ = .inl a := by
          have h₀ := hlt ⟨0, hr⟩ ⟨0, hr⟩
          rw [he] at h₀
          cases he' : t ⟨0, hr⟩ with
          | inl a => exact ⟨a, rfl⟩
          | inr b' => simp [he'] at h₀
        exact extract_rectangle S hr t l (fun i j => (hlt j i).symm) hright
    obtain ⟨f, g, hfg⟩ := hex
    exact h f g hfg

variable [Fintype B]

/-- The common elements of `r` distinctly indexed blocks. -/
noncomputable def common (S : A → Finset B) {r : ℕ} (f : Fin r ↪ A) : Finset B := by
  classical
  exact univ.filter (fun b => ∀ i, b ∈ S (f i))

@[simp] theorem mem_common (S : A → Finset B) {r : ℕ} (f : Fin r ↪ A) (b : B) :
    b ∈ common S f ↔ ∀ i, b ∈ S (f i) := by
  classical
  simp [common]

/-- The exact forbidden-intersection condition. It concerns distinct block indices,
not necessarily distinct block values. -/
theorem free_iff_common_card (S : A → Finset B) {r : ℕ} (hr : 0 < r) :
    (completeBipartiteGraph (Fin r) (Fin r)).Free (incidence S) ↔
      ∀ f : Fin r ↪ A, (common S f).card < r := by
  classical
  rw [free_iff_no_rectangle S hr]
  constructor
  · intro h f
    by_contra! hc
    obtain ⟨s, hs, hcard⟩ := exists_subset_card_eq hc
    let e : Fin r ≃ s := (Fintype.equivFinOfCardEq (by simpa using hcard)).symm
    let g : Fin r ↪ B := e.toEmbedding.trans (Function.Embedding.subtype _)
    apply h f g
    intro i j
    exact (mem_common S f (g j)).mp (hs (e j).property) i
  · intro h f g hfg
    have hs : univ.map g ⊆ common S f := by
      intro b hb
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hb
      exact (mem_common S f (g j)).mpr (fun i => hfg i j)
    have hc := card_le_card hs
    simp only [card_map, card_univ, Fintype.card_fin] at hc
    exact (h f).not_ge hc

variable [Fintype A]

open Classical

/-- Each incidence is counted once as an undirected edge. -/
theorem incidence_edges (S : A → Finset B) :
    (incidence S).edgeFinset.card = ∑ a, (S a).card := by
  classical
  let e : (Σ _ : A, B) ↪ Sym2 (A ⊕ B) :=
    ⟨fun p => s(Sum.inl p.1, Sum.inr p.2), by
      rintro ⟨a, b⟩ ⟨a', b'⟩ h
      simp only [Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq,
        Sum.inl_ne_inr, Sum.inr_ne_inl, and_false, or_false] at h
      rcases h with ⟨rfl, rfl⟩
      rfl⟩
  have hedge : (incidence S).edgeFinset = (univ.sigma S).map e := by
    ext z
    induction z using Sym2.inductionOn with
    | hf x y =>
      cases x <;> cases y <;>
        simp [mem_edgeFinset, mem_edgeSet, Finset.mem_map, e, eq_comm,
          incidence, Sigma.exists]
  rw [hedge, card_map, card_sigma]

/-- The dual incidence system, with block indices and points interchanged. -/
noncomputable def dual (S : A → Finset B) (b : B) : Finset A := by
  classical
  exact univ.filter (fun a => b ∈ S a)

omit [Fintype B] in
@[simp] theorem mem_dual (S : A → Finset B) (a : A) (b : B) :
    a ∈ dual S b ↔ b ∈ S a := by
  simp [dual]

/-- Block indices containing every point of `T`. -/
noncomputable def blocksContaining (S : A → Finset B) (T : Finset B) : Finset A := by
  classical
  exact univ.filter (fun a => T ⊆ S a)

omit [Fintype B] in
@[simp] theorem mem_blocksContaining (S : A → Finset B) (T : Finset B) (a : A) :
    a ∈ blocksContaining S T ↔ T ⊆ S a := by
  simp [blocksContaining]

/-- Packing with index at most `r-1`: every `r`-element point set belongs to fewer
than `r` indexed blocks. -/
def IsPacking (S : A → Finset B) (r : ℕ) : Prop :=
  ∀ T : Finset B, T.card = r → (blocksContaining S T).card < r

omit [Fintype B] in
lemma common_dual_eq (S : A → Finset B) {r : ℕ} (g : Fin r ↪ B) :
    common (dual S) g = blocksContaining S (univ.map g) := by
  ext a
  simp only [mem_common, mem_dual, mem_blocksContaining]
  constructor
  · intro h b hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hb
    exact h i
  · intro h i
    exact h (Finset.mem_map.mpr ⟨i, mem_univ _, rfl⟩)

/-- For balanced bicliques the forbidden-intersection condition is self-dual. -/
theorem common_card_dual_iff (S : A → Finset B) {r : ℕ} (hr : 0 < r) :
    (∀ f : Fin r ↪ A, (common S f).card < r) ↔
      ∀ g : Fin r ↪ B, (common (dual S) g).card < r := by
  rw [← free_iff_common_card S hr, ← free_iff_common_card (dual S) hr,
    free_iff_no_rectangle S hr, free_iff_no_rectangle (dual S) hr]
  constructor
  · intro h g f hfg
    apply h f g
    intro i j
    exact (mem_dual S (f i) (g j)).mp (hfg j i)
  · intro h f g hfg
    apply h g f
    intro j i
    exact (mem_dual S (f i) (g j)).mpr (hfg i j)

/-- The intersection formulation and the usual point-packing formulation coincide. -/
theorem isPacking_iff_common_card (S : A → Finset B) {r : ℕ} (hr : 0 < r) :
    IsPacking S r ↔ ∀ f : Fin r ↪ A, (common S f).card < r := by
  rw [common_card_dual_iff S hr]
  constructor
  · intro h g
    rw [common_dual_eq]
    apply h
    simp
  · intro h T hT
    obtain ⟨g : Fin r ↪ B, hg⟩ :=
      Function.Embedding.exists_of_card_eq_finset (α := Fin r) (s := T)
        (by simpa using hT.symm)
    simpa only [common_dual_eq, hg] using h g

/-- The neighborhood set system of a free graph has bounded `r`-fold intersections. -/
theorem neighborhood_common_card {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {r : ℕ}
    (hG : (completeBipartiteGraph (Fin r) (Fin r)).Free G) (f : Fin r ↪ V) :
    (common (fun v => G.neighborFinset v) f).card < r := by
  classical
  by_contra! hc
  obtain ⟨s, hs, hcard⟩ := exists_subset_card_eq hc
  apply hG
  refine ⟨Copy.completeBipartiteGraph (univ.map f) s (by simp) (by simpa using hcard) ?_⟩
  intro v hv w hw
  change v ∈ univ.map f at hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hv
  have hi := (mem_common _ f w).mp (hs hw) i
  simpa using hi

end Erdos714Packing
end

noncomputable section
open Finset Classical
namespace Erdos714Unbalanced
open Erdos714Packing
variable {A B : Type*} [Fintype A] [Fintype B]

def starEquiv (S : A → Finset B) (r : ℕ) :
    (Σ a : A, Fin r ↪ S a) ≃
      (Σ f : Fin r ↪ B, {a : A // a ∈ common (dual S) f}) where
  toFun p := ⟨⟨fun i => (p.2 i).val, fun i j h => p.2.injective (Subtype.ext h)⟩,
    ⟨p.1, by simp only [mem_common, mem_dual]; exact fun i => (p.2 i).property⟩⟩
  invFun p := ⟨p.2.val, ⟨fun i => ⟨p.1 i, by
    have h := (mem_common (dual S) p.1 p.2.val).mp p.2.property i
    exact (mem_dual S p.2.val (p.1 i)).mp h⟩,
    fun i j h => p.1.injective (congrArg Subtype.val h)⟩⟩
  left_inv p := by rcases p with ⟨a,f⟩; rfl
  right_inv p := by rcases p with ⟨f,a,h⟩; rfl

end Erdos714Unbalanced
end


/-
A local star-count refinement for the fourth balanced Zarankiewicz case.
These are necessary degree bounds, not a solution of Erdős 714.
-/
noncomputable section
open Finset SimpleGraph Classical
set_option maxHeartbeats 2000000
namespace Erdos714FourthLocal
open Erdos714Packing
variable {A B : Type*} [Fintype A] [Fintype B]

abbrev PairCommon (S : A → Finset B) (a b : A) := ↥(S a ∩ S b)

/-- Restrict to two rows' common columns, and remove those two rows. -/
def localRows (S : A → Finset B) (a b c : A) : Finset (PairCommon S a b) :=
  if c = a ∨ c = b then ∅ else univ.filter (fun x => x.val ∈ S c)

omit [Fintype A] [Fintype B] in
lemma mem_localRows (S : A → Finset B) (a b c : A) (x : PairCommon S a b) :
    x ∈ localRows S a b c ↔ c ≠ a ∧ c ≠ b ∧ x.val ∈ S c := by
  simp only [localRows]
  split_ifs with h
  · simp only [notMem_empty, false_iff]
    tauto
  · simp_all

/-- Four common columns admit at most one row other than the two already fixed. -/
theorem local_common_le_one (S : A → Finset B) (a b : A) (hab : a ≠ b)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (f : Fin 4 ↪ PairCommon S a b) :
    (common (dual (localRows S a b)) f).card ≤ 1 := by
  let g : Fin 4 ↪ B := f.trans ⟨Subtype.val, Subtype.val_injective⟩
  let D := common (dual S) g
  let E := common (dual (localRows S a b)) f
  have hD : D.card < 4 :=
    (common_card_dual_iff S (by decide)).mp
      ((free_iff_common_card S (by decide)).mp hfree) g
  have haD : a ∈ D := by
    simp only [D, mem_common, mem_dual]
    exact fun i => (mem_inter.mp (f i).property).1
  have hbD : b ∈ D := by
    simp only [D, mem_common, mem_dual]
    exact fun i => (mem_inter.mp (f i).property).2
  have hE (c : A) (hc : c ∈ E) : c ≠ a ∧ c ≠ b ∧ c ∈ D := by
    have hc' : ∀ i, f i ∈ localRows S a b c := by
      simpa only [E, mem_common, mem_dual] using hc
    have h₀ := (mem_localRows S a b c (f 0)).mp (hc' 0)
    refine ⟨h₀.1, h₀.2.1, ?_⟩
    simp only [D, mem_common, mem_dual]
    exact fun i => ((mem_localRows S a b c (f i)).mp (hc' i)).2.2
  have haE : a ∉ E := fun h => (hE a h).1 rfl
  have hbE : b ∉ E := fun h => (hE b h).2.1 rfl
  have hsub : insert a (insert b E) ⊆ D := by
    simp only [insert_subset_iff]
    exact ⟨haD, hbD, fun c hc => (hE c hc).2.2⟩
  have hcard := card_le_card hsub
  rw [card_insert_of_notMem (by simp [hab, haE]), card_insert_of_notMem hbE] at hcard
  change E.card ≤ 1
  omega

/-- The local ordered-star bound has coefficient one, rather than three. -/
theorem local_fourth_moment (S : A → Finset B) (a b : A) (hab : a ≠ b)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    (∑ c : A, ((localRows S a b c).card - 3)^4) ≤ (S a ∩ S b).card^4 := by
  have hcount := Fintype.card_congr (Erdos714Unbalanced.starEquiv (localRows S a b) 4)
  simp only [Fintype.card_sigma, Fintype.card_embedding_eq, Fintype.card_fin,
    Fintype.card_coe] at hcount
  calc
    _ ≤ ∑ c : A, (localRows S a b c).card.descFactorial 4 :=
      sum_le_sum (fun c _ => Nat.pow_sub_le_descFactorial _ 4)
    _ = ∑ f : Fin 4 ↪ PairCommon S a b, (common (dual (localRows S a b)) f).card := hcount
    _ ≤ ∑ _f : Fin 4 ↪ PairCommon S a b, 1 :=
      sum_le_sum (fun f _ => local_common_le_one S a b hab hfree f)
    _ = (S a ∩ S b).card.descFactorial 4 := by simp
    _ ≤ _ := Nat.descFactorial_le_pow _ _

/-- A purely integer version of the local fourth-root estimate. -/
theorem local_edge_bound (S : A → Finset B) (a b : A) (hab : a ≠ b)
    (q : ℕ) (hA : Fintype.card A ≤ q^4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    (∑ c : A, (localRows S a b c).card) ≤
      q^3*(S a ∩ S b).card + 3*Fintype.card A := by
  have hp := pow_sum_le_card_mul_sum_pow (s := (univ : Finset A))
    (f := fun c => (localRows S a b c).card - 3) (by intros; omega) 3
  simp only [card_univ] at hp
  have hpow : (∑ c : A, ((localRows S a b c).card - 3))^4 ≤
      (q^3*(S a ∩ S b).card)^4 := by
    calc
      _ ≤ Fintype.card A^3 * ∑ c : A, ((localRows S a b c).card-3)^4 := hp
      _ ≤ (q^4)^3 * (S a ∩ S b).card^4 := by
        gcongr
        exact local_fourth_moment S a b hab hfree
      _ = _ := by ring
  have hsum := (Nat.pow_le_pow_iff_left (by decide : 4 ≠ 0)).mp hpow
  calc
    _ ≤ ∑ c : A, ((localRows S a b c).card - 3 + 3) :=
      sum_le_sum (fun c _ => by omega)
    _ = (∑ c : A, ((localRows S a b c).card - 3)) + 3*Fintype.card A := by
      simp [sum_add_distrib, mul_comm]
    _ ≤ _ := Nat.add_le_add_right hsum _

omit [Fintype B] in
lemma local_dual (S : A → Finset B) (a b : A) (x : PairCommon S a b) :
    dual (localRows S a b) x = ((dual S x.val).erase a).erase b := by
  ext c
  simp only [mem_dual, mem_localRows, mem_erase]
  tauto

omit [Fintype B] in
/-- Reinsert the two fixed rows in each column count. -/
lemma local_column_count (S : A → Finset B) (a b : A) (hab : a ≠ b)
    (x : PairCommon S a b) :
    (dual (localRows S a b) x).card + 2 = (dual S x.val).card := by
  rw [local_dual]
  have ha : a ∈ dual S x.val := (mem_dual S a x.val).mpr (mem_inter.mp x.property).1
  have hb : b ∈ (dual S x.val).erase a := by
    simp only [mem_erase, mem_dual]
    exact ⟨Ne.symm hab, (mem_inter.mp x.property).2⟩
  have h₁ := card_erase_add_one ha
  have h₂ := card_erase_add_one hb
  omega

/-- Exact degree sum over the fixed pair's common columns. -/
theorem local_degree_sum (S : A → Finset B) (a b : A) (hab : a ≠ b)
    (q : ℕ) (hA : Fintype.card A ≤ q^4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    (∑ x : PairCommon S a b, (dual S x.val).card) ≤
      (q^3+2)*(S a ∩ S b).card + 3*Fintype.card A := by
  have he := local_edge_bound S a b hab q hA hfree
  have hcount' : (∑ c, (localRows S a b c).card) = ∑ x, (dual (localRows S a b) x).card := by
    have hc (c : A) : (localRows S a b c).card =
        ∑ x : PairCommon S a b, if x ∈ localRows S a b c then 1 else 0 := by
      rw [sum_boole]
      congr 1
      ext x
      simp
    simp_rw [hc]
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    simp only [sum_boole, Nat.cast_id, dual]
    congr 1
    ext c
    simp
  have hsum : (∑ x : PairCommon S a b, (dual S x.val).card) =
      (∑ c : A, (localRows S a b c).card) + 2*(S a ∩ S b).card := by
    rw [hcount']
    simp_rw [← local_column_count S a b hab]
    simp [sum_add_distrib, mul_comm]
  rw [hsum]
  nlinarith

/-- Under a uniform column-degree lower bound, every pair intersection is small. -/
theorem pair_degree_bound (S : A → Finset B) (a b : A) (hab : a ≠ b)
    (q d : ℕ) (hA : Fintype.card A ≤ q^4)
    (hd : ∀ x : B, d ≤ (dual S x).card)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    d*(S a ∩ S b).card ≤ (q^3+2)*(S a ∩ S b).card + 3*Fintype.card A := by
  calc
    _ = ∑ _x : PairCommon S a b, d := by simp [mul_comm]
    _ ≤ ∑ x : PairCommon S a b, (dual S x.val).card := sum_le_sum (fun x _ => hd x.val)
    _ ≤ _ := local_degree_sum S a b hab q hA hfree

lemma pair_count (S : A → Finset B) :
    (∑ x : B, (dual S x).card.descFactorial 2) =
      ∑ f : Fin 2 ↪ A, (S (f 0) ∩ S (f 1)).card := by
  have h := Fintype.card_congr (Erdos714Unbalanced.starEquiv (dual S) 2)
  simp only [Fintype.card_sigma, Fintype.card_embedding_eq, Fintype.card_fin,
    Fintype.card_coe] at h
  have hdual : dual (dual S) = S := by
    funext a
    ext x
    simp only [mem_dual]
  rw [hdual] at h
  have hc (f : Fin 2 ↪ A) : common S f = S (f 0) ∩ S (f 1) := by
    ext x
    simp only [mem_common, Fin.forall_fin_two, mem_inter]
  simpa only [hc] using h

/-- A high column minimum degree forces a pair with at least q² common columns. -/
theorem exists_large_pair (S : A → Finset B) (q : ℕ) (hq : 0 < q)
    (hA : Fintype.card A ≤ q^4) (hB : Fintype.card B = q^4)
    (hd : ∀ x : B, q^3+1 ≤ (dual S x).card) :
    ∃ a b : A, a ≠ b ∧ q^2 ≤ (S a ∩ S b).card := by
  have hbase : q^6 ≤ (q^3+1).descFactorial 2 := by
    calc
      _ = (q^3)^2 := by ring
      _ ≤ _ := by simpa using Nat.pow_sub_le_descFactorial (q^3+1) 2
  have hlo : q^10 ≤ ∑ f : Fin 2 ↪ A, (S (f 0) ∩ S (f 1)).card := by
    rw [← pair_count]
    calc
      _ = ∑ _x : B, q^6 := by simp [hB]; ring
      _ ≤ _ := sum_le_sum (fun x _ => hbase.trans (Nat.descFactorial_le 2 (hd x)))
  have hnum : Fintype.card (Fin 2 ↪ A) ≤ q^8 := by
    calc
      _ = (Fintype.card A).descFactorial 2 := by simp
      _ ≤ Fintype.card A^2 := Nat.descFactorial_le_pow _ _
      _ ≤ (q^4)^2 := Nat.pow_le_pow_left hA 2
      _ = _ := by ring
  by_contra! hn
  have hsmall (f : Fin 2 ↪ A) : (S (f 0) ∩ S (f 1)).card < q^2 :=
    hn (f 0) (f 1) (fun h => by have := f.injective h; exact (by decide : (0 : Fin 2) ≠ 1) this)
  have hp : 0 < ∑ f : Fin 2 ↪ A, (S (f 0) ∩ S (f 1)).card := (pow_pos hq _).trans_le hlo
  obtain ⟨f, hf, _⟩ := sum_pos_iff.mp hp
  have hlt := sum_lt_sum_of_nonempty (s := (univ : Finset (Fin 2 ↪ A)))
    ⟨f, hf⟩ (fun f _ => hsmall f)
  have hhi : (∑ f : Fin 2 ↪ A, (S (f 0) ∩ S (f 1)).card) < q^10 := by
    calc
      _ < ∑ _f : Fin 2 ↪ A, q^2 := hlt
      _ = Fintype.card (Fin 2 ↪ A)*q^2 := by simp
      _ ≤ q^8*q^2 := Nat.mul_le_mul_right _ hnum
      _ = _ := by ring
  omega

/-- A fourth-case packing on at most q⁴ rows and exactly q⁴ columns has
column minimum degree at most q³ + 3q² + 2. -/
theorem column_minimum_bound (S : A → Finset B) (q d : ℕ) (hq : 0 < q)
    (hA : Fintype.card A ≤ q^4) (hB : Fintype.card B = q^4)
    (hd : ∀ x : B, d ≤ (dual S x).card)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    d ≤ q^3 + 3*q^2 + 2 := by
  by_contra! hlarge
  obtain ⟨a,b,hab,hm⟩ := exists_large_pair S q hq hA hB (fun x => by have := hd x; omega)
  have hpair := pair_degree_bound S a b hab q d hA hd hfree
  have hmult : (q^3+3*q^2+3)*(S a ∩ S b).card ≤ d*(S a ∩ S b).card :=
    Nat.mul_le_mul_right _ (by omega)
  have hq2 : 0 < q^2 := pow_pos hq _
  have hmul : q^2*q^2 ≤ q^2*(S a ∩ S b).card := Nat.mul_le_mul_left _ hm
  have heq : q^2*q^2 = q^4 := by ring
  nlinarith

/-- The same result without choosing a minimum in advance. -/
theorem exists_small_column (S : A → Finset B) (q : ℕ) (hq : 0 < q)
    (hA : Fintype.card A ≤ q^4) (hB : Fintype.card B = q^4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    ∃ x : B, (dual S x).card ≤ q^3 + 3*q^2 + 2 := by
  by_contra! h
  have hh := column_minimum_bound S q (q^3+3*q^2+3) hq hA hB
    (fun x => by have := h x; omega) hfree
  omega

end Erdos714FourthLocal
end


/-
A fourth-case average-degree refinement of the local star count.
This sharpens an upper-bound constant, not the exponent in Erdős 714.
-/
noncomputable section
open Finset SimpleGraph Classical
set_option maxHeartbeats 2000000
namespace Erdos714FourthLocal
open Erdos714Packing
variable {A B : Type*} [Fintype A] [Fintype B]

/-- Weighted double counting of ordered pairs of rows through a column. -/
lemma weighted_pair_count (S : A → Finset B) (w : B → ℕ) :
    (∑ x : B, w x*(dual S x).card.descFactorial 2) =
      ∑ f : Fin 2 ↪ A, ∑ x ∈ S (f 0) ∩ S (f 1), w x := by
  have h := Fintype.sum_equiv (Erdos714Unbalanced.starEquiv (dual S) 2)
    (fun p => w p.1) (fun p => w p.2.val) (fun p => rfl)
  simp only [Fintype.sum_sigma, sum_const, card_univ, Fintype.card_embedding_eq,
    Fintype.card_fin, nsmul_eq_mul] at h
  have hdual : dual (dual S) = S := by
    funext a
    ext x
    simp only [mem_dual]
  rw [hdual] at h
  have hc (f : Fin 2 ↪ A) : common S f = S (f 0) ∩ S (f 1) := by
    ext x
    simp only [mem_common, Fin.forall_fin_two, mem_inter]
  simp_rw [sum_coe_sort, hc] at h
  simpa only [Fintype.card_coe, Nat.cast_id, mul_comm] using h

/-- The local inequality, summed over all ordered row pairs. -/
theorem degree_cubic_moment (S : A → Finset B) (q : ℕ)
    (hA : Fintype.card A ≤ q^4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    (∑ x : B, (dual S x).card * (dual S x).card.descFactorial 2) ≤
      (q^3+2)*(∑ x : B, (dual S x).card.descFactorial 2) + 3*Fintype.card A^3 := by
  have hl (f : Fin 2 ↪ A) := local_degree_sum S (f 0) (f 1)
    (fun h => (by decide : (0 : Fin 2) ≠ 1) (f.injective h)) q hA hfree
  have h := sum_le_sum (s := (univ : Finset (Fin 2 ↪ A))) (fun f _ => hl f)
  have hsum (f : Fin 2 ↪ A) : (∑ x : PairCommon S (f 0) (f 1), (dual S x.val).card) =
      ∑ x ∈ S (f 0) ∩ S (f 1), (dual S x).card := sum_coe_sort (S (f 0) ∩ S (f 1)) (fun x => (dual S x).card)
  simp_rw [hsum] at h
  rw [sum_add_distrib, ← mul_sum, ← pair_count S,
    ← weighted_pair_count S (fun x => (dual S x).card)] at h
  simp only [sum_const, card_univ, nsmul_eq_mul] at h
  have hn : Fintype.card (Fin 2 ↪ A) ≤ Fintype.card A^2 := by
    simpa only [Fintype.card_embedding_eq, Fintype.card_fin] using
      Nat.descFactorial_le_pow (Fintype.card A) 2
  calc
    _ ≤ _ := h
    _ ≤ _ := by nlinarith [Nat.mul_le_mul_right (3*Fintype.card A) hn]

/-- A cubic supporting-line identity avoids any regularity assumption. -/
lemma cubic_support (Q D x : ℝ) (hx : 0 ≤ x) (hD : Q+1 ≤ 2*D) :
    D*(D-1)*(D-Q) + (D*(D-1)+(D-Q)*(2*D-1))*(x-D) ≤ x*(x-1)*(x-Q) := by
  have h := mul_nonneg (sq_nonneg (x-D)) (show 0 ≤ x+2*D-Q-1 by linarith)
  nlinarith

/-- Balanced fourth-case incidence graphs have leading average-degree constant one.
The row part may be smaller than the column part. -/
theorem average_degree_bound (S : A → Finset B) (q : ℕ)
    (hA : Fintype.card A ≤ q^4) (hAB : Fintype.card A ≤ Fintype.card B)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    (∑ x : B, (dual S x).card) ≤ (q^3+3*q^2+2)*Fintype.card B := by
  let Q : ℝ := (q : ℝ)^3+2
  let D : ℝ := (q : ℝ)^3+3*(q : ℝ)^2+2
  let L : ℝ := D*(D-1)+(D-Q)*(2*D-1)
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hQ : 2 ≤ Q := by dsimp [Q]; have := pow_nonneg hq 3; linarith
  have hDQ : Q ≤ D := by dsimp [Q,D]; nlinarith [sq_nonneg (q : ℝ)]
  have hD : 2 ≤ D := hQ.trans hDQ
  have hL : 0 < L := by
    dsimp [L]
    have h₁ : 0 < D*(D-1) := mul_pos (by linarith) (by linarith)
    have h₂ : 0 ≤ (D-Q)*(2*D-1) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hfD : 3*(q : ℝ)^8 ≤ D*(D-1)*(D-Q) := by
    have h₁ : (q : ℝ)^3 ≤ D := by dsimp [D]; nlinarith [sq_nonneg (q : ℝ)]
    have h₂ : (q : ℝ)^3 ≤ D-1 := by dsimp [D]; nlinarith [sq_nonneg (q : ℝ)]
    have hp : (q : ℝ)^6 ≤ D*(D-1) := by
      calc
        _ = (q : ℝ)^3*(q : ℝ)^3 := by ring
        _ ≤ _ := mul_le_mul h₁ h₂ (by positivity) (by linarith)
    have he : D-Q = 3*(q : ℝ)^2 := by dsimp [D,Q]; ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ 3*(q : ℝ)^2)]
  have hmoment : (∑ x : B, ((dual S x).card : ℝ)*((dual S x).card-1)*((dual S x).card-Q)) ≤
      3*(Fintype.card A : ℝ)^3 := by
    have h := (Nat.cast_le (α := ℝ)).mpr (degree_cubic_moment S q hA hfree)
    simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_descFactorial_two] at h
    calc
      _ = (∑ x : B, ((dual S x).card : ℝ)*((dual S x).card*((dual S x).card-1))) -
          Q*(∑ x : B, ((dual S x).card : ℝ)*((dual S x).card-1)) := by
        rw [mul_sum, ← sum_sub_distrib]
        apply sum_congr rfl
        intro x _
        ring
      _ ≤ _ := by dsimp [Q]; linarith
  have hsupport : (Fintype.card B : ℝ)*(D*(D-1)*(D-Q)) +
      L*((∑ x : B, ((dual S x).card : ℝ))-D*Fintype.card B) ≤
      ∑ x : B, ((dual S x).card : ℝ)*((dual S x).card-1)*((dual S x).card-Q) := by
    have h := sum_le_sum (s := (univ : Finset B))
      (fun x _ => cubic_support Q D ((dual S x).card) (by positivity) (by linarith))
    change (∑ x : B, (D*(D-1)*(D-Q)+L*(((dual S x).card : ℝ)-D))) ≤ _ at h
    rw [sum_add_distrib] at h
    rw [← mul_sum _ _ L, sum_sub_distrib] at h
    simp only [sum_const, card_univ, nsmul_eq_mul] at h
    (convert h using 1; ring)
  have hbudget : 3*(Fintype.card A : ℝ)^3 ≤ (Fintype.card B : ℝ)*(D*(D-1)*(D-Q)) := by
    have ha : (Fintype.card A : ℝ) ≤ (q : ℝ)^4 := by exact_mod_cast hA
    have hab : (Fintype.card A : ℝ) ≤ Fintype.card B := by exact_mod_cast hAB
    calc
      _ = 3*(Fintype.card A : ℝ)*(Fintype.card A : ℝ)^2 := by ring
      _ ≤ 3*(Fintype.card B : ℝ)*((q : ℝ)^4)^2 := by gcongr
      _ = (Fintype.card B : ℝ)*(3*(q : ℝ)^8) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfD (by positivity)
  have he : (∑ x : B, ((dual S x).card : ℝ)) ≤ D*Fintype.card B := by
    have h := hsupport.trans hmoment
    have hmul : L*((∑ x : B, ((dual S x).card : ℝ))-D*Fintype.card B) ≤ 0 := by linarith
    by_contra! hh
    have hp := mul_pos hL (sub_pos.mpr hh)
    linarith
  dsimp [D] at he
  exact_mod_cast he

end Erdos714FourthLocal
end


/- Transfer the fourth-case average-degree bound to actual extremal numbers. -/
noncomputable section
open Finset SimpleGraph Classical Filter
set_option maxHeartbeats 2000000
namespace Erdos714FourthUpper
open Erdos714Packing Erdos714FourthLocal

/-- The bipartite neighborhood double cover preserves the relevant freeness. -/
lemma neighborhood_incidence_free {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free G) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (incidence (fun v => G.neighborFinset v)) := by
  exact (free_iff_common_card _ (by decide)).mpr (neighborhood_common_card G hfree)

/-- Natural fourth-root parameter form, with the factor of two for undirected edges. -/
theorem graph_bound {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℕ) (hq : Fintype.card V ≤ q^4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free G) :
    2*G.edgeFinset.card ≤ (q^3+3*q^2+2)*Fintype.card V := by
  have h := average_degree_bound (fun v => G.neighborFinset v) q hq le_rfl
    (neighborhood_incidence_free G hfree)
  have hd (v : V) : dual (fun w => G.neighborFinset w) v = G.neighborFinset v := by
    ext w
    simp only [mem_dual, mem_neighborFinset, G.adj_comm]
  simp_rw [hd, card_neighborFinset_eq_degree] at h
  rwa [G.sum_degrees_eq_twice_card_edges] at h

/-- The same finite upper bound for the actual Mathlib extremal number. -/
theorem extremal_bound (n q : ℕ) (hq : n ≤ q^4) :
    2*extremalNumber n (completeBipartiteGraph (Fin 4) (Fin 4)) ≤
      (q^3+3*q^2+2)*n := by
  have hn : completeBipartiteGraph (Fin 4) (Fin 4) ≠ ⊥ := by
    intro h
    have he : (completeBipartiteGraph (Fin 4) (Fin 4)).Adj (.inl 0) (.inr 0) := by simp
    rw [h] at he
    exact he
  obtain ⟨G,inst,hG⟩ := exists_isExtremal_free (V := Fin n) hn
  have h := graph_bound G q (by simpa using hq) hG.prop
  rw [card_edgeFinset_of_isExtremal_free hG] at h
  simpa only [Fintype.card_fin] using h

/-- In particular the q⁴-order bound has leading coefficient one half. -/
theorem extremal_scaled_bound (q : ℕ) :
    2*extremalNumber (q^4) (completeBipartiteGraph (Fin 4) (Fin 4)) ≤
      q^7+3*q^6+2*q^4 := by
  have h := extremal_bound (q^4) q le_rfl
  (convert h using 1; ring)

/-- An explicit all-orders real bound; the error has strictly smaller exponent. -/
theorem extremal_real_bound (n : ℕ) :
    (extremalNumber n (completeBipartiteGraph (Fin 4) (Fin 4)) : ℝ) ≤
      (1/2 : ℝ)*(n : ℝ)^((7 : ℝ)/4) + 3*(n : ℝ)^((3 : ℝ)/2) +
      (9/2 : ℝ)*(n : ℝ)^((5 : ℝ)/4) + 3*(n : ℝ) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  let x : ℝ := (n : ℝ)^((1 : ℝ)/4)
  let q : ℕ := ⌈x⌉₊
  have hx : 0 ≤ x := Real.rpow_nonneg hn _
  have hpow (k : ℕ) : x^k = (n : ℝ)^((k : ℝ)/4) := by
    dsimp [x]
    rw [← Real.rpow_mul_natCast hn]
    congr 1
    ring
  have hx4 : x^4 = (n : ℝ) := by simpa using hpow 4
  have hqx : x ≤ (q : ℝ) := Nat.le_ceil x
  have hq : n ≤ q^4 := by
    have h := pow_le_pow_left₀ hx hqx 4
    rw [hx4] at h
    exact_mod_cast h
  have hq' : (q : ℝ) ≤ x+1 := (Nat.ceil_lt_add_one hx).le
  have he : 2*(extremalNumber n (completeBipartiteGraph (Fin 4) (Fin 4)) : ℝ) ≤
      ((q : ℝ)^3+3*(q : ℝ)^2+2)*(n : ℝ) := by exact_mod_cast extremal_bound n q hq
  have he' : 2*(extremalNumber n (completeBipartiteGraph (Fin 4) (Fin 4)) : ℝ) ≤
      x^7+6*x^6+9*x^5+6*x^4 := by
    calc
      _ ≤ ((q : ℝ)^3+3*(q : ℝ)^2+2)*(n : ℝ) := he
      _ ≤ ((x+1)^3+3*(x+1)^2+2)*(n : ℝ) := by gcongr
      _ = _ := by rw [← hx4]; ring
  rw [hpow 7, hpow 6, hpow 5, hx4] at he'
  norm_num at he'
  linarith

/-- A two-term version retaining the leading constant one half. -/
theorem extremal_two_term_bound (n : ℕ) (hn : 1 ≤ n) :
    (extremalNumber n (completeBipartiteGraph (Fin 4) (Fin 4)) : ℝ) ≤
      (1/2 : ℝ)*(n : ℝ)^((7 : ℝ)/4) + (21/2 : ℝ)*(n : ℝ)^((3 : ℝ)/2) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h₁ : (n : ℝ)^((5 : ℝ)/4) ≤ (n : ℝ)^((3 : ℝ)/2) :=
    Real.rpow_le_rpow_of_exponent_le hn' (by norm_num)
  have h₂ : (n : ℝ) ≤ (n : ℝ)^((3 : ℝ)/2) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn' (show (1 : ℝ) ≤ 3/2 by norm_num)
  have h := extremal_real_bound n
  linarith

/-- Any eventual lower-bound constant in the fourth instance is at most one half.
This restricts the constant only; it does not rule out a positive constant. -/
theorem lower_constant_le_half (c : ℝ)
    (h : ∀ᶠ n : ℕ in atTop,
      c*(n : ℝ)^((7 : ℝ)/4) ≤
        (extremalNumber n (completeBipartiteGraph (Fin 4) (Fin 4)) : ℝ)) :
    c ≤ 1/2 := by
  by_contra! hc
  have hd : 0 < 2*c-1 := by linarith
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  obtain ⟨q,hq⟩ := exists_nat_gt (max (N : ℝ) (max 1 (5/(2*c-1))))
  have hq1 : (1 : ℝ) < q := (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hq)
  have hq0 : 0 < q := by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hq1)
  have hqN : N ≤ q := by
    have hn : (N : ℝ) < q := (le_max_left _ _).trans_lt hq
    exact_mod_cast hn.le
  have hqL : 5/(2*c-1) < (q : ℝ) :=
    (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hq)
  have hnq : N ≤ q^4 := hqN.trans (by
    simpa only [pow_one] using pow_le_pow_right' (show 1 ≤ q by omega) (show 1 ≤ 4 by decide))
  have hlo := hN (q^4) hnq
  have hp : ((q^4 : ℕ) : ℝ)^((7 : ℝ)/4) = (q : ℝ)^7 := by
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity)]
    norm_num
  rw [hp] at hlo
  have hup : 2*(extremalNumber (q^4) (completeBipartiteGraph (Fin 4) (Fin 4)) : ℝ) ≤
      (q : ℝ)^7+3*(q : ℝ)^6+2*(q : ℝ)^4 := by exact_mod_cast extremal_scaled_bound q
  have hpow : (q : ℝ)^4 ≤ (q : ℝ)^6 := pow_le_pow_right₀ hq1.le (by decide)
  have hmul : ((2*c-1)*(q : ℝ))*(q : ℝ)^6 ≤ 5*(q : ℝ)^6 := by
    have heq : (q : ℝ)^7 = (q : ℝ)*(q : ℝ)^6 := by ring
    nlinarith
  have hsmall := (mul_le_mul_iff_left₀ (pow_pos (show (0 : ℝ) < q by exact_mod_cast hq0) 6)).mp
    hmul
  have hlarge : 5 < (2*c-1)*(q : ℝ) := by
    have hh := (div_lt_iff₀ hd).mp hqL
    nlinarith
  linarith

end Erdos714FourthUpper
end

namespace Erdos714Progress

/-- Increasing both parts of the forbidden biclique increases the extremal number. -/
theorem extremal_biclique_mono (s r n : ℕ) (hsr : s ≤ r) :
    extremalNumber n (completeBipartiteGraph (Fin s) (Fin s)) ≤
      extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) := by
  let e : Fin s ↪ Fin r := Fin.castLEEmb hsr
  have hcopy : (completeBipartiteGraph (Fin s) (Fin s)) ⊑
      (completeBipartiteGraph (Fin r) (Fin r)) := by
    refine ⟨⟨⟨Sum.map e e, ?_⟩, Sum.map_injective.mpr ⟨e.injective, e.injective⟩⟩⟩
    intro x y hxy
    cases x <;> cases y <;> simp_all
  exact hcopy.extremalNumber_le

/-- The known third-case exponent also applies to every larger balanced biclique. -/
theorem third_exponent_for_larger_bicliques (r : ℕ) (hr : 3 ≤ r) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ)^((5 : ℝ)/3) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ) := by
  obtain ⟨c, hc, hn⟩ := Erdos714Norm.third_instance
  refine ⟨c, hc, ?_⟩
  filter_upwards [hn] with n hn
  have he : (extremalNumber n (completeBipartiteGraph (Fin 3) (Fin 3)) : ℝ) ≤
      (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ) :=
    Nat.cast_le.mpr (extremal_biclique_mono 3 r n hr)
  have hpow : (2 : ℝ)-1/(3 : ℝ) = 5/3 := by norm_num
  rw [hpow] at hn
  exact hn.trans he

/-- Combine the third-case construction with alteration. This is weaker than
 the conjectured exponent in the range beginning at four. -/
theorem combined_known_lower_bound (r : ℕ) (hr : 3 ≤ r) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ)^(max ((5 : ℝ)/3) ((2 : ℝ)-2/(r+1 : ℝ))) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ) := by
  rcases le_total ((2 : ℝ)-2/(r+1 : ℝ)) ((5 : ℝ)/3) with h | h
  · rw [max_eq_left h]
    exact third_exponent_for_larger_bicliques r hr
  · rw [max_eq_right h]
    exact Erdos714Random.all_r_alteration r (by omega)

/-- The cubic norm graph improves the known construction exponent for larger bicliques.
This is still strictly weaker than the conjecture at r=5 and r=6. -/
theorem improved_known_lower_bound (r : ℕ) (hr : 5 ≤ r) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ)^(max ((7 : ℝ)/4) ((2 : ℝ)-2/(r+1 : ℝ))) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ) := by
  rcases le_total ((2 : ℝ)-2/(r+1 : ℝ)) ((7 : ℝ)/4) with h | h
  · rw [max_eq_left h]
    exact Erdos714CubicNormLower.larger_lower r hr
  · rw [max_eq_right h]
    exact Erdos714Random.all_r_alteration r (by omega)

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
