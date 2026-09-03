import FormalConjecturesUtil

/-! The elementary alteration bound for a finite family of forbidden subsets. -/

open Finset Filter SimpleGraph

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

namespace Erdos714Alteration

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

