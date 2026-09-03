import FormalConjecturesUtil

/-! Set-system formulations for the balanced Zarankiewicz problem.

This file contains reductions, not a proof of the conjecture.
-/

open Finset SimpleGraph Filter

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

@[simp] theorem mem_dual (S : A → Finset B) (a : A) (b : B) :
    a ∈ dual S b ↔ b ∈ S a := by
  simp [dual]

/-- Block indices containing every point of `T`. -/
noncomputable def blocksContaining (S : A → Finset B) (T : Finset B) : Finset A := by
  classical
  exact univ.filter (fun a => T ⊆ S a)

@[simp] theorem mem_blocksContaining (S : A → Finset B) (T : Finset B) (a : A) :
    a ∈ blocksContaining S T ↔ T ⊆ S a := by
  simp [blocksContaining]

/-- Packing with index at most `r-1`: every `r`-element point set belongs to fewer
than `r` indexed blocks. -/
def IsPacking (S : A → Finset B) (r : ℕ) : Prop :=
  ∀ T : Finset B, T.card = r → (blocksContaining S T).card < r

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

/-- An exact set-system version of a single instance of the conjecture.
There are `(2^k)^r` indexed blocks on that many points. Their total cardinality
has order `(2^k)^(2*r-1)`, and every `r` distinctly indexed blocks intersect in
fewer than `r` points. -/
theorem packing_criterion (r : ℕ) (hr : 2 ≤ r) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ)) ↔
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∃ S : Fin ((2 ^ k) ^ r) → Finset (Fin ((2 ^ k) ^ r)),
        (∀ f : Fin r ↪ Fin ((2 ^ k) ^ r), (common S f).card < r) ∧
        (2 ^ k) ^ (2 * r - 1) ≤ C * ∑ a, (S a).card) := by
  classical
  constructor
  · intro h
    obtain ⟨C, hC, h⟩ := (Erdos714Criterion.finite_graph_criterion r hr).mp h
    refine ⟨C, hC, ?_⟩
    filter_upwards [h] with k hk
    obtain ⟨G, inst, hG, hb⟩ := hk
    letI := inst
    refine ⟨fun a => G.neighborFinset a, neighborhood_common_card G hG, ?_⟩
    have hs : ∑ a, (G.neighborFinset a).card = 2 * G.edgeFinset.card := by
      simpa using G.sum_degrees_eq_twice_card_edges
    rw [hs]
    exact hb.trans (Nat.mul_le_mul_left C (by omega))
  · rintro ⟨C, hC, h⟩
    apply (Erdos714Criterion.erdos_integer_criterion r hr).mpr
    refine ⟨2 ^ (2 * r - 1) * C, by positivity, ?_⟩
    obtain ⟨K, hK⟩ := eventually_atTop.mp h
    filter_upwards [eventually_ge_atTop (K + 1)] with k hk
    have hk1 : 1 ≤ k := by omega
    obtain ⟨S, hS, hb⟩ := hK (k - 1) (by omega)
    have hfree := (free_iff_common_card S (by omega : 0 < r)).mpr hS
    have he := card_edgeFinset_le_extremalNumber hfree
    rw [incidence_edges] at he
    simp only [Fintype.card_sum, Fintype.card_fin] at he
    have hmono := Erdos714Reduction.extremalNumber_monotone_of_no_isolated
      (completeBipartiteGraph (Fin r) (Fin r)) (by
        intro v
        let i : Fin r := ⟨0, by omega⟩
        cases v with
        | inl v => exact ⟨Sum.inr i, by simp⟩
        | inr v => exact ⟨Sum.inl i, by simp⟩)
    have heq : 2 ^ k = 2 * 2 ^ (k - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hk1, pow_succ]
      omega
    have hsize : (2 ^ (k - 1)) ^ r + (2 ^ (k - 1)) ^ r ≤ (2 ^ k) ^ r := by
      rw [heq, mul_pow]
      have h2 : 2 ≤ (2 : ℕ) ^ r := by
        simpa only [pow_one] using
          (pow_le_pow_right' (by omega : (1 : ℕ) ≤ 2) (by omega : 1 ≤ r))
      simpa only [two_mul] using Nat.mul_le_mul_right ((2 ^ (k - 1)) ^ r) h2
    have he' := he.trans (hmono hsize)
    calc
      (2 ^ k) ^ (2 * r - 1) =
          2 ^ (2 * r - 1) * (2 ^ (k - 1)) ^ (2 * r - 1) := by rw [heq, mul_pow]
      _ ≤ 2 ^ (2 * r - 1) * (C * ∑ a, (S a).card) :=
        Nat.mul_le_mul_left _ hb
      _ ≤ 2 ^ (2 * r - 1) * (C *
          extremalNumber ((2 ^ k) ^ r) (completeBipartiteGraph (Fin r) (Fin r))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ he')
      _ = _ := by ring

/-- The original asymptotic claim is equivalent to a packing problem with index
`r-1`. No regularity, field structure, or formula for the blocks is assumed. -/
theorem point_packing_criterion (r : ℕ) (hr : 2 ≤ r) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ)) ↔
    (∃ C : ℕ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∃ S : Fin ((2 ^ k) ^ r) → Finset (Fin ((2 ^ k) ^ r)),
        IsPacking S r ∧ (2 ^ k) ^ (2 * r - 1) ≤ C * ∑ a, (S a).card) := by
  rw [packing_criterion r hr]
  simp_rw [isPacking_iff_common_card _ (by omega : 0 < r)]

end Erdos714Packing

#print axioms Erdos714Packing.free_iff_common_card
#print axioms Erdos714Packing.incidence_edges
#print axioms Erdos714Packing.packing_criterion

#print axioms Erdos714Packing.point_packing_criterion
