import FormalConjecturesUtil

/-!
# Globally priced extremizers and integral compression repair

The price is a function of vertex count, not an asserted derivative of the
extremal number. Global maximization of `ex(n,H) - p(n)` gives comparison with
**every** finite ordinary `H`-free graph, including graphs of different orders.
Coercivity is an explicit hypothesis in the general selection theorem.

The power-price specialization proves coercivity from a positive exact power
asymptotic and gives a monotone family of selected orders tending to infinity.
The explicit centered quadratic price also has a global optimizer at every
positive scale and penalty coefficient. These results do not prove rationality,
asymptotic localization of the quadratic optimizers, an asymptotic formula for
their backward prices, or a split-copy characterization of identification.
-/

open SimpleGraph Filter Asymptotics

namespace Erdos713Priced

universe u v w

open scoped Classical

/-- Global comparison with all finite ordinary `H`-free graphs. No restriction
on the order of the competitor, or on the sign or monotonicity of `p`. -/
def IsPricedExtremal {V : Type u} {W : Type v} [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V) (p : ℕ → ℝ) : Prop :=
  H.Free G ∧ ∀ (m : ℕ) (J : SimpleGraph (Fin m)), H.Free J →
    (J.edgeFinset.card : ℝ) - (G.edgeFinset.card : ℝ) ≤
      p m - p (Fintype.card V)

/-- A sequence tending to minus infinity attains its global maximum on `ℕ`. -/
theorem exists_global_max_of_tendsto_atBot {s : ℕ → ℝ}
    (hs : Tendsto s atTop atBot) : ∃ n, ∀ m, s m ≤ s n := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hs.eventually_le_atBot (s 0))
  obtain ⟨n, hn, hmax⟩ := (Finset.range (N + 1)).exists_max_image s
    ⟨0, by simp⟩
  refine ⟨n, fun m => ?_⟩
  by_cases hm : m < N + 1
  · exact hmax m (Finset.mem_range.mpr hm)
  · exact (hN m (by omega)).trans (hmax 0 (by simp))

/-- An exact extremizer at a globally maximizing order is globally priced. -/
theorem isPricedExtremal_of_max_score {W : Type v} (H : SimpleGraph W)
    (p : ℕ → ℝ) {n : ℕ} (G : SimpleGraph (Fin n)) (hG : H.Free G)
    (hex : G.edgeFinset.card = extremalNumber n H)
    (hmax : ∀ m, (extremalNumber m H : ℝ) - p m ≤
      (extremalNumber n H : ℝ) - p n) : IsPricedExtremal H G p := by
  refine ⟨hG, ?_⟩
  intro m J hJ
  have hbound := card_edgeFinset_le_extremalNumber hJ
  simp only [Fintype.card_fin] at hbound ⊢
  have hbound' : (J.edgeFinset.card : ℝ) ≤ (extremalNumber m H : ℝ) := by
    exact_mod_cast hbound
  rw [hex]
  linarith [hmax m]

/-- Genuine existence from coercivity. The hypothesis `H ≠ ⊥` ensures that
there is an `H`-free graph at every order, even at the selected order. -/
theorem exists_priced_extremal_of_coercive {W : Type v} (H : SimpleGraph W)
    (hH : H ≠ ⊥) (p : ℕ → ℝ)
    (hcoercive : Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) - p n)
      atTop atBot) :
    ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
      G.edgeFinset.card = extremalNumber n H ∧ IsPricedExtremal H G p ∧
      ∀ m, (extremalNumber m H : ℝ) - p m ≤
        (extremalNumber n H : ℝ) - p n := by
  obtain ⟨n, hn⟩ := exists_global_max_of_tendsto_atBot hcoercive
  obtain ⟨G, dG, hG⟩ := exists_isExtremal_free (V := Fin n) hH
  obtain ⟨hfree, hex⟩ := isExtremal_free_iff.mp hG
  simp only [Fintype.card_fin] at hex
  refine ⟨n, G, ?_, ?_, hn⟩
  · convert hex
  · exact isPricedExtremal_of_max_score H p G hfree (by convert hex) hn

/-- A concrete superlinear price, with a linear selection parameter. -/
noncomputable def powerPrice (a c ℓ : ℝ) (n : ℕ) : ℝ :=
  2 * c * (n : ℝ) ^ a - ℓ * (n : ℝ)

/-- The exact power asymptotic itself proves coercivity for every real `ℓ`.
Only the explicit power is estimated; no increments of `f` are estimated. -/
theorem powerPrice_coercive {f : ℕ → ℝ} {a c : ℝ} (ha : 1 < a) (hc : 0 < c)
    (hf : f ~[atTop] (fun n : ℕ => c * (n : ℝ) ^ a)) (ℓ : ℝ) :
    Tendsto (fun n : ℕ => f n - powerPrice a c ℓ n) atTop atBot := by
  have herror := hf.isLittleO.of_const_mul_right.bound (show 0 < c / 4 by positivity)
  have hgrow : Tendsto (fun n : ℕ => (n : ℝ) ^ (a - 1)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < a - 1)).comp tendsto_natCast_atTop_atTop
  have hpower : Tendsto (fun n : ℕ => c / 2 * (n : ℝ) ^ a) atTop atTop :=
    ((tendsto_rpow_atTop (by linarith : 0 < a)).comp
      tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity)
  apply tendsto_atBot_mono' atTop (f₂ := fun n : ℕ => -(c / 2 * (n : ℝ) ^ a))
    ?_ (tendsto_neg_atTop_atBot.comp hpower)
  filter_upwards [herror, hgrow.eventually_ge_atTop (|ℓ| / (c / 4)),
    eventually_gt_atTop 0] with n herr hn hnpos
  have hnpos' : (0 : ℝ) < n := by exact_mod_cast hnpos
  simp only [Pi.sub_apply, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) a)] at herr
  have hlin : |ℓ| ≤ c / 4 * (n : ℝ) ^ (a - 1) := by
    have h := (div_le_iff₀ (show 0 < c / 4 by positivity)).mp hn
    nlinarith
  have hlin' := mul_le_mul_of_nonneg_right hlin hnpos'.le
  rw [Real.rpow_sub hnpos', Real.rpow_one, mul_assoc,
    div_mul_cancel₀ _ hnpos'.ne'] at hlin'
  have hℓ := mul_le_mul_of_nonneg_right (le_abs_self ℓ) hnpos'.le
  dsimp [powerPrice]
  linarith [(abs_le.mp herr).2]

/-- For every linear parameter there really is a globally priced, exact
extremizer. No upper restriction on `a` is needed for this theorem. -/
theorem exists_power_priced_extremal {W : Type v} (H : SimpleGraph W)
    (hH : H ≠ ⊥) {a c : ℝ} (ha : 1 < a) (hc : 0 < c)
    (hf : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ a)) (ℓ : ℝ) :
    ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
      G.edgeFinset.card = extremalNumber n H ∧
      IsPricedExtremal H G (powerPrice a c ℓ) ∧
      ∀ m, (extremalNumber m H : ℝ) - powerPrice a c ℓ m ≤
        (extremalNumber n H : ℝ) - powerPrice a c ℓ n :=
  exists_priced_extremal_of_coercive H hH (powerPrice a c ℓ)
    (powerPrice_coercive ha hc hf ℓ)

/-- Orders maximizing a linearly tilted sequence escape every finite set as
the tilt tends to positive infinity. This is an actual selection consequence,
not an assumption about the maximizing orders. -/
theorem maximizing_orders_tendsto_atTop (b : ℕ → ℝ) (n : ℝ → ℕ)
    (hmax : ∀ ℓ m, b m + ℓ * (m : ℝ) ≤ b (n ℓ) + ℓ * (n ℓ : ℝ)) :
    Tendsto n atTop atTop := by
  apply tendsto_atTop.mpr
  intro M
  obtain ⟨k, _, hk⟩ := (Finset.range (M + 1)).exists_max_image b ⟨0, by simp⟩
  filter_upwards [eventually_ge_atTop (|b k - b M| + 1)] with ℓ hℓ
  by_contra! hn
  have hnk : b (n ℓ) ≤ b k := hk (n ℓ) (Finset.mem_range.mpr (by omega))
  have hnM : (n ℓ : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hn
  have hℓpos : 0 ≤ ℓ := by linarith [abs_nonneg (b k - b M)]
  have hmul := mul_le_mul_of_nonneg_left hnM hℓpos
  linarith [hmax ℓ M, le_abs_self (b k - b M)]

/-- The selected orders are monotone in the linear tilt, regardless of how
ties between maximizers are broken. -/
theorem maximizing_orders_monotone (b : ℕ → ℝ) (n : ℝ → ℕ)
    (hmax : ∀ ℓ m, b m + ℓ * (m : ℝ) ≤ b (n ℓ) + ℓ * (n ℓ : ℝ)) :
    Monotone n := by
  intro ℓ₁ ℓ₂ hℓ
  rcases hℓ.eq_or_lt with h | h
  · simp only [h, le_refl]
  · by_contra! hn
    have hn' : (n ℓ₂ : ℝ) < (n ℓ₁ : ℝ) := by exact_mod_cast hn
    have hprod := mul_pos (sub_pos.mpr h) (sub_pos.mpr hn')
    nlinarith [hmax ℓ₁ (n ℓ₂), hmax ℓ₂ (n ℓ₁)]

/-- An unbounded monotone family of genuine globally priced exact extremizers.
Thus the power-price existence theorem is not merely an existence statement
at a possibly fixed small order. -/
theorem exists_power_priced_family {W : Type v} (H : SimpleGraph W)
    (hH : H ≠ ⊥) {a c : ℝ} (ha : 1 < a) (hc : 0 < c)
    (hf : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ a)) :
    ∃ (n : ℝ → ℕ) (G : ∀ ℓ : ℝ, SimpleGraph (Fin (n ℓ))),
      (∀ ℓ, (G ℓ).edgeFinset.card = extremalNumber (n ℓ) H ∧
        IsPricedExtremal H (G ℓ) (powerPrice a c ℓ)) ∧
      Monotone n ∧ Tendsto n atTop atTop := by
  have hex := fun ℓ : ℝ => exists_power_priced_extremal H hH ha hc hf ℓ
  choose n G hcard hpriced hmax using hex
  let b : ℕ → ℝ := fun m => (extremalNumber m H : ℝ) - 2 * c * (m : ℝ) ^ a
  have hb : ∀ ℓ m, b m + ℓ * (m : ℝ) ≤ b (n ℓ) + ℓ * (n ℓ : ℝ) := by
    intro ℓ m
    have h := hmax ℓ m
    dsimp [powerPrice] at h
    dsimp [b]
    linarith
  exact ⟨n, G, fun ℓ => ⟨hcard ℓ, hpriced ℓ⟩,
    maximizing_orders_monotone b n hb, maximizing_orders_tendsto_atTop b n hb⟩

/-- The exact backward price for this explicit price function. -/
lemma powerPrice_backward (a c ℓ : ℝ) {n : ℕ} (hn : 0 < n) :
    powerPrice a c ℓ n - powerPrice a c ℓ (n - 1) =
      2 * c * ((n : ℝ) ^ a - ((n - 1 : ℕ) : ℝ) ^ a) - ℓ := by
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  simp only [powerPrice, hcast]
  ring

/-- A fixed positive quadratic penalty dominates the asymptotic error of a
subquadratic power law. The center `R` may be any real number. -/
theorem quadratic_penalty_coercive {f : ℕ → ℝ} {a c b : ℝ} (ha : a < 2)
    (hb : 0 < b) (hf : f ~[atTop] (fun n : ℕ => c * (n : ℝ) ^ a)) (R : ℝ) :
    Tendsto (fun n : ℕ => f n - (c * (n : ℝ) ^ a + b * ((n : ℝ) - R) ^ 2))
      atTop atBot := by
  have herror := hf.isLittleO.of_const_mul_right.bound (show (0 : ℝ) < 1 by norm_num)
  have hgrow : Tendsto (fun n : ℕ => (n : ℝ) ^ (2 - a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr ha)).comp tendsto_natCast_atTop_atTop
  have hpower : Tendsto (fun n : ℕ => b / 8 * (n : ℝ) ^ (2 : ℝ)) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp
      tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity)
  have hnegative : Tendsto (fun n : ℕ => -(b / 8 * (n : ℝ) ^ 2)) atTop atBot := by
    simpa only [Real.rpow_two] using tendsto_neg_atTop_atBot.comp hpower
  apply tendsto_atBot_mono' atTop (f₂ := fun n : ℕ => -(b / 8 * (n : ℝ) ^ 2))
    ?_ hnegative
  filter_upwards [herror, hgrow.eventually_ge_atTop (1 / (b / 8)),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * |R|),
    eventually_gt_atTop 0] with n herr hn hnR hnpos
  have hnpos' : (0 : ℝ) < n := by exact_mod_cast hnpos
  simp only [Pi.sub_apply, Real.norm_eq_abs, one_mul,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) a)] at herr
  have hsmall : 1 ≤ b / 8 * (n : ℝ) ^ (2 - a) := by
    have h := (div_le_iff₀ (show 0 < b / 8 by positivity)).mp hn
    nlinarith
  have hsmall' := mul_le_mul_of_nonneg_right hsmall
    (Real.rpow_nonneg (Nat.cast_nonneg n) a)
  rw [one_mul, Real.rpow_sub hnpos', Real.rpow_two, mul_assoc,
    div_mul_cancel₀ _ (Real.rpow_pos_of_pos hnpos' a).ne'] at hsmall'
  have hdist : (n : ℝ) / 2 ≤ (n : ℝ) - R := by linarith [le_abs_self R]
  have hsq := mul_le_mul hdist hdist (by positivity : 0 ≤ (n : ℝ) / 2)
    (by linarith : 0 ≤ (n : ℝ) - R)
  have hsq' := mul_le_mul_of_nonneg_left hsq hb.le
  nlinarith [(abs_le.mp herr).2]

/-- The explicit centered price. Its coefficient may be chosen separately at
every positive scale; no rate of decay is imposed or asserted here. -/
noncomputable def quadraticPrice (a c κ : ℝ) (N n : ℕ) : ℝ :=
  c * (n : ℝ) ^ a + c * κ * (N : ℝ) ^ (a - 2) * ((n : ℝ) - (N : ℝ)) ^ 2

/-- At every positive scale and every positive penalty coefficient, the
explicit quadratic price has a genuine global maximizer and exact free graph.
This proves existence, not asymptotic localization of the chosen order. -/
theorem exists_quadratic_priced_extremal {W : Type v} (H : SimpleGraph W)
    (hH : H ≠ ⊥) {a c κ : ℝ} (ha : a < 2) (hc : 0 < c) (hκ : 0 < κ)
    (hf : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ a)) (N : ℕ) (hN : 0 < N) :
    ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
      G.edgeFinset.card = extremalNumber n H ∧
      IsPricedExtremal H G (quadraticPrice a c κ N) ∧
      ∀ m, (extremalNumber m H : ℝ) - quadraticPrice a c κ N m ≤
        (extremalNumber n H : ℝ) - quadraticPrice a c κ N n := by
  apply exists_priced_extremal_of_coercive H hH
  apply quadratic_penalty_coercive ha _ hf (N : ℝ)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  exact mul_pos (mul_pos hc hκ) (Real.rpow_pos_of_pos hN' _)

/-- The exact finite displacement inequality from quadratic-price optimality.
The right side consists of errors in function values, not discrete derivatives. -/
theorem quadratic_displacement_bound (f : ℕ → ℝ) (a c κ : ℝ) (N n : ℕ)
    (hmax : ∀ m, f m - quadraticPrice a c κ N m ≤ f n - quadraticPrice a c κ N n) :
    c * κ * (N : ℝ) ^ (a - 2) * ((n : ℝ) - (N : ℝ)) ^ 2 ≤
      (f n - c * (n : ℝ) ^ a) - (f N - c * (N : ℝ) ^ a) := by
  have h := hmax N
  simp only [quadraticPrice, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, add_zero] at h
  linarith

/-- Exact backward difference of the explicit centered quadratic price.
This is an identity for `p`, not a differentiation of the extremal number. -/
lemma quadraticPrice_backward (a c κ : ℝ) (N : ℕ) {n : ℕ} (hn : 0 < n) :
    quadraticPrice a c κ N n - quadraticPrice a c κ N (n - 1) =
      c * ((n : ℝ) ^ a - ((n - 1 : ℕ) : ℝ) ^ a) +
        c * κ * (N : ℝ) ^ (a - 2) * (2 * ((n : ℝ) - (N : ℝ)) - 1) := by
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  simp only [quadraticPrice, hcast]
  ring

section Consequences

variable {V : Type u} {W : Type v} [Fintype V]
variable {H : SimpleGraph W} {G : SimpleGraph V} {p : ℕ → ℝ}

/-- Transfer of global comparison to an arbitrary finite vertex type. -/
theorem IsPricedExtremal.compare (hG : IsPricedExtremal H G p)
    {U : Type w} [Fintype U] (J : SimpleGraph U) (hJ : H.Free J) :
    (J.edgeFinset.card : ℝ) - (G.edgeFinset.card : ℝ) ≤
      p (Fintype.card U) - p (Fintype.card V) := by
  let e := Fintype.equivFin U
  let K := J.map e.toEmbedding
  have hK : H.Free K := (free_congr Iso.refl (Iso.map e J)).mp hJ
  have h := hG.2 (Fintype.card U) K hK
  have he := (Iso.map e J).card_edgeFinset_eq
  have he' : J.edgeFinset.card = K.edgeFinset.card := by convert he
  have h' : (K.edgeFinset.card : ℝ) - (G.edgeFinset.card : ℝ) ≤
      p (Fintype.card U) - p (Fintype.card V) := by convert h
  rwa [← he'] at h'

/-- Every globally priced graph is an exact extremizer at its own order. -/
theorem IsPricedExtremal.exact (hG : IsPricedExtremal H G p) :
    G.edgeFinset.card = extremalNumber (Fintype.card V) H := by
  apply le_antisymm (card_edgeFinset_le_extremalNumber hG.1)
  rw [extremalNumber_le_iff]
  intro J _ hJ
  have h : (J.edgeFinset.card : ℝ) - (G.edgeFinset.card : ℝ) ≤
      p (Fintype.card V) - p (Fintype.card V) := by convert hG.compare J hJ
  have h' : (J.edgeFinset.card : ℝ) ≤ (G.edgeFinset.card : ℝ) := by linarith
  exact_mod_cast h'

/-- Deleting a vertex of the actual global optimizer gives the backward price
bound. There is no peeling or replacement of `G` by a trimmed core. -/
theorem IsPricedExtremal.backward_price_le_degree (hG : IsPricedExtremal H G p)
    (x : V) : p (Fintype.card V) - p (Fintype.card V - 1) ≤ (G.degree x : ℝ) := by
  let S : Set V := {x}ᶜ
  have hfree : H.Free (G.induce S) :=
    fun h => hG.1 (h.trans ⟨Copy.induce G S⟩)
  have h := hG.compare (G.induce S) hfree
  have hsize : Fintype.card S = Fintype.card V - 1 := by
    change Fintype.card ({x}ᶜ : Set V) = Fintype.card V - 1
    rw [Fintype.card_compl_set]
    simp only [Fintype.card_unique]
  have hedge : (G.induce S).edgeFinset.card + G.degree x = G.edgeFinset.card := by
    change (G.induce ({x}ᶜ : Set V)).edgeFinset.card + G.degree x = G.edgeFinset.card
    rw [G.card_edgeFinset_induce_compl_singleton, G.card_edgeFinset_deleteIncidenceSet]
    exact Nat.sub_add_cancel (G.degree_le_card_edgeFinset x)
  have hedge' : ((G.induce S).edgeFinset.card : ℝ) + (G.degree x : ℝ) =
      (G.edgeFinset.card : ℝ) := by exact_mod_cast hedge
  rw [hsize] at h
  linarith

/-- General edge-accounting interface for repair. The native loss `L` is a real
number; the number `d` of deleted old edges is integral. -/
theorem IsPricedExtremal.repair_bound (hG : IsPricedExtremal H G p)
    {U : Type w} [Fintype U] (J : SimpleGraph U) (hJ : H.Free J)
    (L : ℝ) (d : ℕ)
    (hcount : (G.edgeFinset.card : ℝ) - L - (d : ℝ) ≤ (J.edgeFinset.card : ℝ)) :
    p (Fintype.card V) - p (Fintype.card U) ≤ L + (d : ℝ) := by
  have h := hG.compare J hJ
  linarith

end Consequences

section Compression

variable {V : Type u} {U : Type w}

/-- The simple edge image under an arbitrary vertex map. Loops are discarded
and parallel images become a single edge. Injectivity is not assumed. -/
def compression (G : SimpleGraph V) (π : V → U) : SimpleGraph U :=
  fromEdgeSet (Sym2.map π '' G.edgeSet)

/-- Adjacency in the simple edge image, in terms of actual old endpoints. -/
lemma compression_adj (G : SimpleGraph V) (π : V → U) {x y : U} :
    (compression G π).Adj x y ↔
      x ≠ y ∧ ∃ a b, G.Adj a b ∧ π a = x ∧ π b = y := by
  simp only [compression, fromEdgeSet_adj, Set.mem_image, Sym2.exists,
    mem_edgeSet, Sym2.map_pair_eq, Sym2.eq, Sym2.rel_iff]
  constructor
  · rintro ⟨⟨a, b, hab, h | h⟩, hne⟩
    · exact ⟨hne, a, b, hab, h⟩
    · exact ⟨hne, b, a, hab.symm, h.2, h.1⟩
  · rintro ⟨hne, a, b, hab, h⟩
    exact ⟨⟨a, b, hab, Or.inl h⟩, hne⟩

variable [Fintype V] [Fintype U]

/-- Exact finite edge set of the compression. -/
lemma edgeFinset_compression (G : SimpleGraph V) (π : V → U) :
    (compression G π).edgeFinset =
      (G.edgeFinset.image (Sym2.map π)).filter (fun e => ¬e.IsDiag) := by
  ext e
  simp only [compression, mem_edgeFinset, edgeSet_fromEdgeSet, Set.mem_diff,
    Set.mem_image, Finset.mem_filter, Finset.mem_image, Sym2.mem_diagSet_iff_isDiag]

/-- Compression never increases the number of simple edges. -/
lemma card_compression_le (G : SimpleGraph V) (π : V → U) :
    (compression G π).edgeFinset.card ≤ G.edgeFinset.card := by
  rw [edgeFinset_compression]
  exact (Finset.card_filter_le _ _).trans Finset.card_image_le

/-- Every lost quotient edge is the image of a deleted old edge. In particular,
this does not mistakenly count every old edge as a different quotient edge. -/
lemma compression_lost_subset (G : SimpleGraph V) (π : V → U)
    (D : Finset (Sym2 V)) :
    (compression G π).edgeFinset \
      (compression (G.deleteEdges (D : Set (Sym2 V))) π).edgeFinset ⊆
        D.image (Sym2.map π) := by
  intro e he
  obtain ⟨heG, heJ⟩ := Finset.mem_sdiff.mp he
  rw [edgeFinset_compression, Finset.mem_filter] at heG
  obtain ⟨⟨d, hd, hde⟩, hdiag⟩ := (Finset.mem_image.mp heG.1), heG.2
  refine Finset.mem_image.mpr ⟨d, ?_, hde⟩
  by_contra hnot
  apply heJ
  rw [edgeFinset_compression, Finset.mem_filter]
  refine ⟨Finset.mem_image.mpr ⟨d, ?_, hde⟩, hdiag⟩
  rw [edgeFinset_deleteEdges]
  exact Finset.mem_sdiff.mpr ⟨hd, hnot⟩

/-- Deleting `|D|` old edges loses at most `|D|` quotient edges. No freeness
hypothesis is needed for this purely finite counting statement. -/
theorem compression_lost_card_le (G : SimpleGraph V) (π : V → U)
    (D : Finset (Sym2 V)) :
    ((compression G π).edgeFinset \
      (compression (G.deleteEdges (D : Set (Sym2 V))) π).edgeFinset).card ≤ D.card :=
  (Finset.card_le_card (compression_lost_subset G π D)).trans Finset.card_image_le

/-- The native loss, before any repair. This natural subtraction is exact
because compression does not increase the edge count. -/
noncomputable def nativeLoss (G : SimpleGraph V) (π : V → U) : ℕ :=
  G.edgeFinset.card - (compression G π).edgeFinset.card

lemma nativeLoss_add_card (G : SimpleGraph V) (π : V → U) :
    nativeLoss G π + (compression G π).edgeFinset.card = G.edgeFinset.card :=
  Nat.sub_add_cancel (card_compression_le G π)

/-- Complete integral edge transfer for an actual compression and old-edge
deletion. The theorem even allows `D` to contain irrelevant nonedges. -/
theorem compression_repair_edge_transfer (G : SimpleGraph V) (π : V → U)
    (D : Finset (Sym2 V)) :
    G.edgeFinset.card ≤ nativeLoss G π + D.card +
      (compression (G.deleteEdges (D : Set (Sym2 V))) π).edgeFinset.card := by
  have h := compression_lost_card_le G π D
  have hcard := Finset.card_le_card_sdiff_add_card
    (s := (compression G π).edgeFinset)
    (t := (compression (G.deleteEdges (D : Set (Sym2 V))) π).edgeFinset)
  have hnative := nativeLoss_add_card G π
  omega

variable {W : Type v} {H : SimpleGraph W} {G : SimpleGraph V} {p : ℕ → ℝ}

/-- Global variational comparison forces every successful compression repair
to pay the full price drop, with native loss accounted for separately. -/
theorem IsPricedExtremal.compression_repair_bound (hG : IsPricedExtremal H G p)
    (π : V → U) (D : Finset (Sym2 V))
    (hfree : H.Free (compression (G.deleteEdges (D : Set (Sym2 V))) π)) :
    p (Fintype.card V) - p (Fintype.card U) ≤
      (nativeLoss G π : ℝ) + (D.card : ℝ) := by
  apply hG.repair_bound _ hfree (nativeLoss G π) D.card
  have h := compression_repair_edge_transfer G π D
  have h' : (G.edgeFinset.card : ℝ) ≤ (nativeLoss G π : ℝ) + (D.card : ℝ) +
      ((compression (G.deleteEdges (D : Set (Sym2 V))) π).edgeFinset.card : ℝ) := by
    exact_mod_cast h
  linarith

/-- Integer rounding is legitimate: the repair plus native loss is an integer,
so it is at least the natural ceiling of the (possibly negative) price drop. -/
theorem IsPricedExtremal.compression_repair_integral (hG : IsPricedExtremal H G p)
    (π : V → U) (D : Finset (Sym2 V))
    (hfree : H.Free (compression (G.deleteEdges (D : Set (Sym2 V))) π)) :
    ⌈p (Fintype.card V) - p (Fintype.card U)⌉₊ ≤ nativeLoss G π + D.card := by
  apply Nat.ceil_le.mpr
  simpa only [Nat.cast_add] using hG.compression_repair_bound π D hfree

end Compression

section TwoVertices

variable {V : Type u}

/-- Identify `drop` with `keep`, temporarily retaining an isolated `drop` in
the ambient vertex type. The actual smaller target is defined below. -/
noncomputable def mergeVertex (keep drop x : V) : V :=
  if x = drop then keep else x

lemma mergeVertex_ne_drop (keep drop : V) (hne : keep ≠ drop) (x : V) :
    mergeVertex keep drop x ≠ drop := by
  by_cases hx : x = drop <;> simp [mergeVertex, hx, hne]

/-- Away from `keep`, merging only removes edges incident to `drop`. -/
lemma compression_merge_delete (G : SimpleGraph V) (keep drop : V) :
    (compression G (mergeVertex keep drop)).deleteIncidenceSet keep =
      (G.deleteIncidenceSet drop).deleteIncidenceSet keep := by
  ext x y
  simp only [deleteIncidenceSet_adj, compression_adj]
  constructor
  · rintro ⟨⟨_, a, b, hab, hax, hby⟩, hx, hy⟩
    have ha : a ≠ drop := by
      intro h; subst a
      simp only [mergeVertex] at hax
      exact hx hax.symm
    have hb : b ≠ drop := by
      intro h; subst b
      simp only [mergeVertex] at hby
      exact hy hby.symm
    have hax' : a = x := by simpa [mergeVertex, ha] using hax
    have hby' : b = y := by simpa [mergeVertex, hb] using hby
    subst a; subst b
    exact ⟨⟨hab, ha, hb⟩, hx, hy⟩
  · rintro ⟨⟨hxy, hx, hy⟩, hxk, hyk⟩
    exact ⟨⟨hxy.ne, x, y, hxy, by simp [mergeVertex, hx],
      by simp [mergeVertex, hy]⟩, hxk, hyk⟩

variable [Fintype V]

lemma neighborFinset_merge (G : SimpleGraph V) (keep drop : V) (hne : keep ≠ drop) :
    (compression G (mergeVertex keep drop)).neighborFinset keep =
      (G.neighborFinset keep).erase drop ∪ (G.neighborFinset drop).erase keep := by
  ext x
  simp only [mem_neighborFinset, compression_adj, Finset.mem_union, Finset.mem_erase]
  constructor
  · rintro ⟨hx, a, b, hab, ha, hb⟩
    have hbd : b ≠ drop := by
      intro h; subst b
      simp only [mergeVertex] at hb
      exact hx hb
    have hbx : b = x := by simpa [mergeVertex, hbd] using hb
    subst b
    by_cases had : a = drop
    · subst a
      exact Or.inr ⟨hx.symm, hab⟩
    · have hak : a = keep := by simpa [mergeVertex, had] using ha
      subst a
      exact Or.inl ⟨hbd, hab⟩
  · rintro (⟨hx, hG⟩ | ⟨hx, hG⟩)
    · exact ⟨hG.ne, keep, x, hG, by simp [mergeVertex, hne],
        by simp [mergeVertex, hx]⟩
    · exact ⟨hx.symm, drop, x, hG, by simp [mergeVertex],
        by simp [mergeVertex, hG.ne.symm]⟩

/-- Codegree is the number of common neighbors, with no asymptotic convention. -/
noncomputable def codegree (G : SimpleGraph V) (x y : V) : ℕ :=
  (G.neighborFinset x ∩ G.neighborFinset y).card

lemma codegree_eq_card_commonNeighbors (G : SimpleGraph V) (x y : V) :
    codegree G x y = Fintype.card (G.commonNeighbors x y) := by
  rw [← Set.toFinset_card]
  simp only [codegree, commonNeighbors, Set.toFinset_inter, neighborFinset]

/-- Exact two-vertex loss in the ambient type: one edge for adjacency of the
identified vertices, plus one for each common neighbor. -/
theorem card_merge_add_loss (G : SimpleGraph V) (keep drop : V) (hne : keep ≠ drop) :
    (compression G (mergeVertex keep drop)).edgeFinset.card +
      (if G.Adj keep drop then 1 else 0) + codegree G keep drop = G.edgeFinset.card := by
  let Q := compression G (mergeVertex keep drop)
  let K := G.deleteIncidenceSet drop
  let A := (G.neighborFinset keep).erase drop
  let B := (G.neighborFinset drop).erase keep
  have hA : K.neighborFinset keep = A := by
    ext x
    simp only [K, A, mem_neighborFinset, deleteIncidenceSet_adj, Finset.mem_erase]
    tauto
  have hQ : Q.neighborFinset keep = A ∪ B := neighborFinset_merge G keep drop hne
  have hI : A ∩ B = G.neighborFinset keep ∩ G.neighborFinset drop := by
    ext x
    simp only [A, B, Finset.mem_inter, Finset.mem_erase, mem_neighborFinset]
    constructor
    · tauto
    · rintro ⟨hk, hd⟩
      exact ⟨⟨hd.ne.symm, hk⟩, hk.ne.symm, hd⟩
  have hdeg : Q.degree keep + codegree G keep drop = K.degree keep + B.card := by
    simpa only [degree, hA, hQ, codegree, hI] using Finset.card_union_add_card_inter A B
  have hB : B.card + (if G.Adj keep drop then 1 else 0) = G.degree drop := by
    dsimp [B]
    by_cases h : G.Adj keep drop
    · rw [if_pos h]
      exact Finset.card_erase_add_one (by simpa using h.symm)
    · rw [if_neg h, add_zero, Finset.erase_eq_of_notMem (by simpa [adj_comm] using h)]
      rfl
  have hdel : Q.deleteIncidenceSet keep = K.deleteIncidenceSet keep :=
    compression_merge_delete G keep drop
  have hQcount : (Q.deleteIncidenceSet keep).edgeFinset.card + Q.degree keep =
      Q.edgeFinset.card := by
    rw [card_edgeFinset_deleteIncidenceSet]
    exact Nat.sub_add_cancel (Q.degree_le_card_edgeFinset keep)
  have hKcount : (K.deleteIncidenceSet keep).edgeFinset.card + K.degree keep =
      K.edgeFinset.card := by
    rw [card_edgeFinset_deleteIncidenceSet]
    exact Nat.sub_add_cancel (K.degree_le_card_edgeFinset keep)
  have hGcount : K.edgeFinset.card + G.degree drop = G.edgeFinset.card := by
    change (G.deleteIncidenceSet drop).edgeFinset.card + G.degree drop = G.edgeFinset.card
    rw [card_edgeFinset_deleteIncidenceSet]
    exact Nat.sub_add_cancel (G.degree_le_card_edgeFinset drop)
  have hdelcard : (Q.deleteIncidenceSet keep).edgeFinset.card =
      (K.deleteIncidenceSet keep).edgeFinset.card := by
    convert congrArg (fun F : SimpleGraph V => F.edgeFinset.card) hdel
  rw [hdelcard] at hQcount
  change Q.edgeFinset.card + _ + _ = _
  omega

/-- The actual two-vertex identification has one fewer vertex. -/
noncomputable def mergeMap (keep drop : V) (hne : keep ≠ drop) : V → ({drop}ᶜ : Set V) :=
  fun x => ⟨mergeVertex keep drop x, by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      mergeVertex_ne_drop keep drop hne x⟩

omit [Fintype V] in
/-- The smaller quotient is the ambient edge image with its isolated vertex removed. -/
lemma compression_mergeMap (G : SimpleGraph V) (keep drop : V) (hne : keep ≠ drop) :
    compression G (mergeMap keep drop hne) =
      (compression G (mergeVertex keep drop)).induce ({drop}ᶜ : Set V) := by
  ext x y
  simp only [induce_adj, compression_adj, ne_eq, Subtype.ext_iff, mergeMap]

lemma card_compression_mergeMap (G : SimpleGraph V) (keep drop : V) (hne : keep ≠ drop) :
    (compression G (mergeMap keep drop hne)).edgeFinset.card =
      (compression G (mergeVertex keep drop)).edgeFinset.card := by
  let Q := compression G (mergeVertex keep drop)
  have hz : Q.neighborFinset drop = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hadj : Q.Adj drop x := by simpa only [mem_neighborFinset] using hx
    obtain ⟨_, a, b, _, ha, _⟩ := (compression_adj G _).mp hadj
    exact mergeVertex_ne_drop keep drop hne a ha
  have hd : Q.degree drop = 0 := by simp only [degree, hz, Finset.card_empty]
  have hc : (Q.induce ({drop}ᶜ : Set V)).edgeFinset.card = Q.edgeFinset.card := by
    rw [card_edgeFinset_induce_compl_singleton, card_edgeFinset_deleteIncidenceSet, hd,
      Nat.sub_zero]
  have he := compression_mergeMap G keep drop hne
  have hecard : (compression G (mergeMap keep drop hne)).edgeFinset.card =
      (Q.induce ({drop}ᶜ : Set V)).edgeFinset.card := by
    convert congrArg (fun F : SimpleGraph ({drop}ᶜ : Set V) => F.edgeFinset.card) he
  exact hecard.trans hc

/-- Native loss for the genuine one-vertex-smaller identification. -/
theorem nativeLoss_mergeMap (G : SimpleGraph V) (keep drop : V) (hne : keep ≠ drop) :
    nativeLoss G (mergeMap keep drop hne) =
      (if G.Adj keep drop then 1 else 0) + codegree G keep drop := by
  have hcount := card_merge_add_loss G keep drop hne
  have hmap := card_compression_mergeMap G keep drop hne
  dsimp [nativeLoss]
  omega

/-- Exact global-price repair bound for two-vertex identification. All deleted
edges belong to the old graph's vertex type; no quotient-edge repair surrogate
is substituted. -/
theorem IsPricedExtremal.merge_repair_bound {W : Type v} {H : SimpleGraph W}
    {G : SimpleGraph V} {p : ℕ → ℝ} (hG : IsPricedExtremal H G p)
    (keep drop : V) (hne : keep ≠ drop) (D : Finset (Sym2 V))
    (hfree : H.Free (compression (G.deleteEdges (D : Set (Sym2 V)))
      (mergeMap keep drop hne))) :
    p (Fintype.card V) - p (Fintype.card V - 1) ≤
      (D.card : ℝ) + (if G.Adj keep drop then 1 else 0) + (codegree G keep drop : ℝ) := by
  have h := hG.compression_repair_bound (mergeMap keep drop hne) D hfree
  have hsize : Fintype.card ({drop}ᶜ : Set V) = Fintype.card V - 1 := by
    rw [Fintype.card_compl_set]
    simp only [Fintype.card_unique]
  rw [hsize, nativeLoss_mergeMap] at h
  simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at h
  linarith

/-- Integral version of the two-vertex repair inequality. -/
theorem IsPricedExtremal.merge_repair_integral {W : Type v} {H : SimpleGraph W}
    {G : SimpleGraph V} {p : ℕ → ℝ} (hG : IsPricedExtremal H G p)
    (keep drop : V) (hne : keep ≠ drop) (D : Finset (Sym2 V))
    (hfree : H.Free (compression (G.deleteEdges (D : Set (Sym2 V)))
      (mergeMap keep drop hne))) :
    ⌈p (Fintype.card V) - p (Fintype.card V - 1)⌉₊ ≤
      D.card + (if G.Adj keep drop then 1 else 0) + codegree G keep drop := by
  apply Nat.ceil_le.mpr
  simpa only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using
    hG.merge_repair_bound keep drop hne D hfree

end TwoVertices

end Erdos713Priced
