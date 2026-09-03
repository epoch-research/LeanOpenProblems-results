import Submission.IncidenceBridge

/-!
# The `r = 2` case of the complete bipartite extremal lower bound

Affine lines over a finite field give a `K_{2,2}`-free incidence graph with
`2 q²` vertices and `q³` edges. Bertrand's postulate and padding by isolated
vertices extend this to all sufficiently large vertex counts.

This file proves only the `r = 2` case of Erdős problem 714. It neither
imports `Submission.Spec` nor asserts the general conjecture.
-/

namespace Erdos714.CaseTwo

open Filter SimpleGraph IncidenceBridge

section AffineLines

variable {F : Type*} [CommRing F] [IsDomain F]

/-- The affine function with slope `x.1` and intercept `x.2`. -/
def affine (x : F × F) (t : F) : F := x.1 * t + x.2

/-- Two affine functions agreeing at two distinct coordinates have the same
slope and intercept. This works over any integral domain. -/
theorem affine_eq_of_agree_two {x y : F × F} {t u : F} (htu : t ≠ u)
    (ht : affine x t = affine y t) (hu : affine x u = affine y u) : x = y := by
  dsimp [affine] at ht hu
  have hmul : (x.1 - y.1) * (t - u) = 0 := by
    linear_combination ht - hu
  have ha : x.1 = y.1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr htu))
  apply Prod.ext ha
  rw [ha] at ht
  exact add_left_cancel ht

/-- No `r` distinct affine functions can agree at `r` distinct coordinates
when `r ≥ 2`. -/
theorem affine_noAgreementRectangle {r : ℕ} (hr : 2 ≤ r) :
    ¬ HasAgreementRectangle (affine (F := F)) r := by
  rintro ⟨x, t, hx, ht, h⟩
  let i : Fin r := ⟨0, by omega⟩
  let j : Fin r := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro heq
    have := congrArg Fin.val heq
    dsimp [i, j] at this
    omega
  exact hij (hx (affine_eq_of_agree_two (ht.ne hij) (h i j i) (h i j j)))

/-- The affine incidence graph is `K_{r,r}`-free for every `r ≥ 2`, in
particular it is `K_{2,2}`-free. -/
theorem affineGraph_free {r : ℕ} (hr : 2 ≤ r) :
    (completeBipartiteGraph (Fin r) (Fin r)).Free (incidenceGraph (affine (F := F))) :=
  (free_iff_noAgreementRectangle _ (by omega)).2 (affine_noAgreementRectangle hr)

variable [Fintype F]

omit [CommRing F] [IsDomain F] in
/-- The two parts of the affine incidence graph each have `q²` vertices. -/
theorem affineGraph_card_vertices :
    Fintype.card ((F × F) ⊕ (F × F)) = 2 * Fintype.card F ^ 2 := by
  simp only [Fintype.card_sum, Fintype.card_prod]
  ring

omit [IsDomain F] in
/-- The affine incidence graph has exactly `q³` edges. -/
theorem affineGraph_card_edgeFinset
    [Fintype (incidenceGraph (affine (F := F))).edgeSet] :
    (incidenceGraph (affine (F := F))).edgeFinset.card = Fintype.card F ^ 3 := by
  rw [incidenceGraph_card_edgeFinset, Fintype.card_prod]
  ring

/-- The affine construction at its exact vertex count. -/
theorem affine_le_extremalNumber {r : ℕ} (hr : 2 ≤ r) :
    Fintype.card F ^ 3 ≤ extremalNumber (2 * Fintype.card F ^ 2)
      (completeBipartiteGraph (Fin r) (Fin r)) := by
  have h := le_extremalNumber_of_noAgreementRectangle (affine (F := F))
    (by omega : 0 < r) (affine_noAgreementRectangle hr)
  simpa only [Fintype.card_prod, show ∀ q : ℕ, q * q * q = q ^ 3 by intro q; ring,
    show ∀ q : ℕ, q * q + q * q = 2 * q ^ 2 by intro q; ring] using h

/-- In particular, every prime supplies the required finite field. -/
theorem prime_cube_le_extremalNumber {p : ℕ} (hp : p.Prime) :
    p ^ 3 ≤ extremalNumber (2 * p ^ 2)
      (completeBipartiteGraph (Fin 2) (Fin 2)) := by
  letI : Fact p.Prime := ⟨hp⟩
  simpa only [ZMod.card] using (affine_le_extremalNumber (F := ZMod p) (r := 2) le_rfl)

end AffineLines

section Padding

variable {U V W : Type*}

/-- Adding isolated vertices preserves freeness when the forbidden graph
has no isolated vertices. No finiteness assumption is needed. -/
theorem free_map_of_no_isolated (H : SimpleGraph U)
    (hH : ∀ u, ∃ v, H.Adj u v) {G : SimpleGraph V} (hG : H.Free G) (f : V ↪ W) :
    H.Free (G.map f) := by
  classical
  rintro ⟨φ⟩
  have hpre : ∀ u, ∃ v, f v = φ.toHom u := by
    intro u
    obtain ⟨u', hu⟩ := hH u
    obtain ⟨v, w, hvw, hv, hw⟩ := φ.toHom.map_adj hu
    exact ⟨v, hv⟩
  choose g hg using hpre
  apply hG
  refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
  · intro u v huv
    have h := φ.toHom.map_adj huv
    rw [← hg u, ← hg v] at h
    exact map_adj_apply.mp h
  · intro u v huv
    change g u = g v at huv
    apply φ.injective
    rw [← hg u, ← hg v, huv]

/-- Extremal numbers are monotone in the number of vertices whenever the
forbidden graph has no isolated vertices. -/
theorem extremalNumber_mono_of_no_isolated (H : SimpleGraph U)
    (hH : ∀ u, ∃ v, H.Adj u v) : Monotone (fun n => extremalNumber n H) := by
  classical
  intro m n hmn
  rw [← Fintype.card_fin m, extremalNumber_le_iff]
  intro G _ hG
  have h := card_edgeFinset_le_extremalNumber
    (free_map_of_no_isolated H hH hG (Fin.castLEEmb hmn))
  calc
    G.edgeFinset.card = (G.map (Fin.castLEEmb hmn)).edgeFinset.card := by
      convert (card_edgeFinset_map (Fin.castLEEmb hmn) G).symm
    _ ≤ extremalNumber n H := by simpa only [Fintype.card_fin] using h

/-- In particular, nonempty complete bipartite forbidden graphs allow
padding by isolated vertices. -/
theorem extremalNumber_completeBipartite_mono {s t : ℕ} (hs : 0 < s) (ht : 0 < t) :
    Monotone (fun n => extremalNumber n (completeBipartiteGraph (Fin s) (Fin t))) := by
  apply extremalNumber_mono_of_no_isolated
  intro v
  cases v with
  | inl i => exact ⟨Sum.inr ⟨0, ht⟩, by simp⟩
  | inr j => exact ⟨Sum.inl ⟨0, hs⟩, by simp⟩

end Padding

/-- A prime of the right scale for an affine incidence graph on at most `n`
vertices. The factor-eight upper estimate is deliberately not optimized. -/
theorem exists_prime_for_padding {n : ℕ} (hn : 8 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ 2 * p ^ 2 ≤ n ∧ n < 8 * p ^ 2 := by
  let k := Nat.sqrt (n / 8)
  have hk : k ≠ 0 := by
    apply ne_of_gt
    apply Nat.sqrt_pos.mpr
    omega
  obtain ⟨p, hp, hkp, hpk⟩ := Nat.exists_prime_lt_and_le_two_mul k hk
  refine ⟨p, hp, ?_, ?_⟩
  · have hkSq : k ^ 2 ≤ n / 8 := Nat.sqrt_le' (n / 8)
    have hdiv : 8 * (n / 8) ≤ n := Nat.mul_div_le n 8
    have hpsq : p ^ 2 ≤ (2 * k) ^ 2 := Nat.pow_le_pow_left hpk 2
    nlinarith
  · have hkSq : n / 8 < (k + 1) ^ 2 := Nat.lt_succ_sqrt' (n / 8)
    have hpsq : (k + 1) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hkp 2
    have hdiv : n / 8 < p ^ 2 := hkSq.trans_le hpsq
    have hlt : n < p ^ 2 * 8 := (Nat.div_lt_iff_lt_mul (by norm_num)).mp hdiv
    simpa only [Nat.mul_comm] using hlt

/-- A convenient real-power estimate without any square-root coercions. -/
theorem rpow_three_halves_le_cube {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x ≤ y ^ 2) : x ^ ((2 : ℝ) - 1 / (2 : ℝ)) ≤ y ^ 3 := by
  calc
    _ ≤ (y ^ 2) ^ ((2 : ℝ) - 1 / (2 : ℝ)) :=
      Real.rpow_le_rpow hx hxy (by norm_num)
    _ = y ^ 3 := by
      rw [← Real.rpow_natCast_mul hy]
      norm_num

/-- An explicit `K_{2,2}` extremal lower bound, valid for every `n ≥ 8`. -/
theorem case_two_lower_bound {n : ℕ} (hn : 8 ≤ n) :
    (1 / 64 : ℝ) * (n : ℝ) ^ ((2 : ℝ) - 1 / (2 : ℝ)) ≤
      (extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2)) : ℝ) := by
  obtain ⟨p, hp, hpn, hnp⟩ := exists_prime_for_padding hn
  have he : p ^ 3 ≤ extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2)) :=
    (prime_cube_le_extremalNumber hp).trans
      (extremalNumber_completeBipartite_mono (by norm_num) (by norm_num) hpn)
  have hnp' : (n : ℝ) < 8 * (p : ℝ) ^ 2 := by exact_mod_cast hnp
  have hnSq : (n : ℝ) ≤ (4 * (p : ℝ)) ^ 2 := by nlinarith [sq_nonneg (p : ℝ)]
  have hpow := rpow_three_halves_le_cube (Nat.cast_nonneg n) (by positivity) hnSq
  have he' : (p : ℝ) ^ 3 ≤
      (extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2)) : ℝ) := by
    exact_mod_cast he
  nlinarith

/-- The `r = 2` instance, with the same quantifiers and exponent as in the
problem statement. This is not the assertion for general `r`. -/
theorem erdos_714_case_two :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (2 : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2)) : ℝ) := by
  refine ⟨1 / 64, by norm_num, ?_⟩
  exact Filter.eventually_atTop.mpr ⟨8, fun n hn => case_two_lower_bound hn⟩

end Erdos714.CaseTwo
