import Submission.RothQuant
import Submission.FTRectangle
import Submission.GapCounting

/-!
# A finite global square-multiple band bound

This combines the verified integer pair-label estimates, four-point rectangle
spacing, and finite gap-counting lemmas. In a dyadic band `[N, 2*N]`, square
multiples hitting `(x, x+H]` satisfy the rational bound

`card S ≤ 2 + 2*N/B + 8*x*B^4/N^4 + 1440*H*B/V`

provided `N`, `B`, and `V` are positive, `256*H ≤ N`, and
`5*x*B*V^3 < N^5`. The proof retains the two endpoint contributions in both
zero isolation and fibre packing. All counting estimates before the final
conversion are division-free inequalities over the natural numbers.

This is a finite band estimate for the partial one-fifth-power argument, not
an all-positive-exponents squarefree-gap theorem. No conjecture is assumed.
-/

open Finset

namespace FTBand

/-- The integer label of a consecutive edge of an indexed sequence of hits. -/
def edgeLabel {T : ℕ} (f m : Fin (T + 1) → ℕ) (i : Fin T) : ℤ :=
  RothQuant.label (f i.castSucc) (f i.succ) (m i.castSucc) (m i.succ)

/-- Consecutive edges with prescribed gap and positive integer label. -/
def positiveGapEdges {T : ℕ} (f m : Fin (T + 1) → ℕ) (b : ℕ) :
    Finset (Fin T) :=
  univ.filter (fun i => GapCounting.edgeGap f i = b ∧ 0 < edgeLabel f m i)

/-- A fixed positive-label fibre has the exact scaled packing bound, including
empty and singleton fibres. The local rectangle condition uses its gap `b`. -/
theorem fixed_label_count {x H N b V k T : ℕ}
    {f m : Fin (T + 1) → ℕ} (E : Finset (Fin T))
    (hf : StrictMono f) (hN : 0 < N) (hH : 256 * H ≤ N)
    (hb : 0 < b) (hV : 0 < V) (hk : 0 < k)
    (hsmall : 5 * x * b * V ^ 3 < N ^ 5)
    (hband : ∀ i, N ≤ f i ∧ f i ≤ 2 * N)
    (hhit : ∀ i, x < m i * f i ^ 2 ∧ m i * f i ^ 2 ≤ x + H)
    (hE : ∀ i ∈ E, GapCounting.edgeGap f i = b ∧ edgeLabel f m i = (k : ℤ)) :
    k * V * E.card ≤ 2 * k * V + 20 * H := by
  let S := E.image (fun i => f i.castSucc)
  have hcard : S.card = E.card := by
    apply card_image_iff.mpr
    intro i _ j _ hij
    exact Fin.castSucc_injective T (hf.injective hij)
  have hsubset : S ⊆ GapCounting.fixedGapStarts f b := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hu
    exact GapCounting.mem_fixedGapStarts.mpr ⟨i, (hE i hi).1, rfl⟩
  have hdata (u : ℕ) (hu : u ∈ S) :
      N ≤ u ∧ u + b ≤ 2 * N ∧ ∃ a a' : ℕ,
        (x < a * u ^ 2 ∧ a * u ^ 2 ≤ x + H) ∧
        (x < a' * (u + b) ^ 2 ∧ a' * (u + b) ^ 2 ≤ x + H) ∧
        RothQuant.label u (u + b) a a' = (k : ℤ) := by
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hu
    obtain ⟨hgap, hl⟩ := hE i hi
    have heq : f i.castSucc + b = f i.succ := by
      have hle := (hf (Fin.castSucc_lt_succ (i := i))).le
      dsimp [GapCounting.edgeGap] at hgap
      omega
    refine ⟨(hband i.castSucc).1, ?_, m i.castSucc, m i.succ, hhit i.castSucc, ?_, ?_⟩
    · simpa only [heq] using (hband i.succ).2
    · simpa only [heq] using hhit i.succ
    · simpa only [heq, edgeLabel] using hl
  have hsep : GapCounting.TripleSeparated S V := by
    intro u hu v hv w hw huv hvw
    have huvGap := GapCounting.fixedGapStarts_separated hf (hsubset hu) (hsubset hv) huv
    have hvwGap := GapCounting.fixedGapStarts_separated hf (hsubset hv) (hsubset hw) hvw
    have hbc : 2 * b ≤ w - u := by omega
    have hwu : u + (w - u) = w := by omega
    have hwub : u + b + (w - u) = w + b := by omega
    obtain ⟨huN, hub, a0, a1, ha0, ha1, hka⟩ := hdata u hu
    obtain ⟨_, hwb, a2, a3, ha2, ha3, _⟩ := hdata w hw
    have hpos : 0 < RothQuant.label u (u + b) a0 a1 := by
      rw [hka]
      exact_mod_cast hk
    have hlarge : N ^ 4 ≤ 2 * x * b ^ 3 := by
      simpa only [Nat.add_sub_cancel_left] using
        RothQuant.positive_label_gap hN hH huN (Nat.le_add_right u b) hub ha0 ha1 hpos
    have hrect := FTRectangle.four_point_spacing (n := u) (b := b) (c := w - u)
      hN hH hb hbc huN (by omega) ha0 ha1
      (by simpa only [hwu] using ha2) (by simpa only [hwub] using ha3) hlarge
    by_contra hnot
    have hc : w - u ≤ V := le_of_not_gt hnot
    have hupper : 5 * x * b * (w - u) ^ 3 ≤ 5 * x * b * V ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hc 3)
    exact (not_le_of_gt hsmall) (hrect.trans hupper)
  have hdiam : ∀ u ∈ S, ∀ v ∈ S, u < v → k * (v - u) ≤ 10 * H := by
    intro u hu v hv huv
    obtain ⟨huN, _, a0, a1, ha0, ha1, hka⟩ := hdata u hu
    obtain ⟨_, hvb, a2, a3, ha2, ha3, hkb⟩ := hdata v hv
    exact RothQuant.same_positive_label_diameter_nat hN hH huN huv.le hvb
      ha0 ha1 ha2 ha3 hka hkb hk
  simpa only [hcard] using GapCounting.packing_scaled_le_twenty hV hsep hdiam

/-- Summing positive-label fibres without a floor or endpoint loss. The
upper label bound controls the number of occupied labels; the lower one
allows the weighted packing inequalities to be summed uniformly. -/
private lemma sum_positive_label_fibres {ι : Type*} {E : Finset ι}
    (l : ι → ℕ) {X Q V H : ℕ} (hQ : 0 < Q)
    (hlabels : ∀ i ∈ E, 0 < l i ∧ X ≤ 18 * l i * Q ∧ l i * Q ≤ 2 * X)
    (hpack : ∀ k ∈ E.image l,
      k * V * (E.filter (fun i => l i = k)).card ≤ 2 * k * V + 20 * H) :
    Q * V * E.card ≤ 4 * X * V + 720 * H * Q := by
  classical
  by_cases hE : E.Nonempty
  · obtain ⟨i, hi⟩ := hE
    have hi0 := (hlabels i hi).1
    have hiup := (hlabels i hi).2.2
    have hX : 0 < X := by
      have := Nat.mul_pos hi0 hQ
      omega
    let K := E.image l
    have hK : K.card * Q ≤ 2 * X := by
      have hc : K.card ≤ 2 * X / Q := by
        calc
          K.card ≤ (Icc 1 (2 * X / Q)).card := by
            apply card_le_card
            intro k hk
            obtain ⟨j, hj, rfl⟩ := mem_image.mp hk
            obtain ⟨hj0, _, hjup⟩ := hlabels j hj
            exact mem_Icc.mpr ⟨hj0, (Nat.le_div_iff_mul_le hQ).mpr hjup⟩
          _ = 2 * X / Q := by simp
      exact (Nat.mul_le_mul_right Q hc).trans (Nat.div_mul_le_self (2 * X) Q)
    have hF : ∀ k ∈ K,
        X * V * (E.filter (fun i => l i = k)).card ≤ 2 * X * V + 360 * H * Q := by
      intro k hk
      obtain ⟨j, hj, hjk⟩ := mem_image.mp hk
      obtain ⟨hk0, hlo, _⟩ := hlabels j hj
      rw [hjk] at hk0 hlo
      apply Nat.le_of_mul_le_mul_left (c := k) ?_ hk0
      calc
        k * (X * V * (E.filter (fun i => l i = k)).card) =
            X * (k * V * (E.filter (fun i => l i = k)).card) := by ring
        _ ≤ X * (2 * k * V + 20 * H) := Nat.mul_le_mul_left X (hpack k hk)
        _ = k * (2 * X * V) + (20 * H) * X := by ring
        _ ≤ k * (2 * X * V) + (20 * H) * (18 * k * Q) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left (20 * H) hlo) _
        _ = k * (2 * X * V + 360 * H * Q) := by ring
    have hsum : X * V * E.card ≤ K.card * (2 * X * V + 360 * H * Q) := by
      calc
        X * V * E.card =
            ∑ k ∈ K, X * V * (E.filter (fun i => l i = k)).card := by
          rw [card_eq_sum_card_image l E, mul_sum]
        _ ≤ ∑ _k ∈ K, (2 * X * V + 360 * H * Q) := sum_le_sum hF
        _ = K.card * (2 * X * V + 360 * H * Q) := by simp
    apply Nat.le_of_mul_le_mul_left (c := X) ?_ hX
    calc
      X * (Q * V * E.card) = Q * (X * V * E.card) := by ring
      _ ≤ Q * (K.card * (2 * X * V + 360 * H * Q)) := Nat.mul_le_mul_left Q hsum
      _ = (K.card * Q) * (2 * X * V + 360 * H * Q) := by ring
      _ ≤ (2 * X) * (2 * X * V + 360 * H * Q) := Nat.mul_le_mul_right _ hK
      _ = X * (4 * X * V + 720 * H * Q) := by ring
  · rw [not_nonempty_iff_eq_empty.mp hE]
    simp

/-- The positive edges of one prescribed gap satisfy a division-free bound
with constant `720`, even when `x*b^3 = 0` (when the positive fibre is empty). -/
theorem positive_gap_count {x H N b V T : ℕ} {f m : Fin (T + 1) → ℕ}
    (hf : StrictMono f) (hN : 0 < N) (hH : 256 * H ≤ N)
    (hb : 0 < b) (hV : 0 < V) (hsmall : 5 * x * b * V ^ 3 < N ^ 5)
    (hband : ∀ i, N ≤ f i ∧ f i ≤ 2 * N)
    (hhit : ∀ i, x < m i * f i ^ 2 ∧ m i * f i ^ 2 ≤ x + H) :
    N ^ 4 * V * (positiveGapEdges f m b).card ≤
      4 * x * b ^ 3 * V + 720 * H * N ^ 4 := by
  let E := positiveGapEdges f m b
  let l : Fin T → ℕ := fun i => (edgeLabel f m i).toNat
  have hlabels : ∀ i ∈ E,
      0 < l i ∧ x * b ^ 3 ≤ 18 * l i * N ^ 4 ∧ l i * N ^ 4 ≤ 2 * (x * b ^ 3) := by
    intro i hi
    obtain ⟨hgap, hpos⟩ := (mem_filter.mp hi).2
    have hbnds := RothQuant.positive_label_bounds_nat hN hH (hband i.castSucc).1
      (hf (Fin.castSucc_lt_succ (i := i))).le (hband i.succ).2
      (hhit i.castSucc) (hhit i.succ) hpos
    change x * GapCounting.edgeGap f i ^ 3 ≤ 18 * l i * N ^ 4 ∧
      l i * N ^ 4 ≤ 2 * x * GapCounting.edgeGap f i ^ 3 at hbnds
    rw [hgap] at hbnds
    refine ⟨?_, hbnds.1, ?_⟩
    · dsimp [l]
      omega
    · simpa only [mul_assoc] using hbnds.2
  have hpack : ∀ k ∈ E.image l,
      k * V * (E.filter (fun i => l i = k)).card ≤ 2 * k * V + 20 * H := by
    intro k hk
    have hkpos : 0 < k := by
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hk
      exact (hlabels i hi).1
    apply fixed_label_count _ hf hN hH hb hV hkpos hsmall hband hhit
    intro i hi
    obtain ⟨hiE, hil⟩ := mem_filter.mp hi
    obtain ⟨hgap, hpos⟩ := (mem_filter.mp hiE).2
    refine ⟨hgap, ?_⟩
    calc
      edgeLabel f m i = ((edgeLabel f m i).toNat : ℤ) :=
        (Int.toNat_of_nonneg hpos.le).symm
      _ = (k : ℤ) := by change (l i : ℤ) = (k : ℤ); rw [hil]
  have h := sum_positive_label_fibres l (pow_pos hN 4) hlabels hpack
  simpa only [mul_assoc] using h

/-- Summing all positive edges of gaps `1, …, B`, using the coarse but exact
cube-sum bound `∑ b^3 ≤ B^4`. -/
theorem small_gap_count {x H N B V T : ℕ} {f m : Fin (T + 1) → ℕ}
    (hf : StrictMono f) (hN : 0 < N) (hH : 256 * H ≤ N)
    (hV : 0 < V) (hsmall : 5 * x * B * V ^ 3 < N ^ 5)
    (hband : ∀ i, N ≤ f i ∧ f i ≤ 2 * N)
    (hhit : ∀ i, x < m i * f i ^ 2 ∧ m i * f i ^ 2 ≤ x + H) :
    N ^ 4 * V * (∑ b ∈ Icc 1 B, (positiveGapEdges f m b).card) ≤
      4 * x * B ^ 4 * V + 720 * H * B * N ^ 4 := by
  have hcube : ∑ b ∈ Icc 1 B, b ^ 3 ≤ B ^ 4 := by
    calc
      ∑ b ∈ Icc 1 B, b ^ 3 ≤ ∑ _b ∈ Icc 1 B, B ^ 3 := by
        apply sum_le_sum
        intro b hb
        exact Nat.pow_le_pow_left (mem_Icc.mp hb).2 3
      _ = B ^ 4 := by simp; ring
  calc
    N ^ 4 * V * (∑ b ∈ Icc 1 B, (positiveGapEdges f m b).card) =
        ∑ b ∈ Icc 1 B, N ^ 4 * V * (positiveGapEdges f m b).card := by rw [mul_sum]
    _ ≤ ∑ b ∈ Icc 1 B, (4 * x * V * b ^ 3 + 720 * H * N ^ 4) := by
      apply sum_le_sum
      intro b hb
      obtain ⟨hb0, hbB⟩ := mem_Icc.mp hb
      have hlocal : 5 * x * b * V ^ 3 < N ^ 5 := by
        apply lt_of_le_of_lt _ hsmall
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hbB)
      have h := positive_gap_count hf hN hH hb0 hV hlocal hband hhit
      nlinarith only [h]
    _ = 4 * x * V * (∑ b ∈ Icc 1 B, b ^ 3) + B * (720 * H * N ^ 4) := by
      rw [sum_add_distrib, ← mul_sum]
      simp
    _ ≤ 4 * x * V * B ^ 4 + B * (720 * H * N ^ 4) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ hcube) _
    _ = 4 * x * B ^ 4 * V + 720 * H * B * N ^ 4 := by ring

/-- The finite global band bound for an increasing indexed sequence of hits.
The `T+1` vertices retain the exact additive endpoint allowance `2`. -/
theorem indexed_band_bound {x H N B V T : ℕ} {f m : Fin (T + 1) → ℕ}
    (hf : StrictMono f) (hN : 0 < N) (hH : 256 * H ≤ N)
    (hB : 0 < B) (hV : 0 < V) (hsmall : 5 * x * B * V ^ 3 < N ^ 5)
    (hband : ∀ i, N ≤ f i ∧ f i ≤ 2 * N)
    (hhit : ∀ i, x < m i * f i ^ 2 ∧ m i * f i ^ 2 ≤ x + H) :
    ((T + 1 : ℕ) : ℚ) ≤
      2 + 2 * (N : ℚ) / B + 8 * (x : ℚ) * B ^ 4 / N ^ 4 + 1440 * (H : ℚ) * B / V := by
  let P := univ.filter (fun i : Fin T => 0 < edgeLabel f m i)
  have hnonneg : ∀ i, 0 ≤ edgeLabel f m i := by
    intro i
    exact RothQuant.label_nonneg hN hH (hband i.castSucc).1
      (hf (Fin.castSucc_lt_succ (i := i))).le (hband i.succ).2
      (hhit i.castSucc) (hhit i.succ)
  have hisolated : ∀ i j : Fin T, i.val + 1 = j.val →
      ¬ (edgeLabel f m i = 0 ∧ edgeLabel f m j = 0) := by
    intro i j hij ⟨hi0, hj0⟩
    have heq : i.succ = j.castSucc := Fin.ext hij
    have hijlt : f i.castSucc < f j.castSucc := by
      simpa only [heq] using hf (Fin.castSucc_lt_succ (i := i))
    dsimp only [edgeLabel] at hi0 hj0
    rw [heq] at hi0
    exact RothQuant.no_two_adjacent_zero_labels hN hH (hband i.castSucc).1
      hijlt (hf (Fin.castSucc_lt_succ (i := j))) (hband j.succ).2
      (hhit i.castSucc) (hhit j.castSucc) (hhit j.succ) hi0 hj0
  have hvertices : T + 1 ≤ 2 * P.card + 2 :=
    GapCounting.zero_isolation_count_fin (edgeLabel f m) hnonneg hisolated
  have hcover : P ⊆ GapCounting.largeGapEdges f B ∪
      (Icc 1 B).biUnion (positiveGapEdges f m) := by
    intro i hi
    have hpos := (mem_filter.mp hi).2
    by_cases hlarge : B < GapCounting.edgeGap f i
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hlarge⟩)
    · apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨GapCounting.edgeGap f i, ?_, ?_⟩
      · exact mem_Icc.mpr ⟨GapCounting.edgeGap_pos hf i, le_of_not_gt hlarge⟩
      · exact mem_filter.mpr ⟨mem_univ _, rfl, hpos⟩
  have hP : P.card ≤ (GapCounting.largeGapEdges f B).card +
      ∑ b ∈ Icc 1 B, (positiveGapEdges f m b).card := by
    calc
      P.card ≤ (GapCounting.largeGapEdges f B ∪
          (Icc 1 B).biUnion (positiveGapEdges f m)).card := card_le_card hcover
      _ ≤ (GapCounting.largeGapEdges f B).card +
          ((Icc 1 B).biUnion (positiveGapEdges f m)).card := card_union_le _ _
      _ ≤ (GapCounting.largeGapEdges f B).card +
          ∑ b ∈ Icc 1 B, (positiveGapEdges f m b).card :=
        Nat.add_le_add_left card_biUnion_le _
  have hbudget := GapCounting.sum_edgeGap_le_of_endpoints hf.monotone
    (hband 0).1 (hband (Fin.last T)).2
  have hlargeNat : B * (GapCounting.largeGapEdges f B).card ≤ N :=
    (GapCounting.mul_card_largeGapEdges_le_sum f B).trans hbudget
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hBq : (0 : ℚ) < B := by exact_mod_cast hB
  have hVq : (0 : ℚ) < V := by exact_mod_cast hV
  have hlargeQ : ((GapCounting.largeGapEdges f B).card : ℚ) ≤ (N : ℚ) / B := by
    apply (le_div_iff₀ hBq).mpr
    have h : (B : ℚ) * (GapCounting.largeGapEdges f B).card ≤ N := by
      exact_mod_cast hlargeNat
    nlinarith only [h]
  have hsmallNat := small_gap_count hf hN hH hV hsmall hband hhit
  have hsmallQ : ((∑ b ∈ Icc 1 B, (positiveGapEdges f m b).card : ℕ) : ℚ) ≤
      4 * (x : ℚ) * B ^ 4 / N ^ 4 + 720 * (H : ℚ) * B / V := by
    apply (mul_le_mul_iff_right₀ (mul_pos (pow_pos hNq 4) hVq)).mp
    have heq : (N : ℚ) ^ 4 * V *
        (4 * (x : ℚ) * B ^ 4 / N ^ 4 + 720 * (H : ℚ) * B / V) =
        4 * (x : ℚ) * B ^ 4 * V + 720 * (H : ℚ) * B * N ^ 4 := by
      field_simp
    rw [heq]
    exact_mod_cast hsmallNat
  have hPQ : (P.card : ℚ) ≤ ((GapCounting.largeGapEdges f B).card : ℚ) +
      ((∑ b ∈ Icc 1 B, (positiveGapEdges f m b).card : ℕ) : ℚ) := by
    exact_mod_cast hP
  have hverticesQ : ((T + 1 : ℕ) : ℚ) ≤ 2 * (P.card : ℚ) + 2 := by
    exact_mod_cast hvertices
  simp only [div_eq_mul_inv] at hlargeQ hsmallQ ⊢
  linarith only [hlargeQ, hsmallQ, hPQ, hverticesQ]

/-- **Finite global square-multiple band bound.** A finite set of bases in
`[N,2*N]`, each with a square multiple in `(x,x+H]`, satisfies the stated
rational inequality. This includes the empty set and singletons, assumes no
conjecture, and preserves the constants `2`, `8`, and `1440` exactly. -/
theorem finite_band_bound {x H N B V : ℕ} (S : Finset ℕ)
    (hN : 0 < N) (hH : 256 * H ≤ N) (hB : 0 < B) (hV : 0 < V)
    (hsmall : 5 * x * B * V ^ 3 < N ^ 5)
    (hband : S ⊆ Icc N (2 * N))
    (hhit : ∀ d ∈ S, ∃ m : ℕ, x < m * d ^ 2 ∧ m * d ^ 2 ≤ x + H) :
    (S.card : ℚ) ≤
      2 + 2 * (N : ℚ) / B + 8 * (x : ℚ) * B ^ 4 / N ^ 4 + 1440 * (H : ℚ) * B / V := by
  classical
  cases hcard : S.card with
  | zero => positivity
  | succ T =>
      let f : Fin (T + 1) ↪o ℕ := S.orderEmbOfFin hcard
      have hfmem : ∀ i, f i ∈ S := fun i => S.orderEmbOfFin_mem hcard i
      have hfband : ∀ i, N ≤ f i ∧ f i ≤ 2 * N :=
        fun i => mem_Icc.mp (hband (hfmem i))
      have hfhits : ∀ i, ∃ m : ℕ, x < m * f i ^ 2 ∧ m * f i ^ 2 ≤ x + H :=
        fun i => hhit (f i) (hfmem i)
      choose m hm using hfhits
      have h := indexed_band_bound f.strictMono hN hH hB hV hsmall hfband hm
      simpa only [hcard] using h

#print axioms indexed_band_bound
#print axioms finite_band_bound

end FTBand
