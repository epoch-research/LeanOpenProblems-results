import Submission.RamseyTools

/-!
# A structural seed bound for the two-colour triple Ramsey number

This file is independent of `Submission.Spec` and of any proposed recurrence.
The proof counts balanced quadruples (two triples of each colour). On fifteen
vertices the mixed-pair count bounds their number by 315. On every nine vertices,
parity and a small weighted-degree argument give at least 30; double counting
then gives at least 325.

## Human-scale argument

Write `m` for the number of balanced quadruples. In a colouring with no
monochromatic quadruple, each quadruple has one, two, or three red triples.
A mixed pair of triples with a common pair belongs to one quadruple. Thus
`∑ P, d(P) * (13 - d(P)) = 3 * choose 15 4 + m`, and each product is at most
`6 * 7`; hence `m ≤ 315`.

In a five-set, the sum of the red counts of its five quadruples is even,
since every triple occurs twice. Consequently an odd number of its
quadruples are balanced.

On nine vertices take complements of the balanced quadruples, obtaining
an odd `(9,5,4)` cover with `b` five-blocks. For every four-set `T` put
`w(T) = (d(T) - 1) / 2`, so `w(T) ∈ {0,1,2}`. If `q = ∑ T, w(T)`, then
`5*b = 126 + 2*q`. If `b < 30`, this forces `b = 26` or `28`, and hence
`q = 2` or `7`. Double counting at a pair and a vertex shows respectively
that every weighted pair degree is divisible by three and every weighted
vertex degree is even.

Every active vertex has weighted degree at least four: an incident
four-block supplies three neighbours, each of pair degree at least three,
and the vertex degree is even. This excludes `q = 2`. If `q = 7`, all
vertex degrees are `0`, `4`, or `6`, and their sum is `28`, so some vertex
has degree four. Its support neighbourhood has at most four vertices.
Every active vertex outside that neighbourhood would have disjoint
incidence from it, and degree at most `7 - 4 = 3`, a contradiction.
Thus all positive blocks avoiding the chosen vertex lie in a set of at
most four vertices: at most one such block, of weight at most two.
But their total weight is `7 - 4 = 3`, another contradiction. Therefore
there are at least thirty balanced quadruples in every nine-set.

Averaging over the nine-sets gives
`choose 11 5 * m ≥ 30 * choose 15 9`, or `m ≥ 325`, contradicting `m ≤ 315`.

For context, the sharper exact value `R₃(4) = 13` is attributed to McKay and
Radziszowski (1991) in McKay, *A class of Ramsey-extremal hypergraphs*,
arXiv:1608.07762, Introduction. This file does not rely on that enumeration
or on a claim of Greenwood and Gleason.

No native evaluation, exhaustive colouring search, or reduction axiom is used.
-/

namespace Combinatorics.SmallRamsey

open Finset

universe u

section Counting

variable {α : Type u} [DecidableEq α]

/-- Weighted incidence degree of a set in a uniform family. -/
def degree (V : Finset α) (k : ℕ) (w : Finset α → ℕ) (T : Finset α) : ℕ :=
  ∑ S ∈ V.powersetCard k, if T ⊆ S then w S else 0

/-- The total weight is the degree of the empty set. -/
def total (V : Finset α) (k : ℕ) (w : Finset α → ℕ) : ℕ :=
  ∑ S ∈ V.powersetCard k, w S

lemma degree_empty (V : Finset α) (k : ℕ) (w : Finset α → ℕ) :
    degree V k w ∅ = total V k w := by
  simp [degree, total]

lemma degree_add (V : Finset α) (k : ℕ) (w z : Finset α → ℕ) (T : Finset α) :
    degree V k (fun S => w S + z S) T = degree V k w T + degree V k z T := by
  simp only [degree, ← sum_add_distrib]
  apply sum_congr rfl
  intro S _
  split_ifs <;> simp

lemma degree_mul (V : Finset α) (k : ℕ) (w : Finset α → ℕ) (T : Finset α) (a : ℕ) :
    degree V k (fun S => a * w S) T = a * degree V k w T := by
  simp only [degree, mul_sum]
  apply sum_congr rfl
  intro S _
  split_ifs <;> simp

lemma degree_congr (V : Finset α) (k : ℕ) (w z : Finset α → ℕ) (T : Finset α)
    (h : ∀ S ∈ V.powersetCard k, T ⊆ S → w S = z S) :
    degree V k w T = degree V k z T := by
  apply sum_congr rfl
  intro S hS
  by_cases hTS : T ⊆ S
  · simp [hTS, h S hS hTS]
  · simp [hTS]

/-- Number of sets of a given size containing a prescribed subset. -/
lemma card_supersets (V T : Finset α) (k : ℕ) (hTV : T ⊆ V) (hTk : T.card ≤ k) :
    ((V.powersetCard k).filter (fun S => T ⊆ S)).card =
      (V.card - T.card).choose (k - T.card) := by
  rw [← card_sdiff_of_subset hTV, ← card_powersetCard]
  apply card_bij (fun S _ => S \ T)
  · intro S hS
    obtain ⟨⟨hSV, hSk⟩, hTS⟩ := by
      simpa only [mem_filter, mem_powersetCard] using hS
    apply mem_powersetCard.mpr
    constructor
    · exact sdiff_subset_sdiff hSV (Subset.refl _)
    · rw [card_sdiff_of_subset hTS, hSk]
  · intro S hS U hU hSU
    have hTS : T ⊆ S := (mem_filter.mp hS).2
    have hTU : T ⊆ U := (mem_filter.mp hU).2
    calc
      S = T ∪ (S \ T) := (union_sdiff_of_subset hTS).symm
      _ = T ∪ (U \ T) := by rw [hSU]
      _ = U := union_sdiff_of_subset hTU
  · intro U hU
    obtain ⟨hUV, hUk⟩ := mem_powersetCard.mp hU
    have hUT : Disjoint T U := by
      apply disjoint_left.mpr
      intro x hxT hxU
      exact (mem_sdiff.mp (hUV hxU)).2 hxT
    have hsub : T ∪ U ⊆ V := union_subset hTV (hUV.trans sdiff_subset)
    have hcard : (T ∪ U).card = k := by
      rw [card_union_of_disjoint hUT, hUk]
      omega
    refine ⟨T ∪ U, mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hsub, hcard⟩,
      subset_union_left⟩, ?_⟩
    ext x
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨hx | hx, hn⟩
      · exact (hn hx).elim
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, fun hxT => (disjoint_left.mp hUT hxT hx)⟩

lemma degree_one (V T : Finset α) (k : ℕ) (hTV : T ⊆ V) (hTk : T.card ≤ k) :
    degree V k (fun _ => 1) T = (V.card - T.card).choose (k - T.card) := by
  rw [degree, sum_boole]
  exact card_supersets V T k hTV hTk

lemma sum_subsets_const (V S : Finset α) (i a : ℕ) (hSV : S ⊆ V) :
    (∑ T ∈ V.powersetCard i, if T ⊆ S then a else 0) = S.card.choose i * a := by
  rw [← sum_filter]
  have hf : (V.powersetCard i).filter (fun T => T ⊆ S) = S.powersetCard i := by
    ext T
    simp only [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨⟨_, hc⟩, hs⟩
      exact ⟨hs, hc⟩
    · rintro ⟨hs, hc⟩
      exact ⟨⟨hs.trans hSV, hc⟩, hs⟩
  rw [hf]
  simp

/-- Summing weighted degrees counts each edge once for each of its subsets. -/
lemma sum_degrees (V : Finset α) (k i : ℕ) (w : Finset α → ℕ) :
    (∑ T ∈ V.powersetCard i, degree V k w T) = k.choose i * total V k w := by
  simp only [degree]
  rw [sum_comm]
  simp only [total, mul_sum]
  apply sum_congr rfl
  intro S hS
  obtain ⟨hSV, hSk⟩ := mem_powersetCard.mp hS
  rw [sum_subsets_const V S i (w S) hSV, hSk]

lemma degree_le_total (V : Finset α) (k : ℕ) (w : Finset α → ℕ) (T : Finset α) :
    degree V k w T ≤ total V k w := by
  apply sum_le_sum
  intro S _
  split_ifs <;> omega

lemma weight_le_degree {V S T : Finset α} {k : ℕ} {w : Finset α → ℕ}
    (hS : S ∈ V.powersetCard k) (hTS : T ⊆ S) :
    w S ≤ degree V k w T := by
  have h := single_le_sum (f := fun U => if T ⊆ U then w U else 0)
    (fun _ _ => Nat.zero_le _) hS
  simpa only [if_pos hTS] using h

lemma degree_pos_iff (V T : Finset α) (k : ℕ) (w : Finset α → ℕ) :
    0 < degree V k w T ↔ ∃ S ∈ V.powersetCard k, T ⊆ S ∧ 0 < w S := by
  simp only [degree, sum_pos_iff]
  constructor
  · rintro ⟨S, hS, hs⟩
    by_cases hTS : T ⊆ S
    · exact ⟨S, hS, hTS, by simpa [hTS] using hs⟩
    · simp [hTS] at hs
  · rintro ⟨S, hS, hTS, hs⟩
    exact ⟨S, hS, by simpa [hTS] using hs⟩

/-- The elementary inclusion-exclusion inequality for weighted degrees. -/
lemma degree_union_le (V : Finset α) (k : ℕ) (w : Finset α → ℕ) (P Q : Finset α) :
    degree V k w P + degree V k w Q ≤ total V k w + degree V k w (P ∪ Q) := by
  simp only [degree, total, ← sum_add_distrib]
  apply sum_le_sum
  intro S _
  by_cases hP : P ⊆ S <;> by_cases hQ : Q ⊆ S <;>
    simp [hP, hQ, union_subset_iff]

lemma total_restrict (V S : Finset α) (k : ℕ) (w : Finset α → ℕ) (hSV : S ⊆ V) :
    total S k w = ∑ T ∈ V.powersetCard k, if T ⊆ S then w T else 0 := by
  rw [← sum_filter]
  have hf : (V.powersetCard k).filter (fun T => T ⊆ S) = S.powersetCard k := by
    ext T
    simp only [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨⟨_, hc⟩, hs⟩
      exact ⟨hs, hc⟩
    · rintro ⟨hs, hc⟩
      exact ⟨⟨hs.trans hSV, hc⟩, hs⟩
  rw [hf]
  rfl

lemma degree_const (V P : Finset α) (k a : ℕ) (hPV : P ⊆ V) (hPk : P.card ≤ k) :
    degree V k (fun _ => a) P = (V.card - P.card).choose (k - P.card) * a := by
  simpa only [mul_one, degree_one V P k hPV hPk, Nat.mul_comm] using
    degree_mul V k (fun _ => 1) P a

/-- Incidence count between a lower and an upper prescribed set. -/
lemma sum_between_const (V P S : Finset α) (i a : ℕ) (hSV : S ⊆ V)
    (hPi : P.card ≤ i) :
    (∑ T ∈ V.powersetCard i, if P ⊆ T ∧ T ⊆ S then a else 0) =
      if P ⊆ S then (S.card - P.card).choose (i - P.card) * a else 0 := by
  by_cases hPS : P ⊆ S
  · rw [if_pos hPS, ← sum_filter]
    have hf : (V.powersetCard i).filter (fun T => P ⊆ T ∧ T ⊆ S) =
        (S.powersetCard i).filter (fun T => P ⊆ T) := by
      ext T
      simp only [mem_filter, mem_powersetCard]
      constructor
      · rintro ⟨⟨_, hc⟩, hp, hs⟩
        exact ⟨⟨hs, hc⟩, hp⟩
      · rintro ⟨⟨hs, hc⟩, hp⟩
        exact ⟨⟨hs.trans hSV, hc⟩, hp, hs⟩
    rw [hf]
    simp only [sum_const, smul_eq_mul]
    rw [card_supersets S P i hPS hPi]
  · rw [if_neg hPS]
    apply sum_eq_zero
    intro T _
    have hn : ¬ (P ⊆ T ∧ T ⊆ S) := fun h => hPS (h.1.trans h.2)
    simp [hn]

/-- Iterated degrees are scalar multiples of the original degree. -/
lemma degree_degree (V P : Finset α) (k i : ℕ) (w : Finset α → ℕ)
    (hPi : P.card ≤ i) :
    degree V i (fun T => degree V k w T) P =
      (k - P.card).choose (i - P.card) * degree V k w P := by
  have hexpand : degree V i (fun T => degree V k w T) P =
      ∑ T ∈ V.powersetCard i, ∑ S ∈ V.powersetCard k,
        if P ⊆ T ∧ T ⊆ S then w S else 0 := by
    unfold degree
    apply sum_congr rfl
    intro T _
    by_cases hPT : P ⊆ T <;> simp [hPT]
  rw [hexpand, sum_comm]
  simp only [degree, mul_sum]
  apply sum_congr rfl
  intro S hS
  obtain ⟨hSV, hSk⟩ := mem_powersetCard.mp hS
  rw [sum_between_const V P S i (w S) hSV hPi, hSk]
  split_ifs <;> simp

/-- Double counting all small subsets inside all larger subsets. -/
lemma sum_totals_subsets (V : Finset α) (k i : ℕ) (w : Finset α → ℕ) (hik : i ≤ k) :
    (∑ T ∈ V.powersetCard k, total T i w) =
      (V.card - i).choose (k - i) * total V i w := by
  have hrestrict : (∑ T ∈ V.powersetCard k, total T i w) =
      ∑ T ∈ V.powersetCard k, ∑ S ∈ V.powersetCard i,
        if S ⊆ T then w S else 0 := by
    apply sum_congr rfl
    intro T hT
    exact total_restrict V T i w (mem_powersetCard.mp hT).1
  rw [hrestrict, sum_comm]
  simp only [total, mul_sum]
  apply sum_congr rfl
  intro S hS
  obtain ⟨hSV, hSi⟩ := mem_powersetCard.mp hS
  change degree V k (fun _ => w S) S = _
  rw [degree_const V S k (w S) hSV (hSi ▸ hik), hSi]

lemma sum_vertex_degrees (V : Finset α) (k : ℕ) (w : Finset α → ℕ) :
    (∑ v ∈ V, degree V k w {v}) = k * total V k w := by
  have h := sum_degrees V k 1 w
  simpa only [powersetCard_one, sum_map, Function.Embedding.coeFn_mk, Nat.choose_one_right]
    using h

lemma sum_pairs_containing {V : Finset α} {v : α} (hv : v ∈ V) (f : Finset α → ℕ) :
    degree V 2 f {v} = ∑ u ∈ V.erase v, f {v, u} := by
  rw [degree, ← sum_filter]
  symm
  apply sum_bij (fun u _ => {v, u})
  · intro u hu
    obtain ⟨huv, huV⟩ := mem_erase.mp hu
    apply mem_filter.mpr
    refine ⟨mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
    · simp only [insert_subset_iff, singleton_subset_iff]
      exact ⟨hv, huV⟩
    · simp [Ne.symm huv]
    · simp
  · intro u hu z hz h
    have huv : u ≠ v := (mem_erase.mp hu).1
    have hum : u ∈ ({v, z} : Finset α) := h ▸ mem_insert_of_mem (mem_singleton_self u)
    simpa only [mem_insert, mem_singleton, huv, false_or] using hum
  · intro S hS
    obtain ⟨⟨hSV, hS2⟩, hvS⟩ := by
      simpa only [mem_filter, mem_powersetCard, singleton_subset_iff] using hS
    have hcard : (S.erase v).card = 1 := by
      rw [card_erase_of_mem hvS, hS2]
    obtain ⟨u, hu⟩ := card_eq_one.mp hcard
    have huS : u ∈ S.erase v := hu ▸ mem_singleton_self u
    have huV : u ∈ V.erase v := mem_erase.mpr
      ⟨(mem_erase.mp huS).1, hSV (mem_erase.mp huS).2⟩
    refine ⟨u, huV, ?_⟩
    rw [← insert_erase hvS, hu]
  · intro u _
    rfl

lemma sum_pair_degrees {V : Finset α} {v : α} (hv : v ∈ V)
    (k : ℕ) (w : Finset α → ℕ) :
    (∑ u ∈ V.erase v, degree V k w {v, u}) =
      (k - 1) * degree V k w {v} := by
  rw [← sum_pairs_containing hv]
  have h := degree_degree V {v} k 2 w (by simp)
  simpa only [card_singleton, Nat.reduceSub, Nat.choose_one_right] using h

/-- Neighbours in the support graph of a weighted four-uniform family. -/
def neighbors (V : Finset α) (w : Finset α → ℕ) (v : α) : Finset α :=
  (V.erase v).filter (fun u => 0 < degree V 4 w {v, u})

lemma neighbors_card_le_degree {V : Finset α} {w : Finset α → ℕ} {v : α}
    (hv : v ∈ V) (hp : ∀ P ∈ V.powersetCard 2, 3 ∣ degree V 4 w P) :
    (neighbors V w v).card ≤ degree V 4 w {v} := by
  have hpoint : ∀ u ∈ V.erase v,
      (if 0 < degree V 4 w {v, u} then 3 else 0) ≤ degree V 4 w {v, u} := by
    intro u hu
    by_cases hpos : 0 < degree V 4 w {v, u}
    · rw [if_pos hpos]
      apply Nat.le_of_dvd hpos
      apply hp
      obtain ⟨huv, huV⟩ := mem_erase.mp hu
      apply mem_powersetCard.mpr
      exact ⟨by simp only [insert_subset_iff, singleton_subset_iff]; exact ⟨hv, huV⟩,
        by simp [Ne.symm huv]⟩
    · simp [hpos]
  have h := sum_le_sum hpoint
  rw [← sum_filter, sum_const, smul_eq_mul, sum_pair_degrees hv] at h
  change (neighbors V w v).card * 3 ≤ (4 - 1) * degree V 4 w {v} at h
  omega

lemma erase_subset_neighbors {V S : Finset α} {w : Finset α → ℕ} {v : α}
    (hS : S ∈ V.powersetCard 4) (hvS : v ∈ S) (hwS : 0 < w S) :
    S.erase v ⊆ neighbors V w v := by
  intro u hu
  obtain ⟨huv, huS⟩ := mem_erase.mp hu
  apply mem_filter.mpr
  refine ⟨mem_erase.mpr ⟨huv, (mem_powersetCard.mp hS).1 huS⟩, ?_⟩
  exact lt_of_lt_of_le hwS (weight_le_degree hS (by
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨hvS, huS⟩))

/-- Every active vertex has weighted degree at least four. Pair degrees are
multiples of three; its incident edge supplies three neighbours; its degree is even. -/
lemma surplus_vertex_lower {V : Finset α} {w : Finset α → ℕ}
    (hp : ∀ P ∈ V.powersetCard 2, 3 ∣ degree V 4 w P)
    (he : ∀ v ∈ V, 2 ∣ degree V 4 w {v}) {v : α} (hv : v ∈ V)
    (hpos : 0 < degree V 4 w {v}) :
    4 ≤ degree V 4 w {v} := by
  obtain ⟨S, hS, hvS, hwS⟩ := (degree_pos_iff V {v} 4 w).mp hpos
  have hvS' : v ∈ S := singleton_subset_iff.mp hvS
  have hcard : (S.erase v).card = 3 := by
    rw [card_erase_of_mem hvS', (mem_powersetCard.mp hS).2]
  have hn := card_le_card (erase_subset_neighbors hS hvS' hwS)
  have hd := neighbors_card_le_degree hv hp
  have hev := he v hv
  rw [Nat.dvd_iff_mod_eq_zero] at hev
  omega

lemma total_split_vertex (V : Finset α) (k : ℕ) (w : Finset α → ℕ) (v : α) :
    total V k w = degree V k w {v} +
      ∑ S ∈ V.powersetCard k, if v ∉ S then w S else 0 := by
  simp only [total, degree, ← sum_add_distrib, singleton_subset_iff]
  apply sum_congr rfl
  intro S _
  by_cases hv : v ∈ S <;> simp [hv]

/-- The small surplus obstruction underlying the nine-point odd-cover bound.
Only weighted degrees are used; no classification or exhaustive colouring search occurs. -/
lemma surplus_not_two_or_seven {V : Finset α} {w : Finset α → ℕ}
    (hw : ∀ S ∈ V.powersetCard 4, w S ≤ 2)
    (hp : ∀ P ∈ V.powersetCard 2, 3 ∣ degree V 4 w P)
    (he : ∀ v ∈ V, 2 ∣ degree V 4 w {v}) :
    total V 4 w ≠ 2 ∧ total V 4 w ≠ 7 := by
  constructor
  · intro htwo
    have hpos : 0 < total V 4 w := by omega
    obtain ⟨S, hS, hwS⟩ := sum_pos_iff.mp hpos
    have hScard : S.card = 4 := (mem_powersetCard.mp hS).2
    obtain ⟨v, hvS⟩ := card_pos.mp (show 0 < S.card by omega)
    have hv : v ∈ V := (mem_powersetCard.mp hS).1 hvS
    have hdpos : 0 < degree V 4 w {v} :=
      lt_of_lt_of_le hwS (weight_le_degree hS (singleton_subset_iff.mpr hvS))
    have hlower := surplus_vertex_lower hp he hv hdpos
    have hupper := degree_le_total V 4 w {v}
    omega
  · intro hseven
    have hsum : (∑ v ∈ V, degree V 4 w {v}) = 28 := by
      rw [sum_vertex_degrees, hseven]
    have hex : ∃ v ∈ V, degree V 4 w {v} = 4 := by
      by_contra hnone
      have hdiv : 3 ∣ ∑ v ∈ V, degree V 4 w {v} := by
        apply dvd_sum
        intro v hv
        have hne : degree V 4 w {v} ≠ 4 := fun h => hnone ⟨v, hv, h⟩
        have hupper := degree_le_total V 4 w {v}
        have heven := he v hv
        rw [Nat.dvd_iff_mod_eq_zero] at heven
        have hlower : degree V 4 w {v} = 0 ∨ 4 ≤ degree V 4 w {v} := by
          by_cases hpos : 0 < degree V 4 w {v}
          · exact Or.inr (surplus_vertex_lower hp he hv hpos)
          · exact Or.inl (by omega)
        apply Nat.dvd_of_mod_eq_zero
        omega
      rw [hsum] at hdiv
      norm_num at hdiv
    obtain ⟨v, hv, hd⟩ := hex
    let N := neighbors V w v
    have hNcard : N.card ≤ 4 := by
      simpa only [hd] using neighbors_card_le_degree hv hp
    have hcontained : ∀ S ∈ V.powersetCard 4, v ∉ S → 0 < w S → S ⊆ N := by
      intro S hS hvS hwS u huS
      have hu : u ∈ V := (mem_powersetCard.mp hS).1 huS
      have huv : u ≠ v := by rintro rfl; exact hvS huS
      by_contra huN
      have hpair : degree V 4 w {v, u} = 0 := by
        have hnot : ¬ 0 < degree V 4 w {v, u} := by
          intro hpos
          exact huN (mem_filter.mpr ⟨mem_erase.mpr ⟨huv, hu⟩, hpos⟩)
        omega
      have hdu : 0 < degree V 4 w {u} :=
        lt_of_lt_of_le hwS (weight_le_degree hS (singleton_subset_iff.mpr huS))
      have hlo := surplus_vertex_lower hp he hu hdu
      have hinc := degree_union_le V 4 w {v} {u}
      simp only [singleton_union, hd, hseven, hpair, add_zero] at hinc
      omega
    have hrest : (∑ S ∈ V.powersetCard 4, if v ∉ S then w S else 0) = 3 := by
      have hsplit := total_split_vertex V 4 w v
      rw [hseven, hd] at hsplit
      omega
    have hrestpos : 0 < ∑ S ∈ V.powersetCard 4, if v ∉ S then w S else 0 := by omega
    obtain ⟨S, hS, hpos⟩ := sum_pos_iff.mp hrestpos
    have hvS : v ∉ S := by
      by_contra h
      simp [h] at hpos
    have hwS : 0 < w S := by simpa [hvS] using hpos
    have hSN : S = N := eq_of_subset_of_card_le (hcontained S hS hvS hwS)
      (by rw [(mem_powersetCard.mp hS).2]; exact hNcard)
    have hsingle : (∑ T ∈ V.powersetCard 4, if v ∉ T then w T else 0) = w S := by
      rw [sum_eq_single_of_mem S hS]
      · simp [hvS]
      · intro T hT hTS
        by_cases hvT : v ∉ T
        · by_cases hwT : 0 < w T
          · have hTN : T = N := eq_of_subset_of_card_le (hcontained T hT hvT hwT)
              (by rw [(mem_powersetCard.mp hT).2]; exact hNcard)
            exact (hTS (hTN.trans hSN.symm)).elim
          · simp [hvT, show w T = 0 by omega]
        · simp [hvT]
    have hbound := hw S hS
    omega

lemma degree_le_one {V : Finset α} {k : ℕ} {w : Finset α → ℕ}
    (hw : ∀ S ∈ V.powersetCard k, w S ≤ 1) (P : Finset α) :
    degree V k w P ≤ degree V k (fun _ => 1) P := by
  apply sum_le_sum
  intro S hS
  by_cases hPS : P ⊆ S
  · simpa [hPS] using hw S hS
  · simp [hPS]

/-- An odd `(9,5,4)` cover has at least thirty blocks. This also holds for
zero-one weights, so no separate family representation is required. -/
theorem odd_cover_nine (V : Finset α) (hV : V.card = 9) (b : Finset α → ℕ)
    (hb : ∀ S ∈ V.powersetCard 5, b S ≤ 1)
    (ho : ∀ T ∈ V.powersetCard 4, Odd (degree V 5 b T)) :
    30 ≤ total V 5 b := by
  let w : Finset α → ℕ := fun T => (degree V 5 b T - 1) / 2
  have hs : ∀ T ∈ V.powersetCard 4,
      degree V 5 b T = 1 + 2 * w T ∧ w T ≤ 2 := by
    intro T hT
    obtain ⟨hTV, hT4⟩ := mem_powersetCard.mp hT
    have hbound := degree_le_one hb T
    rw [degree_one V T 5 hTV (by omega), hV, hT4] at hbound
    norm_num at hbound
    obtain ⟨j, hj⟩ := ho T hT
    dsimp only [w]
    omega
  have hlinear : ∀ P : Finset α, P ⊆ V → P.card ≤ 4 →
      degree V 4 (fun T => degree V 5 b T) P =
        (V.card - P.card).choose (4 - P.card) + 2 * degree V 4 w P := by
    intro P hPV hP4
    rw [degree_congr V 4 (fun T => degree V 5 b T) (fun T => 1 + 2 * w T) P
      (fun T hT _ => (hs T hT).1)]
    rw [degree_add, degree_mul, degree_one V P 4 hPV hP4]
  have htotal : 5 * total V 5 b = 126 + 2 * total V 4 w := by
    have hd := degree_degree V ∅ 5 4 b (by simp)
    have ha := hlinear ∅ (empty_subset _) (by simp)
    norm_num [degree_empty, hV, Nat.choose] at hd ha
    omega
  have hp : ∀ P ∈ V.powersetCard 2, 3 ∣ degree V 4 w P := by
    intro P hP
    obtain ⟨hPV, hP2⟩ := mem_powersetCard.mp hP
    have hd := degree_degree V P 5 4 b (by omega)
    have ha := hlinear P hPV (by omega)
    norm_num [hV, hP2, Nat.choose] at hd ha
    apply Nat.dvd_of_mod_eq_zero
    omega
  have he : ∀ v ∈ V, 2 ∣ degree V 4 w {v} := by
    intro v hv
    have hd := degree_degree V {v} 5 4 b (by simp)
    have ha := hlinear {v} (singleton_subset_iff.mpr hv) (by simp)
    norm_num [hV, Nat.choose] at hd ha
    apply Nat.dvd_of_mod_eq_zero
    omega
  have hnot := surplus_not_two_or_seven (fun T hT => (hs T hT).2) hp he
  omega

/-- Taking complements turns an incidence degree into a total on the
complement of the prescribed set. -/
lemma degree_complement (V P : Finset α) (k : ℕ) (w : Finset α → ℕ)
    (hPV : P ⊆ V) (hk : k ≤ V.card) :
    degree V k (fun S => w (V \ S)) P = total (V \ P) (V.card - k) w := by
  rw [degree, ← sum_filter]
  apply sum_bij (fun S _ => V \ S)
  · intro S hS
    obtain ⟨⟨hSV, hSk⟩, hPS⟩ := by
      simpa only [mem_filter, mem_powersetCard] using hS
    apply mem_powersetCard.mpr
    exact ⟨sdiff_subset_sdiff (Subset.refl _) hPS,
      by rw [card_sdiff_of_subset hSV, hSk]⟩
  · intro S hS T hT heq
    have hSV := (mem_powersetCard.mp (mem_filter.mp hS).1).1
    have hTV := (mem_powersetCard.mp (mem_filter.mp hT).1).1
    calc
      S = V \ (V \ S) := (Finset.sdiff_sdiff_eq_self hSV).symm
      _ = V \ (V \ T) := by rw [heq]
      _ = T := Finset.sdiff_sdiff_eq_self hTV
  · intro T hT
    obtain ⟨hTP, hTcard⟩ := mem_powersetCard.mp hT
    have hTV : T ⊆ V := hTP.trans sdiff_subset
    have hcard : (V \ T).card = k := by
      rw [card_sdiff_of_subset hTV, hTcard]
      omega
    have hsub : P ⊆ V \ T := by
      intro x hx
      apply mem_sdiff.mpr
      refine ⟨hPV hx, ?_⟩
      intro hxT
      exact (mem_sdiff.mp (hTP hxT)).2 hx
    refine ⟨V \ T, mem_filter.mpr ⟨mem_powersetCard.mpr ⟨sdiff_subset, hcard⟩, hsub⟩,
      Finset.sdiff_sdiff_eq_self hTV⟩
  · intro S _
    rfl

/-- Indicator weight of one colour. -/
def colorWeight (c : Finset α → Bool) (color : Bool) (e : Finset α) : ℕ :=
  if c e = color then 1 else 0

/-- Indicator of a balanced quadruple. -/
def balanced (c : Finset α → Bool) (Q : Finset α) : ℕ :=
  if total Q 3 (colorWeight c true) = 2 then 1 else 0

/-- A colouring with no monochromatic quadruple in the given vertex set. -/
def NoMonoFour (c : Finset α → Bool) (V : Finset α) : Prop :=
  ∀ Q ∈ V.powersetCard 4, ∀ color : Bool, ¬ ∀ e ∈ Q.powersetCard 3, c e = color

omit [DecidableEq α] in
lemma NoMonoFour.mono {c : Finset α → Bool} {V U : Finset α}
    (hc : NoMonoFour c V) (hUV : U ⊆ V) : NoMonoFour c U := by
  intro Q hQ color
  exact hc Q (powersetCard_mono hUV hQ) color

omit [DecidableEq α] in
lemma colorWeight_le_one (c : Finset α → Bool) (color : Bool) (e : Finset α) :
    colorWeight c color e ≤ 1 := by
  unfold colorWeight
  split_ifs <;> omega

omit [DecidableEq α] in
lemma colorWeight_add (c : Finset α → Bool) (e : Finset α) :
    colorWeight c true e + colorWeight c false e = 1 := by
  cases h : c e <;> simp [colorWeight, h]

omit [DecidableEq α] in
lemma colorWeight_mul (c : Finset α → Bool) (e : Finset α) :
    colorWeight c true e * colorWeight c false e = 0 := by
  cases h : c e <;> simp [colorWeight, h]

omit [DecidableEq α] in
lemma total_color_eq_card (c : Finset α → Bool) (color : Bool) (S : Finset α) (k : ℕ) :
    total S k (colorWeight c color) = ((S.powersetCard k).filter (fun e => c e = color)).card := by
  exact sum_boole _ _

omit [DecidableEq α] in
lemma total_colors_add (c : Finset α → Bool) (S : Finset α) (k : ℕ) :
    total S k (colorWeight c true) + total S k (colorWeight c false) = S.card.choose k := by
  simp only [total, ← sum_add_distrib, colorWeight_add, sum_const, smul_eq_mul, mul_one,
    card_powersetCard]

omit [DecidableEq α] in
lemma noMono_red_count {c : Finset α → Bool} {V Q : Finset α}
    (hc : NoMonoFour c V) (hQ : Q ∈ V.powersetCard 4) :
    total Q 3 (colorWeight c true) = 1 ∨
      total Q 3 (colorWeight c true) = 2 ∨ total Q 3 (colorWeight c true) = 3 := by
  have hQ4 := (mem_powersetCard.mp hQ).2
  have hcard : (Q.powersetCard 3).card = 4 := by simp [hQ4]
  rw [total_color_eq_card]
  let F := (Q.powersetCard 3).filter (fun e => c e = true)
  have hbound : F.card ≤ 4 := (card_le_card (filter_subset _ _)).trans hcard.le
  have hzero : F.card ≠ 0 := by
    intro h
    have hempty : F = ∅ := card_eq_zero.mp h
    apply hc Q hQ false
    intro e he
    cases hcolor : c e with
    | false => rfl
    | true =>
      have heF : e ∈ F := mem_filter.mpr ⟨he, hcolor⟩
      simp [hempty] at heF
  have hfour : F.card ≠ 4 := by
    intro h
    have hF : F = Q.powersetCard 3 := eq_of_subset_of_card_le (filter_subset _ _)
      (by rw [hcard, h])
    apply hc Q hQ true
    intro e he
    have heF : e ∈ (Q.powersetCard 3).filter (fun e => c e = true) := by
      change e ∈ F
      rw [hF]
      exact he
    exact (mem_filter.mp heF).2
  change F.card = 1 ∨ F.card = 2 ∨ F.card = 3
  omega

omit [DecidableEq α] in
lemma balanced_le_one (c : Finset α → Bool) (Q : Finset α) : balanced c Q ≤ 1 := by
  unfold balanced
  split_ifs <;> omega

/-- Each five-set contains an odd number of balanced quadruples. Each triple
occurs twice in the sum of the red counts of its five quadruples. -/
lemma balanced_odd_five {c : Finset α → Bool} {V : Finset α}
    (hV : V.card = 5) (hc : NoMonoFour c V) : Odd (total V 4 (balanced c)) := by
  have hcounts := sum_totals_subsets V 4 3 (colorWeight c true) (by decide)
  norm_num [hV] at hcounts
  have hpoint : ∀ Q ∈ V.powersetCard 4,
      total Q 3 (colorWeight c true) = 1 + balanced c Q +
        2 * (if total Q 3 (colorWeight c true) = 3 then 1 else 0) := by
    intro Q hQ
    rcases noMono_red_count hc hQ with h | h | h <;> simp [balanced, h]
  have hsum : (∑ Q ∈ V.powersetCard 4, total Q 3 (colorWeight c true)) =
      5 + total V 4 (balanced c) +
        2 * ∑ Q ∈ V.powersetCard 4, if total Q 3 (colorWeight c true) = 3 then 1 else 0 := by
    calc
      _ = ∑ Q ∈ V.powersetCard 4, (1 + balanced c Q +
          2 * (if total Q 3 (colorWeight c true) = 3 then 1 else 0)) :=
        sum_congr rfl hpoint
      _ = _ := by
        simp only [sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul, mul_one,
          card_powersetCard, hV, total]
        norm_num
  refine ⟨total V 4 (balanced c) / 2, ?_⟩
  omega

/-- The local lower bound: at least thirty balanced quadruples on nine vertices. -/
theorem balanced_nine {c : Finset α → Bool} {V : Finset α}
    (hV : V.card = 9) (hc : NoMonoFour c V) : 30 ≤ total V 4 (balanced c) := by
  let b : Finset α → ℕ := fun S => balanced c (V \ S)
  have hb : ∀ S ∈ V.powersetCard 5, b S ≤ 1 := by
    intro S _
    exact balanced_le_one c (V \ S)
  have ho : ∀ T ∈ V.powersetCard 4, Odd (degree V 5 b T) := by
    intro T hT
    obtain ⟨hTV, hT4⟩ := mem_powersetCard.mp hT
    have hcomp : (V \ T).card = 5 := by
      rw [card_sdiff_of_subset hTV, hV, hT4]
    have hodd := balanced_odd_five hcomp (hc.mono sdiff_subset)
    have hdeg := degree_complement V T 5 (balanced c) hTV (by omega)
    change Odd (degree V 5 (fun S => balanced c (V \ S)) T)
    rw [hdeg]
    simpa only [hV, Nat.reduceSub] using hodd
  have h := odd_cover_nine V hV b hb ho
  have hcomp := degree_complement V ∅ 5 (balanced c) (empty_subset _) (by omega)
  have heq : total V 5 b = total V 4 (balanced c) := by
    simpa only [degree_empty, sdiff_empty, hV, Nat.reduceSub] using hcomp
  rwa [heq] at h

/-- The local lower bound, averaged over all nine-subsets of fifteen vertices. -/
theorem balanced_lower_fifteen {c : Finset α → Bool} {V : Finset α}
    (hV : V.card = 15) (hc : NoMonoFour c V) : 325 ≤ total V 4 (balanced c) := by
  have hsum : (∑ A ∈ V.powersetCard 9, 30) ≤
      ∑ A ∈ V.powersetCard 9, total A 4 (balanced c) := by
    apply sum_le_sum
    intro A hA
    obtain ⟨hAV, hA9⟩ := mem_powersetCard.mp hA
    exact balanced_nine hA9 (hc.mono hAV)
  have hid := sum_totals_subsets V 9 4 (balanced c) (by decide)
  norm_num [hV, Nat.choose] at hid
  norm_num [hV, Nat.choose] at hsum
  omega

/-- Two distinct triples share a two-set exactly when their union is a four-set.
Both incidence families then consist of one set; otherwise both are empty. -/
lemma common_pair_quad_card {V A B : Finset α}
    (hA : A ∈ V.powersetCard 3) (hB : B ∈ V.powersetCard 3) (hne : A ≠ B) :
    ((V.powersetCard 2).filter (fun P => P ⊆ A ∧ P ⊆ B)).card =
      ((V.powersetCard 4).filter (fun Q => A ⊆ Q ∧ B ⊆ Q)).card := by
  obtain ⟨hAV, hA3⟩ := mem_powersetCard.mp hA
  obtain ⟨hBV, hB3⟩ := mem_powersetCard.mp hB
  have hI : (A ∩ B).card ≤ 2 := by
    have hle : (A ∩ B).card ≤ 3 := (card_le_card inter_subset_left).trans hA3.le
    by_contra hn
    have heA : A ∩ B = A := eq_of_subset_of_card_le inter_subset_left (by omega)
    have heB : A ∩ B = B := eq_of_subset_of_card_le inter_subset_right (by omega)
    exact hne (heA.symm.trans heB)
  have hU := card_union_add_card_inter A B
  rw [hA3, hB3] at hU
  by_cases hI2 : (A ∩ B).card = 2
  · have hU4 : (A ∪ B).card = 4 := by omega
    have hleft : (V.powersetCard 2).filter (fun P => P ⊆ A ∧ P ⊆ B) = {A ∩ B} := by
      ext P
      simp only [mem_filter, mem_powersetCard, mem_singleton]
      constructor
      · rintro ⟨⟨_, hP2⟩, hPA, hPB⟩
        exact eq_of_subset_of_card_le (subset_inter hPA hPB) (by omega)
      · rintro rfl
        exact ⟨⟨inter_subset_left.trans hAV, hI2⟩, inter_subset_left, inter_subset_right⟩
    have hright : (V.powersetCard 4).filter (fun Q => A ⊆ Q ∧ B ⊆ Q) = {A ∪ B} := by
      ext Q
      simp only [mem_filter, mem_powersetCard, mem_singleton]
      constructor
      · rintro ⟨⟨_, hQ4⟩, hAQ, hBQ⟩
        exact (eq_of_subset_of_card_le (union_subset hAQ hBQ) (by omega)).symm
      · rintro rfl
        exact ⟨⟨union_subset hAV hBV, hU4⟩, subset_union_left, subset_union_right⟩
    simp only [hleft, hright, card_singleton]
  · have hI1 : (A ∩ B).card ≤ 1 := by omega
    have hU5 : 5 ≤ (A ∪ B).card := by omega
    have hleft : (V.powersetCard 2).filter (fun P => P ⊆ A ∧ P ⊆ B) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro P hP
      obtain ⟨⟨_, hP2⟩, hPA, hPB⟩ := by
        simpa only [mem_filter, mem_powersetCard] using hP
      have hle := card_le_card (subset_inter hPA hPB)
      omega
    have hright : (V.powersetCard 4).filter (fun Q => A ⊆ Q ∧ B ⊆ Q) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro Q hQ
      obtain ⟨⟨_, hQ4⟩, hAQ, hBQ⟩ := by
        simpa only [mem_filter, mem_powersetCard] using hQ
      have hle := card_le_card (union_subset hAQ hBQ)
      omega
    rw [hleft, hright]

lemma degree_mul_expand (V P : Finset α) (k : ℕ) (w z : Finset α → ℕ) :
    degree V k w P * degree V k z P =
      ∑ A ∈ V.powersetCard k, ∑ B ∈ V.powersetCard k,
        if P ⊆ A ∧ P ⊆ B then w A * z B else 0 := by
  simp only [degree, sum_mul_sum]
  apply sum_congr rfl
  intro A _
  apply sum_congr rfl
  intro B _
  by_cases hPA : P ⊆ A <;> by_cases hPB : P ⊆ B <;> simp [hPA, hPB]

lemma total_mul_expand (V Q : Finset α) (k : ℕ) (w z : Finset α → ℕ) (hQV : Q ⊆ V) :
    total Q k w * total Q k z =
      ∑ A ∈ V.powersetCard k, ∑ B ∈ V.powersetCard k,
        if A ⊆ Q ∧ B ⊆ Q then w A * z B else 0 := by
  rw [total_restrict V Q k w hQV, total_restrict V Q k z hQV, sum_mul_sum]
  apply sum_congr rfl
  intro A _
  apply sum_congr rfl
  intro B _
  by_cases hAQ : A ⊆ Q <;> by_cases hBQ : B ⊆ Q <;> simp [hAQ, hBQ]

/-- Count mixed pairs of triples by their common pair or by their union quadruple. -/
lemma mixed_triple_count (V : Finset α) (w z : Finset α → ℕ)
    (ho : ∀ A ∈ V.powersetCard 3, w A * z A = 0) :
    (∑ P ∈ V.powersetCard 2, degree V 3 w P * degree V 3 z P) =
      ∑ Q ∈ V.powersetCard 4, total Q 3 w * total Q 3 z := by
  calc
    _ = ∑ P ∈ V.powersetCard 2, ∑ A ∈ V.powersetCard 3, ∑ B ∈ V.powersetCard 3,
        if P ⊆ A ∧ P ⊆ B then w A * z B else 0 := by
      apply sum_congr rfl
      intro P _
      exact degree_mul_expand V P 3 w z
    _ = ∑ A ∈ V.powersetCard 3, ∑ B ∈ V.powersetCard 3, ∑ P ∈ V.powersetCard 2,
        if P ⊆ A ∧ P ⊆ B then w A * z B else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro A _
      rw [sum_comm]
    _ = ∑ A ∈ V.powersetCard 3, ∑ B ∈ V.powersetCard 3, ∑ Q ∈ V.powersetCard 4,
        if A ⊆ Q ∧ B ⊆ Q then w A * z B else 0 := by
      apply sum_congr rfl
      intro A hA
      apply sum_congr rfl
      intro B hB
      by_cases hAB : A = B
      · subst B
        simp only [ho A hA, ite_self, sum_const_zero]
      · rw [← sum_filter, ← sum_filter, sum_const, sum_const, smul_eq_mul, smul_eq_mul]
        rw [common_pair_quad_card hA hB hAB]
    _ = ∑ Q ∈ V.powersetCard 4, ∑ A ∈ V.powersetCard 3, ∑ B ∈ V.powersetCard 3,
        if A ⊆ Q ∧ B ⊆ Q then w A * z B else 0 := by
      symm
      rw [sum_comm]
      apply sum_congr rfl
      intro A _
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro Q hQ
      exact (total_mul_expand V Q 3 w z (mem_powersetCard.mp hQ).1).symm

lemma degree_colors_add (c : Finset α → Bool) (V P : Finset α)
    (hPV : P ⊆ V) (hP3 : P.card ≤ 3) :
    degree V 3 (colorWeight c true) P + degree V 3 (colorWeight c false) P =
      (V.card - P.card).choose (3 - P.card) := by
  rw [← degree_add]
  rw [degree_congr V 3 (fun S => colorWeight c true S + colorWeight c false S)
    (fun _ => 1) P (fun S _ _ => colorWeight_add c S)]
  exact degree_one V P 3 hPV hP3

omit [DecidableEq α] in
lemma quadruple_mixed_value {c : Finset α → Bool} {V Q : Finset α}
    (hc : NoMonoFour c V) (hQ : Q ∈ V.powersetCard 4) :
    total Q 3 (colorWeight c true) * total Q 3 (colorWeight c false) = 3 + balanced c Q := by
  have hsum := total_colors_add c Q 3
  rw [(mem_powersetCard.mp hQ).2] at hsum
  norm_num at hsum
  rcases noMono_red_count hc hQ with h | h | h <;>
    simp only [balanced, h] <;> norm_num <;> omega

/-- With thirteen possible third vertices the largest mixed-pair product is `6 * 7`. -/
lemma product_le_fortytwo {a b : ℕ} (h : a + b = 13) : a * b ≤ 42 := by
  have hZ : (a : ℤ) + (b : ℤ) = 13 := by exact_mod_cast h
  have hsplit : a ≤ 6 ∨ 7 ≤ a := by omega
  have hprod : (a : ℤ) * (b : ℤ) ≤ 42 := by
    rcases hsplit with hsmall | hlarge
    · have hnonneg : 0 ≤ (6 - (a : ℤ)) * (7 - (a : ℤ)) :=
        mul_nonneg (by omega) (by omega)
      nlinarith
    · have hnonneg : 0 ≤ ((a : ℤ) - 6) * ((a : ℤ) - 7) :=
        mul_nonneg (by omega) (by omega)
      nlinarith
  exact_mod_cast hprod

/-- The global upper bound from counting mixed pairs of incident triples. -/
theorem balanced_upper_fifteen {c : Finset α → Bool} {V : Finset α}
    (hV : V.card = 15) (hc : NoMonoFour c V) : total V 4 (balanced c) ≤ 315 := by
  have hcount := mixed_triple_count V (colorWeight c true) (colorWeight c false)
    (fun A _ => colorWeight_mul c A)
  have hupper : (∑ P ∈ V.powersetCard 2,
      degree V 3 (colorWeight c true) P * degree V 3 (colorWeight c false) P) ≤
        ∑ P ∈ V.powersetCard 2, 42 := by
    apply sum_le_sum
    intro P hP
    obtain ⟨hPV, hP2⟩ := mem_powersetCard.mp hP
    have hsum := degree_colors_add c V P hPV (by omega)
    norm_num [hV, hP2] at hsum
    exact product_le_fortytwo hsum
  norm_num [hV, Nat.choose] at hupper
  have hquad : (∑ Q ∈ V.powersetCard 4,
      total Q 3 (colorWeight c true) * total Q 3 (colorWeight c false)) =
        4095 + total V 4 (balanced c) := by
    calc
      _ = ∑ Q ∈ V.powersetCard 4, (3 + balanced c Q) :=
        sum_congr rfl (fun Q hQ => quadruple_mixed_value hc hQ)
      _ = _ := by
        simp only [sum_add_distrib, sum_const, smul_eq_mul, card_powersetCard, hV]
        change (15 : ℕ).choose 4 * 3 + total V 4 (balanced c) = _
        norm_num [Nat.choose]
  omega

/-- The two balanced-quadruple counts are incompatible on fifteen vertices. -/
theorem not_noMonoFour_fifteen {c : Finset α → Bool} {V : Finset α}
    (hV : V.card = 15) : ¬ NoMonoFour c V := by
  intro hc
  have hlo := balanced_lower_fifteen hV hc
  have hup := balanced_upper_fifteen hV hc
  omega

/-- Every two-colouring of triples on fifteen vertices has a monochromatic four-set. -/
theorem exists_monochromatic_four (c : Finset α → Bool) (V : Finset α) (hV : V.card = 15) :
    ∃ S ⊆ V, S.card = 4 ∧ ∃ color : Bool, ∀ e ⊆ S, e.card = 3 → c e = color := by
  classical
  by_contra hnone
  apply not_noMonoFour_fifteen hV
  intro Q hQ color hmono
  obtain ⟨hQV, hQ4⟩ := mem_powersetCard.mp hQ
  apply hnone
  refine ⟨Q, hQV, hQ4, color, ?_⟩
  intro e he hcard
  exact hmono e (mem_powersetCard.mpr ⟨he, hcard⟩)

end Counting

/-- The seed bound in the universe-polymorphic Ramsey interface. -/
theorem hasUniformRamseyProperty_three_fifteen :
    RamseyTools.HasUniformRamseyProperty.{u} 3 15 4 4 := by
  classical
  intro α c V hV
  obtain ⟨U, hUV, hU15⟩ := Finset.exists_subset_card_eq hV
  obtain ⟨S, hSU, hS4, color, hmono⟩ := exists_monochromatic_four c U hU15
  cases color with
  | false => exact Or.inl ⟨S, hSU.trans hUV, hS4, hmono⟩
  | true => exact Or.inr ⟨S, hSU.trans hUV, hS4, hmono⟩

/-- The exact witness required by the definition of `hypergraphRamsey`. -/
theorem ramsey_three_four_fifteen_witness : HypergraphRamseyWitness 3 4 15 := by
  intro c
  rcases hasUniformRamseyProperty_three_fifteen.{0} c (Finset.univ : Finset (Fin 15))
      (by simp) with ⟨S, _, hS4, hmono⟩ | ⟨S, _, hS4, hmono⟩
  · exact ⟨S, hS4, false, hmono⟩
  · exact ⟨S, hS4, true, hmono⟩

/-- A structural, non-computational proof of `R₃(4) ≤ 15`. -/
theorem hypergraphRamsey_three_four_le_fifteen : hypergraphRamsey 3 4 ≤ 15 :=
  (hypergraphRamsey_le_iff 3 4 15).mpr ramsey_three_four_fifteen_witness

/-- The seed remains strictly subcritical for the potential exponent twelve:
`15 * 4096 = 61440 < 65536`. This proves no recurrence. -/
theorem weighted_seed : hypergraphRamsey 3 4 * 2 ^ 12 < 2 ^ (2 ^ 4) := by
  have h := Nat.mul_le_mul_right (2 ^ 12) hypergraphRamsey_three_four_le_fifteen
  norm_num at h ⊢
  omega

end Combinatorics.SmallRamsey
