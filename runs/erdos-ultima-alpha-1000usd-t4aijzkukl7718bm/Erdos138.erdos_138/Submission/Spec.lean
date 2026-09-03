import FormalConjecturesUtil

/-!
# Erdős Problem 138

*References:*
- [erdosproblems.com/138](https://www.erdosproblems.com/138)
- [Be68] Berlekamp, E. R., A construction for partitions which avoid long arithmetic progressions. Canad. Math. Bull. (1968), 409-414.
- [Er80] Erdős, Paul, A survey of problems in combinatorial number theory. Ann. Discrete Math. (1980), 89-115.
- [Er81] Erdős, P., On the combinatorial problems which I would most like to see solved. Combinatorica (1981), 25-42.
- [Go01] Gowers, W. T., A new proof of Szemerédi's theorem. Geom. Funct. Anal. (2001), 465-588.
-/

open Nat Filter

namespace Erdos138

/--
The set of natural numbers that guarantee a monochromatic arithmetic progression.

A number `N` belongs to this set if, for a given number of colors `r` and an arithmetic
progression length `k`, any `r`-coloring of the integers `{1, ..., N}` must contain a
monochromatic arithmetic progression of length `k`.
-/
def monoAP_guarantee_set (r k : ℕ) : Set ℕ :=
  { N | ∀ coloring : Finset.Icc 1 N → Fin r, ContainsMonoAPofLength coloring k}

/--
The **van der Waerden number**, is the smallest integer `N` such that any `r`-coloring of
`{1, ..., N}` is guaranteed to contain a monochromatic arithmetic progression of
length `k`. It is defined as the infimum of the (non-empty) set of all such numbers `N`.
-/
noncomputable def monoAPNumber (r k : ℕ) : ℕ := sInf (monoAP_guarantee_set r k)

/--
An abbreviation for the van der Waerden number for 2 colors, commonly written as `W(k)`.
This represents the smallest integer `N` such that any 2-coloring of `{1, ..., N}`
must contain a monochromatic arithmetic progression of length `k`.
-/
noncomputable abbrev W : ℕ → ℕ := monoAPNumber 2


lemma length_le_of_guarantee {k N : ℕ} (h : N ∈ monoAP_guarantee_set 2 k) : k ≤ N := by
  obtain ⟨c, ap, hp, hc⟩ := h (fun _ ↦ (0 : Fin 2))
  have hs : Subtype.val '' ap ⊆ (Finset.Icc 1 N : Set ℕ) := by
    rintro _ ⟨x, hx, rfl⟩
    exact x.property
  have he := Set.encard_mono hs
  rw [← ENat.card_coe_set_eq, hp.card] at he
  simpa only [Set.encard_coe_eq_coe_finsetCard, Nat.card_Icc, Nat.cast_le] using he


lemma range_isAP {k a d : ℕ} (hd : 0 < d) :
    (Set.range (fun i : Fin k ↦ a + (i : ℕ) * d)).IsAPOfLength k := by
  refine ⟨a, d, ?_, ?_⟩
  · have hi : Function.Injective (fun i : Fin k ↦ a + (i : ℕ) * d) := by
      intro x y h
      apply Fin.ext
      exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel h)
    rw [ENat.card_coe_set_eq, ← Set.image_univ, hi.encard_image, Set.encard_univ,
      ENat.card_eq_coe_fintype_card]
    simp
  · ext x
    simp only [Set.mem_range, Set.mem_setOf_eq, nsmul_eq_mul, Nat.cast_lt]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.isLt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩

lemma guarantee_nonempty (k : ℕ) : (monoAP_guarantee_set 2 k).Nonempty := by
  classical
  obtain ⟨ι, fi, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin k) (Fin 2)
  let N := 1 + Fintype.card ι * k
  refine ⟨N, ?_⟩
  intro C
  let f : (ι → Fin k) → Finset.Icc 1 N := fun v ↦ ⟨1 + ∑ i, (v i : ℕ), by
    apply Finset.mem_Icc.mpr
    constructor
    · omega
    · dsimp [N]
      apply Nat.add_le_add_left
      calc
        (∑ i, (v i : ℕ)) ≤ ∑ _i : ι, k := Finset.sum_le_sum (fun i _ ↦ (v i).isLt.le)
        _ = Fintype.card ι * k := by simp⟩
  obtain ⟨l, c, hl⟩ := hι (C ∘ f)
  let s : Finset ι := {i | l.idxFun i = none}
  let a := 1 + ∑ i ∈ sᶜ, ((l.idxFun i).map (fun x : Fin k ↦ (x : ℕ))).getD 0
  let d := s.card
  have hd : 0 < d := by
    apply Finset.card_pos.mpr
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨i, by simp [s, hi]⟩
  have hf (x : Fin k) : (f (l x) : ℕ) = a + (x : ℕ) * d := by
    change 1 + ∑ i, (l x i : ℕ) = _
    rw [← Finset.sum_add_sum_compl s]
    have hs : ∑ i ∈ s, (l x i : ℕ) = d * (x : ℕ) := by
      calc
        _ = ∑ _i ∈ s, (x : ℕ) := Finset.sum_congr rfl (fun i hi ↦ by
          rw [l.apply_none x i (by simpa [s] using hi)])
        _ = _ := by simp [d]
    have hc : ∑ i ∈ sᶜ, (l x i : ℕ) = a - 1 := by
      dsimp [a]
      simp only [Nat.add_sub_cancel_left]
      apply Finset.sum_congr rfl
      intro i hi
      have hn : l.idxFun i ≠ none := by simpa [s] using hi
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp hn
      simp [← hy]
    rw [hs, hc, Nat.mul_comm d]
    dsimp [a]
    omega
  refine ⟨c, Set.range (fun x : Fin k ↦ f (l x)), ?_, ?_⟩
  · have he : Subtype.val '' Set.range (fun x : Fin k ↦ f (l x)) =
        Set.range (fun x : Fin k ↦ a + (x : ℕ) * d) := by
      rw [← Set.range_comp]
      congr 1
      funext x
      exact hf x
    change (Subtype.val '' Set.range (fun x : Fin k ↦ f (l x))).IsAPOfLength k
    rw [he]
    exact range_isAP hd
  · rintro _ ⟨x, rfl⟩
    exact hl x

lemma le_W (k : ℕ) : k ≤ W k :=
  length_le_of_guarantee (Nat.sInf_mem (guarantee_nonempty k))


lemma root_ge_iff {b : ℝ} (hb : 0 ≤ b) {k : ℕ} (hk : 0 < k) :
    b ≤ (W k : ℝ) ^ (1 / (k : ℝ)) ↔ b ^ k ≤ (W k : ℝ) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  simpa only [one_div, Real.rpow_natCast] using
    Real.le_rpow_inv_iff_of_pos hb (show (0 : ℝ) ≤ W k by positivity) hk'

lemma root_tendsto_iff :
    Tendsto (fun k ↦ (W k : ℝ) ^ (1 / (k : ℝ))) atTop atTop ↔
      ∀ b : ℝ, 0 ≤ b → ∀ᶠ k : ℕ in atTop, b ^ k ≤ (W k : ℝ) := by
  constructor
  · intro h b hb
    filter_upwards [h.eventually_ge_atTop b, eventually_gt_atTop 0] with k hkb hk
    exact (root_ge_iff hb hk).mp hkb
  · intro h
    apply tendsto_atTop.2
    intro b
    filter_upwards [h (max b 0) (le_max_right _ _), eventually_gt_atTop 0] with k hkb hk
    exact (le_max_left b 0).trans ((root_ge_iff (le_max_right b 0) hk).mpr hkb)

lemma W_tendsto : Tendsto W atTop atTop :=
  Filter.tendsto_atTop_mono le_W tendsto_id


lemma guarantee_mono {r k M N : ℕ} (hMN : M ≤ N)
    (hM : M ∈ monoAP_guarantee_set r k) : N ∈ monoAP_guarantee_set r k := by
  intro C
  let f : Finset.Icc 1 M → Finset.Icc 1 N := fun x ↦
    ⟨x.val, Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp x.property).1, (Finset.mem_Icc.mp x.property).2.trans hMN⟩⟩
  obtain ⟨c, ap, hp, hc⟩ := hM (C ∘ f)
  refine ⟨c, f '' ap, ?_, ?_⟩
  · change (Subtype.val '' (f '' ap)).IsAPOfLength k
    rw [Set.image_image]
    exact hp
  · rintro _ ⟨x, hx, rfl⟩
    exact hc x hx

lemma W_le_iff_guarantee {k N : ℕ} : W k ≤ N ↔ N ∈ monoAP_guarantee_set 2 k := by
  constructor
  · intro h
    exact guarantee_mono h (Nat.sInf_mem (guarantee_nonempty k))
  · intro h
    exact Nat.sInf_le h

lemma lt_W_iff_avoiding {k N : ℕ} :
    N < W k ↔ ∃ C : Finset.Icc 1 N → Fin 2, ¬ ContainsMonoAPofLength C k := by
  rw [← not_le, W_le_iff_guarantee]
  simp only [monoAP_guarantee_set, Set.mem_setOf_eq, not_forall]

lemma root_tendsto_iff_avoiding :
    Tendsto (fun k ↦ (W k : ℝ) ^ (1 / (k : ℝ))) atTop atTop ↔
      ∀ b : ℕ, ∀ᶠ k : ℕ in atTop,
        ∃ C : Finset.Icc 1 (b ^ k) → Fin 2, ¬ ContainsMonoAPofLength C k := by
  constructor
  · intro h b
    filter_upwards [h.eventually_gt_atTop (b : ℝ), eventually_gt_atTop 0] with k hkb hk
    apply lt_W_iff_avoiding.mp
    have hr : (0 : ℝ) < k := by exact_mod_cast hk
    have hh := (Real.lt_rpow_inv_iff_of_pos (Nat.cast_nonneg b)
      (Nat.cast_nonneg (W k)) hr).mp (by simpa only [one_div] using hkb)
    rw [Real.rpow_natCast, ← Nat.cast_pow] at hh
    exact_mod_cast hh
  · intro h
    apply root_tendsto_iff.mpr
    intro b hb
    obtain ⟨n, hn⟩ := exists_nat_ge b
    filter_upwards [h n] with k hk
    have ht : n ^ k < W k := lt_W_iff_avoiding.mpr hk
    have ht' : (n : ℝ) ^ k < (W k : ℝ) := by exact_mod_cast ht
    exact (pow_le_pow_left₀ hb hn k).trans ht'.le


/-- Failure of the conjectured limit is equivalent to an exponential upper bound
along an unbounded set of progression lengths. -/
lemma not_root_tendsto_iff :
    (¬ Tendsto (fun k ↦ (W k : ℝ) ^ (1 / (k : ℝ))) atTop atTop) ↔
      ∃ b : ℕ, ∀ K : ℕ, ∃ k ≥ K, W k ≤ b ^ k := by
  rw [root_tendsto_iff_avoiding]
  simp only [← lt_W_iff_avoiding, not_forall, not_eventually, not_lt,
    frequently_atTop]


lemma W_mono_ge_two {k l : ℕ} (hk : 2 ≤ k) (hkl : k ≤ l) : W k ≤ W l := by
  apply W_le_iff_guarantee.mpr
  intro C
  obtain ⟨c, ap, ⟨a, d, hcard, heq⟩, hc⟩ :=
    Nat.sInf_mem (guarantee_nonempty l) C
  have hd : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    have hs : Subtype.val '' ap ⊆ ({a} : Set ℕ) := by
      rw [heq]
      rintro x ⟨n, hn, rfl⟩
      simp [hd0]
    have hh := Set.encard_mono hs
    rw [← ENat.card_coe_set_eq, hcard, Set.encard_singleton] at hh
    have : l ≤ 1 := by exact_mod_cast hh
    omega
  have ht (i : Fin k) : ∃ x ∈ ap, x.val = a + i.val * d := by
    have hm : a + i.val * d ∈ Subtype.val '' ap := by
      rw [heq]
      exact ⟨i.val, by exact_mod_cast (i.isLt.trans_le hkl), by simp⟩
    exact hm
  choose f hf hfv using ht
  refine ⟨c, Set.range f, ?_, ?_⟩
  · have him : Subtype.val '' Set.range f =
        Set.range (fun i : Fin k ↦ a + i.val * d) := by
      rw [← Set.range_comp]
      congr 1
      funext i
      exact hfv i
    change (Subtype.val '' Set.range f).IsAPOfLength k
    rw [him]
    exact range_isAP hd
  · rintro _ ⟨i, rfl⟩
    exact hc _ (hf i)

/-- It is sufficient to construct avoiding colorings at every sufficiently
large prime length. Bertrand's postulate bridges the gaps between primes. -/
lemma root_tendsto_iff_prime :
    Tendsto (fun k ↦ (W k : ℝ) ^ (1 / (k : ℝ))) atTop atTop ↔
      ∀ b : ℕ, ∃ K : ℕ, ∀ p ≥ K, p.Prime → b ^ p < W p := by
  constructor
  · intro h b
    obtain ⟨K, hK⟩ := eventually_atTop.mp (root_tendsto_iff_avoiding.mp h b)
    exact ⟨K, fun p hp _ ↦ lt_W_iff_avoiding.mpr (hK p hp)⟩
  · intro h
    apply root_tendsto_iff_avoiding.mpr
    intro b
    let c := max b 1
    obtain ⟨K, hK⟩ := h (c ^ 2)
    filter_upwards [eventually_ge_atTop (2 * max K 2)] with k hk
    obtain ⟨p, hp, hkp, hpk⟩ :=
      Nat.exists_prime_lt_and_le_two_mul (k / 2) (by omega)
    have hpK : K ≤ p := by omega
    have hpk' : p ≤ k := by omega
    have hkp' : k ≤ 2 * p := by omega
    have hb : b ^ k ≤ c ^ k := Nat.pow_le_pow_left (le_max_left b 1) k
    have hc : c ^ k ≤ c ^ (2 * p) :=
      Nat.pow_le_pow_right (le_max_right b 1) hkp'
    apply lt_W_iff_avoiding.mp
    calc
      b ^ k ≤ c ^ k := hb
      _ ≤ c ^ (2 * p) := hc
      _ = (c ^ 2) ^ p := pow_mul c 2 p
      _ < W p := hK p hpK hp
      _ ≤ W k := W_mono_ge_two hp.two_le hpk'


end Erdos138


/- Finite counting estimates for two-colorings. -/

open Finset

namespace RandomColoring

variable {α ι : Type*} [Fintype α] [DecidableEq α]

noncomputable def fixedColorings (s : Finset α) (c : Fin 2) : Finset (α → Fin 2) :=
  Fintype.piFinset (fun x ↦ if x ∈ s then {c} else univ)

lemma mem_fixedColorings (s : Finset α) (c : Fin 2) (f : α → Fin 2) :
    f ∈ fixedColorings s c ↔ ∀ x ∈ s, f x = c := by
  simp only [fixedColorings, Fintype.mem_piFinset]
  constructor
  · intro h x hx
    simpa only [if_pos hx, mem_singleton] using h x
  · intro h x
    by_cases hx : x ∈ s
    · simpa only [if_pos hx, mem_singleton] using h x hx
    · simp [hx]

lemma card_fixedColorings (s : Finset α) (c : Fin 2) :
    (fixedColorings s c).card = 2 ^ (Fintype.card α - s.card) := by
  simp only [fixedColorings, Fintype.card_piFinset, apply_ite Finset.card, Finset.card_singleton, Finset.card_univ,
    Fintype.card_fin]
  rw [prod_ite]
  simp only [prod_const_one, one_mul, prod_const]
  congr 1
  have he : (univ.filter fun x : α ↦ x ∉ s) = sᶜ := by ext; simp
  rw [he, card_compl]


noncomputable def monoColorings (s : Finset α) : Finset (α → Fin 2) :=
  univ.biUnion (fixedColorings s)

lemma mem_monoColorings (s : Finset α) (f : α → Fin 2) :
    f ∈ monoColorings s ↔ ∃ c : Fin 2, ∀ x ∈ s, f x = c := by
  classical
  simp only [monoColorings, mem_biUnion, mem_univ, true_and, mem_fixedColorings]

lemma card_monoColorings_le (s : Finset α) :
    (monoColorings s).card ≤ 2 * 2 ^ (Fintype.card α - s.card) := by
  classical
  calc
    _ ≤ ∑ c : Fin 2, (fixedColorings s c).card := card_biUnion_le
    _ = _ := by simp [card_fixedColorings]

lemma exists_avoiding [DecidableEq ι] (I : Finset ι) (S : ι → Finset α) (k : ℕ)
    (hS : ∀ i ∈ I, (S i).card = k) (hI : 2 * I.card < 2 ^ k) :
    ∃ C : α → Fin 2, ∀ i ∈ I, ¬ ∃ c : Fin 2, ∀ x ∈ S i, C x = c := by
  classical
  rcases I.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ ↦ 0, by simp⟩
  have hkn : k ≤ Fintype.card α := by
    obtain ⟨i, hi⟩ := hne
    rw [← hS i hi]
    exact card_le_univ _
  let bad := I.biUnion (fun i ↦ monoColorings (S i))
  have hbad : bad.card < (univ : Finset (α → Fin 2)).card := by
    calc
      bad.card ≤ ∑ i ∈ I, (monoColorings (S i)).card := card_biUnion_le
      _ ≤ ∑ _i ∈ I, 2 * 2 ^ (Fintype.card α - k) := by
        apply sum_le_sum
        intro i hi
        simpa only [hS i hi] using card_monoColorings_le (S i)
      _ = (2 * I.card) * 2 ^ (Fintype.card α - k) := by simp; ring
      _ < 2 ^ k * 2 ^ (Fintype.card α - k) :=
        Nat.mul_lt_mul_of_pos_right hI (Nat.pow_pos (by decide))
      _ = 2 ^ Fintype.card α := by rw [← pow_add, Nat.add_sub_of_le hkn]
      _ = _ := by simp
  obtain ⟨C, _, hC⟩ := exists_mem_notMem_of_card_lt_card hbad
  refine ⟨C, ?_⟩
  intro i hi hmono
  exact hC (mem_biUnion.mpr ⟨i, hi, (mem_monoColorings _ _).mpr hmono⟩)

end RandomColoring


/- A finite counting formulation of a local-lemma argument. -/

open Finset

namespace FiniteLocalLemma

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]

noncomputable def avoid (E : ι → Finset Ω) (S : Finset ι) : Finset Ω :=
  univ.filter (fun ω ↦ ∀ i ∈ S, ω ∉ E i)

omit [DecidableEq ι] in
lemma mem_avoid (E : ι → Finset Ω) (S : Finset ι) (ω : Ω) :
    ω ∈ avoid E S ↔ ∀ i ∈ S, ω ∉ E i := by
  classical
  simp [avoid]

omit [DecidableEq ι] in
lemma avoid_empty (E : ι → Finset Ω) : avoid E ∅ = univ := by
  classical
  ext ω
  simp [mem_avoid]

omit [DecidableEq ι] in
lemma avoid_anti (E : ι → Finset Ω) {S T : Finset ι} (hST : S ⊆ T) :
    avoid E T ⊆ avoid E S := by
  intro ω hω
  simp only [mem_avoid] at *
  exact fun i hi ↦ hω i (hST hi)

lemma avoid_insert (E : ι → Finset Ω) (S : Finset ι) (i : ι) :
    avoid E (insert i S) = avoid E S \ E i := by
  classical
  ext ω
  simp only [mem_avoid, mem_insert, forall_eq_or_imp, Finset.mem_sdiff]
  tauto

lemma avoid_insert_card (E : ι → Finset Ω) (S : Finset ι) (i : ι) :
    ((avoid E (insert i S)).card : ℝ) =
      (avoid E S).card - (E i ∩ avoid E S).card := by
  rw [avoid_insert, card_sdiff, Nat.cast_sub (card_le_card inter_subset_right)]

lemma chain_bound (E : ι → Finset Ω) (A B : Finset ι) (x : ℝ)
    (hx : 0 ≤ 1 - x) (hAB : Disjoint A B)
    (hcond : ∀ i ∈ A, ∀ U ⊆ A ∪ B, i ∉ U →
      ((E i ∩ avoid E U).card : ℝ) ≤ x * (avoid E U).card) :
    (1 - x) ^ A.card * (avoid E B).card ≤ (avoid E (A ∪ B)).card := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih =>
    have hiB : i ∉ B := by
      exact fun h ↦ (disjoint_left.mp hAB) (mem_insert_self _ _) h
    have hAB' : Disjoint A B := hAB.mono_left (subset_insert _ _)
    have hcond' : ∀ j ∈ A, ∀ U ⊆ A ∪ B, j ∉ U →
        ((E j ∩ avoid E U).card : ℝ) ≤ x * (avoid E U).card := by
      intro j hj U hU hjU
      exact hcond j (mem_insert_of_mem hj) U
        (hU.trans (union_subset_union (subset_insert _ _) Subset.rfl)) hjU
    have hstep := hcond i (mem_insert_self _ _) (A ∪ B)
      (union_subset_union (subset_insert _ _) Subset.rfl)
      (by simp [hi, hiB])
    rw [card_insert_of_notMem hi, pow_succ, insert_union, avoid_insert_card]
    have hprev := ih hAB' hcond'
    have hm := mul_le_mul_of_nonneg_left hprev hx
    nlinarith


lemma conditional_bound (E : ι → Finset Ω) (D : ι → Finset ι) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hind : ∀ i M, i ∉ M → Disjoint M (D i) →
      ((E i ∩ avoid E M).card : ℝ) ≤
        x * (1 - x) ^ (D i).card * (avoid E M).card) :
    ∀ S i, i ∉ S → ((E i ∩ avoid E S).card : ℝ) ≤ x * (avoid E S).card := by
  classical
  intro S
  refine Finset.strongInductionOn S ?_
  intro S ih i hi
  have hx : 0 ≤ 1 - x := by linarith
  let A := S ∩ D i
  let B := S \ D i
  have hu : A ∪ B = S := by
    dsimp [A, B]
    rw [union_comm, sdiff_union_inter]
  have hAB : Disjoint A B := (disjoint_sdiff_inter S (D i)).symm
  have hlocal : ∀ j ∈ A, ∀ U ⊆ A ∪ B, j ∉ U →
      ((E j ∩ avoid E U).card : ℝ) ≤ x * (avoid E U).card := by
    intro j hj U hU hjU
    rw [hu] at hU
    have hproper : U ⊂ S := (ssubset_iff_of_subset hU).mpr
      ⟨j, (mem_inter.mp hj).1, hjU⟩
    exact ih U hproper j hjU
  have hchain := chain_bound E A B x hx hAB hlocal
  rw [hu] at hchain
  have hBD : Disjoint B (D i) := by
    apply disjoint_left.mpr
    intro j hj hD
    exact (mem_sdiff.mp hj).2 hD
  have hiB : i ∉ B := fun h ↦ hi (mem_sdiff.mp h).1
  have hpow : (1 - x) ^ (D i).card ≤ (1 - x) ^ A.card := by
    apply pow_le_pow_of_le_one hx (by linarith)
    exact card_le_card inter_subset_right
  calc
    ((E i ∩ avoid E S).card : ℝ) ≤ (E i ∩ avoid E B).card := by
      exact_mod_cast card_le_card
        (inter_subset_inter Subset.rfl (avoid_anti E sdiff_subset))
    _ ≤ x * (1 - x) ^ (D i).card * (avoid E B).card := hind i B hiB hBD
    _ ≤ x * (1 - x) ^ A.card * (avoid E B).card :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hx0) (by positivity)
    _ ≤ x * (avoid E S).card := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hchain hx0

lemma exists_avoiding [Nonempty Ω] (E : ι → Finset Ω) (D : ι → Finset ι)
    (I : Finset ι) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hind : ∀ i M, i ∉ M → Disjoint M (D i) →
      ((E i ∩ avoid E M).card : ℝ) ≤
        x * (1 - x) ^ (D i).card * (avoid E M).card) :
    ∃ ω : Ω, ∀ i ∈ I, ω ∉ E i := by
  classical
  have hcond := conditional_bound E D x hx0 hx1 hind
  have hchain := chain_bound E I ∅ x (by linarith) (by simp)
    (fun i _ U _ hi ↦ hcond U i hi)
  simp only [union_empty, avoid_empty, Finset.card_univ] at hchain
  have hpos : 0 < (1 - x) ^ I.card * (Fintype.card Ω : ℝ) := by
    have hx : 0 < 1 - x := by linarith
    have hc : 0 < Fintype.card Ω := Fintype.card_pos
    positivity
  have hcard : 0 < (avoid E I).card := by exact_mod_cast lt_of_lt_of_le hpos hchain
  obtain ⟨ω, hω⟩ := card_pos.mp hcard
  exact ⟨ω, (mem_avoid E I ω).mp hω⟩


lemma symmetric_exists_avoiding [Nonempty Ω] (E : ι → Finset Ω)
    (D : ι → Finset ι) (I : Finset ι) (d : ℕ) (p : ℝ)
    (hd : 0 < d) (hD : ∀ i, (D i).card ≤ d)
    (hp : 4 * d * p ≤ 1)
    (hind : ∀ i M, i ∉ M → Disjoint M (D i) →
      ((E i ∩ avoid E M).card : ℝ) ≤ p * (avoid E M).card) :
    ∃ ω : Ω, ∀ i ∈ I, ω ∉ E i := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  let x : ℝ := 1 / (2 * d)
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hxhalf : x ≤ 1 / 2 := by
    dsimp [x]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * d)).mpr
    nlinarith
  have hxd : (d : ℝ) * x = 1 / 2 := by
    dsimp [x]
    field_simp
  have hpx : p ≤ x / 2 := by
    have hp' : p ≤ 1 / (4 * (d : ℝ)) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith [hp])
    have he : 1 / (4 * (d : ℝ)) = x / 2 := by dsimp [x]; ring
    exact hp'.trans_eq he
  apply exists_avoiding E D I x hx0.le (by linarith)
  intro i M hi hM
  have hpow : 1 / 2 ≤ (1 - x) ^ (D i).card := by
    have hber := one_add_mul_le_pow (a := -x) (by linarith : -(2 : ℝ) ≤ -x) (D i).card
    have hc : ((D i).card : ℝ) ≤ d := by exact_mod_cast hD i
    have hmul := mul_le_mul_of_nonneg_right hc hx0.le
    rw [hxd] at hmul
    convert le_trans (show (1 : ℝ) / 2 ≤ 1 + (D i).card * -x by nlinarith) hber using 1
  have hpx' : p ≤ x * (1 - x) ^ (D i).card := by
    have hm := mul_le_mul_of_nonneg_left hpow hx0.le
    nlinarith
  exact (hind i M hi hM).trans (mul_le_mul_of_nonneg_right hpx' (by positivity))

end FiniteLocalLemma


/- Counting independence for constraints on disjoint sets of coordinates. -/

open Finset

namespace RandomColoring

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma card_mono_inter_of_outside (s : Finset α) (hs : s.Nonempty)
    (T : Finset (α → Fin 2))
    (hT : ∀ f g : α → Fin 2, (∀ x ∉ s, f x = g x) → (f ∈ T ↔ g ∈ T)) :
    2 ^ s.card * (monoColorings s ∩ T).card = 2 * T.card := by
  classical
  let β := {x // x ∈ s}
  let γ := {x // x ∉ s}
  let e : (α → Fin 2) ≃ (β → Fin 2) × (γ → Fin 2) :=
    Equiv.piEquivPiSubtypeProd (fun x ↦ x ∈ s) (fun _ ↦ Fin 2)
  let G : Finset (γ → Fin 2) := univ.filter (fun g ↦ e.symm ((fun _ ↦ 0), g) ∈ T)
  let H : Finset (β → Fin 2) := univ.image (fun c : Fin 2 ↦ fun _ : β ↦ c)
  have hmem (f : β → Fin 2) (g : γ → Fin 2) : e.symm (f, g) ∈ T ↔ g ∈ G := by
    simp only [G, mem_filter, mem_univ, true_and]
    apply hT
    intro x hx
    simp [e, Equiv.piEquivPiSubtypeProd, hx]
  have hmono (f : β → Fin 2) (g : γ → Fin 2) :
      e.symm (f, g) ∈ monoColorings s ↔ f ∈ H := by
    rw [mem_monoColorings]
    simp only [H, mem_image, mem_univ, true_and, funext_iff]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      intro x
      have h := hc x.val x.property
      simpa [e, Equiv.piEquivPiSubtypeProd, x.property] using h.symm
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      intro x hx
      simpa [e, Equiv.piEquivPiSubtypeProd, hx] using (hc ⟨x, hx⟩).symm
  have hmapT : T.map e.toEmbedding = univ ×ˢ G := by
    ext p
    rcases p with ⟨f, g⟩
    simp only [mem_map_equiv, mem_product, mem_univ, true_and, hmem]
  have hmapM : (monoColorings s ∩ T).map e.toEmbedding = H ×ˢ G := by
    ext p
    rcases p with ⟨f, g⟩
    simp only [mem_map_equiv, mem_inter, mem_product, hmem, hmono]
  have hH : H.card = 2 := by
    have hinj : Function.Injective (fun c : Fin 2 ↦ fun _ : β ↦ c) := by
      intro c d h
      obtain ⟨x, hx⟩ := hs
      exact congr_fun h ⟨x, hx⟩
    simp [H, card_image_of_injective _ hinj]
  have hTc : T.card = 2 ^ s.card * G.card := by
    have h := congr_arg Finset.card hmapT
    simpa [β] using h
  have hMc : (monoColorings s ∩ T).card = 2 * G.card := by
    have h := congr_arg Finset.card hmapM
    simpa only [card_map, card_product, hH] using h
  rw [hTc, hMc]
  ring


lemma exists_avoiding_local {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset α) (k d : ℕ) (hk : 0 < k) (hd : 0 < d)
    (hS : ∀ i, (S i).card = k)
    (hdeg : ∀ i, (univ.filter (fun j ↦ ¬ Disjoint (S i) (S j))).card ≤ d)
    (hnum : 8 * d ≤ 2 ^ k) :
    ∃ C : α → Fin 2, ∀ i, ¬ ∃ c : Fin 2, ∀ x ∈ S i, C x = c := by
  classical
  let E := fun i ↦ monoColorings (S i)
  let D := fun i ↦ univ.filter (fun j ↦ ¬ Disjoint (S i) (S j))
  have hpowpos : (0 : ℝ) < 2 ^ k := by positivity
  have hsmall : 4 * (d : ℝ) * (2 / (2 : ℝ) ^ k) ≤ 1 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hpowpos).mpr
    have hn : (8 : ℝ) * d ≤ 2 ^ k := by exact_mod_cast hnum
    nlinarith
  have hind : ∀ i M, i ∉ M → Disjoint M (D i) →
      ((E i ∩ FiniteLocalLemma.avoid E M).card : ℝ) ≤
        (2 / (2 : ℝ) ^ k) * (FiniteLocalLemma.avoid E M).card := by
    intro i M hi hMD
    have hdisj : ∀ j ∈ M, Disjoint (S i) (S j) := by
      intro j hj
      by_contra h
      apply (disjoint_left.mp hMD) hj
      exact mem_filter.mpr ⟨mem_univ _, h⟩
    have hstable : ∀ f g : α → Fin 2, (∀ x ∉ S i, f x = g x) →
        (f ∈ FiniteLocalLemma.avoid E M ↔ g ∈ FiniteLocalLemma.avoid E M) := by
      intro f g hfg
      have he : ∀ j ∈ M, f ∈ E j ↔ g ∈ E j := by
        intro j hj
        change f ∈ monoColorings (S j) ↔ g ∈ monoColorings (S j)
        simp only [mem_monoColorings]
        have hx : ∀ x ∈ S j, f x = g x := by
          intro x hx
          apply hfg
          exact fun hx' ↦ (disjoint_left.mp (hdisj j hj)) hx' hx
        constructor
        · rintro ⟨c, hc⟩
          exact ⟨c, fun x h ↦ (hx x h).symm.trans (hc x h)⟩
        · rintro ⟨c, hc⟩
          exact ⟨c, fun x h ↦ (hx x h).trans (hc x h)⟩
      simp only [FiniteLocalLemma.mem_avoid]
      constructor
      · intro hf j hj hg
        exact hf j hj ((he j hj).mpr hg)
      · intro hg j hj hf
        exact hg j hj ((he j hj).mp hf)
    have hs : (S i).Nonempty := card_pos.mp (by simpa [hS i] using hk)
    have he := card_mono_inter_of_outside (S i) hs (FiniteLocalLemma.avoid E M) hstable
    rw [hS i] at he
    have he' : (2 : ℝ) ^ k * (E i ∩ FiniteLocalLemma.avoid E M).card =
        2 * (FiniteLocalLemma.avoid E M).card := by exact_mod_cast he
    have heq : ((E i ∩ FiniteLocalLemma.avoid E M).card : ℝ) =
        (2 * (FiniteLocalLemma.avoid E M).card) / (2 : ℝ) ^ k :=
      (eq_div_iff (ne_of_gt hpowpos)).mpr (by nlinarith [he'])
    rw [heq]
    exact le_of_eq (by ring)
  obtain ⟨C, hC⟩ := FiniteLocalLemma.symmetric_exists_avoiding E D univ d
    (2 / (2 : ℝ) ^ k) hd hdeg hsmall hind
  exact ⟨C, fun i h ↦ hC i (mem_univ _) ((mem_monoColorings _ _).mpr h)⟩

end RandomColoring


/- An elementary probabilistic lower bound, proved by finite counting. -/

open Finset Filter

namespace Erdos138

lemma avoid_of_exponential_bound {k N : ℕ} (hk : 2 ≤ k)
    (hbound : 2 * (N + 1) ^ 2 < 2 ^ k) : N < W k := by
  classical
  let α := ↥(Finset.Icc 1 N)
  let β := Fin (N + 1) × Fin (N + 1)
  let S : β → Finset α := fun p ↦ univ.filter
    (fun x ↦ ∃ n < k, (p.1 : ℕ) + n * (p.2 : ℕ) = x.val)
  let I : Finset β := univ.filter (fun p ↦ (S p).card = k)
  have hI : 2 * I.card < 2 ^ k := by
    calc
      2 * I.card ≤ 2 * Fintype.card β := Nat.mul_le_mul_left 2 (card_le_univ I)
      _ = 2 * (N + 1) ^ 2 := by simp [β, pow_two]
      _ < _ := hbound
  obtain ⟨C, hC⟩ := RandomColoring.exists_avoiding I S k
    (fun p hp ↦ (mem_filter.mp hp).2) hI
  apply lt_W_iff_avoiding.mpr
  refine ⟨C, ?_⟩
  rintro ⟨c, ap, ⟨a, d, hcard, heq⟩, hc⟩
  have ht {n : ℕ} (hn : n < k) : a + n * d ∈ Subtype.val '' ap := by
    rw [heq]
    exact ⟨n, by exact_mod_cast hn, by simp⟩
  have ha : a ≤ N := by
    obtain ⟨x, hx, he⟩ := ht (n := 0) (by omega)
    have h := (Finset.mem_Icc.mp (show x.val ∈ Finset.Icc 1 N from x.property)).2
    simp only [Nat.zero_mul, Nat.add_zero] at he
    omega
  have hd : d ≤ N := by
    obtain ⟨x, hx, he⟩ := ht (n := 1) (by omega)
    have h := (Finset.mem_Icc.mp (show x.val ∈ Finset.Icc 1 N from x.property)).2
    simp only [Nat.one_mul] at he
    omega
  let p : β := (⟨a, by omega⟩, ⟨d, by omega⟩)
  have hSp : (S p : Set α) = ap := by
    ext x
    simp only [Finset.mem_coe, S, mem_filter, mem_univ, true_and]
    change (∃ n < k, a + n * d = x.val) ↔ x ∈ ap
    constructor
    · rintro ⟨n, hn, he⟩
      obtain ⟨y, hy, hyx⟩ := ht hn
      have hyx' : y = x := Subtype.ext (hyx.trans he)
      simpa only [hyx'] using hy
    · intro hx
      have him : x.val ∈ Subtype.val '' ap := ⟨x, hx, rfl⟩
      rw [heq] at him
      obtain ⟨n, hn, he⟩ := him
      exact ⟨n, by exact_mod_cast hn, by simpa only [nsmul_eq_mul] using he⟩
  have hScard : (S p).card = k := by
    have hi : Function.Injective (Subtype.val : α → ℕ) := Subtype.coe_injective
    change ENat.card (Subtype.val '' ap) = (k : ℕ∞) at hcard
    rw [← hSp, ENat.card_coe_set_eq] at hcard
    change ((Subtype.val : α → ℕ) '' (S p : Set α)).encard = (k : ℕ∞) at hcard
    rw [hi.encard_image, Set.encard_coe_eq_coe_finsetCard] at hcard
    exact_mod_cast hcard
  apply hC p (mem_filter.mpr ⟨mem_univ _, hScard⟩)
  refine ⟨c, ?_⟩
  intro x hx
  apply hc x
  rw [← hSp]
  exact hx


lemma two_pow_le_W (m : ℕ) : 2 ^ m ≤ W (2 * m + 2) := by
  have hpos : 0 < (2 : ℕ) ^ m := by positivity
  have hbound : 2 * (2 ^ m - 1 + 1) ^ 2 < 2 ^ (2 * m + 2) := by
    rw [Nat.sub_add_cancel hpos, ← pow_mul, mul_comm m 2, pow_add]
    have he : (2 : ℕ) ^ (2 * m) = (2 ^ m) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [he]
    norm_num
    nlinarith
  have hw := avoid_of_exponential_bound (k := 2 * m + 2) (N := 2 ^ m - 1)
    (by omega) hbound
  omega

end Erdos138


/- A local-lemma lower bound for the van der Waerden numbers. -/

open Finset Filter

namespace Erdos138

lemma avoid_of_local_bound {k N : ℕ} (hk : 2 ≤ k)
    (hbound : 8 * k ^ 2 * (N + 1) ≤ 2 ^ k) : N < W k := by
  classical
  let α := ↥(Finset.Icc 1 N)
  let β := Fin (N + 1) × Fin (N + 1)
  let S : β → Finset α := fun p ↦ univ.filter
    (fun x ↦ ∃ n < k, (p.1 : ℕ) + n * (p.2 : ℕ) = x.val)
  let I : Finset β := univ.filter (fun p ↦ (S p).card = k)
  let ι := ↥I
  let P (x : α) : Finset β := univ.image (fun q : Fin k × Fin (N + 1) ↦
    (⟨x.val - (q.1 : ℕ) * (q.2 : ℕ),
      lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_of_le (Finset.mem_Icc.mp x.property).2)⟩,
      q.2))
  have hPcard (x : α) : (P x).card ≤ k * (N + 1) := by
    calc
      (P x).card ≤ (univ : Finset (Fin k × Fin (N + 1))).card := card_image_le
      _ = _ := by simp
  have hPmem {x : α} {p : β} (hx : x ∈ S p) : p ∈ P x := by
    obtain ⟨n, hn, he⟩ := (mem_filter.mp hx).2
    apply mem_image.mpr
    refine ⟨(⟨n, hn⟩, p.2), mem_univ _, ?_⟩
    apply Prod.ext
    · apply Fin.ext
      change x.val - n * (p.2 : ℕ) = (p.1 : ℕ)
      omega
    · rfl
  have hScard (i : ι) : (S i.val).card = k := (mem_filter.mp i.property).2
  have hdeg (i : ι) :
      (univ.filter (fun j : ι ↦ ¬ Disjoint (S i.val) (S j.val))).card ≤ k ^ 2 * (N + 1) := by
    let D : Finset ι := univ.filter (fun j ↦ ¬ Disjoint (S i.val) (S j.val))
    have hsub : D.image Subtype.val ⊆ (S i.val).biUnion P := by
      rintro p hp
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hp
      obtain ⟨x, hxi, hxj⟩ := not_disjoint_iff.mp (mem_filter.mp hj).2
      exact mem_biUnion.mpr ⟨x, hxi, hPmem hxj⟩
    calc
      D.card = (D.image Subtype.val).card :=
        (Finset.card_image_of_injective _ Subtype.coe_injective).symm
      _ ≤ ((S i.val).biUnion P).card := card_le_card hsub
      _ ≤ ∑ x ∈ S i.val, (P x).card := card_biUnion_le
      _ ≤ ∑ _x ∈ S i.val, k * (N + 1) := sum_le_sum (fun x _ ↦ hPcard x)
      _ = k ^ 2 * (N + 1) := by simp [hScard i]; ring
  obtain ⟨C, hC0⟩ := RandomColoring.exists_avoiding_local
    (fun i : ι ↦ S i.val) k (k ^ 2 * (N + 1)) (by omega)
    (by
      have hk0 : 0 < k := by omega
      positivity) hScard hdeg (by simpa [mul_assoc] using hbound)
  have hC : ∀ p ∈ I, ¬ ∃ c : Fin 2, ∀ x ∈ S p, C x = c := fun p hp ↦ hC0 ⟨p, hp⟩
  apply lt_W_iff_avoiding.mpr
  refine ⟨C, ?_⟩
  rintro ⟨c, ap, ⟨a, d, hcard, heq⟩, hc⟩
  have ht {n : ℕ} (hn : n < k) : a + n * d ∈ Subtype.val '' ap := by
    rw [heq]
    exact ⟨n, by exact_mod_cast hn, by simp⟩
  have ha : a ≤ N := by
    obtain ⟨x, hx, he⟩ := ht (n := 0) (by omega)
    have h := (Finset.mem_Icc.mp (show x.val ∈ Finset.Icc 1 N from x.property)).2
    simp only [Nat.zero_mul, Nat.add_zero] at he
    omega
  have hd : d ≤ N := by
    obtain ⟨x, hx, he⟩ := ht (n := 1) (by omega)
    have h := (Finset.mem_Icc.mp (show x.val ∈ Finset.Icc 1 N from x.property)).2
    simp only [Nat.one_mul] at he
    omega
  let p : β := (⟨a, by omega⟩, ⟨d, by omega⟩)
  have hSp : (S p : Set α) = ap := by
    ext x
    simp only [Finset.mem_coe, S, mem_filter, mem_univ, true_and]
    change (∃ n < k, a + n * d = x.val) ↔ x ∈ ap
    constructor
    · rintro ⟨n, hn, he⟩
      obtain ⟨y, hy, hyx⟩ := ht hn
      have hyx' : y = x := Subtype.ext (hyx.trans he)
      simpa only [hyx'] using hy
    · intro hx
      have him : x.val ∈ Subtype.val '' ap := ⟨x, hx, rfl⟩
      rw [heq] at him
      obtain ⟨n, hn, he⟩ := him
      exact ⟨n, by exact_mod_cast hn, by simpa only [nsmul_eq_mul] using he⟩
  have hScard : (S p).card = k := by
    have hi : Function.Injective (Subtype.val : α → ℕ) := Subtype.coe_injective
    change ENat.card (Subtype.val '' ap) = (k : ℕ∞) at hcard
    rw [← hSp, ENat.card_coe_set_eq] at hcard
    change ((Subtype.val : α → ℕ) '' (S p : Set α)).encard = (k : ℕ∞) at hcard
    rw [hi.encard_image, Set.encard_coe_eq_coe_finsetCard] at hcard
    exact_mod_cast hcard
  apply hC p (mem_filter.mpr ⟨mem_univ _, hScard⟩)
  refine ⟨c, ?_⟩
  intro x hx
  apply hc x
  rw [← hSp]
  exact hx



lemma exponential_div_le_W {k : ℕ} (hk : 2 ≤ k) : 2 ^ k / (8 * k ^ 2) ≤ W k := by
  let q := 2 ^ k / (8 * k ^ 2)
  by_cases hq : q = 0
  · change q ≤ W k
    rw [hq]
    exact Nat.zero_le _
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    have hbound : 8 * k ^ 2 * ((q - 1) + 1) ≤ 2 ^ k := by
      rw [Nat.sub_add_cancel hqpos]
      exact Nat.mul_div_le _ _
    have h := avoid_of_local_bound hk hbound
    change q ≤ W k
    omega

end Erdos138


/- Analytic consequences of the local-lemma lower bound. -/

open Filter

namespace Erdos138

lemma eventually_pow_le_W {b : ℝ} (hb1 : 1 < b) (hb2 : b < 2) :
    ∀ᶠ k : ℕ in atTop, b ^ k ≤ (W k : ℝ) := by
  have hb0 : 0 < b := by linarith
  have hr0 : 0 ≤ b / 2 := by positivity
  have hr1 : b / 2 < 1 := by linarith
  have ht := (tendsto_pow_const_mul_const_pow_of_lt_one 2 hr0 hr1).const_mul 24
  have ht' : Tendsto (fun k : ℕ ↦ 24 * ((k : ℝ) ^ 2 * (b / 2) ^ k)) atTop (nhds 0) := by
    simpa using ht
  filter_upwards [ht'.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop 2] with k hk hk2
  let N := ⌈b ^ k⌉₊
  have hbpow : 1 ≤ b ^ k := one_le_pow₀ hb1.le
  have hceil : (N : ℝ) < b ^ k + 1 := Nat.ceil_lt_add_one (by positivity)
  have hN : (N : ℝ) + 1 ≤ 3 * b ^ k := by nlinarith
  have h2pos : (0 : ℝ) < 2 ^ k := by positivity
  have hpow : 24 * (k : ℝ) ^ 2 * b ^ k ≤ 2 ^ k := by
    have hratio : (24 * (k : ℝ) ^ 2 * b ^ k) / 2 ^ k ≤ 1 := by
      simpa only [div_pow, mul_div_assoc, mul_assoc] using hk
    exact (div_le_iff₀ h2pos).mp hratio |>.trans_eq (one_mul _)
  have hbound : 8 * k ^ 2 * (N + 1) ≤ 2 ^ k := by
    have hm := mul_le_mul_of_nonneg_left hN (show (0 : ℝ) ≤ 8 * (k : ℝ) ^ 2 by positivity)
    have hreal : 8 * (k : ℝ) ^ 2 * ((N : ℝ) + 1) ≤ 2 ^ k := by nlinarith [hm, hpow]
    exact_mod_cast hreal
  have hw : N < W k := avoid_of_local_bound hk2 hbound
  exact (Nat.le_ceil (b ^ k)).trans (by exact_mod_cast hw.le)

lemma eventually_root_ge {b : ℝ} (hb : b < 2) :
    ∀ᶠ k : ℕ in atTop, b ≤ (W k : ℝ) ^ (1 / (k : ℝ)) := by
  let c := (max b 1 + 2) / 2
  have hc1 : 1 < c := by dsimp [c]; have := le_max_right b 1; linarith
  have hc2 : c < 2 := by
    have hm : max b 1 < (2 : ℝ) := max_lt hb (by norm_num)
    dsimp [c]
    linarith
  have hbc : b ≤ c := by dsimp [c]; have := le_max_left b 1; have := max_lt hb (by norm_num : (1 : ℝ) < 2); linarith
  filter_upwards [eventually_pow_le_W hc1 hc2, eventually_gt_atTop 0] with k hk hk0
  exact hbc.trans ((root_ge_iff (by linarith) hk0).mpr hk)

end Erdos138


/- A prime-dimensional finite-field construction. These are lower bounds,
not a proof of the superexponential-growth conjecture. -/

namespace Erdos138.FiniteFieldConstruction

open Module

lemma powerBasis_of_prime_degree {F : Type*} [Field F] [Algebra (ZMod 2) F]
    [FiniteDimensional (ZMod 2) F] {p : ℕ}
    (hp : p.Prime) (hdim : finrank (ZMod 2) F = p)
    {b : F} (hb0 : b ≠ 0) (hb1 : b ≠ 1) :
    ∃ B : PowerBasis (ZMod 2) F, B.gen = b ∧ B.dim = p := by
  haveI := IntermediateField.isSimpleOrder_of_finrank_prime (ZMod 2) F (hdim ▸ hp)
  have ht : IntermediateField.adjoin (ZMod 2) {b} = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top (IntermediateField.adjoin (ZMod 2) {b}) with h | h
    · have hm := IntermediateField.mem_adjoin_simple_self (ZMod 2) b
      rw [h, IntermediateField.mem_bot] at hm
      obtain ⟨c, hc⟩ := hm
      have hc01 : c = 0 ∨ c = 1 := by
        fin_cases c <;> simp
      rcases hc01 with rfl | rfl
      · exact (hb0 (by simpa using hc.symm)).elim
      · exact (hb1 (by simpa using hc.symm)).elim
    · exact h
  let e := (IntermediateField.equivOfEq ht).trans IntermediateField.topEquiv
  let B := (IntermediateField.adjoin.powerBasis (IsIntegral.of_finite (ZMod 2) b)).map e
  refine ⟨B, ?_, ?_⟩
  · rfl
  · exact B.finrank.symm.trans hdim

lemma not_constant_on_powers {F : Type*} [Field F] [Algebra (ZMod 2) F]
    [FiniteDimensional (ZMod 2) F] {p : ℕ}
    (hp : p.Prime) (hdim : finrank (ZMod 2) F = p)
    (L : F →ₗ[ZMod 2] ZMod 2) (hL : L 1 = 1)
    {a b : F} (ha : a ≠ 0) (hb0 : b ≠ 0) (hb1 : b ≠ 1) (c : ZMod 2) :
    ¬ ∀ i : ℕ, i ≤ p → L (a * b ^ i) = c := by
  intro hc
  obtain ⟨B, hBg, hBd⟩ := powerBasis_of_prime_degree hp hdim hb0 hb1
  let z := a * (b - 1)
  have hz : z ≠ 0 := mul_ne_zero ha (sub_ne_zero.mpr hb1)
  let T := L.comp (LinearMap.mulLeft (ZMod 2) z)
  have hT : T = 0 := by
    apply B.basis.ext
    intro i
    change L (z * B.basis i) = 0
    rw [B.basis_eq_pow, hBg]
    have hi : i.val < p := hBd ▸ i.isLt
    have he : z * b ^ i.val = a * b ^ (i.val + 1) - a * b ^ i.val := by
      dsimp [z]
      rw [pow_succ]
      ring
    rw [he, map_sub, hc _ (by omega), hc _ (by omega), sub_self]
  have he := LinearMap.congr_fun hT z⁻¹
  have : L 1 = 0 := by simpa [T, hz] using he
  exact one_ne_zero (hL.symm.trans this)

end Erdos138.FiniteFieldConstruction

namespace Erdos138

/-- A prime-dimensional binary-field construction, extended periodically
up to the first possible repeated-residue progression. -/
lemma prime_field_lower_bound {p : ℕ} (hp : p.Prime) :
    p * (2 ^ p - 1) < W (p + 1) := by
  classical
  let F := GaloisField 2 p
  have hdim : Module.finrank (ZMod 2) F = p := GaloisField.finrank 2 hp.ne_zero
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  let g : F := u
  have hg0 : g ≠ 0 := u.ne_zero
  have hord : orderOf g = 2 ^ p - 1 := by
    rw [orderOf_units, hu, Nat.card_units]
    rw [GaloisField.card 2 p hp.ne_zero]
  obtain ⟨L, hL⟩ := Module.Projective.exists_dual_eq_one (ZMod 2)
    (show (1 : F) ≠ 0 from one_ne_zero)
  let C : Finset.Icc 1 (p * (2 ^ p - 1)) → Fin 2 := fun x ↦ L (g ^ x.val)
  apply lt_W_iff_avoiding.mpr
  refine ⟨C, ?_⟩
  rintro ⟨c, ap, ⟨a, d, hcard, heq⟩, hc⟩
  have hd : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    have hs : Subtype.val '' ap ⊆ ({a} : Set ℕ) := by
      rw [heq]
      rintro x ⟨n, hn, rfl⟩
      simp [hd0]
    have hh := Set.encard_mono hs
    rw [← ENat.card_coe_set_eq, hcard, Set.encard_singleton] at hh
    have : p + 1 ≤ 1 := by exact_mod_cast hh
    have := hp.pos
    omega
  have hx (i : ℕ) (hi : i ≤ p) : ∃ x ∈ ap, x.val = a + i * d := by
    have hm : a + i * d ∈ Subtype.val '' ap := by
      rw [heq]
      refine ⟨i, ?_, ?_⟩
      · exact_mod_cast (show i < p + 1 by omega)
      · simp
    exact hm
  have ha : 1 ≤ a := by
    obtain ⟨x, _, hxi⟩ := hx 0 (Nat.zero_le p)
    have hm : x.val ∈ Finset.Icc 1 (p * (2 ^ p - 1)) := x.property
    have hx1 := (Finset.mem_Icc.mp hm).1
    simpa [hxi] using hx1
  have hend : a + p * d ≤ p * (2 ^ p - 1) := by
    obtain ⟨x, _, hxi⟩ := hx p le_rfl
    have hm : x.val ∈ Finset.Icc 1 (p * (2 ^ p - 1)) := x.property
    have hxN := (Finset.mem_Icc.mp hm).2
    rwa [hxi] at hxN
  have hdq : d < 2 ^ p - 1 := by
    have := hp.pos
    nlinarith
  have hgpow : g ^ d ≠ 1 := pow_ne_one_of_lt_orderOf hd.ne' (by rwa [hord])
  apply FiniteFieldConstruction.not_constant_on_powers hp hdim L hL
    (pow_ne_zero a hg0) (pow_ne_zero d hg0) hgpow c
  intro i hi
  obtain ⟨x, hxp, hxi⟩ := hx i hi
  have hcx := hc x hxp
  change L (g ^ x.val) = c at hcx
  rw [hxi, pow_add, Nat.mul_comm i d, pow_mul] at hcx
  exact hcx

/-- At prime dimensions at least three, this beats the bound `2^(p+1)`. -/
lemma two_pow_lt_W_prime_succ {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    2 ^ (p + 1) < W (p + 1) := by
  have hpow : 3 ≤ 2 ^ p := by
    have := Nat.pow_le_pow_right (by omega : 0 < 2) hp3
    norm_num at this
    omega
  have hsub : 2 ^ p - 1 + 1 = 2 ^ p := Nat.sub_add_cancel (by omega)
  have hm := Nat.mul_le_mul_right (2 ^ p - 1) hp3
  have hle : 2 ^ (p + 1) ≤ p * (2 ^ p - 1) := by
    rw [pow_succ]
    nlinarith
  exact hle.trans_lt (prime_field_lower_bound hp)

/-- The roots exceed two for an unbounded set of progression lengths.
This does not imply divergence to infinity. -/
lemma frequently_root_gt_two :
    ∃ᶠ k : ℕ in Filter.atTop, 2 < (W k : ℝ) ^ (1 / (k : ℝ)) := by
  apply Filter.frequently_atTop.mpr
  intro K
  obtain ⟨p, hKp, hp⟩ := Nat.exists_infinite_primes (max K 3)
  have hp3 : 3 ≤ p := (le_max_right K 3).trans hKp
  refine ⟨p + 1, by have := (le_max_left K 3).trans hKp; omega, ?_⟩
  have hh : (2 : ℝ) ^ (p + 1) < (W (p + 1) : ℝ) := by
    exact_mod_cast two_pow_lt_W_prime_succ hp hp3
  have hpos : (0 : ℝ) < (p + 1 : ℕ) := by positivity
  rw [one_div]
  apply (Real.lt_rpow_inv_iff_of_pos (by norm_num) (by positivity) hpos).mpr
  simpa only [Real.rpow_natCast] using hh

end Erdos138


namespace Erdos138

lemma avoid_of_linear_local_bound {k N : ℕ} (hk : 2 ≤ k)
    (hbound : 16 * k * N ≤ 2 ^ k) : N < W k := by
  classical
  by_cases hN : N = 0
  · subst N
    exact lt_of_lt_of_le (by omega : 0 < k) (le_W k)
  have hNpos : 0 < N := by omega
  have hkpred : 0 < k - 1 := by omega
  let M := N / (k - 1)
  have hcount : k * M ≤ 2 * N := by
    have hdiv : (k - 1) * M ≤ N := Nat.mul_div_le N (k - 1)
    have hmul := Nat.mul_le_mul_right M (show k ≤ 2 * (k - 1) by omega)
    nlinarith
  let α := ↥(Finset.Icc 1 N)
  let β := Fin (N + 1) × Fin M
  let S : β → Finset α := fun p ↦ univ.filter
    (fun x ↦ ∃ n < k, (p.1 : ℕ) + n * ((p.2 : ℕ) + 1) = x.val)
  let I : Finset β := univ.filter (fun p ↦ (S p).card = k)
  let ι := ↥I
  let P (x : α) : Finset β := univ.image (fun q : Fin k × Fin M ↦
    (⟨x.val - (q.1 : ℕ) * ((q.2 : ℕ) + 1),
      lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_of_le (Finset.mem_Icc.mp x.property).2)⟩,
      q.2))
  have hPcard (x : α) : (P x).card ≤ k * M := by
    calc
      (P x).card ≤ (univ : Finset (Fin k × Fin M)).card := card_image_le
      _ = _ := by simp
  have hPmem {x : α} {p : β} (hx : x ∈ S p) : p ∈ P x := by
    obtain ⟨n, hn, he⟩ := (mem_filter.mp hx).2
    apply mem_image.mpr
    refine ⟨(⟨n, hn⟩, p.2), mem_univ _, ?_⟩
    apply Prod.ext
    · apply Fin.ext
      change x.val - n * ((p.2 : ℕ) + 1) = (p.1 : ℕ)
      omega
    · rfl
  have hScard (i : ι) : (S i.val).card = k := (mem_filter.mp i.property).2
  have hdeg (i : ι) :
      (univ.filter (fun j : ι ↦ ¬ Disjoint (S i.val) (S j.val))).card ≤ 2 * k * N := by
    let D : Finset ι := univ.filter (fun j ↦ ¬ Disjoint (S i.val) (S j.val))
    have hsub : D.image Subtype.val ⊆ (S i.val).biUnion P := by
      rintro p hp
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hp
      obtain ⟨x, hxi, hxj⟩ := not_disjoint_iff.mp (mem_filter.mp hj).2
      exact mem_biUnion.mpr ⟨x, hxi, hPmem hxj⟩
    calc
      D.card = (D.image Subtype.val).card :=
        (Finset.card_image_of_injective _ Subtype.coe_injective).symm
      _ ≤ ((S i.val).biUnion P).card := card_le_card hsub
      _ ≤ ∑ x ∈ S i.val, (P x).card := card_biUnion_le
      _ ≤ ∑ _x ∈ S i.val, k * M := sum_le_sum (fun x _ ↦ hPcard x)
      _ = k * (k * M) := by simp [hScard i]
      _ ≤ 2 * k * N := by nlinarith [Nat.mul_le_mul_left k hcount]
  obtain ⟨C, hC0⟩ := RandomColoring.exists_avoiding_local
    (fun i : ι ↦ S i.val) k (2 * k * N) (by omega)
    (by
      have hk0 : 0 < k := by omega
      positivity) hScard hdeg (by nlinarith [hbound])
  have hC : ∀ p ∈ I, ¬ ∃ c : Fin 2, ∀ x ∈ S p, C x = c := fun p hp ↦ hC0 ⟨p, hp⟩
  apply lt_W_iff_avoiding.mpr
  refine ⟨C, ?_⟩
  rintro ⟨c, ap, ⟨a, d, hcard, heq⟩, hc⟩
  have ht {n : ℕ} (hn : n < k) : a + n * d ∈ Subtype.val '' ap := by
    rw [heq]
    exact ⟨n, by exact_mod_cast hn, by simp⟩
  have ha : a ≤ N := by
    obtain ⟨x, hx, he⟩ := ht (n := 0) (by omega)
    have h := (Finset.mem_Icc.mp (show x.val ∈ Finset.Icc 1 N from x.property)).2
    simp only [Nat.zero_mul, Nat.add_zero] at he
    omega
  have hdpos : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    have hs : Subtype.val '' ap ⊆ ({a} : Set ℕ) := by
      rw [heq]
      rintro x ⟨n, hn, rfl⟩
      simp [hd0]
    have hh := Set.encard_mono hs
    rw [← ENat.card_coe_set_eq, hcard, Set.encard_singleton] at hh
    have : k ≤ 1 := by exact_mod_cast hh
    omega
  have hd : d ≤ M := by
    obtain ⟨x, hx, he⟩ := ht (n := k - 1) (by omega)
    have h := (Finset.mem_Icc.mp (show x.val ∈ Finset.Icc 1 N from x.property)).2
    apply (Nat.le_div_iff_mul_le hkpred).mpr
    nlinarith
  let p : β := (⟨a, by omega⟩, ⟨d - 1, by omega⟩)
  have hstep : (p.2 : ℕ) + 1 = d := by dsimp [p]; omega
  have hSp : (S p : Set α) = ap := by
    ext x
    simp only [Finset.mem_coe, S, mem_filter, mem_univ, true_and]
    change (∃ n < k, a + n * ((p.2 : ℕ) + 1) = x.val) ↔ x ∈ ap
    rw [hstep]
    constructor
    · rintro ⟨n, hn, he⟩
      obtain ⟨y, hy, hyx⟩ := ht hn
      have hyx' : y = x := Subtype.ext (hyx.trans he)
      simpa only [hyx'] using hy
    · intro hx
      have him : x.val ∈ Subtype.val '' ap := ⟨x, hx, rfl⟩
      rw [heq] at him
      obtain ⟨n, hn, he⟩ := him
      exact ⟨n, by exact_mod_cast hn, by simpa only [nsmul_eq_mul] using he⟩
  have hScard : (S p).card = k := by
    have hi : Function.Injective (Subtype.val : α → ℕ) := Subtype.coe_injective
    change ENat.card (Subtype.val '' ap) = (k : ℕ∞) at hcard
    rw [← hSp, ENat.card_coe_set_eq] at hcard
    change ((Subtype.val : α → ℕ) '' (S p : Set α)).encard = (k : ℕ∞) at hcard
    rw [hi.encard_image, Set.encard_coe_eq_coe_finsetCard] at hcard
    exact_mod_cast hcard
  apply hC p (mem_filter.mpr ⟨mem_univ _, hScard⟩)
  refine ⟨c, ?_⟩
  intro x hx
  apply hc x
  rw [← hSp]
  exact hx


/-- A uniform exponential lower bound with a linear, rather than quadratic,
polynomial loss. This still has limiting exponential base two. -/
lemma exponential_linear_div_lt_W {k : ℕ} (hk : 2 ≤ k) :
    2 ^ k / (16 * k) < W k := by
  apply avoid_of_linear_local_bound hk
  exact Nat.mul_div_le _ _

/-
Development of cyclic XOR products of linear trace sequences. Every theorem
in this file is auxiliary; no superexponential lower bound is asserted.
-/
namespace TraceProduct
open Finset Polynomial

lemma zero_all_of_initial {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hV : 0 < Module.finrank K V)
    (T : Module.End K V) (L : V →ₗ[K] K) (v : V)
    (h : ∀ i < Module.finrank K V, L ((T ^ i) v) = 0) :
    ∀ n : ℕ, L ((T ^ n) v) = 0 := by
  intro n
  have hne : T.charpoly ≠ 1 := by
    intro he
    have hh := T.charpoly_natDegree
    rw [he, natDegree_one] at hh
    omega
  have hdeg : (X ^ n %ₘ T.charpoly).natDegree < Module.finrank K V := by
    simpa only [T.charpoly_natDegree] using
      natDegree_modByMonic_lt (X ^ n) T.charpoly_monic hne
  rw [T.pow_eq_aeval_mod_charpoly n, aeval_eq_sum_range' hdeg]
  simp only [LinearMap.sum_apply, map_sum]
  apply sum_eq_zero
  intro i hi
  simp only [LinearMap.smul_apply, map_smul, h i (mem_range.mp hi), smul_zero]

lemma constant_all_of_initial {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hV : 0 < Module.finrank K V)
    (T : Module.End K V) (L : V →ₗ[K] K) (v : V) (c : K)
    (h : ∀ i ≤ Module.finrank K V, L ((T ^ i) v) = c) :
    ∀ n : ℕ, L ((T ^ n) v) = c := by
  let D := L.comp (T - 1)
  have he (i : ℕ) : D ((T ^ i) v) = L ((T ^ (i + 1)) v) - L ((T ^ i) v) := by
    simp only [D, LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply,
      map_sub, _root_.pow_succ', Module.End.mul_apply]
  have hz : ∀ i < Module.finrank K V, D ((T ^ i) v) = 0 := by
    intro i hi
    rw [he, h _ (by omega), h _ hi.le, sub_self]
  have hall := zero_all_of_initial hV T D v hz
  intro n
  induction n with
  | zero => exact h 0 (Nat.zero_le _)
  | succ n ih =>
    have hn := hall n
    rw [he, sub_eq_zero] at hn
    exact hn.trans ih

lemma geometric_sum_constant_all {ι : Type*} [Fintype ι]
    {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Algebra (ZMod 2) (F i)]
    [∀ i, FiniteDimensional (ZMod 2) (F i)]
    (hpos : 0 < ∑ i, Module.finrank (ZMod 2) (F i))
    (L : (i : ι) → F i →ₗ[ZMod 2] ZMod 2) (a b : ∀ i, F i) (c : ZMod 2)
    (h : ∀ n ≤ ∑ i, Module.finrank (ZMod 2) (F i), ∑ i, L i (a i * b i ^ n) = c) :
    ∀ n : ℕ, ∑ i, L i (a i * b i ^ n) = c := by
  let T : Module.End (ZMod 2) (∀ i, F i) :=
    { toFun := fun v i ↦ b i * v i
      map_add' := by intro v w; funext i; simp [mul_add]
      map_smul' := by
        intro t v
        funext i
        simp only [Pi.smul_apply, RingHom.id_apply, Algebra.smul_def]
        ring }
  let S : (∀ i, F i) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun v ↦ ∑ i, L i (v i)
      map_add' := by intro v w; simp [map_add, sum_add_distrib]
      map_smul' := by intro t v; simp [map_smul, Finset.mul_sum] }
  have hT (n : ℕ) : (T ^ n) a = fun i ↦ a i * b i ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [_root_.pow_succ', Module.End.mul_apply, ih]
      funext i
      change b i * (a i * b i ^ n) = a i * b i ^ (n + 1)
      rw [_root_.pow_succ]
      ring
  have hdim : Module.finrank (ZMod 2) (∀ i, F i) = ∑ i, Module.finrank (ZMod 2) (F i) :=
    Module.finrank_pi_fintype (ZMod 2)
  have hz : ∀ n ≤ Module.finrank (ZMod 2) (∀ i, F i), S ((T ^ n) a) = c := by
    intro n hn
    simpa only [hT, S, LinearMap.coe_mk, AddHom.coe_mk] using h n (hdim ▸ hn)
  have hall := constant_all_of_initial (hdim ▸ hpos) T S a c hz
  intro n
  simpa only [hT, S, LinearMap.coe_mk, AddHom.coe_mk] using hall n

/-- Coprime trace periods can be combined by XOR. Every positive step
below their product is protected, with forbidden length one plus the sum
of the binary dimensions. -/
theorem trace_sum_small_step {ι : Type*} [Fintype ι] [Nonempty ι]
    {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Algebra (ZMod 2) (F i)]
    [∀ i, FiniteDimensional (ZMod 2) (F i)]
    (p M : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hdim : ∀ i, Module.finrank (ZMod 2) (F i) = p i)
    (L : (i : ι) → F i →ₗ[ZMod 2] ZMod 2) (hL : ∀ i, L i 1 = 1)
    (g : ∀ i, F i) (hg : ∀ i, g i ≠ 0) (horder : ∀ i, orderOf (g i) = M i)
    (hcop : Pairwise (fun i j ↦ (M i).Coprime (M j)))
    (a d : ℕ) (hd : 0 < d) (hdP : d < ∏ i, M i) (c : ZMod 2) :
    ¬ ∀ n ≤ ∑ i, p i, ∑ i, L i (g i ^ (a + n * d)) = c := by
  classical
  intro hc
  have hpos : 0 < ∑ i, Module.finrank (ZMod 2) (F i) :=
    sum_pos (fun i _ ↦ Module.finrank_pos) univ_nonempty
  have hdimSum : (∑ i, Module.finrank (ZMod 2) (F i)) = ∑ i, p i := by
    simp_rw [hdim]
  have hinit : ∀ n ≤ ∑ i, Module.finrank (ZMod 2) (F i),
      ∑ i, L i (g i ^ a * (g i ^ d) ^ n) = c := by
    intro n hn
    have h := hc n (hdimSum ▸ hn)
    convert h using 1
    apply sum_congr rfl
    intro i _
    rw [pow_add, ← pow_mul, Nat.mul_comm d n]
  have hall := geometric_sum_constant_all hpos L (fun i ↦ g i ^ a)
    (fun i ↦ g i ^ d) c hinit
  have hex : ∃ i, ¬ M i ∣ d := by
    by_contra hn
    push_neg at hn
    have hdiv : (∏ i, M i) ∣ d := Fintype.prod_dvd_of_isRelPrime
      (fun i j hij ↦ Nat.coprime_iff_isRelPrime.mp (hcop hij)) hn
    exact (Nat.not_dvd_of_pos_of_lt hd hdP) hdiv
  obtain ⟨i, hi⟩ := hex
  let e := ∏ j ∈ univ.erase i, M j
  have hecop : (M i).Coprime e := Nat.Coprime.prod_right
    (fun j hj ↦ hcop (mem_erase.mp hj).1.symm)
  have hb : g i ^ d ≠ 1 := by
    intro he
    exact hi (by rw [← horder i]; exact orderOf_dvd_iff_pow_eq_one.mpr he)
  have hbe : (g i ^ d) ^ e ≠ 1 := by
    intro he
    have hdiv : M i ∣ d * e := by
      rw [← horder i]
      apply orderOf_dvd_iff_pow_eq_one.mpr
      simpa only [pow_mul] using he
    exact hi (hecop.dvd_mul_right.mp hdiv)
  have hother (j : ι) (hji : j ≠ i) : (g j ^ d) ^ e = 1 := by
    have hdiv : M j ∣ e := dvd_prod_of_mem M (mem_erase.mpr ⟨hji, mem_univ _⟩)
    have hpw : g j ^ e = 1 := by
      apply orderOf_dvd_iff_pow_eq_one.mp
      rwa [horder j]
    rw [← pow_mul, Nat.mul_comm d e, pow_mul, hpw, one_pow]
  apply Erdos138.FiniteFieldConstruction.not_constant_on_powers (hp i) (hdim i) (L i) (hL i)
    (mul_ne_zero (pow_ne_zero a (hg i)) (sub_ne_zero.mpr hbe))
    (pow_ne_zero d (hg i)) hb 0
  intro n hn
  have hsum : (∑ j, (L j (g j ^ a * (g j ^ d) ^ (n + e)) -
      L j (g j ^ a * (g j ^ d) ^ n))) = 0 := by
    rw [sum_sub_distrib, hall, hall, sub_self]
  rw [sum_eq_single i] at hsum
  · have he : (g i ^ a * ((g i ^ d) ^ e - 1)) * (g i ^ d) ^ n =
        g i ^ a * (g i ^ d) ^ (n + e) - g i ^ a * (g i ^ d) ^ n := by
      rw [pow_add]
      ring
    rwa [he, map_sub]
  · intro j hj hji
    rw [pow_add, hother j hji, mul_one, sub_self]
  · simp

/-- A finite set of distinct prime dimensions yields a genuine integer
lower bound with product period and additive forbidden-length cost. -/
theorem distinct_prime_product_lower_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    (∑ i, p i) * (∏ i, (2 ^ p i - 1)) < Erdos138.W ((∑ i, p i) + 1) := by
  classical
  let F (i : ι) := GaloisField 2 (p i)
  let M (i : ι) := 2 ^ p i - 1
  have hdim (i : ι) : Module.finrank (ZMod 2) (F i) = p i :=
    GaloisField.finrank 2 (hp i).ne_zero
  have hgen (i : ι) : ∃ g : F i, g ≠ 0 ∧ orderOf g = M i := by
    obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (F i)ˣ)
    refine ⟨u, u.ne_zero, ?_⟩
    rw [orderOf_units, hu, Nat.card_units, GaloisField.card 2 (p i) (hp i).ne_zero]
  choose g hg horder using hgen
  have hlinear (i : ι) : ∃ L : F i →ₗ[ZMod 2] ZMod 2, L 1 = 1 :=
    Module.Projective.exists_dual_eq_one (ZMod 2) (show (1 : F i) ≠ 0 from one_ne_zero)
  choose L hL using hlinear
  have hcop : Pairwise (fun i j ↦ (M i).Coprime (M j)) := by
    intro i j hij
    have hpq : (p i).Coprime (p j) := (Nat.coprime_primes (hp i) (hp j)).mpr
      (fun he ↦ hij (hinj he))
    change (2 ^ p i - 1).gcd (2 ^ p j - 1) = 1
    rw [Nat.pow_sub_one_gcd_pow_sub_one, hpq.gcd_eq_one]
    norm_num
  let R := ∑ i, p i
  let P := ∏ i, M i
  have hR : 0 < R := sum_pos (fun i _ ↦ (hp i).pos) univ_nonempty
  let C : Finset.Icc 1 (R * P) → Fin 2 := fun x ↦ ∑ i, L i (g i ^ x.val)
  apply Erdos138.lt_W_iff_avoiding.mpr
  refine ⟨C, ?_⟩
  rintro ⟨c, ap, ⟨a, d, hcard, heq⟩, hc⟩
  have hd : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    have hs : Subtype.val '' ap ⊆ ({a} : Set ℕ) := by
      rw [heq]
      rintro x ⟨n, hn, rfl⟩
      simp [hd0]
    have hh := Set.encard_mono hs
    rw [← ENat.card_coe_set_eq, hcard, Set.encard_singleton] at hh
    have : R + 1 ≤ 1 := by exact_mod_cast hh
    omega
  have hx (n : ℕ) (hn : n ≤ R) : ∃ x ∈ ap, x.val = a + n * d := by
    have hm : a + n * d ∈ Subtype.val '' ap := by
      rw [heq]
      refine ⟨n, ?_, ?_⟩
      · exact_mod_cast (show n < R + 1 by omega)
      · simp
    exact hm
  have ha : 1 ≤ a := by
    obtain ⟨x, _, hxi⟩ := hx 0 (Nat.zero_le _)
    have h := (Finset.mem_Icc.mp (show x.val ∈ Finset.Icc 1 (R * P) from x.property)).1
    simpa only [hxi, Nat.zero_mul, Nat.add_zero] using h
  have hend : a + R * d ≤ R * P := by
    obtain ⟨x, _, hxi⟩ := hx R le_rfl
    have h := (Finset.mem_Icc.mp (show x.val ∈ Finset.Icc 1 (R * P) from x.property)).2
    simpa only [hxi] using h
  have hdP : d < P := by nlinarith
  apply trace_sum_small_step p M hp hdim L hL g hg horder hcop a d hd hdP c
  intro n hn
  obtain ⟨x, hxp, hxi⟩ := hx n hn
  have h := hc x hxp
  change (∑ i, L i (g i ^ x.val)) = c at h
  rwa [hxi] at h

theorem primeset_lower_bound (S : Finset ℕ) (hS : S.Nonempty)
    (hp : ∀ p ∈ S, p.Prime) :
    (∑ p ∈ S, p) * (∏ p ∈ S, (2 ^ p - 1)) < Erdos138.W ((∑ p ∈ S, p) + 1) := by
  classical
  letI : Nonempty S := hS.to_subtype
  have h := distinct_prime_product_lower_bound (fun p : S ↦ p.val)
    (fun p ↦ hp p.val p.property) Subtype.val_injective
  have hs : (∑ p : S, p.val) = ∑ p ∈ S, p := Finset.sum_coe_sort S id
  have ht : (∏ p : S, (2 ^ p.val - 1)) = ∏ p ∈ S, (2 ^ p - 1) :=
    Finset.prod_coe_sort S (fun p : ℕ ↦ 2 ^ p - 1)
  change (∑ p : S, p.val) * (∏ p : S, (2 ^ p.val - 1)) <
    Erdos138.W ((∑ p : S, p.val) + 1) at h
  rwa [hs, ht] at h

end TraceProduct

/- An elementary distinct-prime subset-sum consequence of Bertrand's postulate. -/
namespace DistinctPrimeSums
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open Finset

private def Good (p : ℕ) (S : Finset ℕ) : Prop :=
  0 < p ∧ (∀ q ∈ S, q.Prime ∧ q ≤ p) ∧ 2 * p + 14 ≤ ∑ q ∈ S, q ∧
  ∀ n : ℕ, 7 ≤ n → n + 7 ≤ ∑ q ∈ S, q → ∃ T ⊆ S, ∑ q ∈ T, q = n

private lemma good_seed : Good 17 {2, 3, 5, 7, 11, 13, 17} := by
  refine ⟨by omega, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · intro n hn hsum
    have hn' : n ∈ Icc 7 51 := by
      norm_num at hsum
      simp only [mem_Icc]
      omega
    have h : ∀ n ∈ Icc 7 51, ∃ T ∈ ({2, 3, 5, 7, 11, 13, 17} : Finset ℕ).powerset,
        ∑ q ∈ T, q = n := by decide
    obtain ⟨T, hT, he⟩ := h n hn'
    exact ⟨T, mem_powerset.mp hT, he⟩

private lemma good_extend {p : ℕ} {S : Finset ℕ} (h : Good p S) :
    ∃ q : ℕ, Good q (insert q S) ∧ (∑ t ∈ S, t) < ∑ t ∈ insert q S, t := by
  obtain ⟨hp, hprime, hsum, hcover⟩ := h
  obtain ⟨q, hq, hpq, hq2⟩ := Nat.bertrand p (by omega)
  have hqS : q ∉ S := by
    intro hqS
    exact (not_le_of_gt hpq) (hprime q hqS).2
  have hsum' : (∑ t ∈ insert q S, t) = q + ∑ t ∈ S, t := sum_insert hqS
  refine ⟨q, ⟨hq.pos, ?_, ?_, ?_⟩, ?_⟩
  · intro t ht
    rcases mem_insert.mp ht with rfl | ht
    · exact ⟨hq, le_rfl⟩
    · exact ⟨(hprime t ht).1, (hprime t ht).2.trans hpq.le⟩
  · rw [hsum']
    omega
  · intro n hn hnS
    by_cases hnold : n + 7 ≤ ∑ t ∈ S, t
    · obtain ⟨T, hT, he⟩ := hcover n hn hnold
      exact ⟨T, hT.trans (subset_insert _ _), he⟩
    · rw [hsum'] at hnS
      obtain ⟨T, hT, he⟩ := hcover (n - q) (by omega) (by omega)
      refine ⟨insert q T, insert_subset_insert q hT, ?_⟩
      rw [sum_insert (fun hqT ↦ hqS (hT hqT)), he]
      omega
  · rw [hsum']
    omega

private lemma good_arbitrarily_large (n : ℕ) :
    ∃ p S, Good p S ∧ n ≤ ∑ q ∈ S, q := by
  induction n with
  | zero => exact ⟨17, _, good_seed, Nat.zero_le _⟩
  | succ n ih =>
    obtain ⟨p, S, hg, hn⟩ := ih
    obtain ⟨q, hg', hs⟩ := good_extend hg
    exact ⟨q, insert q S, hg', by omega⟩

/-- Every natural number at least seven is a sum of distinct primes. -/
theorem exists_prime_sum {n : ℕ} (hn : 7 ≤ n) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ ∑ p ∈ S, p = n := by
  obtain ⟨p, S, hp, hs⟩ := good_arbitrarily_large (n + 7)
  obtain ⟨T, hT, he⟩ := hp.2.2.2 n hn hs
  exact ⟨T, fun q hq ↦ (hp.2.1 q (hT hq)).1, he⟩

end DistinctPrimeSums

/- A uniform fixed-base lower bound derived from coprime trace products. -/
namespace UniformTraceProduct
open Finset

lemma one_sub_sum_le_product {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i ∧ f i ≤ 1) :
    1 - ∑ i ∈ S, f i ≤ ∏ i ∈ S, (1 - f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hfa := hf a (mem_insert_self _ _)
    have hfS := fun i hi ↦ hf i (mem_insert_of_mem hi)
    have hs : 0 ≤ ∑ i ∈ S, f i := sum_nonneg (fun i hi ↦ (hfS i hi).1)
    rw [sum_insert ha, prod_insert ha]
    calc
      1 - (f a + ∑ i ∈ S, f i) ≤ (1 - f a) * (1 - ∑ i ∈ S, f i) := by
        nlinarith [mul_nonneg hfa.1 hs]
      _ ≤ (1 - f a) * ∏ i ∈ S, (1 - f i) :=
        mul_le_mul_of_nonneg_left (ih hfS) (by linarith)

lemma binary_reciprocal_sum (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    (∑ p ∈ S, (1 / 2 : ℝ) ^ p) ≤ 1 / 2 := by
  have h0 : 0 ∉ S := by intro h; have := hS 0 h; omega
  have h1 : 1 ∉ S := by intro h; have := hS 1 h; omega
  have h := sum_le_hasSum (insert 0 (insert 1 S))
    (fun n _ ↦ pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n)
    (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  simp only [sum_insert (show 0 ∉ insert 1 S by simp [h0]), sum_insert h1,
    pow_zero, pow_one] at h
  norm_num at h
  linarith

lemma mersenne_product_bound (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    2 ^ (∑ p ∈ S, p) ≤ 2 * ∏ p ∈ S, (2 ^ p - 1) := by
  have hsum := binary_reciprocal_sum S hS
  have hprod := one_sub_sum_le_product S (fun p ↦ (1 / 2 : ℝ) ^ p)
    (fun p hp ↦ ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩)
  have he : (∏ p ∈ S, (1 - (1 / 2 : ℝ) ^ p)) =
      (∏ p ∈ S, ((2 : ℝ) ^ p - 1)) / (2 : ℝ) ^ (∑ p ∈ S, p) := by
    rw [← prod_pow_eq_pow_sum S (fun p ↦ p), ← prod_div_distrib]
    apply prod_congr rfl
    intro p hp
    rw [div_pow, one_pow]
    field_simp
  rw [he] at hprod
  have hhalf : (1 / 2 : ℝ) ≤
      (∏ p ∈ S, ((2 : ℝ) ^ p - 1)) / (2 : ℝ) ^ (∑ p ∈ S, p) := by linarith
  have hmul := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (∑ p ∈ S, p))).mp hhalf
  have hc : ((∏ p ∈ S, (2 ^ p - 1) : ℕ) : ℝ) = ∏ p ∈ S, ((2 : ℝ) ^ p - 1) := by
    push_cast
    apply prod_congr rfl
    intro p hp
    rw [Nat.cast_sub Nat.one_le_two_pow]
    norm_cast
  have hr : (2 : ℝ) ^ (∑ p ∈ S, p) ≤ 2 * ((∏ p ∈ S, (2 ^ p - 1) : ℕ) : ℝ) := by
    rw [hc]
    linarith
  exact_mod_cast hr

/-- Uniform lower bound, still with limiting exponential base two. -/
theorem lower_bound {k : ℕ} (hk : 8 ≤ k) :
    (k - 1) * 2 ^ (k - 2) < Erdos138.W k := by
  obtain ⟨S, hp, hs⟩ := DistinctPrimeSums.exists_prime_sum (show 7 ≤ k - 1 by omega)
  have hne : S.Nonempty := by
    by_contra h
    have he : S = ∅ := not_nonempty_iff_eq_empty.mp h
    simp [he] at hs
    omega
  have ht := TraceProduct.primeset_lower_bound S hne hp
  have hm := mersenne_product_bound S (fun p hpS ↦ (hp p hpS).two_le)
  rw [hs] at hm ht
  have hpow : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by
    rw [show k - 1 = (k - 2) + 1 by omega, _root_.pow_succ, Nat.mul_comm]
  rw [hpow] at hm
  have hle : 2 ^ (k - 2) ≤ ∏ p ∈ S, (2 ^ p - 1) := by omega
  have hk' : k - 1 + 1 = k := by omega
  rw [hk'] at ht
  exact (Nat.mul_le_mul_left (k - 1) hle).trans_lt ht

end UniformTraceProduct

/- An unconditional uniform root bound, not divergence to infinity. -/
namespace UniformRootLower
open Filter

lemma two_pow_lt {k : ℕ} (hk : 8 ≤ k) : 2 ^ k < Erdos138.W k := by
  have he : 2 ^ k = 4 * 2 ^ (k - 2) := by
    nth_rw 1 [show k = (k - 2) + 2 by omega]
    rw [pow_add]
    ring
  calc
    2 ^ k = 4 * 2 ^ (k - 2) := he
    _ ≤ (k - 1) * 2 ^ (k - 2) := Nat.mul_le_mul_right _ (by omega)
    _ < Erdos138.W k := UniformTraceProduct.lower_bound hk

/-- Strictly exceeds two at every length at least eight. -/
theorem root_gt_two {k : ℕ} (hk : 8 ≤ k) :
    (2 : ℝ) < (Erdos138.W k : ℝ) ^ (1 / (k : ℝ)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hp : (2 : ℝ) ^ (k : ℝ) < (Erdos138.W k : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast two_pow_lt hk
  simpa only [one_div] using
    (Real.lt_rpow_inv_iff_of_pos (by norm_num : (0 : ℝ) ≤ 2)
      (Nat.cast_nonneg (Erdos138.W k)) hk').mpr hp

theorem eventually_root_gt_two :
    ∀ᶠ k : ℕ in atTop, (2 : ℝ) < (Erdos138.W k : ℝ) ^ (1 / (k : ℝ)) := by
  filter_upwards [eventually_ge_atTop 8] with k hk
  exact root_gt_two hk

end UniformRootLower

/-
Distinct-prime representations from a finite interval-covering seed.
The concrete seed below avoids every prime below seventeen.
-/
namespace LargePrimeSums
open Finset
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option Elab.async false

/-- An interval of subset sums wide enough to survive a Bertrand extension. -/
def Good (B A p : ℕ) (S : Finset ℕ) : Prop :=
  0 < p ∧ B ≤ p ∧
  (∀ q ∈ S, q.Prime ∧ B ≤ q ∧ q ≤ p) ∧
  2*p+2*A ≤ ∑ q ∈ S, q ∧
  ∀ n : ℕ, A ≤ n → n+A ≤ ∑ q ∈ S, q →
    ∃ T ⊆ S, ∑ q ∈ T, q=n

lemma good_extend {B A p : ℕ} {S : Finset ℕ} (h : Good B A p S) :
    ∃ q : ℕ, Good B A q (insert q S) ∧
      (∑ t ∈ S, t) < ∑ t ∈ insert q S, t := by
  obtain ⟨hp,hBp,hprime,hsum,hcover⟩ := h
  obtain ⟨q,hq,hpq,hq2⟩ := Nat.bertrand p (by omega)
  have hqS : q ∉ S := by
    intro hqS
    exact (not_le_of_gt hpq) (hprime q hqS).2.2
  have hsum' : (∑ t ∈ insert q S, t)=q+∑ t ∈ S, t := sum_insert hqS
  refine ⟨q,⟨hq.pos,hBp.trans hpq.le,?_,?_,?_⟩,?_⟩
  · intro t ht
    rcases mem_insert.mp ht with rfl | ht
    · exact ⟨hq,hBp.trans hpq.le,le_rfl⟩
    · exact ⟨(hprime t ht).1,(hprime t ht).2.1,(hprime t ht).2.2.trans hpq.le⟩
  · rw [hsum']
    omega
  · intro n hn hnS
    by_cases hold : n+A ≤ ∑ t ∈ S, t
    · obtain ⟨T,hT,he⟩ := hcover n hn hold
      exact ⟨T,hT.trans (subset_insert _ _),he⟩
    · rw [hsum'] at hnS
      obtain ⟨T,hT,he⟩ := hcover (n-q) (by omega) (by omega)
      refine ⟨insert q T,insert_subset_insert q hT,?_⟩
      rw [sum_insert (fun hqT => hqS (hT hqT)),he]
      omega
  · rw [hsum']
    omega

lemma arbitrarily_large {B A p : ℕ} {S : Finset ℕ}
    (hS : Good B A p S) (n : ℕ) :
    ∃ q T, Good B A q T ∧ n ≤ ∑ r ∈ T, r := by
  induction n with
  | zero => exact ⟨p,S,hS,Nat.zero_le _⟩
  | succ n ih =>
    obtain ⟨q,T,hT,hn⟩ := ih
    obtain ⟨r,hr,hs⟩ := good_extend hT
    exact ⟨r,insert r T,hr,by omega⟩

/-- A single verified finite seed gives all sufficiently large sums, with
no reintroduction of the excluded small primes. -/
theorem exists_prime_sum_of_seed {B A p : ℕ} {S : Finset ℕ}
    (hS : Good B A p S) {n : ℕ} (hn : A ≤ n) :
    ∃ T : Finset ℕ, (∀ q ∈ T, q.Prime ∧ B ≤ q) ∧ ∑ q ∈ T, q=n := by
  obtain ⟨q,T,hT,hs⟩ := arbitrarily_large hS (n+A)
  obtain ⟨U,hU,he⟩ := hT.2.2.2.2 n hn hs
  exact ⟨U,fun r hr => ⟨(hT.2.2.1 r (hU hr)).1,(hT.2.2.1 r (hU hr)).2.1⟩,he⟩

private def seed : Finset ℕ := {17,19,23,29,31,37,41,43,47,53}

private lemma seed_cover : ∀ n ∈ Icc 99 241,
    ∃ T ∈ seed.powerset, ∑ q ∈ T, q=n := by
  decide +kernel

private lemma good_seed : Good 17 99 53 seed := by
  refine ⟨by omega,by omega,?_,?_,?_⟩
  · norm_num [seed]
  · norm_num [seed]
  · intro n hn hsum
    have hns : n ∈ Icc 99 241 := by
      norm_num [seed] at hsum
      exact mem_Icc.mpr ⟨hn,by omega⟩
    obtain ⟨T,hT,he⟩ := seed_cover n hns
    exact ⟨T,mem_powerset.mp hT,he⟩

/-- Every integer at least 99 is a sum of distinct primes at least 17. -/
theorem exists_prime_sum {n : ℕ} (hn : 99 ≤ n) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ 17 ≤ p) ∧ ∑ p ∈ S, p=n :=
  exists_prime_sum_of_seed good_seed hn

end LargePrimeSums

/-
A sharper uniform trace-product lower bound, using only prime dimensions
at least seventeen. The exponential base remains two; this does not prove
that the roots of the van der Waerden numbers tend to infinity.
-/
namespace LargeTraceProduct
open Finset
set_option maxHeartbeats 1000000
set_option Elab.async false

lemma binary_tail_sum (r : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, r+1 ≤ p) :
    (∑ p ∈ S, (1/2 : ℝ)^p) ≤ (1/2 : ℝ)^r := by
  let T := S.image (fun p => p-(r+1))
  have hsum : (∑ n ∈ T, (1/2 : ℝ)^n) ≤ 2 := by
    have h := sum_le_hasSum T
      (fun n _ => pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) n)
      (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num))
    norm_num at h
    exact h
  have he : (∑ p ∈ S, (1/2 : ℝ)^p) = (1/2 : ℝ)^(r+1)*∑ n ∈ T, (1/2 : ℝ)^n := by
    dsimp only [T]
    rw [sum_image]
    · rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      rw [← pow_add,Nat.add_sub_of_le (hS p hp)]
    · intro x hx y hy he
      have hx' := hS x hx
      have hy' := hS y hy
      dsimp only at he
      omega
  rw [he]
  calc
    _ ≤ (1/2 : ℝ)^(r+1)*2 := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (1/2 : ℝ)^r := by rw [pow_succ]; ring

/-- Uniform control of the product loss when small dimensions are excluded. -/
lemma mersenne_product_tail (r : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, r+1 ≤ p) :
    (2^r-1)*2^(∑ p ∈ S, p) ≤ 2^r*∏ p ∈ S, (2^p-1) := by
  have hsum := binary_tail_sum r S hS
  have hprod := UniformTraceProduct.one_sub_sum_le_product S (fun p => (1/2 : ℝ)^p)
    (fun p _ => ⟨by positivity,pow_le_one₀ (by norm_num) (by norm_num)⟩)
  have he : (∏ p ∈ S, (1-(1/2 : ℝ)^p)) =
      (∏ p ∈ S, ((2 : ℝ)^p-1))/(2 : ℝ)^(∑ p ∈ S, p) := by
    rw [← prod_pow_eq_pow_sum S (fun p => p),← prod_div_distrib]
    apply prod_congr rfl
    intro p _
    rw [div_pow,one_pow]
    field_simp
  rw [he] at hprod
  have hlo : 1-(1/2 : ℝ)^r ≤
      (∏ p ∈ S, ((2 : ℝ)^p-1))/(2 : ℝ)^(∑ p ∈ S, p) := by linarith
  have hmul := mul_le_mul_of_nonneg_left
    ((le_div_iff₀ (by positivity : (0 : ℝ) < 2^(∑ p ∈ S, p))).mp hlo)
    (show (0 : ℝ) ≤ 2^r by positivity)
  have hleft : (2 : ℝ)^r*((1-(1/2 : ℝ)^r)*2^(∑ p ∈ S, p)) =
      ((2 : ℝ)^r-1)*2^(∑ p ∈ S, p) := by
    rw [one_div,inv_pow]
    field_simp
  rw [hleft] at hmul
  have hc : ((∏ p ∈ S, (2^p-1) : ℕ) : ℝ) = ∏ p ∈ S, ((2 : ℝ)^p-1) := by
    push_cast
    apply prod_congr rfl
    intro p _
    rw [Nat.cast_sub Nat.one_le_two_pow]
    norm_cast
  rw [← hc] at hmul
  have hcast : (((2^r-1)*2^(∑ p ∈ S, p) : ℕ) : ℝ) =
      ((2 : ℝ)^r-1)*2^(∑ p ∈ S, p) := by
    rw [Nat.cast_mul,Nat.cast_sub Nat.one_le_two_pow]
    norm_cast
  rw [← hcast] at hmul
  exact_mod_cast hmul

/-- A nearly lossless uniform Berlekamp-product bound, still with base two. -/
theorem lower_bound {k : ℕ} (hk : 100 ≤ k) :
    65535*(k-1)*2^(k-17) < Erdos138.W k := by
  obtain ⟨S,hp,hs⟩ := LargePrimeSums.exists_prime_sum (show 99 ≤ k-1 by omega)
  have hne : S.Nonempty := by
    by_contra hn
    have he : S=∅ := not_nonempty_iff_eq_empty.mp hn
    simp [he] at hs
    omega
  have ht := TraceProduct.primeset_lower_bound S hne (fun p hpS => (hp p hpS).1)
  have hm := mersenne_product_tail 16 S (fun p hpS => (hp p hpS).2)
  rw [hs] at ht hm
  norm_num only [Nat.reducePow,Nat.reduceSub] at hm
  have hpow : 2^(k-1)=65536*2^(k-17) := by
    rw [show k-1=(k-17)+16 by omega,pow_add]
    norm_num
    ring
  rw [hpow] at hm
  have hle : 65535*2^(k-17) ≤ ∏ p ∈ S, (2^p-1) := by nlinarith
  rw [show k-1+1=k by omega] at ht
  calc
    _ = (k-1)*(65535*2^(k-17)) := by ring
    _ ≤ (k-1)*∏ p ∈ S, (2^p-1) := Nat.mul_le_mul_left _ hle
    _ < Erdos138.W k := ht

/-- Equivalent real-valued form, showing the improved constant explicitly. -/
theorem real_lower_bound {k : ℕ} (hk : 100 ≤ k) :
    (65535/65536 : ℝ)*(k-1)*2^(k-1) < (Erdos138.W k : ℝ) := by
  have h := lower_bound hk
  have he : (65535/65536 : ℝ)*(k-1)*2^(k-1) =
      ((65535*(k-1)*2^(k-17) : ℕ) : ℝ) := by
    rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num only [Nat.cast_ofNat,Nat.cast_pow,Nat.cast_one]
    rw [show k-1=(k-17)+16 by omega,pow_add]
    norm_num
    ring
  rw [he]
  exact_mod_cast h

end LargeTraceProduct

/--
In [Er80] Erdős asks whether
$$ \lim_{k \to \infty} (W(k))^{1/k} = \infty $$
-/
theorem erdos_138 : atTop.Tendsto (fun k => (W k : ℝ)^(1/(k : ℝ))) atTop := by
  sorry

end Erdos138
