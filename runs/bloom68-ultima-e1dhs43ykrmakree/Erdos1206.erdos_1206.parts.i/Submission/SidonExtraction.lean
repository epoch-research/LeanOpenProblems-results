import FormalConjecturesUtil

/-!
# Finite hypergraph alteration and Sidon extraction

All sampling below is a count over the finite set of functions to `Fin q`.
There is no measure theory and no number-theoretic assumption about cubes.

* `exists_large_avoiding`: a generic finite hypergraph alteration lemma, requiring
  only that edges have at least three vertices and `2*|E| ≤ q²*|A|`.
* `isSidon_iff_avoids_badSupports`: the counted supports are exactly the obstructions
  to the imported `IsSidon` condition (including repeated summands).
* `exists_sidon_subset_of_badSupports_le`: if `|badSupports A| ≤ K*|A|` and
  `0 < q`, `2*K ≤ q²`, there is a Sidon `B ⊆ A` with `|A| ≤ 2*q*|B|`.
* `exists_sidon_subset_const_sq`: choosing `q = K+2` gives `|A| ≤ q²*|B|`.

The missing number-theoretic input for any future application to cubes is a bound
on the number of bad supports. No such bound is asserted here.
-/

open scoped BigOperators

namespace SidonExtraction

/-- A vertex set avoids a finite hypergraph if it contains none of its edges. -/
def Avoids {α : Type*} (E : Finset (Finset α)) (B : Finset α) : Prop :=
  ∀ e ∈ E, ¬ e ⊆ B

/-- Deleting at most one vertex per nonempty edge leaves an edge-free set. -/
theorem exists_avoiding_card_add {α : Type*} (S : Finset α)
    (E : Finset (Finset α)) (hne : ∀ e ∈ E, (e : Finset α).Nonempty) :
    ∃ B ⊆ S, Avoids E B ∧ S.card ≤ B.card + E.card := by
  classical
  induction E using Finset.induction_on with
  | empty =>
      exact ⟨S, Finset.Subset.refl S, by simp [Avoids], by simp⟩
  | @insert e E he ih =>
      obtain ⟨B, hBS, hBE, hcard⟩ := ih (fun f hf => hne f (Finset.mem_insert_of_mem hf))
      by_cases heb : e ⊆ B
      · obtain ⟨x, hx⟩ := hne e (Finset.mem_insert_self _ _)
        refine ⟨B.erase x, (Finset.erase_subset x B).trans hBS, ?_, ?_⟩
        · intro f hf hfb
          rcases Finset.mem_insert.mp hf with rfl | hf
          · exact (Finset.notMem_erase x B) (hfb hx)
          · exact hBE f hf (hfb.trans (Finset.erase_subset x B))
        · have hc := Finset.card_erase_add_one (heb hx)
          rw [Finset.card_insert_of_notMem he]
          omega
      · refine ⟨B, hBS, ?_, ?_⟩
        · intro f hf
          rcases Finset.mem_insert.mp hf with rfl | hf
          · exact heb
          · exact hBE f hf
        · rw [Finset.card_insert_of_notMem he]
          omega

/-- Double counting a finite relation. -/
theorem sum_card_filter_swap {α β : Type*} (s : Finset α) (t : Finset β)
    (R : α → β → Prop) [DecidableRel R] :
    (∑ x ∈ s, (t.filter (R x)).card) =
      ∑ y ∈ t, (s.filter (fun x => R x y)).card := by
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

/-- The number of labelings that give a prescribed label to every vertex of `e`. -/
theorem card_labelings_constant {V : Type*} [Fintype V] [DecidableEq V] (e : Finset V)
    {q : ℕ} (c : Fin q) :
    ((Finset.univ : Finset (V → Fin q)).filter (fun f => ∀ x ∈ e, f x = c)).card =
      q ^ (Fintype.card V - e.card) := by
  classical
  have heq :
      ((Finset.univ : Finset (V → Fin q)).filter (fun f => ∀ x ∈ e, f x = c)) =
        Fintype.piFinset (fun x : V => if x ∈ e then {c} else Finset.univ) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h x
      by_cases hx : x ∈ e <;> simp [hx, h]
    · intro h x hx
      simpa [hx] using h x
  rw [heq, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, Finset.card_singleton, Finset.card_univ, Fintype.card_fin]
  have hprod : (∏ x : V, if x ∈ e then 1 else q) = ∏ x ∈ eᶜ, q := by
    rw [← Finset.prod_ite_mem_eq eᶜ (fun _ => q)]
    apply Finset.prod_congr rfl
    intro x hx
    by_cases h : x ∈ e <;> simp [h]
  rw [hprod]
  simp [Finset.card_compl]

/-- Finite-labeling alteration: a hypergraph with edges of size at least three
has an independent set of size at least `|V| / (2*q)` whenever
`2*|E| ≤ q²*|V|`.  No bound on the maximum edge size is needed. -/
theorem exists_large_avoiding_fintype {V : Type*} [Fintype V]
    (E : Finset (Finset V)) (q : ℕ) (hq : 0 < q)
    (hsize : ∀ e ∈ E, 3 ≤ (e : Finset V).card)
    (hcount : 2 * E.card ≤ q ^ 2 * Fintype.card V) :
    ∃ B : Finset V, Avoids E B ∧ Fintype.card V ≤ 2 * q * B.card := by
  classical
  by_cases hn : 3 ≤ Fintype.card V
  · let n := Fintype.card V
    let c : Fin q := ⟨0, hq⟩
    let S : (V → Fin q) → Finset V := fun f => Finset.univ.filter (fun x => f x = c)
    let T : (V → Fin q) → Finset (Finset V) := fun f => E.filter (fun e => e ⊆ S f)
    have hsumS : (∑ f : V → Fin q, (S f).card) = n * q ^ (n - 1) := by
      calc
        _ = ∑ x : V,
            ((Finset.univ : Finset (V → Fin q)).filter (fun f => f x = c)).card :=
          sum_card_filter_swap (Finset.univ : Finset (V → Fin q))
            (Finset.univ : Finset V) (fun f x => f x = c)
        _ = ∑ _x : V, q ^ (n - 1) := by
          apply Finset.sum_congr rfl
          intro x hx
          simpa only [Finset.mem_singleton, forall_eq, Finset.card_singleton]
            using card_labelings_constant ({x} : Finset V) c
        _ = _ := by simp [n]
    have hsumT : (∑ f : V → Fin q, (T f).card) ≤ E.card * q ^ (n - 3) := by
      calc
        _ = ∑ e ∈ E,
            ((Finset.univ : Finset (V → Fin q)).filter (fun f => e ⊆ S f)).card :=
          sum_card_filter_swap (Finset.univ : Finset (V → Fin q))
            E (fun f e => e ⊆ S f)
        _ = ∑ e ∈ E, q ^ (n - e.card) := by
          apply Finset.sum_congr rfl
          intro e he
          simpa [S, Finset.subset_iff] using card_labelings_constant e c
        _ ≤ ∑ _e ∈ E, q ^ (n - 3) := by
          apply Finset.sum_le_sum
          intro e he
          exact pow_le_pow_right₀ (by omega) (Nat.sub_le_sub_left (hsize e he) n)
        _ = _ := by simp
    have hp3 : q ^ n = q ^ 3 * q ^ (n - 3) := by
      rw [← pow_add]
      congr 1
      dsimp [n]
      omega
    have hp1 : q ^ (n - 1) = q ^ 2 * q ^ (n - 3) := by
      rw [← pow_add]
      congr 1
      dsimp [n]
      omega
    have hsum :
        (∑ f : V → Fin q, (n + 2 * q * (T f).card)) ≤
          ∑ f : V → Fin q, 2 * q * (S f).card := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      rw [hsumS]
      calc
        q ^ n * n + 2 * q * ∑ f : V → Fin q, (T f).card
            ≤ q ^ n * n + 2 * q * (E.card * q ^ (n - 3)) := by gcongr
        _ ≤ 2 * q * (n * q ^ (n - 1)) := by
          have hm := Nat.mul_le_mul_right (q * q ^ (n - 3)) hcount
          change 2 * E.card * (q * q ^ (n - 3)) ≤
            q ^ 2 * n * (q * q ^ (n - 3)) at hm
          rw [hp3, hp1]
          nlinarith only [hm]
    have hu : (Finset.univ : Finset (V → Fin q)).Nonempty :=
      ⟨fun _ => c, Finset.mem_univ _⟩
    obtain ⟨f, _, hf⟩ := Finset.exists_le_of_sum_le hu hsum
    obtain ⟨B, hBS, hBT, hcard⟩ := exists_avoiding_card_add (S f) (T f) (by
      intro e he
      exact Finset.card_pos.mp (by
        have := hsize e (Finset.mem_filter.mp he).1
        omega))
    refine ⟨B, ?_, ?_⟩
    · intro e he heb
      exact hBT e (Finset.mem_filter.mpr ⟨he, heb.trans hBS⟩) heb
    · have hc := Nat.mul_le_mul_left (2 * q) hcard
      change n ≤ 2 * q * B.card
      nlinarith only [hf, hc]
  · have hempty : E = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      exact hn ((hsize e he).trans (Finset.card_le_univ e))
    refine ⟨Finset.univ, by simp [Avoids, hempty], ?_⟩
    simpa only [Finset.card_univ, one_mul] using
      Nat.mul_le_mul_right (Fintype.card V) (show 1 ≤ 2 * q by omega)

/-- The alteration lemma on an arbitrary finite vertex set. -/
theorem exists_large_avoiding {α : Type*} (A : Finset α)
    (E : Finset (Finset α)) (q : ℕ) (hq : 0 < q)
    (hsub : ∀ e ∈ E, e ⊆ A)
    (hsize : ∀ e ∈ E, 3 ≤ (e : Finset α).card)
    (hcount : 2 * E.card ≤ q ^ 2 * A.card) :
    ∃ B ⊆ A, Avoids E B ∧ A.card ≤ 2 * q * B.card := by
  classical
  let E' : Finset (Finset A) := E.image (fun e => e.subtype (· ∈ A))
  have hsize' : ∀ e ∈ E', 3 ≤ (e : Finset A).card := by
    intro e' he'
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp he'
    simpa [Finset.card_subtype, Finset.filter_eq_self.mpr (hsub e he)] using hsize e he
  have hcount' : 2 * E'.card ≤ q ^ 2 * Fintype.card A := by
    calc
      2 * E'.card ≤ 2 * E.card := Nat.mul_le_mul_left 2 Finset.card_image_le
      _ ≤ q ^ 2 * A.card := hcount
      _ = _ := by simp
  obtain ⟨B, hBE, hBcard⟩ := exists_large_avoiding_fintype E' q hq hsize' hcount'
  refine ⟨B.map (Function.Embedding.subtype (· ∈ A)), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hx
    exact b.property
  · intro e he heb
    apply hBE (e.subtype (· ∈ A)) (Finset.mem_image_of_mem _ he)
    intro x hx
    exact (Finset.mem_map' (Function.Embedding.subtype (· ∈ A))).mp
      (heb (Finset.mem_subtype.mp hx))
  · simpa using hBcard

/-- A linear number of edges gives a linearly sized independent set.
The sampling denominator can be any positive `q` with `2*K ≤ q²`. -/
theorem exists_large_avoiding_of_card_le {α : Type*} (A : Finset α)
    (E : Finset (Finset α)) (K q : ℕ) (hq : 0 < q)
    (hKq : 2 * K ≤ q ^ 2)
    (hsub : ∀ e ∈ E, e ⊆ A)
    (hsize : ∀ e ∈ E, 3 ≤ (e : Finset α).card)
    (hcount : E.card ≤ K * A.card) :
    ∃ B ⊆ A, Avoids E B ∧ A.card ≤ 2 * q * B.card := by
  apply exists_large_avoiding A E q hq hsub hsize
  calc
    2 * E.card ≤ 2 * (K * A.card) := Nat.mul_le_mul_left 2 hcount
    _ = (2 * K) * A.card := by ring
    _ ≤ q ^ 2 * A.card := Nat.mul_le_mul_right A.card hKq

/-- The support of a nontrivial equality `a+b=c+d`, with its size made explicit.
In particular, repeated summands are allowed: three-element obstructions are included. -/
def IsBadSupport (e : Finset ℕ) : Prop :=
  3 ≤ e.card ∧ e.card ≤ 4 ∧
    ∃ a b c d : ℕ, e = {a, b, c, d} ∧ a + b = c + d ∧
      ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))

/-- Distinct bad supports in `A`, rather than ordered additive quadruples. -/
noncomputable def badSupports (A : Finset ℕ) : Finset (Finset ℕ) := by
  classical
  exact A.powerset.filter IsBadSupport

@[simp]
theorem mem_badSupports {A e : Finset ℕ} :
    e ∈ badSupports A ↔ e ⊆ A ∧ IsBadSupport e := by
  classical
  simp [badSupports]

/-- A nontrivial additive collision in `ℕ` cannot have a support of size one or two. -/
theorem three_le_card_support {a b c d : ℕ} (hsum : a + b = c + d)
    (hnt : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    3 ≤ ({a, b, c, d} : Finset ℕ).card := by
  change 2 < ({a, b, c, d} : Finset ℕ).card
  apply Finset.two_lt_card_iff.mpr
  by_cases hab : a = b
  · refine ⟨a, c, d, by simp, by simp, by simp, ?_, ?_, ?_⟩ <;> omega
  · refine ⟨a, b, c, by simp, by simp, by simp, hab, ?_, ?_⟩ <;> omega

/-- Every nontrivial collision gives one of the bad supports being counted. -/
theorem isBadSupport_of_collision {a b c d : ℕ} (hsum : a + b = c + d)
    (hnt : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    IsBadSupport {a, b, c, d} :=
  ⟨three_le_card_support hsum hnt, Finset.card_le_four, a, b, c, d, rfl, hsum, hnt⟩

/-- Avoiding these supports is exactly the standard unordered-pair Sidon condition. -/
theorem isSidon_iff_avoids_badSupports {A B : Finset ℕ} (hBA : B ⊆ A) :
    IsSidon (B : Set ℕ) ↔ Avoids (badSupports A) B := by
  constructor
  · intro hB e he heb
    obtain ⟨_, _, _, a, b, c, d, rfl, hsum, hnt⟩ := mem_badSupports.mp he
    apply hnt
    exact hB a (heb (by simp)) c (heb (by simp)) b (heb (by simp)) d (heb (by simp)) hsum
  · intro hB a ha c hc b hb d hd hsum
    by_contra hnt
    have heB : ({a, b, c, d} : Finset ℕ) ⊆ B := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨ha, hb, hc, hd⟩
    exact hB _ (mem_badSupports.mpr ⟨heB.trans hBA, isBadSupport_of_collision hsum hnt⟩) heB

/-- Sidon extraction with the sharper `2*q` denominator, for any positive `q`
satisfying `2*K ≤ q²`. -/
theorem exists_sidon_subset_of_badSupports_le (A : Finset ℕ) (K q : ℕ)
    (hq : 0 < q) (hKq : 2 * K ≤ q ^ 2)
    (hcount : (badSupports A).card ≤ K * A.card) :
    ∃ B ⊆ A, IsSidon (B : Set ℕ) ∧ A.card ≤ 2 * q * B.card := by
  obtain ⟨B, hBA, hB, hcard⟩ :=
    exists_large_avoiding_of_card_le A (badSupports A) K q hq hKq
      (fun e he => (mem_badSupports.mp he).1)
      (fun e he => (mem_badSupports.mp he).2.1) hcount
  exact ⟨B, hBA, (isSidon_iff_avoids_badSupports hBA).mpr hB, hcard⟩

/-- The requested square-denominator bound. -/
theorem exists_sidon_subset_sq_bound (A : Finset ℕ) (K q : ℕ)
    (hq : 2 ≤ q) (hKq : 2 * K ≤ q ^ 2)
    (hcount : (badSupports A).card ≤ K * A.card) :
    ∃ B ⊆ A, IsSidon (B : Set ℕ) ∧ A.card ≤ q ^ 2 * B.card := by
  obtain ⟨B, hBA, hB, hcard⟩ :=
    exists_sidon_subset_of_badSupports_le A K q (by omega) hKq hcount
  refine ⟨B, hBA, hB, hcard.trans ?_⟩
  exact Nat.mul_le_mul_right B.card (show 2 * q ≤ q ^ 2 by nlinarith)

/-- A completely explicit choice of a constant depending only on `K`.
This is linear in `A.card`; no number-theoretic hypothesis is hidden in the conclusion. -/
theorem exists_sidon_subset_linear (A : Finset ℕ) (K : ℕ)
    (hcount : (badSupports A).card ≤ K * A.card) :
    ∃ B ⊆ A, IsSidon (B : Set ℕ) ∧ A.card ≤ 2 * (K + 2) * B.card := by
  exact exists_sidon_subset_of_badSupports_le A K (K + 2) (by omega) (by nlinarith) hcount

/-- In particular, taking `q = K+2` gives `q²*|B| ≥ |A|`. -/
theorem exists_sidon_subset_const_sq (A : Finset ℕ) (K : ℕ)
    (hcount : (badSupports A).card ≤ K * A.card) :
    ∃ B ⊆ A, IsSidon (B : Set ℕ) ∧ A.card ≤ (K + 2) ^ 2 * B.card := by
  exact exists_sidon_subset_sq_bound A K (K + 2) (by omega) (by nlinarith) hcount

/- Axiom audit: only Lean's standard logical axioms; in particular no `sorryAx`. -/
#print axioms exists_avoiding_card_add
#print axioms sum_card_filter_swap
#print axioms card_labelings_constant
#print axioms exists_large_avoiding_fintype
#print axioms exists_large_avoiding
#print axioms exists_large_avoiding_of_card_le
#print axioms mem_badSupports
#print axioms three_le_card_support
#print axioms isBadSupport_of_collision
#print axioms isSidon_iff_avoids_badSupports
#print axioms exists_sidon_subset_of_badSupports_le
#print axioms exists_sidon_subset_sq_bound
#print axioms exists_sidon_subset_linear
#print axioms exists_sidon_subset_const_sq

end SidonExtraction
