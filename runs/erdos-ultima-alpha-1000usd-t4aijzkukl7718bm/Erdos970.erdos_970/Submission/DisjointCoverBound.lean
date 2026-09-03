import FormalConjecturesUtil

/-!
A quadratic length bound for exact covers by pairwise-coprime residue classes.
The no-overlap hypothesis is essential to this argument. It is not assumed in
the Jacobsthal conjecture, so this file alone does not settle Erdős 970.
-/
namespace Erdos970.DisjointCover
open Finset

/-- Positions hit by one class in the finite interval. -/
def hits (m p a : ℕ) : Finset ℕ := (range m).filter (fun i => i ≡ a [MOD p])

/-- Every position is covered by exactly one of the selected classes. -/
def ExactCover (P : Finset ℕ) (r : ℕ → ℕ) (m : ℕ) : Prop :=
  (∀ i < m, ∃ p ∈ P, i ≡ r p [MOD p]) ∧
  (∀ i < m, ∀ p ∈ P, ∀ q ∈ P,
    i ≡ r p [MOD p] → i ≡ r q [MOD q] → p = q)

lemma hits_card_le (m p a : ℕ) : (hits m p a).card ≤ (m - 1) / p + 1 := by
  classical
  apply (card_le_card_of_injOn (s := hits m p a)
    (t := range ((m - 1) / p + 1)) (fun i => i / p) ?_ ?_).trans_eq (card_range _)
  · intro i hi
    have him := mem_range.mp (mem_filter.mp hi).1
    dsimp only
    exact mem_range.mpr (by have : i / p ≤ (m - 1) / p := Nat.div_le_div_right (show i ≤ m - 1 by omega); omega)
  · intro i hi j hj hij
    change i ∈ hits m p a at hi
    change j ∈ hits m p a at hj
    change i / p = j / p at hij
    have hiq : i ≡ a [MOD p] := (mem_filter.mp hi).2
    have hjq : j ≡ a [MOD p] := (mem_filter.mp hj).2
    have hmod : i % p = j % p := hiq.trans hjq.symm
    have hi' := Nat.mod_add_div i p
    have hj' := Nat.mod_add_div j p
    rw [hij, hmod] at hi'
    omega

lemma cover_card_le_sum {P : Finset ℕ} {r : ℕ → ℕ} {m : ℕ}
    (h : ∀ i < m, ∃ p ∈ P, i ≡ r p [MOD p]) :
    m ≤ ∑ p ∈ P, (hits m p (r p)).card := by
  classical
  have hsub : range m ⊆ P.biUnion (fun p => hits m p (r p)) := by
    intro i hi
    obtain ⟨p, hp, hip⟩ := h i (mem_range.mp hi)
    exact mem_biUnion.mpr ⟨p, hp, mem_filter.mpr ⟨hi, hip⟩⟩
  have hh := (card_le_card hsub).trans card_biUnion_le
  simpa only [card_range] using hh

/-- Otherwise CRT would force an overlap inside the interval. -/
lemma product_gt_of_exact {P : Finset ℕ} {r : ℕ → ℕ} {m p q : ℕ}
    (h : ExactCover P r m) (hp : p ∈ P) (hq : q ∈ P)
    (hp0 : 0 < p) (hq0 : 0 < q) (hpq : p.Coprime q) (hne : p ≠ q) :
    m < p * q := by
  by_contra hbad
  let b := Nat.chineseRemainder hpq (r p) (r q)
  have hb : b.val < p * q := Nat.chineseRemainder_lt_mul hpq (r p) (r q) hp0.ne' hq0.ne'
  exact hne (h.2 b.val (by omega) p hp q hq b.property.1 b.property.2)

/-- A class disjoint from the p-class has fewer than p hits. -/
lemma other_hits_card_lt {P : Finset ℕ} {r : ℕ → ℕ} {m p q : ℕ}
    (h : ExactCover P r m) (hp : p ∈ P) (hq : q ∈ P)
    (hp0 : 0 < p) (hq0 : 0 < q) (hpq : p.Coprime q) (hne : p ≠ q) :
    (hits m q (r q)).card ≤ p - 1 := by
  classical
  have hm := product_gt_of_exact h hp hq hp0 hq0 hpq hne
  have hmap : ∀ i ∈ hits m q (r q), i % p ∈ (range p).erase (r p % p) := by
    intro i hi
    obtain ⟨him, hiq⟩ := mem_filter.mp hi
    have hne' : i % p ≠ r p % p := by
      intro hip
      exact hne (h.2 i (mem_range.mp him) p hp q hq hip hiq)
    exact mem_erase.mpr ⟨hne', mem_range.mpr (Nat.mod_lt i hp0)⟩
  have hinj : Set.InjOn (fun i => i % p) (↑(hits m q (r q)) : Set ℕ) := by
    intro i hi j hj hij
    change i ∈ hits m q (r q) at hi
    change j ∈ hits m q (r q) at hj
    have him : i < m := mem_range.mp (mem_filter.mp hi).1
    have hjm : j < m := mem_range.mp (mem_filter.mp hj).1
    have hiq : i ≡ r q [MOD q] := (mem_filter.mp hi).2
    have hjq : j ≡ r q [MOD q] := (mem_filter.mp hj).2
    have he : i ≡ j [MOD p * q] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hpq).mp ⟨hij, hiq.trans hjq.symm⟩
    exact he.eq_of_lt_of_lt (him.trans hm) (hjm.trans hm)
  have hc := card_le_card_of_injOn (s := hits m q (r q))
    (t := (range p).erase (r p % p)) (fun i => i % p) hmap hinj
  simpa only [card_erase_of_mem (mem_range.mpr (Nat.mod_lt (r p) hp0)), card_range] using hc

/-- Fixing any one modulus p bounds an exact cover by p*(k-1)+1. -/
lemma length_le_of_member {P : Finset ℕ} {r : ℕ → ℕ} {m p : ℕ}
    (h : ExactCover P r m) (hp : p ∈ P)
    (hpos : ∀ q ∈ P, 1 < q)
    (hco : ∀ q ∈ P, p ≠ q → p.Coprime q) :
    m ≤ p * (P.card - 1) + 1 := by
  classical
  by_cases hm0 : m = 0
  · omega
  have hm_pred : m - 1 + 1 = m := by omega
  have hk : 1 ≤ P.card := card_pos.mpr ⟨p, hp⟩
  have hp2 := hpos p hp
  let d := (m - 1) / p
  have hother : (∑ q ∈ P.erase p, (hits m q (r q)).card) ≤
      (P.card - 1) * (p - 1) := by
    calc
      _ ≤ ∑ _q ∈ P.erase p, (p - 1) := by
        apply sum_le_sum
        intro q hq
        obtain ⟨hqp, hqP⟩ := mem_erase.mp hq
        exact other_hits_card_lt h hp hqP (by omega) (by have := hpos q hqP; omega)
          (hco q hqP hqp.symm) hqp.symm
      _ = _ := by simp only [sum_const, nsmul_eq_mul, card_erase_of_mem hp, Nat.cast_id]
  have hsum : m ≤ d + 1 + (P.card - 1) * (p - 1) := by
    have hh := cover_card_le_sum h.1
    rw [← sum_erase_add _ _ hp] at hh
    have hc := hits_card_le m p (r p)
    change _ ≤ d + 1 at hc
    omega
  have hd : p * d ≤ m - 1 := Nat.mul_div_le _ _
  have hpred : p - 1 + 1 = p := by omega
  have hdle : d ≤ P.card - 1 := by nlinarith
  nlinarith

/-- Exact covers by k pairwise-coprime moduli greater than one have length at
most k squared. General prime-class covers need not be exact. -/
theorem exact_cover_quadratic {P : Finset ℕ} {r : ℕ → ℕ} {m : ℕ}
    (h : ExactCover P r m) (hpos : ∀ p ∈ P, 1 < p)
    (hco : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → p.Coprime q) :
    m ≤ P.card ^ 2 := by
  classical
  by_cases hm0 : m = 0
  · omega
  have hm_pred : m - 1 + 1 = m := by omega
  obtain ⟨q, hq, _⟩ := h.1 0 (by omega)
  have hk : 1 ≤ P.card := card_pos.mpr ⟨q, hq⟩
  by_cases hs : ∃ p ∈ P, p ≤ P.card + 1
  · obtain ⟨p, hp, hpk⟩ := hs
    have hh := length_le_of_member h hp hpos (hco p hp)
    have hmul := Nat.mul_le_mul_right (P.card - 1) hpk
    have hpred : P.card - 1 + 1 = P.card := by omega
    nlinarith
  · push_neg at hs
    let d := (m - 1) / (P.card + 1)
    have hc (p : ℕ) (hp : p ∈ P) : (hits m p (r p)).card ≤ d + 1 := by
      apply (hits_card_le m p (r p)).trans
      have hd : (m - 1) / p ≤ (m - 1) / (P.card + 1) := Nat.div_le_div_left (show P.card + 1 ≤ p from (hs p hp).le) (by omega)
      omega
    have hh : m ≤ P.card * (d + 1) := by
      apply (cover_card_le_sum h.1).trans
      calc
        _ ≤ ∑ _p ∈ P, (d + 1) := sum_le_sum hc
        _ = _ := by simp
    have hd : (P.card + 1) * d ≤ m - 1 := Nat.mul_div_le _ _
    have hpred : P.card - 1 + 1 = P.card := by omega
    have hdle : d ≤ P.card - 1 := by nlinarith
    nlinarith

/-- Specialization to the actual prime moduli. -/
theorem prime_exact_cover_quadratic {P : Finset ℕ} {r : ℕ → ℕ} {m : ℕ}
    (h : ExactCover P r m) (hP : ∀ p ∈ P, p.Prime) : m ≤ P.card ^ 2 :=
  exact_cover_quadratic h (fun p hp => (hP p hp).one_lt)
    (fun p hp q hq hpq => (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq)

#print axioms length_le_of_member
#print axioms exact_cover_quadratic
#print axioms prime_exact_cover_quadratic
end Erdos970.DisjointCover
