import Submission.BlockMomentObstruction
import Submission.ConstructiveCover

/-!
For every fixed degree there are arbitrarily large sets of DISTINCT PRIME
marginals admitting a nonnegative, empty-free synthetic model with exact
moments through that degree. This does not construct a residue-class cover.
-/
namespace Erdos970.PrimeBlockMomentObstruction
open Finset
open Erdos970.BlockMomentObstruction

lemma density_half_of_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hprod : 2 * (∏ p ∈ P, (p - 1)) ≤ ∏ p ∈ P, p) :
    (∏ p ∈ P, (1 - 1 / (p : ℝ))) ≤ 1 / 2 := by
  have hpos : (0 : ℝ) < ∏ p ∈ P, (p : ℝ) :=
    prod_pos (fun p hp => by exact_mod_cast (hP p hp).pos)
  have he : (∏ p ∈ P, (1 - 1 / (p : ℝ))) =
      ((∏ p ∈ P, (p - 1) : ℕ) : ℝ) / (∏ p ∈ P, (p : ℝ)) := by
    rw [Nat.cast_prod, ← prod_div_distrib]
    apply prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (hP p hp).one_le, Nat.cast_one]
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
    field_simp
  rw [he]
  apply (div_le_iff₀ hpos).mpr
  have hh : (2 : ℝ) * ((∏ p ∈ P, (p - 1) : ℕ) : ℝ) ≤ ∏ p ∈ P, (p : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast hprod
  linarith

/-- Disjoint prime blocks of arbitrarily small avoidance probability exist
beyond every fixed threshold. The supply uses Euler's divergent prime series. -/
theorem exists_prime_blocks (b A : ℕ) :
    ∃ P : Fin b → Finset ℕ,
      (∀ j, ∀ p ∈ P j, p.Prime ∧ A < p) ∧
      (Pairwise fun i j => Disjoint (P i) (P j)) ∧
      (∀ j, (∏ p ∈ P j, (1 - 1 / (p : ℝ))) ≤ 1 / 2) := by
  classical
  induction b generalizing A with
  | zero =>
    refine ⟨Fin.elim0, ?_, ?_, ?_⟩
    · intro j; exact Fin.elim0 j
    · intro i; exact Fin.elim0 i
    · intro j; exact Fin.elim0 j
  | succ b ih =>
    obtain ⟨S, hS, hden⟩ := ConstructiveCover.exists_prime_tail_density A 2
    obtain ⟨P, hP, hdis, hhalf⟩ := ih (max A (S.sup id))
    have hSP (j : Fin b) : Disjoint S (P j) := by
      apply disjoint_left.mpr
      intro p hpS hpP
      have hle : p ≤ S.sup id := le_sup (f := id) hpS
      have hgt := (hP j p hpP).2
      have hm := le_max_right A (S.sup id)
      omega
    refine ⟨Fin.cases S P, ?_, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · exact hS
      · intro p hp
        exact ⟨(hP j p hp).1, lt_of_le_of_lt (le_max_left _ _) (hP j p hp).2⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro hij; exact False.elim (hij rfl)
        · intro _; exact hSP j
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro _; exact (hSP i).symm
        · intro hij
          exact hdis (fun he => hij (congrArg Fin.succ he))
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · exact density_half_of_product S (fun p hp => (hS p hp).1) hden
      · exact hhalf j

lemma block_nonempty {b : ℕ} (P : Fin b → Finset ℕ)
    (hhalf : ∀ j, (∏ p ∈ P j, (1 - 1 / (p : ℝ))) ≤ 1 / 2) (j : Fin b) :
    (P j).Nonempty := by
  by_contra hbad
  have he : P j = ∅ := not_nonempty_iff_eq_empty.mp hbad
  have hh := hhalf j
  norm_num [he] at hh

lemma block_union_card {b : ℕ} (P : Fin b → Finset ℕ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (hhalf : ∀ j, (∏ p ∈ P j, (1 - 1 / (p : ℝ))) ≤ 1 / 2) :
    b ≤ (univ.biUnion P).card := by
  rw [card_biUnion (fun i _ j _ hij => hdis hij)]
  have hh := sum_le_sum (s := (univ : Finset (Fin b)))
    (fun j _ => show 1 ≤ (P j).card from card_pos.mpr (block_nonempty P hhalf j))
  simpa using hh

/-- No repeated prime is hidden by the block indexing. -/
lemma primeIndex_injective {b : ℕ} (P : Fin b → Finset ℕ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) :
    Function.Injective (fun t : (j : Fin b) × (P j) => t.2.val) := by
  rintro ⟨i, p⟩ ⟨j, q⟩ he
  change p.val = q.val at he
  have hij : i = j := by
    by_contra hne
    exact (disjoint_left.mp (hdis hne)) p.property (he.symm ▸ q.property)
  subst j
  have hpq : p = q := Subtype.ext he
  subst q
  rfl

/-- An exact empty-free model for any mass, on the specified prime blocks. -/
theorem exact_prime_model {b : ℕ} (hb : 0 < b) (P : Fin b → Finset ℕ)
    (hP : ∀ j, ∀ p ∈ P j, p.Prime)
    (hhalf : ∀ j, (∏ p ∈ P j, (1 - 1 / (p : ℝ))) ≤ 1 / 2)
    (X : ℝ) (hX : 0 ≤ X) :
    ∃ w : ((j : Fin b) → (P j) → Bool) → ℝ,
      (∀ v, 0 ≤ w v) ∧ w (fun _ _ => false) = 0 ∧ (∑ v, w v) = X ∧
      ∀ T : (j : Fin b) → Finset (P j), degree T < b →
        (∑ v, w v * test T v) = X * ∏ j, ∏ p ∈ T j, 1 / (p.val : ℝ) := by
  classical
  letI : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  let q : (j : Fin b) → (P j) → ℝ := fun _ p => 1 / (p.val : ℝ)
  have hq : ∀ j p, 0 ≤ q j p ∧ q j p ≤ 1 := by
    intro j p
    have hp := hP j p.val p.property
    have hpR : (0 : ℝ) < p.val := by exact_mod_cast hp.pos
    refine ⟨by dsimp [q]; positivity, ?_⟩
    exact (div_le_one hpR).mpr (by exact_mod_cast hp.one_le)
  have hh : ∀ j, (∏ p : P j, (1 - q j p)) ≤ 1 / 2 := by
    intro j
    change (∏ p ∈ (P j).attach, (1 - 1 / (p.val : ℝ))) ≤ 1 / 2
    rw [Finset.prod_attach (f := fun p : ℕ => (1 - 1 / (p : ℝ)))]
    exact hhalf j
  simpa only [Fintype.card_fin] using scaled_model q hq hh X hX

/-- Every fixed degree fails as a uniform moment-only method: there are prime
sets beyond any prescribed threshold, with arbitrarily large cardinality,
whose low-degree moments admit an empty-free nonnegative model at EVERY mass.
The constructed model need not be an actual interval population. -/
theorem exists_fixed_degree_obstruction (d K A : ℕ) :
    ∃ P : Fin (d + K + 1) → Finset ℕ,
      (∀ j, ∀ p ∈ P j, p.Prime ∧ A < p) ∧
      (Pairwise fun i j => Disjoint (P i) (P j)) ∧
      K ≤ (univ.biUnion P).card ∧
      ∀ X : ℝ, 0 ≤ X →
        ∃ w : ((j : Fin (d + K + 1)) → (P j) → Bool) → ℝ,
          (∀ v, 0 ≤ w v) ∧ w (fun _ _ => false) = 0 ∧ (∑ v, w v) = X ∧
          ∀ T : (j : Fin (d + K + 1)) → Finset (P j), degree T ≤ d →
            (∑ v, w v * test T v) = X * ∏ j, ∏ p ∈ T j, 1 / (p.val : ℝ) := by
  obtain ⟨P, hP, hdis, hhalf⟩ := exists_prime_blocks (d + K + 1) A
  refine ⟨P, hP, hdis, (show K ≤ d + K + 1 by omega).trans
    (block_union_card P hdis hhalf), ?_⟩
  intro X hX
  obtain ⟨w, hw, he, hsum, hmoment⟩ := exact_prime_model (by omega) P
    (fun j p hp => (hP j p hp).1) hhalf X hX
  exact ⟨w, hw, he, hsum, fun T hT => hmoment T (by omega)⟩

#print axioms exists_prime_blocks
#print axioms primeIndex_injective
#print axioms exact_prime_model
#print axioms exists_fixed_degree_obstruction
end Erdos970.PrimeBlockMomentObstruction
