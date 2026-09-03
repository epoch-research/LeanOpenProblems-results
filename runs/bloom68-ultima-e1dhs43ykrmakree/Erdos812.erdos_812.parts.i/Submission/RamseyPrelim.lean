import FormalConjecturesUtil

/-!
# Preliminary facts about the diagonal two-colour graph Ramsey numbers

These lemmas concern `Combinatorics.hypergraphRamsey 2 n`. In particular, a
one-step lower bound for the ratio is not a lower bound by a fixed constant
strictly greater than one, and does not settle that stronger question.
-/

namespace Combinatorics.RamseyPrelim

/-- The exact predicate in the defining set of `hypergraphRamsey 2 n`. -/
def HasRamseyProperty (m n : ℕ) : Prop :=
  ∀ (c : Finset (Fin m) → Bool),
    ∃ (S : Finset (Fin m)), S.card = n ∧
      ∃ (color : Bool), ∀ (e : Finset (Fin m)),
        e ⊆ S → e.card = 2 → c e = color

lemma ramsey_eq_sInf (n : ℕ) :
    hypergraphRamsey 2 n = sInf {m | HasRamseyProperty m n} := rfl

/-- The binomial bound is a member of the exact defining set. -/
lemma choose_hasRamseyProperty (n : ℕ) :
    HasRamseyProperty (Nat.choose (n + n) n) n := by
  intro c
  have hV : Nat.choose (n + n) n ≤
      (Finset.univ : Finset (Fin (Nat.choose (n + n) n))).card := by simp
  rcases Diagonal.hasRamseyProperty_choose n n c Finset.univ hV with
    ⟨S, _, hScard, hSmono⟩ | ⟨S, _, hScard, hSmono⟩
  · exact ⟨S, hScard, false, hSmono⟩
  · exact ⟨S, hScard, true, hSmono⟩

/-- Nonemptiness, stated literally for the set used to define the Ramsey number. -/
lemma definingSet_nonempty (n : ℕ) :
    {m | ∀ (c : Finset (Fin m) → Bool),
      ∃ (S : Finset (Fin m)), S.card = n ∧
        ∃ (color : Bool), ∀ (e : Finset (Fin m)),
          e ⊆ S → e.card = 2 → c e = color}.Nonempty :=
  ⟨Nat.choose (n + n) n, choose_hasRamseyProperty n⟩

lemma le_ramsey (n : ℕ) : n ≤ hypergraphRamsey 2 n :=
  le_hypergraphRamsey 2 n (definingSet_nonempty n)

lemma ramsey_pos {n : ℕ} (hn : 0 < n) : 0 < hypergraphRamsey 2 n :=
  hn.trans_le (le_ramsey n)

/-- The infimum really satisfies the defining Ramsey property. -/
lemma ramsey_property (n : ℕ) :
    ∀ (c : Finset (Fin (hypergraphRamsey 2 n)) → Bool),
      ∃ (S : Finset (Fin (hypergraphRamsey 2 n))), S.card = n ∧
        ∃ (color : Bool), ∀ (e : Finset (Fin (hypergraphRamsey 2 n))),
          e ⊆ S → e.card = 2 → c e = color :=
  Nat.sInf_mem (definingSet_nonempty n)

lemma ramsey_le_of_property {m n : ℕ} (h : HasRamseyProperty m n) :
    hypergraphRamsey 2 n ≤ m :=
  Nat.sInf_le h

/-- Pulling back along `Fin.castSucc` removes at most the last vertex. -/
lemma card_preimage_castSucc {m : ℕ} (S : Finset (Fin (m + 1))) :
    (S.preimage Fin.castSuccEmb Fin.castSuccEmb.injective.injOn).card =
      (S.erase (Fin.last m)).card := by
  classical
  rw [Finset.card_preimage]
  apply congrArg Finset.card
  ext x
  have hx : (x : ℕ) < m ↔ x ≠ Fin.last m := Fin.lt_last_iff_ne_last
  simp only [Finset.mem_filter, Fin.coe_castSuccEmb, Fin.range_castSucc,
    Set.mem_setOf_eq, Finset.mem_erase, hx, and_comm]

/-- Extend a coloring by one vertex and then discard that vertex from a
monochromatic set. At least `n` of its `n + 1` vertices remain. -/
lemma HasRamseyProperty.of_succ {m n : ℕ}
    (h : HasRamseyProperty (m + 1) (n + 1)) : HasRamseyProperty m n := by
  classical
  intro c
  let f : Fin m ↪ Fin (m + 1) := Fin.castSuccEmb
  obtain ⟨S, hScard, color, hSmono⟩ :=
    h (fun e => c (e.preimage f f.injective.injOn))
  have hcard : n ≤ (S.preimage f f.injective.injOn).card := by
    change n ≤ (S.preimage Fin.castSuccEmb Fin.castSuccEmb.injective.injOn).card
    rw [card_preimage_castSucc]
    have hbound := Finset.pred_card_le_card_erase (s := S) (a := Fin.last m)
    simpa only [hScard, Nat.add_sub_cancel] using hbound
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨T, hTcard, color, ?_⟩
  intro e hesub hecard
  have hmap : e.map f ⊆ S :=
    Finset.map_subset_iff_subset_preimage.mpr (hesub.trans hTsub)
  have hcolor := hSmono (e.map f) hmap (by simpa only [Finset.card_map] using hecard)
  simpa only [Finset.preimage_map] using hcolor

/-- Strict increase holds even at `n = 0`. -/
lemma ramsey_lt_succ (n : ℕ) :
    hypergraphRamsey 2 n < hypergraphRamsey 2 (n + 1) := by
  have hpos := ramsey_pos (Nat.succ_pos n)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hpos)
  simp only [Nat.succ_eq_add_one] at hm
  have hprop : HasRamseyProperty (m + 1) (n + 1) := by
    rw [← hm]
    exact ramsey_property (n + 1)
  have hle := ramsey_le_of_property hprop.of_succ
  omega

lemma ramsey_strictMono : StrictMono (hypergraphRamsey 2) :=
  strictMono_nat_of_lt_succ ramsey_lt_succ

/-- This bound depends on `n` through the denominator; it does not provide a
uniform multiplicative gap above one. -/
lemma ramsey_ratio_lower_bound {n : ℕ} (hn : 0 < n) :
    1 + 1 / (hypergraphRamsey 2 n : ℝ) ≤
      (hypergraphRamsey 2 (n + 1) : ℝ) / (hypergraphRamsey 2 n : ℝ) := by
  have hpos : (0 : ℝ) < (hypergraphRamsey 2 n : ℝ) := by
    exact_mod_cast ramsey_pos hn
  have hstep : (hypergraphRamsey 2 n : ℝ) + 1 ≤
      (hypergraphRamsey 2 (n + 1) : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (ramsey_lt_succ n)
  calc
    1 + 1 / (hypergraphRamsey 2 n : ℝ) =
        ((hypergraphRamsey 2 n : ℝ) + 1) / (hypergraphRamsey 2 n : ℝ) := by
      rw [add_div, div_self (ne_of_gt hpos)]
    _ ≤ (hypergraphRamsey 2 (n + 1) : ℝ) / (hypergraphRamsey 2 n : ℝ) :=
      div_le_div_of_nonneg_right hstep (le_of_lt hpos)

end Combinatorics.RamseyPrelim

#print axioms Combinatorics.RamseyPrelim.ramsey_eq_sInf
#print axioms Combinatorics.RamseyPrelim.choose_hasRamseyProperty
#print axioms Combinatorics.RamseyPrelim.definingSet_nonempty
#print axioms Combinatorics.RamseyPrelim.le_ramsey
#print axioms Combinatorics.RamseyPrelim.ramsey_pos
#print axioms Combinatorics.RamseyPrelim.ramsey_property
#print axioms Combinatorics.RamseyPrelim.ramsey_le_of_property
#print axioms Combinatorics.RamseyPrelim.card_preimage_castSucc
#print axioms Combinatorics.RamseyPrelim.HasRamseyProperty.of_succ
#print axioms Combinatorics.RamseyPrelim.ramsey_lt_succ
#print axioms Combinatorics.RamseyPrelim.ramsey_strictMono
#print axioms Combinatorics.RamseyPrelim.ramsey_ratio_lower_bound
