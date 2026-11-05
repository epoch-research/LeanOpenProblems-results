import FormalConjecturesUtil

/-!
# Finite uniform Ramsey existence and tools for `hypergraphRamsey`

This file proves finite two-colour uniform Ramsey existence independently of any conjecture.
The proof is an off-diagonal induction on uniformity and the two target sizes. In particular,
the witness set defining `Combinatorics.hypergraphRamsey` is nonempty, including when the
uniformity or target size is zero. The subsequent witness and lower-bound lemmas therefore
do not suffer from `Nat.sInf ∅ = 0`.
-/

namespace Combinatorics

namespace RamseyTools

universe u

/-- Every colouring on a finite set of at least `N` vertices has either a `false`-monochromatic
`s`-set or a `true`-monochromatic `t`-set, for edges of cardinality `r`. -/
def HasUniformRamseyProperty (r N s t : ℕ) : Prop :=
  ∀ {α : Type u} (c : Finset α → Bool) (V : Finset α), N ≤ V.card →
    (∃ S ⊆ V, S.card = s ∧ ∀ e ⊆ S, e.card = r → c e = false) ∨
    (∃ S ⊆ V, S.card = t ∧ ∀ e ⊆ S, e.card = r → c e = true)

/-- Increasing the required number of vertices preserves the Ramsey property. -/
theorem HasUniformRamseyProperty.mono {r N N' s t : ℕ}
    (h : HasUniformRamseyProperty.{u} r N s t) (hNN' : N ≤ N') :
    HasUniformRamseyProperty.{u} r N' s t := by
  intro α c V hV
  exact h c V (hNN'.trans hV)

private theorem monochromatic_insert {α : Type u} [DecidableEq α] {c : Finset α → Bool}
    {r : ℕ} {color : Bool} {S : Finset α} {v : α}
    (hS : ∀ e ⊆ S, e.card = r + 1 → c e = color)
    (hlink : ∀ e ⊆ S, e.card = r → c (insert v e) = color) :
    ∀ e ⊆ insert v S, e.card = r + 1 → c e = color := by
  classical
  intro e he hcard
  by_cases hv : v ∈ e
  · have hsub : e.erase v ⊆ S := by
      intro x hx
      obtain ⟨hxv, hxe⟩ := Finset.mem_erase.mp hx
      exact (Finset.mem_insert.mp (he hxe)).resolve_left hxv
    have hcard' : (e.erase v).card = r := by
      rw [Finset.card_erase_of_mem hv, hcard]
      simp
    simpa only [Finset.insert_erase hv] using hlink (e.erase v) hsub hcard'
  · apply hS e ?_ hcard
    intro x hx
    exact (Finset.mem_insert.mp (he hx)).resolve_left (by
      rintro rfl
      exact hv hx)

/-- The zero-uniform case: only the empty edge is coloured. -/
theorem hasUniformRamseyProperty_zero (s t : ℕ) :
    HasUniformRamseyProperty.{u} 0 (max s t) s t := by
  intro α c V hV
  cases hcolor : c ∅ with
  | false =>
    obtain ⟨S, hSV, hScard⟩ :=
      Finset.exists_subset_card_eq ((le_max_left s t).trans hV)
    refine Or.inl ⟨S, hSV, hScard, ?_⟩
    intro e _ he
    simpa only [Finset.card_eq_zero.mp he] using hcolor
  | true =>
    obtain ⟨S, hSV, hScard⟩ :=
      Finset.exists_subset_card_eq ((le_max_right s t).trans hV)
    refine Or.inr ⟨S, hSV, hScard, ?_⟩
    intro e _ he
    simpa only [Finset.card_eq_zero.mp he] using hcolor

/-- For positive uniformity the empty set is monochromatic in either colour. -/
theorem hasUniformRamseyProperty_zero_left (r t : ℕ) :
    HasUniformRamseyProperty.{u} (r + 1) 0 0 t := by
  intro α c V _
  refine Or.inl ⟨∅, Finset.empty_subset V, by simp, ?_⟩
  intro e he hcard
  have : e = ∅ := Finset.subset_empty.mp he
  simp [this] at hcard

/-- For positive uniformity the empty set is monochromatic in either colour. -/
theorem hasUniformRamseyProperty_zero_right (r s : ℕ) :
    HasUniformRamseyProperty.{u} (r + 1) 0 s 0 := by
  intro α c V _
  refine Or.inr ⟨∅, Finset.empty_subset V, by simp, ?_⟩
  intro e he hcard
  have : e = ∅ := Finset.subset_empty.mp he
  simp [this] at hcard

/-- The off-diagonal recurrence. First find a monochromatic link at one vertex using
uniformity `r`, then use one of the two smaller target-size properties at uniformity `r + 1`.
No positivity assumption on any of the three input bounds is needed. -/
theorem HasUniformRamseyProperty.step {r Ns Nt N s t : ℕ}
    (hlink : HasUniformRamseyProperty.{u} r N Ns Nt)
    (hs : HasUniformRamseyProperty.{u} (r + 1) Ns s (t + 1))
    (ht : HasUniformRamseyProperty.{u} (r + 1) Nt (s + 1) t) :
    HasUniformRamseyProperty.{u} (r + 1) (N + 1) (s + 1) (t + 1) := by
  classical
  intro α c V hV
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < V.card by omega)
  have hV' : N ≤ (V.erase v).card := by
    rw [Finset.card_erase_of_mem hv]
    omega
  rcases hlink (fun e => c (insert v e)) (V.erase v) hV' with
    ⟨B, hBV, hBcard, hBmono⟩ | ⟨B, hBV, hBcard, hBmono⟩
  · have hvB : v ∉ B := fun h => (Finset.notMem_erase v V) (hBV h)
    have hBV' : B ⊆ V := hBV.trans (Finset.erase_subset v V)
    rcases hs c B hBcard.ge with
      ⟨S, hSB, hScard, hSmono⟩ | ⟨S, hSB, hScard, hSmono⟩
    · refine Or.inl ⟨insert v S, ?_, ?_, ?_⟩
      · exact Finset.insert_subset hv (hSB.trans hBV')
      · rw [Finset.card_insert_of_notMem (fun h => hvB (hSB h)), hScard]
      · exact monochromatic_insert hSmono (fun e he => hBmono e (he.trans hSB))
    · exact Or.inr ⟨S, hSB.trans hBV', hScard, hSmono⟩
  · have hvB : v ∉ B := fun h => (Finset.notMem_erase v V) (hBV h)
    have hBV' : B ⊆ V := hBV.trans (Finset.erase_subset v V)
    rcases ht c B hBcard.ge with
      ⟨S, hSB, hScard, hSmono⟩ | ⟨S, hSB, hScard, hSmono⟩
    · exact Or.inl ⟨S, hSB.trans hBV', hScard, hSmono⟩
    · refine Or.inr ⟨insert v S, ?_, ?_, ?_⟩
      · exact Finset.insert_subset hv (hSB.trans hBV')
      · rw [Finset.card_insert_of_notMem (fun h => hvB (hSB h)), hScard]
      · exact monochromatic_insert hSmono (fun e he => hBmono e (he.trans hSB))

/-- Finite off-diagonal uniform Ramsey existence, for all uniformities and target sizes. -/
theorem exists_uniformRamsey (r s t : ℕ) :
    ∃ N, HasUniformRamseyProperty.{u} r N s t := by
  induction r generalizing s t with
  | zero => exact ⟨max s t, hasUniformRamseyProperty_zero s t⟩
  | succ r ihr =>
    induction s generalizing t with
    | zero => exact ⟨0, hasUniformRamseyProperty_zero_left r t⟩
    | succ s ihs =>
      induction t with
      | zero => exact ⟨0, hasUniformRamseyProperty_zero_right r (s + 1)⟩
      | succ t iht =>
        obtain ⟨Ns, hs⟩ := ihs (t + 1)
        obtain ⟨Nt, ht⟩ := iht
        obtain ⟨N, hN⟩ := ihr Ns Nt
        exact ⟨N + 1, hN.step hs ht⟩

end RamseyTools

/-- Membership in the witness set used to define `hypergraphRamsey r n`. -/
def HypergraphRamseyWitness (r n M : ℕ) : Prop :=
  ∀ c : Finset (Fin M) → Bool,
    ∃ S : Finset (Fin M), S.card = n ∧
      ∃ color : Bool, ∀ e : Finset (Fin M), e ⊆ S → e.card = r → c e = color

/-- A Ramsey witness on `Fin M` remains a witness after adding vertices. The colouring is
pulled back along `Fin.castLEEmb`, and the monochromatic set is mapped forward. -/
theorem HypergraphRamseyWitness.mono {r n M N : ℕ}
    (hM : HypergraphRamseyWitness r n M) (hMN : M ≤ N) :
    HypergraphRamseyWitness r n N := by
  intro c
  let f : Fin M ↪ Fin N := Fin.castLEEmb hMN
  obtain ⟨S, hScard, color, hSmono⟩ := hM (fun e => c (e.map f))
  refine ⟨S.map f, by simpa only [Finset.card_map] using hScard, color, ?_⟩
  intro e he hcard
  obtain ⟨e', he'S, rfl⟩ := Finset.subset_map_iff.mp he
  exact hSmono e' he'S (by simpa only [Finset.card_map] using hcard)

/-- Shrinking the desired monochromatic set preserves the witness property. -/
theorem HypergraphRamseyWitness.mono_target {r n n' M : ℕ}
    (hM : HypergraphRamseyWitness r n M) (hn : n' ≤ n) :
    HypergraphRamseyWitness r n' M := by
  intro c
  obtain ⟨S, hScard, color, hSmono⟩ := hM c
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (hn.trans_eq hScard.symm)
  exact ⟨T, hTcard, color, fun e he => hSmono e (he.trans hTS)⟩

/-- Finite two-colour uniform Ramsey existence in the exact format of `hypergraphRamsey`. -/
theorem exists_hypergraphRamseyWitness (r n : ℕ) : ∃ M, HypergraphRamseyWitness r n M := by
  obtain ⟨M, hM⟩ := RamseyTools.exists_uniformRamsey.{0} r n n
  refine ⟨M, ?_⟩
  intro c
  have hcard : M ≤ (Finset.univ : Finset (Fin M)).card := by simp
  rcases hM c Finset.univ hcard with
    ⟨S, _, hScard, hSmono⟩ | ⟨S, _, hScard, hSmono⟩
  · exact ⟨S, hScard, false, hSmono⟩
  · exact ⟨S, hScard, true, hSmono⟩

/-- The literal set in the definition of `hypergraphRamsey` is always nonempty. -/
theorem hypergraphRamsey_witness_set_nonempty (r n : ℕ) :
    {M | ∀ c : Finset (Fin M) → Bool,
      ∃ S : Finset (Fin M), S.card = n ∧
        ∃ color : Bool, ∀ e : Finset (Fin M), e ⊆ S → e.card = r → c e = color}.Nonempty :=
  exists_hypergraphRamseyWitness r n

/-- The minimum defining `hypergraphRamsey` is itself a Ramsey witness. -/
theorem hypergraphRamsey_isWitness (r n : ℕ) :
    HypergraphRamseyWitness r n (hypergraphRamsey r n) :=
  Nat.sInf_mem (hypergraphRamsey_witness_set_nonempty r n)

/-- The elementary lower bound no longer requires a nonemptiness hypothesis. -/
theorem n_le_hypergraphRamsey (r n : ℕ) : n ≤ hypergraphRamsey r n :=
  le_hypergraphRamsey r n (hypergraphRamsey_witness_set_nonempty r n)

/-- Upper bounds are exactly the Ramsey witnesses. The forward implication uses both
nonemptiness (so the minimum is a witness) and upward closure. -/
theorem hypergraphRamsey_le_iff (r n M : ℕ) :
    hypergraphRamsey r n ≤ M ↔ HypergraphRamseyWitness r n M :=
  ⟨fun h => (hypergraphRamsey_isWitness r n).mono h, fun h => Nat.sInf_le h⟩

/-- The defining witness set is the upper interval starting at the Ramsey number. -/
theorem hypergraphRamsey_witness_set_eq_Ici (r n : ℕ) :
    {M | HypergraphRamseyWitness r n M} = Set.Ici (hypergraphRamsey r n) := by
  ext M
  exact (hypergraphRamsey_le_iff r n M).symm

/-- A number lies strictly below the Ramsey number iff it is not a Ramsey witness. -/
theorem lt_hypergraphRamsey_iff_not_witness (r n M : ℕ) :
    M < hypergraphRamsey r n ↔ ¬ HypergraphRamseyWitness r n M := by
  rw [← not_le, hypergraphRamsey_le_iff]

/-- Exact lower-bound/witness equivalence, retaining the usual negated monochromatic-set
statement for a colouring on `Fin M`. -/
theorem lt_hypergraphRamsey_iff_exists_coloring (r n M : ℕ) :
    M < hypergraphRamsey r n ↔
      ∃ c : Finset (Fin M) → Bool,
        ¬ ∃ S : Finset (Fin M), S.card = n ∧
          ∃ color : Bool, ∀ e : Finset (Fin M), e ⊆ S → e.card = r → c e = color := by
  classical
  rw [lt_hypergraphRamsey_iff_not_witness, HypergraphRamseyWitness, not_forall]

/-- A single colouring with no monochromatic `n`-set gives the strict lower bound `M < R`.
There is no separate nonemptiness or positivity hypothesis. -/
theorem lt_hypergraphRamsey_of_no_monochromatic {r n M : ℕ}
    (c : Finset (Fin M) → Bool)
    (hc : ¬ ∃ S : Finset (Fin M), S.card = n ∧
      ∃ color : Bool, ∀ e : Finset (Fin M), e ⊆ S → e.card = r → c e = color) :
    M < hypergraphRamsey r n :=
  (lt_hypergraphRamsey_iff_exists_coloring r n M).2 ⟨c, hc⟩

/-- A convenient pointwise version: for every `n`-set and proposed colour, exhibit an
`r`-edge of a different colour. -/
theorem lt_hypergraphRamsey_of_coloring {r n M : ℕ}
    (c : Finset (Fin M) → Bool)
    (hc : ∀ S : Finset (Fin M), S.card = n → ∀ color : Bool,
      ∃ e : Finset (Fin M), e ⊆ S ∧ e.card = r ∧ c e ≠ color) :
    M < hypergraphRamsey r n := by
  apply lt_hypergraphRamsey_of_no_monochromatic c
  rintro ⟨S, hScard, color, hmono⟩
  obtain ⟨e, heS, hecard, hne⟩ := hc S hScard color
  exact hne (hmono e heS hecard)

/-- The corresponding non-strict lower bound on the Ramsey number. -/
theorem succ_le_hypergraphRamsey_of_no_monochromatic {r n M : ℕ}
    (c : Finset (Fin M) → Bool)
    (hc : ¬ ∃ S : Finset (Fin M), S.card = n ∧
      ∃ color : Bool, ∀ e : Finset (Fin M), e ⊆ S → e.card = r → c e = color) :
    M + 1 ≤ hypergraphRamsey r n :=
  lt_hypergraphRamsey_of_no_monochromatic c hc

/-- Ramsey numbers are monotone in the requested monochromatic-set size. -/
theorem hypergraphRamsey_mono_target (r : ℕ) : Monotone (hypergraphRamsey r) := by
  intro n n' hnn'
  exact (hypergraphRamsey_le_iff r n (hypergraphRamsey r n')).2
    ((hypergraphRamsey_isWitness r n').mono_target hnn')

end Combinatorics
