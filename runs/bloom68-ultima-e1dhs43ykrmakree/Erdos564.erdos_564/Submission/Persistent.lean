import Submission.Critical

/-!
# Persistent near-cores of a robust partial triple coloring

A partial coloring fixes some triples and leaves the others independently free. Robustness
means that every completion avoids monochromatic `n`-sets. The full persistent near-core
formula has exactly the links that legally extend at least one completion as its models.
The completion is explicit: a free triple with a monochromatic pair-link receives the
opposite color; mixed pair-links receive `false`.

No finiteness of the vertex type is needed for this projection. At maximum finite order
`R₃(n) - 1`, positivity of `R₃(n)` makes the persistent formula UNSAT. These are qualitative
statements, not a quantitative Ramsey bound.
-/

set_option autoImplicit false

namespace PersistentColoring

open CriticalColoring

variable {α : Type*}

/-- Respect the partial coloring on fixed triples. Other finset sizes are immaterial. -/
def Completes (P : Finset α → Option Bool) (c : Finset α → Bool) : Prop :=
  ∀ T : Finset α, T.card = 3 → ∀ b : Bool, P T = some b → c T = b

/-- Every independent assignment to the free triples avoids monochromatic `n`-sets. -/
def Robust (P : Finset α → Option Bool) (n : ℕ) : Prop :=
  ∀ c : Finset α → Bool, Completes P c → ¬ HasMonoTripleSet c n

/-- A near-core all of whose triples are already fixed in color `b`. -/
def PersistentNearCore (P : Finset α → Option Bool) (n : ℕ)
    (S : Finset α) (b : Bool) : Prop :=
  S.card = n - 1 ∧ ∀ T : Finset α, T ⊆ S → T.card = 3 → P T = some b

/-- A violated persistent near-core clause: its link pairs all match its fixed color. -/
def PersistentWitness (P : Finset α → Option Bool) (ℓ : Finset α → Bool) (n : ℕ) : Prop :=
  ∃ S : Finset α, ∃ b : Bool, PersistentNearCore P n S b ∧
    ∀ e : Finset α, e ⊆ S → e.card = 2 → ℓ e = b

/-- Satisfaction of every clause of the full persistent near-core formula. -/
def Satisfies (P : Finset α → Option Bool) (ℓ : Finset α → Bool) (n : ℕ) : Prop :=
  ¬ PersistentWitness P ℓ n

/-- A polar completion, assigning one default color to all free triples. -/
def defaultCompletion (P : Finset α → Option Bool) (b : Bool) (T : Finset α) : Bool :=
  (P T).getD b

theorem completes_defaultCompletion (P : Finset α → Option Bool) (b : Bool) :
    Completes P (defaultCompletion P b) := by
  intro T _ d hT
  simp [defaultCompletion, hT]

/-- Robustness is exactly the presence of a fixed triple of each color in every `n`-set.
This includes the vacuous case when there are no `n`-sets. -/
theorem robust_iff_fixed_colors (P : Finset α → Option Bool) (n : ℕ) :
    Robust P n ↔ ∀ S : Finset α, S.card = n → ∀ b : Bool,
      ∃ T : Finset α, T ⊆ S ∧ T.card = 3 ∧ P T = some b := by
  classical
  constructor
  · intro hP S hS b
    by_contra h
    apply hP (defaultCompletion P (!b)) (completes_defaultCompletion P (!b))
    refine ⟨S, hS, !b, ?_⟩
    intro T hTS hT
    have hnot : P T ≠ some b := fun hfixed => h ⟨T, hTS, hT, hfixed⟩
    cases hPT : P T with
    | none => simp [defaultCompletion, hPT]
    | some d =>
      have hd : d ≠ b := by
        intro hdb
        exact hnot (hPT.trans (congrArg some hdb))
      simpa [defaultCompletion, hPT] using (Bool.eq_not_iff.mpr hd)
  · intro h c hc hmono
    obtain ⟨S, hS, b, hm⟩ := hmono
    obtain ⟨T, hTS, hT, hfixed⟩ := h S hS (!b)
    have hcontra : b = !b := (hm T hTS hT).symm.trans (hc T hT (!b) hfixed)
    cases b <;> cases hcontra

/-- Robustness already rules out target size zero, so the projection needs no extra
positivity assumption on `n`. -/
theorem Robust.pos {P : Finset α → Option Bool} {n : ℕ} (hP : Robust P n) : 0 < n := by
  apply Nat.pos_of_ne_zero
  intro hn
  subst n
  apply hP (defaultCompletion P false) (completes_defaultCompletion P false)
  refine ⟨∅, rfl, false, ?_⟩
  intro T hT hcard
  have hle := Finset.card_le_card hT
  simp only [Finset.card_empty] at hle
  omega

/-- Every persistent witness is an actual link witness in every completion. -/
theorem linkWitness_of_persistentWitness {P : Finset α → Option Bool}
    {c ℓ : Finset α → Bool} {n : ℕ} (hc : Completes P c)
    (h : PersistentWitness P ℓ n) : LinkWitness c ℓ n := by
  obtain ⟨S, b, ⟨hS, hfixed⟩, hℓ⟩ := h
  exact ⟨S, hS, b, fun T hTS hT => hc T hT b (hfixed T hTS hT), hℓ⟩

/-- The explicit completion against a proposed link. Free triples with all-false pairs
receive `true`; all-true and mixed pairs receive `false`. Testing the finitely many pairs
makes this a computable definition even when the ambient vertex type is infinite. -/
def completeAgainst (P : Finset α → Option Bool) (ℓ : Finset α → Bool)
    (T : Finset α) : Bool :=
  (P T).getD (if ∀ e ∈ T.powersetCard 2, ℓ e = false then true else false)

theorem completes_completeAgainst (P : Finset α → Option Bool) (ℓ : Finset α → Bool) :
    Completes P (completeAgainst P ℓ) := by
  intro T _ b hT
  simp [completeAgainst, hT]

/-- The combinatorial completion rule: a free triple whose three pairs have color `b`
is filled with `!b`. The existence of a pair inside a triple is essential in the true case. -/
theorem completeAgainst_free_of_monoPairs {P : Finset α → Option Bool}
    {ℓ : Finset α → Bool} {T : Finset α} {b : Bool}
    (hfree : P T = none) (hT : T.card = 3)
    (hℓ : ∀ e : Finset α, e ⊆ T → e.card = 2 → ℓ e = b) :
    completeAgainst P ℓ T = !b := by
  cases b with
  | false =>
    have hall : ∀ e ∈ T.powersetCard 2, ℓ e = false := by
      intro e he
      obtain ⟨heT, hecard⟩ := Finset.mem_powersetCard.mp he
      exact hℓ e heT hecard
    rw [completeAgainst, hfree, if_pos hall]
    rfl
  | true =>
    have hnot : ¬ (∀ e ∈ T.powersetCard 2, ℓ e = false) := by
      intro hall
      obtain ⟨e, heT, hecard⟩ := Finset.exists_subset_card_eq (s := T) (n := 2) (by omega)
      have hf := hall e (Finset.mem_powersetCard.mpr ⟨heT, hecard⟩)
      have ht := hℓ e heT hecard
      simp [ht] at hf
    rw [completeAgainst, hfree, if_neg hnot]
    rfl

/-- A matching monochromatic core in this completion has no free triple: its triples
are precisely fixed triples of the matching color. Restriction of the pair-link to every
internal triple is what makes the completion eliminate all nonpersistent cores at once. -/
theorem monoTripleOn_completeAgainst_iff {P : Finset α → Option Bool}
    {ℓ : Finset α → Bool} {S : Finset α} {b : Bool}
    (hℓ : ∀ e : Finset α, e ⊆ S → e.card = 2 → ℓ e = b) :
    MonoTripleOn (completeAgainst P ℓ) S b ↔
      ∀ T : Finset α, T ⊆ S → T.card = 3 → P T = some b := by
  constructor
  · intro hm T hTS hT
    have hcT := hm T hTS hT
    cases hPT : P T with
    | none =>
      have hf := completeAgainst_free_of_monoPairs hPT hT
        (fun e he hecard => hℓ e (he.trans hTS) hecard)
      have hcontra : b = !b := hcT.symm.trans hf
      cases b <;> cases hcontra
    | some d =>
      have hd := completes_completeAgainst P ℓ T hT d hPT
      have hdb : d = b := hd.symm.trans hcT
      rw [hdb]
  · intro hfixed T hTS hT
    exact completes_completeAgainst P ℓ T hT b (hfixed T hTS hT)

/-- Exact witness elimination; neither robustness nor a lower bound on `n` is needed. -/
theorem linkWitness_completeAgainst_iff (P : Finset α → Option Bool)
    (ℓ : Finset α → Bool) (n : ℕ) :
    LinkWitness (completeAgainst P ℓ) ℓ n ↔ PersistentWitness P ℓ n := by
  constructor
  · rintro ⟨S, hS, b, hm, hℓ⟩
    exact ⟨S, b, ⟨hS, (monoTripleOn_completeAgainst_iff hℓ).mp hm⟩, hℓ⟩
  · rintro ⟨S, b, ⟨hS, hfixed⟩, hℓ⟩
    exact ⟨S, hS, b, (monoTripleOn_completeAgainst_iff hℓ).mpr hfixed, hℓ⟩

section OneVertex

variable [DecidableEq α]

/-- For a robust partial coloring the explicit completion has a legal one-vertex
extension exactly when the proposed link satisfies the persistent formula. -/
theorem satisfies_iff_completeAgainst_legal {P : Finset α → Option Bool} {n : ℕ}
    (hP : Robust P n) (ℓ : Finset α → Bool) :
    Satisfies P ℓ n ↔
      ¬ HasMonoTripleSet (oneVertexExtension (completeAgainst P ℓ) ℓ) n := by
  rw [extension_iff_linkWitness hP.pos (hP _ (completes_completeAgainst P ℓ)),
    linkWitness_completeAgainst_iff]
  rfl

/-- **Exact persistent-core projection**, pointwise in the link:
`Sat(F_P) = ⋃ (c completing P), Ext(c)`. In the forward direction the witness is the
explicit `completeAgainst P ℓ`, not an assumed extension or a choice of completions. -/
theorem satisfies_iff_exists_legal_completion {P : Finset α → Option Bool} {n : ℕ}
    (hP : Robust P n) (ℓ : Finset α → Bool) :
    Satisfies P ℓ n ↔ ∃ c : Finset α → Bool,
      Completes P c ∧ ¬ HasMonoTripleSet (oneVertexExtension c ℓ) n := by
  constructor
  · intro hsat
    exact ⟨completeAgainst P ℓ, completes_completeAgainst P ℓ,
      (satisfies_iff_completeAgainst_legal hP ℓ).mp hsat⟩
  · rintro ⟨c, hc, hlegal⟩ hpersistent
    exact hlegal (extension_of_linkWitness hP.pos
      (linkWitness_of_persistentWitness hc hpersistent))

/-- If every completion is one-vertex nonextendable, the full persistent near-core
formula is UNSAT. Robustness is what makes the old constraints automatic in the projection. -/
theorem unsat_of_all_completions_nonextendable {P : Finset α → Option Bool} {n : ℕ}
    (hP : Robust P n)
    (hmax : ∀ c : Finset α → Bool, Completes P c → ∀ ℓ : Finset α → Bool,
      HasMonoTripleSet (oneVertexExtension c ℓ) n) :
    ¬ ∃ ℓ : Finset α → Bool, Satisfies P ℓ n := by
  rintro ⟨ℓ, hsat⟩
  obtain ⟨c, hc, hlegal⟩ := (satisfies_iff_exists_legal_completion hP ℓ).mp hsat
  exact hlegal (hmax c hc ℓ)

/-- **Maximum-order persistent UNSAT.** On any finite vertex type of cardinality
`R₃(n) - 1`, a robust partial coloring has an UNSAT persistent formula when `R₃(n) > 0`.
No quantitative estimate for the Ramsey number is assumed or concluded. -/
theorem unsat_of_maximum_order [Fintype α] {P : Finset α → Option Bool} {n : ℕ}
    (hR : 0 < Combinatorics.hypergraphRamsey 3 n)
    (hcard : Fintype.card α = Combinatorics.hypergraphRamsey 3 n - 1)
    (hP : Robust P n) :
    ¬ ∃ ℓ : Finset α → Bool, Satisfies P ℓ n := by
  apply unsat_of_all_completions_nonextendable hP
  intro c _ ℓ
  apply ramsey_on_type hR
  simp only [Fintype.card_option]
  omega

end OneVertex

end PersistentColoring

#print axioms PersistentColoring.robust_iff_fixed_colors
#print axioms PersistentColoring.completeAgainst_free_of_monoPairs
#print axioms PersistentColoring.monoTripleOn_completeAgainst_iff
#print axioms PersistentColoring.linkWitness_completeAgainst_iff
#print axioms PersistentColoring.satisfies_iff_completeAgainst_legal
#print axioms PersistentColoring.satisfies_iff_exists_legal_completion
#print axioms PersistentColoring.unsat_of_all_completions_nonextendable
#print axioms PersistentColoring.unsat_of_maximum_order
