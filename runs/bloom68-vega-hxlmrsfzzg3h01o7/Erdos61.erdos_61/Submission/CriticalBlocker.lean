import Submission.IntegerReduction

/-!
# Critical product counterexamples and vertex blockers

This standalone file gives the graphical bridge to the numerical blocker in
`IntegerReduction`. It does not import `Submission.Spec` or use a statement of
Erdős–Hajnal as a theorem. In the final reduction, existence of a small blocker
in every forbidden-induced-subgraph-free critical graph remains an explicit
hypothesis, not a conclusion of this file.

The graph-side powers and blocker-size estimates are in `ℕ`. A deletion `D`
leaves `G.induce (↑Dᶜ : Set V)`, where `Dᶜ` is the finset complement of `D`.

The Ramsey section proves `n < choose (A + W) A` and
`n ≤ (A * W) ^ min A W` from the existing Ramsey recurrence. Consequently both
`A` and `W` exceed the exponent in every strict integer-product counterexample.
The conditional conclusion has the exact real EH exponent `1 / (2 * k)`.
-/

open SimpleGraph

namespace Auxiliary.CriticalBlocker

universe u

section GraphParameters

variable {V U : Type*} [Finite V] [Finite U]

/-- An induced graph embedding cannot increase the clique number. -/
theorem cliqueNum_le_of_embedding {G : SimpleGraph V} {F : SimpleGraph U}
    (f : G ↪g F) : G.cliqueNum ≤ F.cliqueNum := by
  classical
  obtain ⟨S, hS⟩ := G.exists_isNClique_cliqueNum
  have hclique : F.IsClique (S.map f.toEmbedding) := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact f.map_adj_iff.mpr (hS.isClique ha hb (ne_of_apply_ne f hxy))
  simpa only [Finset.card_map, hS.card_eq] using hclique.card_le_cliqueNum

/-- An induced graph embedding cannot increase the independence number. -/
theorem indepNum_le_of_embedding {G : SimpleGraph V} {F : SimpleGraph U}
    (f : G ↪g F) : G.indepNum ≤ F.indepNum := by
  simpa only [cliqueNum_compl] using
    cliqueNum_le_of_embedding (SimpleGraph.Embedding.complEquiv f)

/-- Clique number is invariant under graph isomorphism. -/
theorem cliqueNum_eq_of_iso {G : SimpleGraph V} {F : SimpleGraph U}
    (f : G ≃g F) : G.cliqueNum = F.cliqueNum :=
  le_antisymm (cliqueNum_le_of_embedding f.toEmbedding)
    (cliqueNum_le_of_embedding f.symm.toEmbedding)

/-- Independence number is invariant under graph isomorphism. -/
theorem indepNum_eq_of_iso {G : SimpleGraph V} {F : SimpleGraph U}
    (f : G ≃g F) : G.indepNum = F.indepNum :=
  le_antisymm (indepNum_le_of_embedding f.toEmbedding)
    (indepNum_le_of_embedding f.symm.toEmbedding)

/-- Clique-number monotonicity for an induced vertex subset. -/
theorem cliqueNum_induce_le (G : SimpleGraph V) (S : Set V) :
    (G.induce S).cliqueNum ≤ G.cliqueNum :=
  cliqueNum_le_of_embedding (SimpleGraph.Embedding.induce S)

/-- Independence-number monotonicity for an induced vertex subset. -/
theorem indepNum_induce_le (G : SimpleGraph V) (S : Set V) :
    (G.induce S).indepNum ≤ G.indepNum :=
  indepNum_le_of_embedding (SimpleGraph.Embedding.induce S)

end GraphParameters

section DeletionBridge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every proper induced subgraph obeys the natural-power product bound. -/
def ProperInducedBound (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ S : Finset V, S.card < Fintype.card V →
    S.card ≤ ((G.induce (S : Set V)).indepNum *
      (G.induce (S : Set V)).cliqueNum) ^ k

/-- An induced-minimal counterexample to the product bound with exponent `k`.
Minimality is only with respect to proper induced subgraphs of this graph. -/
def IsProductCritical (G : SimpleGraph V) (k : ℕ) : Prop :=
  (G.indepNum * G.cliqueNum) ^ k < Fintype.card V ∧ ProperInducedBound G k

/-- A strict independence-number drop makes the remaining induced graph proper,
so criticality bounds its order by `((A - 1) * W) ^ k`. No exponent restriction
or strict product counterexample is needed for this first bridge. -/
theorem indep_deletion_bound {G : SimpleGraph V} {k : ℕ}
    (hproper : ProperInducedBound G k) (D : Finset V)
    (hdrop : (G.induce (↑Dᶜ : Set V)).indepNum < G.indepNum) :
    Fintype.card V - D.card ≤ ((G.indepNum - 1) * G.cliqueNum) ^ k := by
  have hsub : Dᶜ.card < Fintype.card V := by
    apply (Finset.card_lt_iff_ne_univ _).mpr
    intro hfull
    have heq := indepNum_eq_of_iso G.induceUnivIso
    rw [hfull, Finset.coe_univ, heq] at hdrop
    exact lt_irrefl _ hdrop
  have hA : (G.induce (↑Dᶜ : Set V)).indepNum ≤ G.indepNum - 1 := by omega
  have hW := cliqueNum_induce_le G (↑Dᶜ : Set V)
  calc
    Fintype.card V - D.card = Dᶜ.card := (Finset.card_compl D).symm
    _ ≤ ((G.induce (↑Dᶜ : Set V)).indepNum *
        (G.induce (↑Dᶜ : Set V)).cliqueNum) ^ k := hproper Dᶜ hsub
    _ ≤ ((G.indepNum - 1) * G.cliqueNum) ^ k :=
      Nat.pow_le_pow_left (Nat.mul_le_mul hA hW) k

/-- The complementary bridge: a strict clique-number drop bounds the remaining
order by `(A * (W - 1)) ^ k`, using induced independence-number monotonicity. -/
theorem clique_deletion_bound {G : SimpleGraph V} {k : ℕ}
    (hproper : ProperInducedBound G k) (D : Finset V)
    (hdrop : (G.induce (↑Dᶜ : Set V)).cliqueNum < G.cliqueNum) :
    Fintype.card V - D.card ≤ (G.indepNum * (G.cliqueNum - 1)) ^ k := by
  have hsub : Dᶜ.card < Fintype.card V := by
    apply (Finset.card_lt_iff_ne_univ _).mpr
    intro hfull
    have heq := cliqueNum_eq_of_iso G.induceUnivIso
    rw [hfull, Finset.coe_univ, heq] at hdrop
    exact lt_irrefl _ hdrop
  have hA := indepNum_induce_le G (↑Dᶜ : Set V)
  have hW : (G.induce (↑Dᶜ : Set V)).cliqueNum ≤ G.cliqueNum - 1 := by omega
  calc
    Fintype.card V - D.card = Dᶜ.card := (Finset.card_compl D).symm
    _ ≤ ((G.induce (↑Dᶜ : Set V)).indepNum *
        (G.induce (↑Dᶜ : Set V)).cliqueNum) ^ k := hproper Dᶜ hsub
    _ ≤ (G.indepNum * (G.cliqueNum - 1)) ^ k :=
      Nat.pow_le_pow_left (Nat.mul_le_mul hA hW) k

/-- An independence blocker in a critical graph satisfies `k * n < 2 * A * b`
when `2 ≤ k ≤ A`. The cardinal bound `b ≤ n` is automatic for a deletion finset. -/
theorem indep_blocker_strong {G : SimpleGraph V} {k : ℕ}
    (hk : 2 ≤ k) (hkA : k ≤ G.indepNum) (hcrit : IsProductCritical G k)
    (D : Finset V) (hdrop : (G.induce (↑Dᶜ : Set V)).indepNum < G.indepNum) :
    k * Fintype.card V < 2 * G.indepNum * D.card := by
  exact IntegerReduction.numerical_blocker_strong hk hkA (Finset.card_le_univ D)
    hcrit.1 (indep_deletion_bound hcrit.2 D hdrop)

/-- The corresponding strong inequality for a clique blocker. -/
theorem clique_blocker_strong {G : SimpleGraph V} {k : ℕ}
    (hk : 2 ≤ k) (hkW : k ≤ G.cliqueNum) (hcrit : IsProductCritical G k)
    (D : Finset V) (hdrop : (G.induce (↑Dᶜ : Set V)).cliqueNum < G.cliqueNum) :
    k * Fintype.card V < 2 * G.cliqueNum * D.card := by
  apply IntegerReduction.numerical_blocker_strong (W := G.indepNum) hk hkW
    (Finset.card_le_univ D)
  · simpa only [Nat.mul_comm] using hcrit.1
  · simpa only [Nat.mul_comm] using clique_deletion_bound hcrit.2 D hdrop

/-- For `2 * C < k`, a critical graph has no independence blocker satisfying
`A * b ≤ C * n` (provided `k ≤ A`). -/
theorem indep_blocker_size_lower {G : SimpleGraph V} {k C : ℕ}
    (hk : 2 ≤ k) (hkA : k ≤ G.indepNum) (hcrit : IsProductCritical G k)
    (D : Finset V) (hdrop : (G.induce (↑Dᶜ : Set V)).indepNum < G.indepNum)
    (hC : 2 * C < k) : C * Fintype.card V < G.indepNum * D.card := by
  exact IntegerReduction.numerical_blocker hk hkA (Finset.card_le_univ D)
    hcrit.1 (indep_deletion_bound hcrit.2 D hdrop) hC

/-- The corresponding exclusion of a small clique blocker. -/
theorem clique_blocker_size_lower {G : SimpleGraph V} {k C : ℕ}
    (hk : 2 ≤ k) (hkW : k ≤ G.cliqueNum) (hcrit : IsProductCritical G k)
    (D : Finset V) (hdrop : (G.induce (↑Dᶜ : Set V)).cliqueNum < G.cliqueNum)
    (hC : 2 * C < k) : C * Fintype.card V < G.cliqueNum * D.card := by
  apply IntegerReduction.numerical_blocker (W := G.indepNum) hk hkW (Finset.card_le_univ D)
  · simpa only [Nat.mul_comm] using hcrit.1
  · simpa only [Nat.mul_comm] using clique_deletion_bound hcrit.2 D hdrop
  · exact hC

end DeletionBridge

section RamseyBound

/-- The sharp off-diagonal binomial bound, using the library's proved Ramsey
recurrence and its singleton base cases. The indices here are shifted by one
relative to `Combinatorics.Diagonal.hasRamseyProperty_choose`. -/
theorem hasRamseyProperty_choose_succ (s t : ℕ) :
    Combinatorics.Diagonal.HasRamseyProperty ((s + t).choose s) (s + 1) (t + 1) := by
  induction s generalizing t with
  | zero =>
      simpa only [Nat.zero_add, Nat.choose_zero_right] using
        @Combinatorics.Diagonal.hasRamseyProperty_one_left (t + 1)
  | succ s ih =>
      induction t with
      | zero =>
          simpa only [Nat.add_zero, Nat.choose_self, Nat.zero_add] using
            @Combinatorics.Diagonal.hasRamseyProperty_one_right (s + 1 + 1)
      | succ t iht =>
          rw [show s + 1 + (t + 1) = (s + (t + 1)) + 1 by omega,
            Nat.choose_succ_succ]
          apply Combinatorics.Diagonal.HasRamseyProperty.step
          · exact ih (t + 1)
          · simpa only [Nat.add_assoc, Nat.add_comm 1 t] using @iht
          · exact Nat.choose_pos (Nat.le_add_right _ _)

/-- A graph on `Fin n` has fewer than `choose (A + W) A` vertices. -/
theorem fin_card_lt_choose {n : ℕ} (G : SimpleGraph (Fin n)) :
    n < (G.indepNum + G.cliqueNum).choose G.indepNum := by
  classical
  by_contra! hn
  let c : Finset (Fin n) → Bool := fun e => decide (G.IsClique e)
  rcases hasRamseyProperty_choose_succ G.indepNum G.cliqueNum c Finset.univ
      (by simpa using hn) with
    ⟨S, _, hScard, hmono⟩ | ⟨S, _, hScard, hmono⟩
  · have hindep : G.IsIndepSet S := by
      intro x hx y hy hxy
      have hc := hmono {x, y}
        (by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
          using And.intro hx hy) (by simp [hxy])
      simpa [c, SimpleGraph.isClique_pair, hxy] using hc
    have hle := hindep.card_le_indepNum
    omega
  · have hclique : G.IsClique S := by
      intro x hx y hy hxy
      have hc := hmono {x, y}
        (by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
          using And.intro hx hy) (by simp [hxy])
      simpa [c, SimpleGraph.isClique_pair, hxy] using hc
    have hle := hclique.card_le_cliqueNum
    omega

variable {V : Type*} [Fintype V]

/-- Cardinal Ramsey bound for an arbitrary finite vertex type, including the
empty type. This is obtained by relabeling to `Fin`, not by an axiom. -/
theorem card_lt_choose (G : SimpleGraph V) :
    Fintype.card V < (G.indepNum + G.cliqueNum).choose G.indepNum := by
  classical
  let e := (Fintype.equivFin V).symm
  have hA := indepNum_eq_of_iso (SimpleGraph.Iso.comap e G)
  have hW := cliqueNum_eq_of_iso (SimpleGraph.Iso.comap e G)
  simpa only [hA, hW] using fin_card_lt_choose (G.comap e.toEmbedding)

private theorem le_mul_pow_left_of_lt_choose {n a b : ℕ} (hab : a ≤ b)
    (hn : n < (a + b).choose a) : n ≤ (a * b) ^ a := by
  by_cases ha0 : a = 0
  · subst a
    simp only [Nat.zero_add, Nat.choose_zero_right] at hn
    simp only [Nat.zero_mul, pow_zero]
    omega
  by_cases ha1 : a = 1
  · subst a
    simp only [Nat.choose_one_right] at hn
    simpa only [Nat.one_mul, pow_one] using (show n ≤ b by omega)
  have ha : 2 ≤ a := by omega
  have hb : 2 ≤ b := by omega
  have hbase : a + b ≤ a * b := by
    have hleft := Nat.mul_le_mul_right b ha
    have hright := Nat.mul_le_mul_left a hb
    omega
  exact hn.le.trans ((Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hbase _))

/-- The requested product-form cardinal Ramsey bound:
`n ≤ (A * W) ^ min A W`. The cases `A ≤ 1` or `W ≤ 1` are included. -/
theorem card_le_product_pow_min (G : SimpleGraph V) :
    Fintype.card V ≤ (G.indepNum * G.cliqueNum) ^ min G.indepNum G.cliqueNum := by
  rcases le_total G.indepNum G.cliqueNum with hAW | hWA
  · simpa only [min_eq_left hAW] using
      le_mul_pow_left_of_lt_choose hAW (card_lt_choose G)
  · have hchoose : Fintype.card V <
        (G.cliqueNum + G.indepNum).choose G.cliqueNum := by
      rw [Nat.add_comm G.cliqueNum G.indepNum, ← Nat.choose_symm_add]
      exact card_lt_choose G
    simpa only [min_eq_right hWA, Nat.mul_comm] using
      le_mul_pow_left_of_lt_choose hWA hchoose

/-- Every strict natural-power product counterexample has both graph parameters
strictly greater than the exponent. No minimality or lower bound on `k` is needed. -/
theorem exponent_lt_parameters_of_counterexample (G : SimpleGraph V) {k : ℕ}
    (hlarge : (G.indepNum * G.cliqueNum) ^ k < Fintype.card V) :
    k < G.indepNum ∧ k < G.cliqueNum := by
  have hn : 0 < Fintype.card V := lt_of_le_of_lt (Nat.zero_le _) hlarge
  haveI : Nonempty V := Fintype.card_pos_iff.mp hn
  have hA : 0 < G.indepNum := SimpleGraph.indepNum_pos
  have hW : 0 < G.cliqueNum := by
    simpa only [indepNum_compl] using (SimpleGraph.indepNum_pos (G := Gᶜ))
  have hbase : 1 ≤ G.indepNum * G.cliqueNum := Nat.mul_pos hA hW
  have hmin : k < min G.indepNum G.cliqueNum := by
    by_contra! hle
    have hpow := pow_le_pow_right' hbase hle
    exact (not_lt_of_ge ((card_le_product_pow_min G).trans hpow)) hlarge
  exact lt_min_iff.mp hmin

end RamseyBound

section ConditionalReduction

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A deletion meeting every maximum independent set or every maximum clique,
with the corresponding scaled size at most `C * n`. Its existence is NOT
asserted here. The alternative is allowed to depend on the critical graph. -/
def HasSmallBlocker (G : SimpleGraph V) (C : ℕ) : Prop :=
  ∃ D : Finset V,
    ((G.induce (↑Dᶜ : Set V)).indepNum < G.indepNum ∧
      G.indepNum * D.card ≤ C * Fintype.card V) ∨
    ((G.induce (↑Dᶜ : Set V)).cliqueNum < G.cliqueNum ∧
      G.cliqueNum * D.card ≤ C * Fintype.card V)

/-- Critical graphs cannot have such small blockers when `2 * C < k` and
`2 ≤ k`. The Ramsey bound supplies the parameter-size hypotheses automatically. -/
theorem IsProductCritical.not_hasSmallBlocker {G : SimpleGraph V} {k C : ℕ}
    (hcrit : IsProductCritical G k) (hk : 2 ≤ k) (hC : 2 * C < k) :
    ¬ HasSmallBlocker G C := by
  obtain ⟨hA, hW⟩ := exponent_lt_parameters_of_counterexample G hcrit.1
  rintro ⟨D, hD⟩
  rcases hD with ⟨hdrop, hsize⟩ | ⟨hdrop, hsize⟩
  · exact (not_le_of_gt (indep_blocker_size_lower hk hA.le hcrit D hdrop hC)) hsize
  · exact (not_le_of_gt (clique_blocker_size_lower hk hW.le hcrit D hdrop hC)) hsize

/-- Forbidden-induced-subgraph freeness is inherited by every injective comap.
No finiteness assumption on the forbidden graph is needed for this fact. -/
theorem induced_free_comap {α U V : Type*} {H : SimpleGraph α} {G : SimpleGraph V}
    (hfree : ¬∃ g : α ↪ V, H = G.comap g) (f : U ↪ V) :
    ¬∃ g : α ↪ U, H = (G.comap f).comap g := by
  rintro ⟨g, hg⟩
  exact hfree ⟨g.trans f, hg⟩

/-- **Conditional all-orders product theorem.** If every `H`-free induced-minimal
counterexample at exponent `k` has a small blocker, there are no counterexamples.
The small-blocker assertion is the substantive hypothesis `hblocker`; it is not
proved by this theorem. Strong induction supplies induced minimality, with
freeness and both graph parameters preserved under relabeling to `Fin`. -/
theorem nat_product_bound_of_critical_blockers
    {α : Type*} (H : SimpleGraph α) {k C : ℕ} (hk : 2 ≤ k) (hC : 2 * C < k)
    (hblocker : ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      (¬∃ g : α ↪ Fin n, H = G.comap g) →
        IsProductCritical G k → HasSmallBlocker G C) :
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      (¬∃ g : α ↪ Fin n, H = G.comap g) →
        n ≤ (G.indepNum * G.cliqueNum) ^ k := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro G hfree
      by_contra hbad
      have hcrit : IsProductCritical G k := by
        refine ⟨?_, ?_⟩
        · simpa only [Fintype.card_fin] using Nat.lt_of_not_ge hbad
        · intro S hS
          let e : Fin S.card ≃ (S : Set (Fin n)) := S.equivFin.symm
          let F := (G.induce (S : Set (Fin n))).comap e.toEmbedding
          have hfreeS := induced_free_comap hfree
            (Function.Embedding.subtype (S : Set (Fin n)))
          have hfreeF := induced_free_comap hfreeS e.toEmbedding
          have hbound := ih S.card (by simpa only [Fintype.card_fin] using hS) F hfreeF
          have hA := indepNum_eq_of_iso
            (SimpleGraph.Iso.comap e (G.induce (S : Set (Fin n))))
          have hW := cliqueNum_eq_of_iso
            (SimpleGraph.Iso.comap e (G.induce (S : Set (Fin n))))
          simpa only [F, hA, hW] using hbound
      exact hcrit.not_hasSmallBlocker hk hC (hblocker n G hfree hcrit)

/-- **Conditional exact EH lower bound**, with exponent `1 / (2 * k)`.
The only graph-theoretic input beyond the proved Ramsey/deletion facts is the
explicit small-blocker hypothesis on `H`-free critical graphs. -/
theorem isErdosHajnalLowerBound_of_critical_blockers
    {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α)
    {k C : ℕ} (hk : 2 ≤ k) (hC : 2 * C < k)
    (hblocker : ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      (¬∃ g : α ↪ Fin n, H = G.comap g) →
        IsProductCritical G k → HasSmallBlocker G C) :
    Auxiliary.IsErdosHajnalLowerBound H
      (fun n : ℕ => (n : ℝ) ^ (1 / (2 * (k : ℝ)))) := by
  exact IntegerReduction.isErdosHajnalLowerBound_of_nat_product_bound H (by omega)
    (nat_product_bound_of_critical_blockers H hk hC hblocker)

/-- Fixed-forbidden-graph existential form of the conditional EH theorem. -/
theorem erdosHajnal_of_critical_blockers
    {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α)
    {k C : ℕ} (hk : 2 ≤ k) (hC : 2 * C < k)
    (hblocker : ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      (¬∃ g : α ↪ Fin n, H = G.comap g) →
        IsProductCritical G k → HasSmallBlocker G C) :
    ∃ c > (0 : ℝ), Auxiliary.IsErdosHajnalLowerBound H
      (fun n : ℕ => (n : ℝ) ^ c) := by
  exact IntegerReduction.erdosHajnal_of_exists_all_orders_nat_product_bound H
    ⟨k, by omega, nat_product_bound_of_critical_blockers H hk hC hblocker⟩

/-- **Conditional full Erdős–Hajnal reduction.** The constants and the integral
exponent may depend on the forbidden graph. The displayed small-blocker
hypothesis remains unproved. The conclusion is the original EH formula, using
the standalone exact predicate from `Auxiliary`, not importing `Spec`. -/
theorem erdosHajnal_of_critical_blocker_estimates
    (hblocker : ∀ {α : Type u} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
      ∃ k C : ℕ, 2 ≤ k ∧ 2 * C < k ∧
        ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
          (¬∃ g : α ↪ Fin n, H = G.comap g) →
            IsProductCritical G k → HasSmallBlocker G C) :
    ∀ {α : Type u} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
      ∃ c > (0 : ℝ), Auxiliary.IsErdosHajnalLowerBound H
        (fun n : ℕ => (n : ℝ) ^ c) := by
  intro α _ _ H
  obtain ⟨k, C, hk, hC, h⟩ := hblocker H
  exact erdosHajnal_of_critical_blockers H hk hC h

end ConditionalReduction

end Auxiliary.CriticalBlocker

/- Axiom audit: all public theorems, including the conditional conclusions. -/

#print axioms Auxiliary.CriticalBlocker.cliqueNum_le_of_embedding
#print axioms Auxiliary.CriticalBlocker.indepNum_le_of_embedding
#print axioms Auxiliary.CriticalBlocker.cliqueNum_eq_of_iso
#print axioms Auxiliary.CriticalBlocker.indepNum_eq_of_iso
#print axioms Auxiliary.CriticalBlocker.cliqueNum_induce_le
#print axioms Auxiliary.CriticalBlocker.indepNum_induce_le
#print axioms Auxiliary.CriticalBlocker.indep_deletion_bound
#print axioms Auxiliary.CriticalBlocker.clique_deletion_bound
#print axioms Auxiliary.CriticalBlocker.indep_blocker_strong
#print axioms Auxiliary.CriticalBlocker.clique_blocker_strong
#print axioms Auxiliary.CriticalBlocker.indep_blocker_size_lower
#print axioms Auxiliary.CriticalBlocker.clique_blocker_size_lower
#print axioms Auxiliary.CriticalBlocker.hasRamseyProperty_choose_succ
#print axioms Auxiliary.CriticalBlocker.fin_card_lt_choose
#print axioms Auxiliary.CriticalBlocker.card_lt_choose
#print axioms Auxiliary.CriticalBlocker.card_le_product_pow_min
#print axioms Auxiliary.CriticalBlocker.exponent_lt_parameters_of_counterexample
#print axioms Auxiliary.CriticalBlocker.IsProductCritical.not_hasSmallBlocker
#print axioms Auxiliary.CriticalBlocker.induced_free_comap
#print axioms Auxiliary.CriticalBlocker.nat_product_bound_of_critical_blockers
#print axioms Auxiliary.CriticalBlocker.isErdosHajnalLowerBound_of_critical_blockers
#print axioms Auxiliary.CriticalBlocker.erdosHajnal_of_critical_blockers
#print axioms Auxiliary.CriticalBlocker.erdosHajnal_of_critical_blocker_estimates
