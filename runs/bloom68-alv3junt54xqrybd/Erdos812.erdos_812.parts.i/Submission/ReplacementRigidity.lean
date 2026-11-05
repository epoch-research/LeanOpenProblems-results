import Submission.GlobalCritical

/-!
# Global rigidity of two replacement profiles

On `R(n,n) - 2` old vertices, two profiles which each give an avoiding one-vertex
extension must share a red `(n - 2)`-clique and must jointly miss a blue `(n - 2)`-clique.
The proof uses the Ramsey property on two new vertices, not just local saturation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos812.Support

open Combinatorics

variable {V : Type*}

/-- Complementing an extension complements its old graph and its adjacency profile. -/
lemma profileExtension_compl [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) :
    (profileExtension G A)ᶜ = profileExtension Gᶜ (Finset.univ \ A) := by
  classical
  ext x y
  cases x <;> cases y <;> simp [profileExtension, SimpleGraph.compl_adj]

/-- Pull a finite clique back along an embedding whose range contains all its vertices. -/
private lemma clique_pullback_of_range {W : Type*} {H : SimpleGraph W} {n : ℕ}
    {S : Finset W} (f : V ↪ W) (hS : H.IsNClique n S)
    (hRange : ∀ x ∈ S, x ∈ Set.range f) :
    (H.comap f).IsNClique n (S.preimage f f.injective.injOn) := by
  classical
  refine ⟨?_, ?_⟩
  · intro v hv w hw hvw
    exact hS.isClique (Finset.mem_preimage.mp hv) (Finset.mem_preimage.mp hw)
      (by intro h; exact hvw (f.injective h))
  · rw [Finset.card_preimage, Finset.filter_eq_self.mpr hRange, hS.card_eq]

/-- With a red edge between the two new vertices, the Ramsey clique must be red and
must use both of them. Its old vertices therefore lie in both profiles. -/
private lemma two_profile_red_core [Fintype V] [DecidableEq V] {n : ℕ}
    (hn : 2 ≤ n) (G : SimpleGraph V) (A B : Finset V)
    (hcard : Fintype.card V + 2 = hypergraphRamsey 2 n)
    (hAr : (profileExtension G A).CliqueFree n)
    (hAb : (profileExtension G A)ᶜ.CliqueFree n)
    (hBr : (profileExtension G B).CliqueFree n)
    (hBb : (profileExtension G B)ᶜ.CliqueFree n) :
    ∃ S : Finset V, G.IsNClique (n - 2) S ∧ S ⊆ A ∩ B := by
  classical
  -- The inner new vertex is `some none`, the outer one is `none`, and old
  -- vertices are `some (some v)`. Including inner `none` in `C` makes their edge red.
  let C : Finset (Option V) := insert none (B.map Function.Embedding.some)
  let H := profileExtension (profileExtension G A) C
  let f : Option V ↪ Option (Option V) :=
    Function.Embedding.optionMap Function.Embedding.some
  have hA : H.comap Option.some = profileExtension G A := by simp [H]
  have hAc : Hᶜ.comap Option.some = (profileExtension G A)ᶜ := by simp [H]
  have hB : H.comap f = profileExtension G B := by
    ext x y
    cases x <;> cases y <;>
      simp [H, C, f, Function.Embedding.optionMap, profileExtension]
  have hBc : Hᶜ.comap f = (profileExtension G B)ᶜ := by
    rw [← hB]
    ext x y
    simp [SimpleGraph.compl_adj, f.injective.eq_iff]
  have hBoth {K : SimpleGraph (Option (Option V))}
      (hKA : (K.comap Option.some).CliqueFree n)
      (hKB : (K.comap f).CliqueFree n)
      {S : Finset (Option (Option V))} (hS : K.IsNClique n S) :
      none ∈ S ∧ some none ∈ S := by
    constructor
    · by_contra hNone
      have hRange : ∀ x ∈ S,
          x ∈ Set.range (Function.Embedding.some : Option V ↪ Option (Option V)) := by
        intro x hx
        cases x with
        | none => exact False.elim (hNone hx)
        | some x => exact ⟨x, rfl⟩
      exact hKA _ (clique_pullback_of_range Function.Embedding.some hS hRange)
    · by_contra hInner
      have hRange : ∀ x ∈ S, x ∈ Set.range f := by
        intro x hx
        cases x with
        | none => exact ⟨none, rfl⟩
        | some x =>
          cases x with
          | none => exact False.elim (hInner hx)
          | some v => exact ⟨some v, rfl⟩
      exact hKB _ (clique_pullback_of_range f hS hRange)
  have horder : hypergraphRamsey 2 n ≤ Fintype.card (Option (Option V)) := by
    rw [Fintype.card_option, Fintype.card_option]
    omega
  obtain ⟨S, hS⟩ := graph_ramsey_of_card_ge H horder
  rcases hS with hS | hS
  · obtain ⟨hOuter, hInner⟩ := hBoth
      (by simpa only [hA] using hAr) (by simpa only [hB] using hBr) hS
    refine ⟨S.eraseNone.eraseNone, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro v hv w hw hvw
        exact hS.isClique
          (Finset.mem_eraseNone.mp (Finset.mem_eraseNone.mp hv))
          (Finset.mem_eraseNone.mp (Finset.mem_eraseNone.mp hw))
          (by simpa only [ne_eq, Option.some.injEq] using hvw)
      · have hInner' : none ∈ S.eraseNone := Finset.mem_eraseNone.mpr hInner
        rw [Finset.card_eraseNone_of_mem hInner',
          Finset.card_eraseNone_of_mem hOuter, hS.card_eq]
        omega
    · intro v hv
      have hvS : some (some v) ∈ S :=
        Finset.mem_eraseNone.mp (Finset.mem_eraseNone.mp hv)
      apply Finset.mem_inter.mpr
      constructor
      · exact hS.isClique hInner hvS (by simp)
      · have hAdj : (some v : Option V) ∈ C := hS.isClique hOuter hvS (by simp)
        simpa [C] using hAdj
  · obtain ⟨hOuter, hInner⟩ := hBoth
      (by simpa only [hAc] using hAb) (by simpa only [hBc] using hBb) hS
    have hRed : H.Adj none (some none) := by
      change (none : Option V) ∈ C
      simp [C]
    have hBlue := hS.isClique hOuter hInner (by simp)
    exact False.elim (((H.compl_adj _ _).mp hBlue).2 hRed)

/-- **Global two-profile replacement rigidity.** If both one-vertex extensions avoid
an `n`-clique in both colors and the old graph has exactly `R(n,n) - 2` vertices, then
there is a red `(n - 2)`-clique in the intersection of the profiles **and** a blue
`(n - 2)`-clique outside their union. No extra local or structural hypothesis is used. -/
lemma global_two_profile_rigidity [Fintype V] [DecidableEq V] {n : ℕ}
    (hn : 2 ≤ n) (G : SimpleGraph V) (A B : Finset V)
    (hcard : Fintype.card V + 2 = hypergraphRamsey 2 n)
    (hAr : (profileExtension G A).CliqueFree n)
    (hAb : (profileExtension G A)ᶜ.CliqueFree n)
    (hBr : (profileExtension G B).CliqueFree n)
    (hBb : (profileExtension G B)ᶜ.CliqueFree n) :
    (∃ S : Finset V, G.IsNClique (n - 2) S ∧ S ⊆ A ∩ B) ∧
      (∃ T : Finset V, Gᶜ.IsNClique (n - 2) T ∧ T ⊆ Finset.univ \ (A ∪ B)) := by
  classical
  refine ⟨two_profile_red_core hn G A B hcard hAr hAb hBr hBb, ?_⟩
  obtain ⟨T, hT, hTAB⟩ := two_profile_red_core hn Gᶜ
    (Finset.univ \ A) (Finset.univ \ B) hcard
    (by simpa only [← profileExtension_compl G A] using hAb)
    (by simpa only [← profileExtension_compl G A, compl_compl] using hAr)
    (by simpa only [← profileExtension_compl G B] using hBb)
    (by simpa only [← profileExtension_compl G B, compl_compl] using hBr)
  refine ⟨T, hT, ?_⟩
  intro v hv
  obtain ⟨hvA, hvB⟩ := Finset.mem_inter.mp (hTAB hv)
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hvAB
  rcases Finset.mem_union.mp hvAB with hvA' | hvB'
  · exact (Finset.mem_sdiff.mp hvA).2 hvA'
  · exact (Finset.mem_sdiff.mp hvB).2 hvB'

end Erdos812.Support
