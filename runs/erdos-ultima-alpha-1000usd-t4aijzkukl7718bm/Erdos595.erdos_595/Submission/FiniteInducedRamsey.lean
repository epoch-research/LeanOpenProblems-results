import Submission.FiniteFolkmanHomogenize

/-!
Finite induced edge-Ramsey hosts for finite K4-free targets, with a binary
palette. This uses only finitely many partite steps and makes no
countable-palette or infinite-target assertion.
-/

set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595FiniteInducedRamsey

/-- Ordinary finite binary Ramsey, in an embedding form. -/
theorem finite_binary_clique (A : Type) [Finite A] :
    ∃ (R : Type) (_ : Finite R), ∀ c : Sym2 R → Bool,
      ∃ (f : A ↪ R) (z : Bool), ∀ a b, a ≠ b → c s(f a,f b) = z := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  let n := Fintype.card A
  let N := Nat.choose (n+n) n
  refine ⟨Fin N,inferInstance,?_⟩
  intro c
  let d : Finset (Fin N) → Bool := fun S =>
    decide (∀ a ∈ S, ∀ b ∈ S, a ≠ b → c s(a,b) = true)
  have hd (a b : Fin N) (hab : a ≠ b) : d {a,b} = c s(a,b) := by
    simp only [d,Finset.mem_insert,Finset.mem_singleton]
    cases hc : c s(a,b) <;> simp [hc,hab,Ne.symm hab,Sym2.eq_swap]
  have hp := Combinatorics.Diagonal.hasRamseyProperty_choose n n d
    (Finset.univ : Finset (Fin N)) (by simp [N])
  have hex : ∃ (S : Finset (Fin N)) (z : Bool), S.card = n ∧
      ∀ e ⊆ S, e.card = 2 → d e = z := by
    rcases hp with ⟨S,_,hS,hm⟩ | ⟨S,_,hS,hm⟩
    · exact ⟨S,false,hS,hm⟩
    · exact ⟨S,true,hS,hm⟩
  obtain ⟨S,z,hS,hm⟩ := hex
  let e : A ≃ S := Fintype.equivOfCardEq (by simp only [Fintype.card_coe,hS]; rfl)
  let f : A ↪ Fin N := e.toEmbedding.trans (Function.Embedding.subtype (· ∈ S))
  refine ⟨f,z,?_⟩
  intro a b hab
  have hne : f a ≠ f b := f.injective.ne hab
  rw [← hd _ _ hne]
  apply hm
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (e a).property
    · exact (e b).property
  · simp [hne]

variable {A R : Type} (H : SimpleGraph A)

/-- Disjoint copies of H, one for each injective part placement. -/
def initial (R : Type) : SimpleGraph ((A ↪ R) × A) where
  Adj a b := a.1 = b.1 ∧ H.Adj a.2 b.2
  symm := fun _ _ h => ⟨h.1.symm,h.2.symm⟩
  loopless := fun _ h => H.loopless _ h.2

def initialCopy (f : A ↪ R) : H ↪g initial H R where
  toFun a := (f,a)
  inj' := fun _ _ h => congrArg Prod.snd h
  map_rel_iff' := by intro a b; exact ⟨And.right,fun h => ⟨rfl,h⟩⟩

lemma initial_cliqueFree (hH : H.CliqueFree 4) : (initial H R).CliqueFree 4 := by
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have he : ∀ i j : Fin 4, i ≠ j → H.Adj (e i).2 (e j).2 :=
    fun i j h => (e.map_rel_iff.mpr h).2
  exact Erdos595Work.no_adj_common_neighbors hH (he 0 1 (by decide))
    (he 0 2 (by decide)) (he 1 2 (by decide)) (he 0 3 (by decide))
    (he 1 3 (by decide)) (he 2 3 (by decide))

/-- A finite K4-free graph has a finite K4-free induced binary Ramsey host. -/
theorem finite_induced_ramsey [Finite A] (hH : H.CliqueFree 4) :
    ∃ (V : Type) (_ : Finite V) (G : SimpleGraph V), G.CliqueFree 4 ∧
      ∀ c : Sym2 V → Bool, ∃ (f : H ↪g G) (z : Bool),
        ∀ a b, H.Adj a b → c s(f a,f b) = z := by
  classical
  obtain ⟨R,hR,hRam⟩ := finite_binary_clique A
  letI := hR
  letI : Fintype R := Fintype.ofFinite R
  letI : LinearOrder R := IsWellOrder.linearOrder WellOrderingRel
  let I := (A ↪ R) × A
  haveI : Finite (A ↪ R) := Finite.of_injective
    (fun f : A ↪ R => (f : A → R)) DFunLike.coe_injective
  let K := initial H R
  let π : I → R := fun a => a.1 a.2
  have hπ : ∀ a b, K.Adj a b → π a ≠ π b := by
    intro a b hab he
    apply hab.2.ne
    apply a.1.injective
    change a.1 a.2 = b.1 b.2 at he
    simpa only [← hab.1] using he
  obtain ⟨V,hV,G,ρ,hG,_,hh⟩ := Erdos595FiniteFolkmanHomogenize.homogenize
    (C := Bool) K (initial_cliqueFree H hH) π hπ (Finset.univ : Finset (R × R))
  refine ⟨V,hV,G,hG,?_⟩
  intro c
  obtain ⟨f,_,hf⟩ := hh c
  have hz : ∀ r s : R, ∃ z : Bool, ∀ a b : I,
      K.Adj a b → π a = r → π b = s → c s(f a,f b) = z := by
    intro r s
    exact hf (r,s) (Finset.mem_univ _)
  choose z hz using hz
  let d₀ : R → R → Bool := fun r s => if r ≤ s then z r s else z s r
  have hd₀ : ∀ r s, d₀ r s = d₀ s r := by
    intro r s
    by_cases h : r ≤ s
    · by_cases h' : s ≤ r
      · have he := le_antisymm h h'; subst s; rfl
      · simp only [d₀,if_pos h,if_neg h']
    · have h' : s ≤ r := le_of_not_ge h
      simp only [d₀,if_neg h,if_pos h']
  let d : Sym2 R → Bool := Sym2.lift ⟨d₀,hd₀⟩
  have hd : ∀ a b : I, K.Adj a b → c s(f a,f b) = d s(π a,π b) := by
    intro a b hab
    change c s(f a,f b) = d₀ (π a) (π b)
    dsimp only [d₀]
    split_ifs with h
    · exact hz (π a) (π b) a b hab rfl rfl
    · simpa only [Sym2.eq_swap] using hz (π b) (π a) b a hab.symm rfl rfl
  obtain ⟨q,w,hq⟩ := hRam d
  refine ⟨f.comp (initialCopy H q),w,?_⟩
  intro a b hab
  exact (hd (q,a) (q,b) ⟨rfl,hab⟩).trans (hq a b hab.ne)

#print axioms finite_binary_clique
#print axioms finite_induced_ramsey
end Erdos595FiniteInducedRamsey
