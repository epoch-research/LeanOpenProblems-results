import FormalConjecturesUtil

/-! Neighborhood shattering in finite forbidden-bipartite-graph problems.
These bounds by themselves are not a rationality criterion. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713NeighborhoodVC
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

noncomputable def family (G : SimpleGraph V) : Finset (Finset V) :=
  univ.image (fun v => G.neighborFinset v)

lemma trace_exists {G : SimpleGraph V} {S T : Finset V}
    (hS : (family G).Shatters S) (hT : T ⊆ S) :
    ∃ v : V, S ∩ G.neighborFinset v = T := by
  obtain ⟨U,hU,hUT⟩ := hS hT
  obtain ⟨v,_hv,rfl⟩ := mem_image.mp hU
  exact ⟨v,hUT⟩

/-- An s-element common core and ell freely variable coordinates give
2^ell distinct rows containing that core. -/
theorem contains_of_shatters (G : SimpleGraph V) (S : Finset V)
    (hS : (family G).Shatters S) (s ell t : ℕ)
    (hsize : s+ell ≤ S.card) (ht : t ≤ 2^ell) :
    completeBipartiteGraph (Fin s) (Fin t) ⊑ G := by
  classical
  obtain ⟨A,hAS,hA⟩ := exists_subset_card_eq (show s ≤ S.card by omega)
  have hrem : ell ≤ (S \ A).card := by rw [card_sdiff_of_subset hAS,hA]; omega
  obtain ⟨T,hT,hTc⟩ := exists_subset_card_eq hrem
  have hTS : T ⊆ S := hT.trans sdiff_subset
  have hTA : ∀ x ∈ T, x ∉ A := fun x hx => (mem_sdiff.mp (hT hx)).2
  obtain ⟨P,hP,hPc⟩ := exists_subset_card_eq
    (show t ≤ T.powerset.card by simpa only [card_powerset,hTc] using ht)
  have hPS (p : P) : A ∪ p.val ⊆ S := union_subset hAS
    ((mem_powerset.mp (hP p.property)).trans hTS)
  choose w hw using fun p : P => trace_exists hS (hPS p)
  have hwi : Function.Injective w := by
    intro p q hpq
    apply Subtype.ext
    have he : A ∪ p.val = A ∪ q.val := (hw p).symm.trans ((congrArg
      (fun v => S ∩ G.neighborFinset v) hpq).trans (hw q))
    have hpT := mem_powerset.mp (hP p.property)
    have hqT := mem_powerset.mp (hP q.property)
    ext x
    constructor
    · intro hx
      have hxA := hTA x (hpT hx)
      have hh : x ∈ A ∪ q.val := he ▸ mem_union_right A hx
      exact (mem_union.mp hh).resolve_left hxA
    · intro hx
      have hxA := hTA x (hqT hx)
      have hh : x ∈ A ∪ p.val := he.symm ▸ mem_union_right A hx
      exact (mem_union.mp hh).resolve_left hxA
  let B := (univ : Finset P).image w
  have hB : B.card = t := by
    change ((univ : Finset P).image w).card = t
    rw [card_image_of_injective _ hwi,card_univ,Fintype.card_coe,hPc]
  apply completeBipartiteGraph_isContained_iff.mpr
  refine ⟨A,B,by simpa only [Fintype.card_fin] using hA,
    by simpa only [Fintype.card_fin] using hB,?_⟩
  intro a ha b hb
  obtain ⟨p,_hp,rfl⟩ := mem_image.mp hb
  have hh : a ∈ S ∩ G.neighborFinset (w p) := (hw p).symm ▸ mem_union_left _ ha
  exact ((G.mem_neighborFinset _ _).mp (mem_inter.mp hh).2).symm

/-- The exponent in this combinatorial complexity bound is integral.
No sharp edge-count estimate is inferred from it. -/
theorem vcDim_le (G : SimpleGraph V) (s ell t : ℕ)
    (hfree : (completeBipartiteGraph (Fin s) (Fin t)).Free G)
    (ht : t ≤ 2^ell) : (family G).vcDim ≤ s+ell-1 := by
  rw [Finset.vcDim,Finset.sup_le_iff]
  intro S hS
  have hs : S.card < s+ell := by
    by_contra hn
    exact hfree (contains_of_shatters G S (mem_shatterer.mp hS) s ell t (by omega) ht)
  omega

omit [Fintype V] in
lemma bipartite_contained_double (G : SimpleGraph V) (hG : G.IsBipartite) :
    G ⊑ completeBipartiteGraph V V := by
  classical
  obtain ⟨c⟩ := hG
  let f : V → V ⊕ V := fun v => if c v = 0 then .inl v else .inr v
  have hproj : Function.LeftInverse (Sum.elim id id) f := by
    intro v
    dsimp only [f]
    split_ifs <;> rfl
  have hfi : Function.Injective f := hproj.injective
  refine ⟨⟨⟨f,?_⟩,hfi⟩⟩
  intro v w hvw
  have hne := c.valid hvw
  dsimp only [f]
  split_ifs with hv hw hw
  · exact (hne (hv.trans hw.symm)).elim
  · simp
  · simp
  · have hc : c v = c w := by
      apply Fin.ext
      have hv' : (c v).val ≠ 0 := by simpa only [Fin.ext_iff,Fin.val_zero] using hv
      have hw' : (c w).val ≠ 0 := by simpa only [Fin.ext_iff,Fin.val_zero] using hw
      omega
    exact (hne hc).elim

/-- Every fixed bipartite forbidden graph gives a uniform neighborhood
VC-dimension bound on its free hosts. -/
theorem vcDim_le_of_bipartite {q : ℕ} (H : SimpleGraph (Fin q)) (hH : H.IsBipartite)
    (G : SimpleGraph V) (hfree : H.Free G) : (family G).vcDim ≤ 2*q-1 := by
  have hK : (completeBipartiteGraph (Fin q) (Fin q)).Free G :=
    fun h => hfree ((bipartite_contained_double H hH).trans h)
  have hh := vcDim_le G q q q hK (Nat.lt_two_pow_self.le)
  simpa only [two_mul] using hh

lemma cycle4_contained_k22 : cycleGraph 4 ⊑ completeBipartiteGraph (Fin 2) (Fin 2) := by
  let f : Fin 4 → Fin 2 ⊕ Fin 2 := ![.inl 0,.inr 0,.inl 1,.inr 1]
  have hfi : Function.Injective f := by decide
  refine ⟨⟨⟨f,?_⟩,hfi⟩⟩
  intro u v h
  fin_cases u <;> fin_cases v <;> simp [f]
  all_goals exact absurd h (by decide)

/-- In particular C4-free graphs have neighborhood VC dimension at most two. -/
theorem vcDim_le_two_of_c4_free (G : SimpleGraph V) (hG : (cycleGraph 4).Free G) :
    (family G).vcDim ≤ 2 := by
  have hK : (completeBipartiteGraph (Fin 2) (Fin 2)).Free G :=
    fun h => hG (cycle4_contained_k22.trans h)
  exact vcDim_le G 2 1 2 hK (by decide)

#print axioms contains_of_shatters
#print axioms vcDim_le_of_bipartite
#print axioms vcDim_le_two_of_c4_free
end Erdos713NeighborhoodVC
