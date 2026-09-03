import FormalConjecturesUtil

/-!
Subgroup-coset obstructions for bipartite Cayley graphs, including cyclic
order-four grids in noncommutative groups. This is not a solution of Erdős 714.
-/

noncomputable section
open SimpleGraph Classical

namespace Erdos714CayleyCosetGrids

variable {G : Type*} [Group G]

/-- No inverse-closure assumption is needed for this two-part graph. -/
def graph (S : Set G) : SimpleGraph (G ⊕ G) where
  Adj x y := match x,y with
    | .inl u, .inr v => u⁻¹*v ∈ S
    | .inr v, .inl u => u⁻¹*v ∈ S
    | _, _ => False
  symm := by intro x y; cases x <;> cases y <;> simp_all
  loopless := by intro x; cases x <;> simp

/-- A full right coset in the connection set supplies a rectangular Cayley grid. -/
def cosetCopy (S : Set G) (H : Subgroup G) (g : G)
    (hS : ∀ h ∈ H, h*g ∈ S) {r s : ℕ} (e : Fin r ↪ H) (f : Fin s ↪ H) :
    Copy (completeBipartiteGraph (Fin r) (Fin s)) (graph S) := by
  let L : Fin r ↪ G := e.trans ⟨Subtype.val, Subtype.val_injective⟩
  let R : Fin s ↪ G := ⟨fun j => (f j : G)*g, by
    intro i j he
    exact f.injective (Subtype.ext (mul_right_cancel he))⟩
  have he (i : Fin r) (j : Fin s) : (L i)⁻¹*R j ∈ S := by
    change (e i : G)⁻¹*((f j : G)*g) ∈ S
    rw [← mul_assoc]
    exact hS _ (H.mul_mem (H.inv_mem (e i).property) (f j).property)
  refine ⟨⟨L.sumMap R, ?_⟩, (L.sumMap R).injective⟩
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl k => simp at h
    | inr j => exact he i j
  | inr j =>
    cases y with
    | inr k => simp at h
    | inl i => exact he i j

lemma order_four {u : G} (h₂ : u^2 ≠ 1) (h₄ : u^4 = 1) : orderOf u = 4 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_pow (p := 2) (n := 1) h₂ h₄

/-- The four distinct powers of an order-four element form an embedding. -/
def fourPowers (u : G) (h₂ : u^2 ≠ 1) (h₄ : u^4 = 1) : Fin 4 ↪ Subgroup.zpowers u where
  toFun i := ⟨u^i.val, Subgroup.npow_mem_zpowers u i.val⟩
  inj' := by
    intro i j he
    apply Fin.ext
    apply pow_injOn_Iio_orderOf (x := u)
    · simpa only [Set.mem_Iio, order_four h₂ h₄] using i.isLt
    · simpa only [Set.mem_Iio, order_four h₂ h₄] using j.isLt
    · exact congrArg Subtype.val he

lemma coset_mem_of_four (S : Set G) (u g : G) (h₄ : u^4 = 1)
    (hS : ∀ i : Fin 4, u^i.val*g ∈ S) :
    ∀ h ∈ Subgroup.zpowers u, h*g ∈ S := by
  rintro h ⟨n, rfl⟩
  have h₄z : u^(4 : ℤ) = 1 := by
    change u^((4 : ℕ) : ℤ) = 1
    rw [zpow_natCast]
    exact h₄
  change u^n*g ∈ S
  rw [zpow_eq_zpow_emod n h₄z]
  have hn0 : 0 ≤ n % 4 := Int.emod_nonneg _ (by norm_num)
  have hn4 : n % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  let i : Fin 4 := ⟨(n % 4).toNat, by omega⟩
  have he : u^(n % 4) = u^i.val := by
    rw [← zpow_natCast]
    congr 1
    exact (Int.toNat_of_nonneg hn0).symm
  rw [he]
  exact hS i

/-- Four consecutive points of a cyclic coset already give the whole K44. -/
def cyclicFourCopy (S : Set G) (u g : G) (h₂ : u^2 ≠ 1) (h₄ : u^4 = 1)
    (hS : ∀ i : Fin 4, u^i.val*g ∈ S) :
    Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph S) :=
  cosetCopy S (Subgroup.zpowers u) g (coset_mem_of_four S u g h₄ hS)
    (fourPowers u h₂ h₄) (fourPowers u h₂ h₄)

/-- Two pairs with a common involutory displacement give a cyclic grid when
 the difference between the pairs squares to that displacement. No ambient
 commutativity is assumed. -/
def matchingPairsCopy (S : Set G) (s t z : G) (hz : z ≠ 1) (hz₂ : z^2 = 1)
    (hu : (t*s⁻¹)^2 = z) (hs : s ∈ S) (ht : t ∈ S)
    (hzs : z*s ∈ S) (hzt : z*t ∈ S) :
    Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph S) := by
  have hu₂ : (t*s⁻¹)^2 ≠ 1 := by rwa [hu]
  have hu₄ : (t*s⁻¹)^4 = 1 := by
    rw [show 4 = 2*2 from rfl, pow_mul, hu, hz₂]
  apply cyclicFourCopy S (t*s⁻¹) s hu₂ hu₄
  intro i
  fin_cases i
  · simpa using hs
  · simpa [mul_assoc] using ht
  · simpa only [Fin.val_two, hu] using hzs
  · change (t*s⁻¹)^3*s ∈ S
    rw [pow_succ, hu, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
    exact hzt

theorem not_free_of_matching_pairs (S : Set G) (s t z : G)
    (hz : z ≠ 1) (hz₂ : z^2 = 1) (hu : (t*s⁻¹)^2 = z)
    (hs : s ∈ S) (ht : t ∈ S) (hzs : z*s ∈ S) (hzt : z*t ∈ S) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph S) := by
  intro hf
  exact hf ⟨matchingPairsCopy S s t z hz hz₂ hu hs ht hzs hzt⟩

end Erdos714CayleyCosetGrids

#print axioms Erdos714CayleyCosetGrids.cosetCopy
#print axioms Erdos714CayleyCosetGrids.cyclicFourCopy
#print axioms Erdos714CayleyCosetGrids.matchingPairsCopy
#print axioms Erdos714CayleyCosetGrids.not_free_of_matching_pairs
