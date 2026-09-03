import FormalConjecturesUtil

/-! Linear-length sorted-pair certificates for finite square-Sidon sets. -/
namespace Erdos773.SidonPairCertificate
open Finset

def orderedPairs (m : ℕ) : Finset (Fin m × Fin m) := univ.filter (fun p => p.1 ≤ p.2)
def pairSum {m : ℕ} (f : Fin m → ℕ) (p : Fin m × Fin m) : ℕ := f p.1 ^ 2 + f p.2 ^ 2

/-- A sorted list of all unordered pairs certifies uniqueness without enumerating
all quadruples. No external solver result is assumed. -/
theorem squares_sidon {m : ℕ} (f : Fin m → ℕ) (L : List (Fin m × Fin m))
    (hvalid : ∀ p ∈ L, p.1 ≤ p.2)
    (hlen : (orderedPairs m).card ≤ L.length)
    (hsort : (L.map (pairSum f)).IsChain (· < ·)) :
    IsSidon ((univ.image (fun i => f i ^ 2) : Finset ℕ) : Set ℕ) := by
  have hn : (L.map (pairSum f)).Nodup := hsort.pairwise.nodup
  have hnL : L.Nodup := List.Nodup.of_map _ hn
  have hsub : L.toFinset ⊆ orderedPairs m := by
    intro p hp
    exact mem_filter.mpr ⟨mem_univ _, hvalid p (List.mem_toFinset.mp hp)⟩
  have hcover : L.toFinset = orderedPairs m :=
    Finset.eq_of_subset_of_card_le hsub (by rwa [List.toFinset_card_of_nodup hnL])
  have hpair (i j k l : Fin m) (hij : i ≤ j) (hkl : k ≤ l)
      (he : f i ^ 2 + f j ^ 2 = f k ^ 2 + f l ^ 2) : i = k ∧ j = l := by
    have hmem (a b : Fin m) (hab : a ≤ b) : (a,b) ∈ L := by
      rw [← List.mem_toFinset, hcover]
      exact mem_filter.mpr ⟨mem_univ _, hab⟩
    have hh := (List.nodup_map_iff_inj_on hnL).mp hn (i,j) (hmem i j hij)
      (k,l) (hmem k l hkl) he
    exact Prod.mk.inj hh
  have hmatch (i j k l : Fin m)
      (he : f i ^ 2 + f j ^ 2 = f k ^ 2 + f l ^ 2) :
      (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
    by_cases hij : i ≤ j
    · by_cases hkl : k ≤ l
      · exact Or.inl (hpair i j k l hij hkl he)
      · exact Or.inr (hpair i j l k hij (le_of_not_ge hkl) (by simpa [add_comm] using he))
    · by_cases hkl : k ≤ l
      · obtain ⟨hjk, hil⟩ := hpair j i k l (le_of_not_ge hij) hkl (by simpa [add_comm] using he)
        exact Or.inr ⟨hil,hjk⟩
      · obtain ⟨hjl, hik⟩ := hpair j i l k (le_of_not_ge hij)
          (le_of_not_ge hkl) (by simpa [add_comm] using he)
        exact Or.inl ⟨hik,hjl⟩
  intro a ha c hc b hb d hd he
  simp only [Finset.mem_coe] at ha hc hb hd
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hd
  rcases hmatch i j k l he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp

#print axioms squares_sidon
end Erdos773.SidonPairCertificate
