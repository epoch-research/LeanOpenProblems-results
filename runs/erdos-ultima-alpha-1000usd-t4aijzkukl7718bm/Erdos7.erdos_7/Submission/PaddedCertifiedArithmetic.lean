import Submission.ArithmeticReduction

/-! Unused prime-like coordinates may be padded without proving their primality.
Only coordinates occurring in the arithmetic moduli require pairwise coprimality. -/
namespace Erdos7KilledSieve
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve Erdos7StarSieve
open Erdos7BinarySieve (expect)
set_option maxHeartbeats 4000000

theorem arithmetic_padded_certified_not_cover {n : ℕ} {κ : Type*} [Fintype κ]
    (p E : Fin n → ℕ) (hp : ∀ i, 1 < p i) (hE : ∀ i, 0 < E i)
    (S : Finset (Fin n)) (hcop : (S : Set (Fin n)).Pairwise (Function.onFun Nat.Coprime p))
    (e : κ → Fin n → ℕ) (he : Function.Injective e) (he0 : ∀ k, ∃ i, e k i≠0)
    (heE : ∀ k i, e k i≤E i) (heS : ∀ k i, e k i≠0 → i∈S) (a : κ → ℤ)
    (c s : Fin n → ℚ) (hc : ∀ i, 1≤c i) (hcp : ∀ i, c i≤p i)
    (hs : ∀ i, 0<s i)
    (hsum : ∀ i, (∑ g∈Finset.range (E i), ((p i:ℚ)⁻¹)^(g+1))≤s i)
    (L : Fin n → ℚ) (m : ℕ → ℚ) (hm0 : m 0=1)
    (hmsucc : ∀ i : Fin n,m (i.val+1)=m i.val-L i)
    (hmpos : ∀ t,t ≤ n → 0 ≤ m t) (hmfinal : 0 < m n)
    (hcert : SieveInvariantCertificate E c s (fun i => powerTail (p i) (c i) (E i)) L m) :
    ¬ (∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k) := by
  intro hcover
  classical
  letI (i : Fin n) : NeZero (p i) := ⟨by have := hp i; omega⟩
  let A (i : Fin n) := ZMod (p i ^ E i)
  let f (k : κ) (i : Fin n) := ZMod.castHom (pow_dvd_pow (p i) (heE k i)) (ZMod (p i ^ e k i))
  let B (k : κ) (i : Fin n) := Finset.univ.filter (fun x : A i => f k i x = (a k : ZMod (p i ^ e k i)))
  have hBcard (k : κ) (i : Fin n) : ((B k i).card : ℚ) ≤
      (Fintype.card (A i) : ℚ) * ((p i : ℚ)⁻¹)^(e k i) := by
    have hh := surjective_fiber_card_rat (f k i).toAddMonoidHom
      (ZMod.castHom_surjective (pow_dvd_pow (p i) (heE k i))) (a k)
    change ((B k i).card : ℚ) = _ at hh
    rw [hh]
    simp only [A, ZMod.card, Nat.cast_pow, div_eq_mul_inv, inv_pow]
    exact le_rfl
  have hbox : ∀ x : ∀ i, A i, ∃ k, ∀ i, x i ∈ B k i := by
    intro x
    let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) (fun i => p i ^ E i) S
      (fun i _ => pow_ne_zero _ (NeZero.ne _))
      (fun i hi j hj hij => (hcop hi hj hij).pow _ _)
    have hz (i : Fin n) (hi : i∈S) : (z.val : A i) = x i := by
      rw [← ZMod.natCast_zmod_val (x i)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i hi)
    obtain ⟨k, hk⟩ := hcover (z.val : ℤ)
    refine ⟨k, ?_⟩
    intro i
    by_cases hi : i∈S
    · have hpi : p i ^ e k i ∣ ∏ j, p j ^ e k j :=
        Finset.dvd_prod_of_mem (fun j => p j ^ e k j) (Finset.mem_univ i)
      have hpi' : ((p i ^ e k i : ℕ) : ℤ) ∣ ((∏ j, p j ^ e k j : ℕ) : ℤ) := by exact_mod_cast hpi
      have hqi := hpi'.trans hk
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hz i hi, map_natCast]
      symm
      simpa only [Int.cast_natCast] using
        (ZMod.intCast_eq_intCast_iff_dvd_sub (a k) (z.val : ℤ) (p i ^ e k i)).mpr hqi
    · have hz : e k i=0 := by
        by_contra hh
        exact hi (heS k i hh)
      simp only [B,Finset.mem_filter,Finset.mem_univ,true_and]
      haveI : Subsingleton (ZMod (p i ^ e k i)) := by rw [hz,pow_zero]; infer_instance
      exact Subsingleton.elim _ _
  have hc0 : ∀ i, 0≤c i := fun i => (by norm_num : (0:ℚ)≤1).trans (hc i)
  have hfrac (k : κ) (i : Fin n) : fraction (B k i)≤((p i:ℚ)⁻¹)^(e k i) := by
    apply (div_le_iff₀ card_pos_rat).mpr
    simpa only [mul_comm] using hBcard k i
  obtain ⟨x,hx⟩ := distinct_box_certified_avoidance A E hE c s (fun i g => ((p i:ℚ)⁻¹)^g)
    (fun i => powerTail (p i) (c i) (E i)) hc hs (fun _ _ _ => by positivity) hsum
    (fun i => powerTail_zero_le_one (p i) (hp i) (c i) (hcp i) (E i))
    (fun i g _ => powerTail_decreasing (p i) (hp i) (c i) (hc0 i) (E i) g)
    (fun i => powerTail_terminal (p i) (c i) (E i))
    (fun i g hg => by simp only [powerTail,if_pos hg,le_refl]) e he heE (by
      intro k
      obtain ⟨i,hi⟩ := he0 k
      exact ⟨i,(mem_expSupport _ _).mpr hi⟩) B (fun k i _ => hfrac k i) L m hm0 hmsucc hmpos hmfinal hcert
  obtain ⟨k,hk⟩ := hbox x
  exact hx k (fun i _ => hk i)


#print axioms arithmetic_padded_certified_not_cover
end Erdos7KilledSieve
