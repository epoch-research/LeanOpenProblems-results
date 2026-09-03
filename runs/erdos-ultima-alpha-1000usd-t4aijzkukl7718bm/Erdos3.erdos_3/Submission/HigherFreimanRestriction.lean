import Submission.VerticalDifferenceBound

/-! Higher-order Freiman restrictions with polynomial losses. The vertical
separation argument preserves any fixed number of summands, not just two. -/
namespace Erdos3HigherFreimanRestriction
open Finset Erdos3FrequencyGraph Erdos3CharacterSeparation Erdos3FreimanFrequencyGraph
  Erdos3FiniteBohr Erdos3BohrCovering
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 4500000

lemma multiset_sum_mem_nsmul {A : Type*} [AddCommMonoid A] [DecidableEq A]
    (H : Finset A) (s : Multiset A) (hs : ∀ x ∈ s, x ∈ H) : s.sum ∈ s.card • H := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
    have hx := hs x (Multiset.mem_cons_self _ _)
    have ht := ih (fun y hy ↦ hs y (Multiset.mem_cons_of_mem hy))
    simpa only [Multiset.sum_cons,Multiset.card_cons,add_nsmul,one_nsmul,add_comm] using add_mem_add hx ht

lemma multiset_sum_centered {A B : Type*} [AddCommGroup B] (s : Multiset A) (f : A → B) (η : B) :
    (s.map (fun a ↦ f a-η)).sum = (s.map f).sum-s.card • η := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp only [Multiset.map_cons,Multiset.sum_cons,Multiset.card_cons,add_nsmul,one_nsmul,ih]
    abel

lemma multiset_sum_graph {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (s : Multiset A) (f : A → B) :
    (s.map (fun a ↦ (a,f a))).sum = (s.sum,(s.map f).sum) := by
  induction s using Multiset.induction_on with
  | empty => simp; rfl
  | @cons a s ih => simp [ih]

lemma multiset_bohr_sum {A : Type*} [AddCommGroup A] [Fintype A]
    (E : Finset (AddChar A ℂ)) (s : Multiset A) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hs : ∀ x ∈ s, x ∈ bohr E ρ) : s.sum ∈ bohr E ((s.card : ℝ)*ρ) := by
  induction s using Multiset.induction_on with
  | empty => simpa using bohr_zero E (le_refl (0 : ℝ))
  | @cons x s ih =>
    have hx := hs x (Multiset.mem_cons_self _ _)
    have ht := ih (fun y hy ↦ hs y (Multiset.mem_cons_of_mem hy))
    have hh := bohr_add hx ht
    simpa only [Multiset.sum_cons,Multiset.card_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm] using hh

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def verticalN (n : ℕ) (H : Finset G) (ξ : G → AddChar G ℂ) : Finset (AddChar G ℂ) :=
  univ.filter (fun χ ↦ (0,χ) ∈ n • frequencyGraph H ξ-n • frequencyGraph H ξ)

def restrictionExponent (n : ℕ) : ℕ := 4*(8*n+1)

lemma higher_separation_grid_cost (n M m : ℕ) (hm : m ≤ 2*(Nat.log 2 M+1)) :
    (8*n+1)^(2*m) ≤ (2*(M+1))^(restrictionExponent n) := by
  let L := Nat.log 2 M+1
  have hpow : 2^L ≤ 2*(M+1) := by
    dsimp [L]
    rw [pow_succ]
    have hh := Nat.pow_log_le_add_one 2 M
    omega
  calc
    _ ≤ (2^(8*n+1))^(2*m) := Nat.pow_le_pow_left (Nat.le_of_lt (8*n+1).lt_two_pow_self) _
    _ = 2^((8*n+1)*(2*m)) := by rw [← pow_mul]
    _ ≤ 2^((8*n+1)*(4*L)) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (by dsimp [L]; omega))
    _ = (2^L)^(restrictionExponent n) := by rw [← pow_mul]; congr 1; dsimp [restrictionExponent]; ring
    _ ≤ _ := Nat.pow_le_pow_left hpow _

lemma separated_higher_freiman_restriction (n : ℕ) (hn : 0 < n)
    (H : Finset G) (ξ : G → AddChar G ℂ) (D : Finset G)
    (hsep : ∀ χ ∈ verticalN n H ξ, χ ≠ 0 → ∃ x ∈ D, 1 < ‖χ x-1‖) :
    ∃ H' ⊆ H, H.card ≤ (8*n+1)^(2*D.card)*H'.card ∧
      IsAddFreimanHom n (H' : Set G) Set.univ ξ := by
  let E : Finset (AddChar (AddChar G ℂ) ℂ) := D.image AddChar.doubleDualEmb
  let ρ : ℝ := 1/(2*(n : ℝ))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  let U : Finset (AddChar G ℂ) := bohr E ρ
  have hU : U.Nonempty := ⟨0,bohr_zero E hρ⟩
  have hcardU : Fintype.card (AddChar G ℂ) ≤ (8*n+1)^(2*D.card)*U.card := by
    have hh := card_bohr_lower E (q := 4*n) (by omega)
    have he : 2/((4*n : ℕ) : ℝ) = ρ := by dsimp [ρ]; push_cast; field_simp; ring
    rw [he,show 2*(4*n)+1 = 8*n+1 by omega] at hh
    exact hh.trans (Nat.mul_le_mul_right _
      (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 2 card_image_le)))
  obtain ⟨η,hη⟩ := exists_large_translate_fiber H ξ U hU hcardU
  let H' := H.filter (fun h ↦ ξ h-η ∈ U)
  refine ⟨H',filter_subset _ _,hη,⟨fun _ _ ↦ Set.mem_univ _,?_⟩⟩
  intro s t hsA htA hs ht hsum
  let χ : AddChar G ℂ := (s.map ξ).sum-(t.map ξ).sum
  have hΓsum (u : Multiset G) (hu : ∀ x ∈ u, x ∈ H') (huc : u.card = n) :
      (u.map (fun a ↦ (a,ξ a))).sum ∈ n • frequencyGraph H ξ := by
    have hh := multiset_sum_mem_nsmul (frequencyGraph H ξ) (u.map (fun a ↦ (a,ξ a))) (by
      intro p hp
      obtain ⟨a,ha,rfl⟩ := Multiset.mem_map.mp hp
      exact (mem_frequencyGraph H ξ _).mpr ⟨(mem_filter.mp (hu a ha)).1,rfl⟩)
    simpa only [Multiset.card_map,huc] using hh
  have hχV : χ ∈ verticalN n H ξ := by
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    have hh := sub_mem_sub (hΓsum s (fun _ h ↦ hsA h) hs) (hΓsum t (fun _ h ↦ htA h) ht)
    rw [multiset_sum_graph,multiset_sum_graph] at hh
    have he : (s.sum,(s.map ξ).sum)-(t.sum,(t.map ξ).sum) = (0,χ) := by
      apply Prod.ext
      · change s.sum-t.sum = 0
        rw [hsum,sub_self]
      · rfl
    rwa [he] at hh
  have hcenter (u : Multiset G) (hu : ∀ x ∈ u, x ∈ H') (huc : u.card = n) :
      (u.map (fun a ↦ ξ a-η)).sum ∈ bohr E ((n : ℝ)*ρ) := by
    have hh := multiset_bohr_sum E (u.map (fun a ↦ ξ a-η)) hρ (by
      intro z hz
      obtain ⟨a,ha,rfl⟩ := Multiset.mem_map.mp hz
      exact (mem_filter.mp (hu a ha)).2)
    simpa only [Multiset.card_map,huc] using hh
  have hχU : χ ∈ bohr E 1 := by
    have hh := bohr_add (hcenter s (fun _ h ↦ hsA h) hs) (bohr_neg (hcenter t (fun _ h ↦ htA h) ht))
    rw [multiset_sum_centered,multiset_sum_centered,hs,ht] at hh
    have he : ((s.map ξ).sum-n • η) + -((t.map ξ).sum-n • η) = χ := by dsimp [χ]; abel
    rw [he] at hh
    have hr : (n : ℝ)*ρ+(n : ℝ)*ρ = 1 := by dsimp [ρ]; field_simp; ring
    rwa [hr] at hh
  have hz : χ = 0 := by
    by_contra hnχ
    obtain ⟨x,hx,hgt⟩ := hsep χ hχV hnχ
    have he : AddChar.doubleDualEmb x ∈ E := mem_image.mpr ⟨x,hx,rfl⟩
    have hle : ‖χ x-1‖ ≤ 1 := mem_bohr.mp hχU _ he
    exact (not_lt_of_ge hle) hgt
  exact sub_eq_zero.mp hz

/-- Restriction to an exact n-Freiman homomorphism costs a polynomial in the
number of vertical 2n-term differences. -/
theorem exists_higher_freiman_restriction (n : ℕ) (hn : 0 < n)
    (H : Finset G) (ξ : G → AddChar G ℂ) :
    ∃ H' ⊆ H, H.card ≤ (2*((verticalN n H ξ).card+1))^(restrictionExponent n)*H'.card ∧
      IsAddFreimanHom n (H' : Set G) Set.univ ξ := by
  let C := (verticalN n H ξ).erase 0
  obtain ⟨D,hD,hsep⟩ := exists_small_separating_set C (fun χ hχ ↦ (mem_erase.mp hχ).1)
  obtain ⟨H',hsub,hsize,hFreiman⟩ := separated_higher_freiman_restriction n hn H ξ D (by
    intro χ hχ hne
    exact hsep χ (mem_erase.mpr ⟨hne,hχ⟩))
  have hcost := higher_separation_grid_cost n C.card D.card hD
  have hC : C.card ≤ (verticalN n H ξ).card := card_le_card (erase_subset _ _)
  refine ⟨H',hsub,?_,hFreiman⟩
  exact hsize.trans (Nat.mul_le_mul_right _ (hcost.trans
    (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hC 1)) _)))

#print axioms exists_higher_freiman_restriction
end Erdos3HigherFreimanRestriction
