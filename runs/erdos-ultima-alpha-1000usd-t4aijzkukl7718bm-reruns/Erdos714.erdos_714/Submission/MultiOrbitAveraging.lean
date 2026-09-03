import Submission.EdgeAveraging

/-!
Averaging a family of blocks over equally sized orbits. Unlike the transitive
version, no single block is required to meet the different orbits equally.
This is a construction-obstruction tool, not a resolution of Erdős 714.
-/

noncomputable section
open Finset Classical
set_option maxHeartbeats 2000000

namespace Erdos714MultiOrbit

variable {E I C Γ : Type*} [Fintype E] [Fintype I] [Fintype C]
  [Group Γ] [Fintype Γ]

variable (ρ : Γ →* Equiv.Perm E) (color : E → C)

def coverage (B : I → Finset E) (x : E) : ℕ :=
  ∑ i, (univ.filter (fun g => x ∈ Erdos714Averaging.translate ρ g (B i))).card

lemma coverage_eq (B : I → Finset E) (x y : E) (h : ∃ g, ρ g x = y) :
    coverage ρ B x = coverage ρ B y := by
  unfold coverage
  exact sum_congr rfl (fun i _ => Erdos714Averaging.coverage_eq ρ (B i) x y h)

lemma sum_coverage (B : I → Finset E) (S : Finset E) :
    ∑ x ∈ S, coverage ρ B x =
      ∑ i, ∑ g : Γ, (S.filter (fun x => x ∈ Erdos714Averaging.translate ρ g (B i))).card := by
  unfold coverage
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  exact (Erdos714Averaging.count_selected (Erdos714Averaging.translate ρ · (B i)) S).symm

omit [Fintype C] in
lemma orbit_coverage (hc : ∀ g x, color (ρ g x) = color x)
    (ht : ∀ x y, color x = color y → ∃ g, ρ g x = y)
    (N : ℕ) (hN : ∀ c, (univ.filter (fun x => color x = c)).card = N)
    (B : I → Finset E) (x : E) :
    N * coverage ρ B x =
      Fintype.card Γ * ∑ i, ((B i).filter (fun y => color y = color x)).card := by
  let S := univ.filter (fun y => color y = color x)
  have hleft : (∑ y ∈ S, coverage ρ B y) = N * coverage ρ B x := by
    calc
      _ = ∑ _y ∈ S, coverage ρ B x := by
        apply sum_congr rfl
        intro y hy
        exact coverage_eq ρ B y x (ht y x (mem_filter.mp hy).2)
      _ = N * coverage ρ B x := by simp [S, hN]
  have hblock (i : I) (g : Γ) :
      (S.filter (fun y => y ∈ Erdos714Averaging.translate ρ g (B i))).card =
        ((B i).filter (fun y => color y = color x)).card := by
    rw [Erdos714Averaging.translate, Erdos714GraphAveraging.filter_image_card]
    congr 1
    ext y
    simp [S, hc]
  rw [← hleft, sum_coverage]
  simp only [hblock, sum_const, card_univ, smul_eq_mul]
  exact (mul_sum ..).symm

omit [Fintype C] in
/-- A lower bound on the aggregate meeting number in each orbit is enough;
    the individual blocks may have different sizes and different local bounds. -/
theorem bound (hc : ∀ g x, color (ρ g x) = color x)
    (ht : ∀ x y, color x = color y → ∃ g, ρ g x = y)
    (N : ℕ) (hN : ∀ c, (univ.filter (fun x => color x = c)).card = N)
    (B : I → Finset E) (S : Finset E) (t : ℕ) (b : I → ℕ)
    (hmeet : ∀ c, t ≤ ∑ i, ((B i).filter (fun x => color x = c)).card)
    (hbound : ∀ i g,
      (S.filter (fun x => x ∈ Erdos714Averaging.translate ρ g (B i))).card ≤ b i) :
    t * S.card ≤ N * ∑ i, b i := by
  have hlow (x : E) : Fintype.card Γ * t ≤ N * coverage ρ B x := by
    rw [orbit_coverage ρ color hc ht N hN B x]
    exact Nat.mul_le_mul_left _ (hmeet (color x))
  have hupper : (∑ x ∈ S, coverage ρ B x) ≤ Fintype.card Γ * ∑ i, b i := by
    rw [sum_coverage]
    calc
      _ ≤ ∑ i, ∑ _g : Γ, b i := sum_le_sum (fun i _ => sum_le_sum (fun g _ => hbound i g))
      _ = _ := by simp [mul_sum]
  apply Nat.le_of_mul_le_mul_left (c := Fintype.card Γ) _ Fintype.card_pos
  calc
    _ = ∑ _x ∈ S, Fintype.card Γ * t := by simp; ring
    _ ≤ ∑ x ∈ S, N * coverage ρ B x := sum_le_sum (fun x _ => hlow x)
    _ = N * ∑ x ∈ S, coverage ρ B x := (mul_sum ..).symm
    _ ≤ N * (Fintype.card Γ * ∑ i, b i) := Nat.mul_le_mul_left _ hupper
    _ = _ := by ring


omit [Fintype C] in
/-- The local input may be a fourth-moment bound instead of an integer upper
    bound. Empty block-index types are included. -/
theorem fourth_power_bound (hc : ∀ g x, color (ρ g x) = color x)
    (ht : ∀ x y, color x = color y → ∃ g, ρ g x = y)
    (N : ℕ) (hN : ∀ c, (univ.filter (fun x => color x = c)).card = N)
    (B : I → Finset E) (S : Finset E) (t U : ℕ)
    (hmeet : ∀ c, t ≤ ∑ i, ((B i).filter (fun x => color x = c)).card)
    (hbound : ∀ i g,
      (S.filter (fun x => x ∈ Erdos714Averaging.translate ρ g (B i))).card^4 ≤ U) :
    (t*S.card)^4 ≤ (N*Fintype.card I)^4 * U := by
  let f : I × Γ → ℕ := fun p =>
    (S.filter (fun x => x ∈ Erdos714Averaging.translate ρ p.2 (B p.1))).card
  let b := univ.sup f
  have hb : b^4 ≤ U := by
    by_cases hne : (univ : Finset (I × Γ)).Nonempty
    · obtain ⟨p,_,hp⟩ := exists_mem_eq_sup univ hne f
      change (univ.sup f)^4 ≤ U
      rw [hp]
      exact hbound p.1 p.2
    · have he : (univ : Finset (I × Γ)) = ∅ := not_nonempty_iff_eq_empty.mp hne
      simp [b, he]
  have h := bound ρ color hc ht N hN B S t (fun _ => b) hmeet
    (fun i g => show f (i,g) ≤ univ.sup f from le_sup (mem_univ _))
  simp only [sum_const, card_univ, smul_eq_mul] at h
  calc
    _ ≤ (N*(Fintype.card I*b))^4 := Nat.pow_le_pow_left h 4
    _ = (N*Fintype.card I)^4*b^4 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hb

#print axioms fourth_power_bound

#print axioms bound
end Erdos714MultiOrbit
