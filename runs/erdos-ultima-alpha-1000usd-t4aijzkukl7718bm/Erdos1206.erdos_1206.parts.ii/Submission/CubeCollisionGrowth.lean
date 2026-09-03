import Submission.PrimitiveCollisionMass

/-!
The number of ordered four-distinct-root cubic collisions grows faster than
linearly. This does not bound the independence ratio of the collision
hypergraph and does not settle the positive-density Sidon conjecture.
-/

namespace Erdos1206.CubeCollisionGrowth
open Finset Filter
open PrimitiveCollisionMass

abbrev Quad := ℕ × ℕ × ℕ × ℕ

def quadGcd (x : Quad) : ℕ :=
  Nat.gcd (Nat.gcd x.1 x.2.1) (Nat.gcd x.2.2.1 x.2.2.2)

def dilate (q : ℕ) (x : Quad) : Quad :=
  (q*x.1, q*x.2.1, q*x.2.2.1, q*x.2.2.2)

lemma quadGcd_dilate (q : ℕ) (x : Quad) : quadGcd (dilate q x) = q * quadGcd x := by
  simp only [quadGcd, dilate, Nat.gcd_mul_left]

lemma primitive_dilate_gcd (q : ℕ) (e : Collision) : quadGcd (dilate q e.val) = q := by
  rw [quadGcd_dilate]
  have he : quadGcd e.val = 1 := e.property.2.2.2.2.2
  rw [he, mul_one]

lemma primitive_dilate_injective {e f : Collision} {q r : ℕ} (hq : 0 < q)
    (heq : dilate q e.val = dilate r f.val) : e = f ∧ q = r := by
  have hqr := congrArg quadGcd heq
  simp only [primitive_dilate_gcd] at hqr
  subst r
  have he : e.val = f.val := by
    apply Prod.ext
    · exact Nat.eq_of_mul_eq_mul_left hq (congrArg (fun x : Quad => x.1) heq)
    · apply Prod.ext
      · exact Nat.eq_of_mul_eq_mul_left hq (congrArg (fun x : Quad => x.2.1) heq)
      · apply Prod.ext
        · exact Nat.eq_of_mul_eq_mul_left hq (congrArg (fun x : Quad => x.2.2.1) heq)
        · exact Nat.eq_of_mul_eq_mul_left hq (congrArg (fun x : Quad => x.2.2.2) heq)
  exact ⟨Subtype.ext he, rfl⟩

/-- Every positive root is at most `N`; roots are strictly increasingly ordered. -/
def collisionsUpTo (N : ℕ) : Finset Quad :=
  ((range (N+1)) ×ˢ ((range (N+1)) ×ˢ ((range (N+1)) ×ˢ (range (N+1))))).filter
    (fun x => 0 < x.1 ∧ x.1 < x.2.1 ∧ x.2.1 < x.2.2.1 ∧
      x.2.2.1 < x.2.2.2 ∧ x.1^3+x.2.2.2^3=x.2.1^3+x.2.2.1^3)

lemma dilate_mem_collisionsUpTo (e : Collision) {q N : ℕ}
    (hq : 0 < q) (hN : q * e.val.2.2.2 ≤ N) :
    dilate q e.val ∈ collisionsUpTo N := by
  have he := e.property
  have hab := Nat.mul_lt_mul_of_pos_left he.2.1 hq
  have hbc := Nat.mul_lt_mul_of_pos_left he.2.2.1 hq
  have hcd := Nat.mul_lt_mul_of_pos_left he.2.2.2.1 hq
  have hid : (q*e.val.1)^3 + (q*e.val.2.2.2)^3 =
      (q*e.val.2.1)^3 + (q*e.val.2.2.1)^3 := by
    simpa only [mul_pow, ← mul_add] using congrArg (fun n : ℕ => q^3*n) he.2.2.2.2.1
  simp only [collisionsUpTo, mem_filter, mem_product, mem_range, dilate]
  exact ⟨⟨by omega, by omega, by omega, by omega⟩,
    Nat.mul_pos hq he.1, hab, hbc, hcd, hid⟩

lemma finite_dilate_count (F : Finset Collision) (N : ℕ) :
    ∑ e ∈ F, N / e.val.2.2.2 ≤ (collisionsUpTo N).card := by
  classical
  let S := F.sigma (fun e => Icc 1 (N / e.val.2.2.2))
  let f : ((e : Collision) × ℕ) → Quad := fun z => dilate z.2 z.1.val
  have hf : Set.InjOn f (S : Set ((e : Collision) × ℕ)) := by
    intro x hx y hy hxy
    have hqx : 0 < x.2 := (mem_Icc.mp (mem_sigma.mp hx).2).1
    obtain ⟨he, hq⟩ := primitive_dilate_injective hqx hxy
    cases x with
    | mk e q =>
      cases y with
      | mk e' q' =>
        dsimp only at he hq
        subst e' q'
        rfl
  have hsub : S.image f ⊆ collisionsUpTo N := by
    intro x hx
    obtain ⟨⟨e,q⟩, hz, rfl⟩ := mem_image.mp hx
    have hq := mem_Icc.mp (mem_sigma.mp hz).2
    apply dilate_mem_collisionsUpTo e hq.1
    exact (Nat.mul_le_mul_right _ hq.2).trans (Nat.div_mul_le_self N _)
  have hh := card_le_card hsub
  rw [card_image_of_injOn hf] at hh
  simpa [S, card_sigma] using hh

lemma primitive_height_pos (e : Collision) : 0 < e.val.2.2.2 :=
  e.property.1.trans (e.property.2.1.trans (e.property.2.2.1.trans e.property.2.2.2.1))

lemma finite_reciprocal_count_bound (F : Finset Collision) (N : ℕ) :
    (N : ℝ) * (∑ e ∈ F, (1 : ℝ) / e.val.2.2.2) ≤
      ((collisionsUpTo N).card : ℝ) + F.card := by
  have hterm (e : Collision) :
      (N : ℝ) / e.val.2.2.2 ≤ ((N / e.val.2.2.2 : ℕ) : ℝ) + 1 := by
    have hpos : (0 : ℝ) < e.val.2.2.2 := by exact_mod_cast primitive_height_pos e
    apply (div_le_iff₀ hpos).mpr
    have h := Nat.lt_mul_div_succ N (primitive_height_pos e)
    have h' : (N : ℝ) < e.val.2.2.2 * (((N / e.val.2.2.2 : ℕ) : ℝ) + 1) := by
      exact_mod_cast h
    nlinarith
  have hc : (∑ e ∈ F, ((N / e.val.2.2.2 : ℕ) : ℝ)) ≤
      ((collisionsUpTo N).card : ℝ) := by exact_mod_cast finite_dilate_count F N
  calc
    _ = ∑ e ∈ F, (N : ℝ) / e.val.2.2.2 := by simp [mul_sum, div_eq_mul_inv]
    _ ≤ ∑ e ∈ F, (((N / e.val.2.2.2 : ℕ) : ℝ) + 1) := sum_le_sum fun e _ => hterm e
    _ = (∑ e ∈ F, ((N / e.val.2.2.2 : ℕ) : ℝ)) + F.card := by simp [sum_add_distrib]
    _ ≤ _ := by linarith

lemma exists_large_primitive_reciprocal_sum (C : ℝ) :
    ∃ F : Finset Collision, C < ∑ e ∈ F, (1 : ℝ) / e.val.2.2.2 := by
  classical
  by_contra! h
  exact primitive_reciprocal_heights_not_summable
    (summable_of_sum_le (fun _ => by positivity) h)

/-- Linear collision-count bounds fail by an arbitrarily large factor, at all
sufficiently large cutoffs. This does not bound the maximum independent set. -/
theorem collision_count_superlinear (C : ℝ) :
    ∃ M : ℕ, ∀ N ≥ M, C * N < ((collisionsUpTo N).card : ℝ) := by
  obtain ⟨F, hF⟩ := exists_large_primitive_reciprocal_sum (C+1)
  refine ⟨F.card + 1, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hFN : (F.card : ℝ) ≤ N := by exact_mod_cast (show F.card ≤ N by omega)
  have hmul := mul_lt_mul_of_pos_left hF hNpos
  have hb := finite_reciprocal_count_bound F N
  nlinarith

theorem collision_count_div_tendsto_atTop :
    Tendsto (fun N : ℕ => ((collisionsUpTo N).card : ℝ) / N) atTop atTop := by
  apply tendsto_atTop.mpr
  intro C
  obtain ⟨M,hM⟩ := collision_count_superlinear C
  filter_upwards [eventually_ge_atTop (M+1)] with N hN
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply (le_div_iff₀ hpos).mpr
  exact (hM N (by omega)).le

#print axioms collision_count_superlinear
#print axioms collision_count_div_tendsto_atTop

end Erdos1206.CubeCollisionGrowth
