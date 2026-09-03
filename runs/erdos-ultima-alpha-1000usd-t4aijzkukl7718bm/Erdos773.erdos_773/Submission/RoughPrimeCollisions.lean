import Submission.LogRoughPrimeCarrier

/-!
Prime roots with arbitrarily prescribed finite sets of excluded pair-norm
prime factors can still have a four-distinct-root square-sum collision.
This refutes only a roughness criterion, not the original conjecture.
-/
namespace Erdos773.RoughPrimeCollisions
open Finset Filter RoughPairNorms PrimeColorCollisions
set_option maxHeartbeats 1000000

private def tag (P : Finset ℕ) (n : ℕ) : Option P :=
  if hn : n∈P then some ⟨n,hn⟩ else none

def color (P : Finset ℕ) (n : ℕ) : (P → Bool) × Option P :=
  (fun p => localColor p.val n, tag P n)

private lemma outside_of_same_tag {P : Finset ℕ} {a b : ℕ}
    (hne : a≠b) (he : tag P a=tag P b) : a∉P := by
  intro ha
  by_cases hb : b∈P
  · have hh : a=b := by simpa [tag,ha,hb,Subtype.ext_iff] using he
    exact hne hh
  · simp [tag,ha,hb] at he

/-- A monochromatic prime collision gives a rough four-root set. -/
theorem rough_set_of_collision (A P : Finset ℕ)
    (hA : ∀ a∈A, a.Prime) (hP : ∀ p∈P, p.Prime ∧ 2<p)
    (hc : FourCollision A (color P)) :
    ∃ B ⊆ A, B.card=4 ∧ FourCollision B (fun _ => ()) ∧
      ¬IsSidon ((B.image (fun n => n^2)) : Set ℕ) ∧
      ∀ a∈B, ∀ b∈B, ∀ p∈P, ¬p ∣ a^2+b^2 := by
  obtain ⟨a,ha,b,hb,c,hc,d,hd,hab,hac,had,hbc,hbd,hcd,he,heab,heac,head⟩ := hc
  let B : Finset ℕ := {a,b,c,d}
  have hBA : B⊆A := by
    intro x hx
    simp only [B,mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have haP : a∉P := outside_of_same_tag hab (congrArg Prod.snd heab)
  have hbP : b∉P := outside_of_same_tag hab.symm (congrArg Prod.snd heab.symm)
  have hcP : c∉P := outside_of_same_tag hac.symm (congrArg Prod.snd heac.symm)
  have hdP : d∉P := outside_of_same_tag had.symm (congrArg Prod.snd head.symm)
  have hunit : ∀ x∈B, ∀ p∈P, ¬p ∣ x := by
    intro x hx p hp hdiv
    have hxP : x∉P := by
      simp only [B,mem_insert,mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have heq : x=p := ((hA x (hBA hx)).dvd_iff_eq (hP p hp).1.ne_one).mp hdiv
    exact hxP (heq ▸ hp)
  have hcolor : ∀ x∈B, color P a=color P x := by
    intro x hx
    simp only [B,mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rfl
    · exact heab
    · exact heac
    · exact head
  refine ⟨B,hBA,?_,?_,?_,?_⟩
  · simp [B,hab,hac,had,hbc,hbd,hcd]
  · exact ⟨a,by simp [B],b,by simp [B],c,by simp [B],d,by simp [B],
      hab,hac,had,hbc,hbd,hcd,he,rfl,rfl,rfl⟩
  · intro hs
    have hmem (x : ℕ) (hx : x∈B) : x^2∈(B.image (fun n => n^2) : Set ℕ) :=
      by
        change x^2∈B.image (fun n => n^2)
        exact mem_image.mpr ⟨x,hx,rfl⟩
    have haa : a∈B := by simp [B]
    have hbb : b∈B := by simp [B]
    have hcc : c∈B := by simp [B]
    have hdd : d∈B := by simp [B]
    rcases hs (a^2) (hmem a haa) (c^2) (hmem c hcc)
      (b^2) (hmem b hbb) (d^2) (hmem d hdd) he with hh | hh
    · exact hac (Nat.pow_left_injective (by decide : (2:ℕ)≠0) hh.1)
    · exact had (Nat.pow_left_injective (by decide : (2:ℕ)≠0) hh.1)
  · intro x hx y hy p hp
    apply localColor_avoids (hP p hp).1 (hP p hp).2 (hunit x hx p hp)
    have hh := congrArg Prod.fst ((hcolor x hx).symm.trans (hcolor y hy))
    exact congrFun hh ⟨p,hp⟩

/-- The same obstruction exists among primes, for every fixed finite
collection of excluded odd primes, at every sufficiently large bit length. -/
theorem eventually_prime_rough_collision (P : Finset ℕ)
    (hP : ∀ p∈P, p.Prime ∧ 2<p) :
    ∀ᶠ m : ℕ in atTop, ∃ B ⊆ sievePrimes (2^m), B.card=4 ∧ FourCollision B (fun _ => ()) ∧
      ¬IsSidon ((B.image (fun n => n^2)) : Set ℕ) ∧
      ∀ a∈B, ∀ b∈B, ∀ p∈P, ¬p ∣ a^2+b^2 := by
  classical
  let κ := (P → Bool) × Option P
  filter_upwards [eventually_prime_color_collision 1,
    eventually_ge_atTop (Fintype.card κ)] with m hm hk
  have hsize : Fintype.card κ≤(m+1)^1 := by simpa using (hk.trans (Nat.le_succ _))
  have hh := hm κ hsize (color P)
  exact rough_set_of_collision (sievePrimes (2^m)) P
    (fun _ ha => (mem_filter.mp ha).2.1) hP hh

end Erdos773.RoughPrimeCollisions
#print axioms Erdos773.RoughPrimeCollisions.rough_set_of_collision
#print axioms Erdos773.RoughPrimeCollisions.eventually_prime_rough_collision
