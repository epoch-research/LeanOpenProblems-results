import Submission.CapsetDoubling
import Submission.FreimanModelCheck
import Submission.FiniteKernelCase

/-! Reciprocal summability for integer sets whose finite subsets admit
characteristic-three Freiman models. This is a restricted case, not Erdős 3. -/
namespace Erdos3FreimanModelCase

open Finset
open scoped Pointwise
open Erdos3CapsetPolynomial Erdos3CapsetDoubling Erdos3FiniteKernelCase
set_option maxHeartbeats 1000000

lemma sumset_card_image_le {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {S : Finset ℕ} {B : Set G} {f : ℕ → G}
    (hf : IsAddFreimanHom 2 (S : Set ℕ) B f) :
    (S.image f + S.image f).card ≤ (S+S).card := by
  classical
  choose a ha b hb he using (fun x : (S+S) ↦ mem_add.mp x.property)
  let f₂ : ℕ → G := fun x ↦ if hx : x ∈ S+S then
    f (a ⟨x,hx⟩) + f (b ⟨x,hx⟩) else 0
  apply card_le_card_of_surjOn f₂
  intro y hy
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_add.mp hy
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hu
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hv
  have hij := add_mem_add hi hj
  refine ⟨i+j, hij, ?_⟩
  dsimp only [f₂]
  rw [dif_pos hij]
  exact hf.add_eq_add (ha ⟨i+j,hij⟩) (hb ⟨i+j,hij⟩) hi hj (he ⟨i+j,hij⟩)

def HasThreeModel (S : Finset ℕ) : Prop :=
  ∃ n : ℕ, ∃ f : ℕ → Vec n,
    IsAddFreimanIso 2 (S : Set ℕ) (f '' (S : Set ℕ)) f

/-- Models may have unbounded dimension, but the resulting doubling bound does not. -/
theorem modeled_card_le_doubling {S : Finset ℕ} (hS : HasThreeModel S) :
    S.card^43 ≤ 3^29 * (S+S).card^42 := by
  classical
  obtain ⟨n, f, hf⟩ := hS
  have hchar (x : Vec n) : 3 • x = 0 := by
    change (2+1) • x = 0
    simpa only [add_nsmul, two_nsmul, one_nsmul] using triple_self x
  have hfree := Erdos3FreimanModelCheck.source_threeAPFree_of_characteristic_three_iso hchar hf
  have hTfree : ThreeAPFree ((S.image f : Finset (Vec n)) : Set (Vec n)) := by
    simpa only [coe_image] using hfree.image hf Set.Subset.rfl
  have hc : (S.image f).card = S.card := card_image_of_injOn hf.bijOn.injOn
  have hd := sumset_card_image_le hf.isAddFreimanHom
  calc
    _ = (S.image f).card^43 := by rw [hc]
    _ ≤ 3^29 * (S.image f + S.image f).card^42 := capset_card_le_doubling _ hTfree
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd 42)

theorem modeled_card_in_range {S : Finset ℕ} {N : ℕ}
    (hS : HasThreeModel S) (hN : ∀ x ∈ S, x < N) :
    S.card^43 ≤ (3^29 * 2^42) * N^42 := by
  have hsum : S+S ⊆ range (2*N) := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hx
    have := hN a ha
    have := hN b hb
    simp only [mem_range]
    omega
  have hc : (S+S).card ≤ 2*N := (card_le_card hsum).trans_eq (card_range _)
  calc
    _ ≤ 3^29 * (S+S).card^42 := modeled_card_le_doubling hS
    _ ≤ 3^29 * (2*N)^42 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hc 42)
    _ = _ := by ring

/-- An integral polynomial saving in the counting function implies reciprocal summability. -/
lemma summable_of_polynomial_count_bound {A : Set ℕ} {C r : ℕ} (hC : 1 ≤ C)
    (hA : ∀ N : ℕ, count A N ^ (r+1) ≤ C * N^r) :
    Summable (fun a : A ↦ 1 / (a : ℝ)) := by
  let Q := (C+1)^(r+1)
  let R := C * (C+1)^r
  have hp : 0 < (C+1)^r := by positivity
  have hQR : Q = R + (C+1)^r := by dsimp [Q, R]; rw [pow_succ]; ring
  have hRQ : R ≤ Q-1 := by omega
  have hQ : 1 < Q := by
    have hh : 1 ≤ (C+1)^r := by omega
    dsimp [Q]
    rw [pow_succ]
    nlinarith
  apply summable_of_count_pow_bound hQ
  intro j
  by_cases hj : j = 0
  · subst j
    simpa using count_le A 1
  have hexp : 1 ≤ j*(r+1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hj (Nat.succ_ne_zero r))
  have hcoef : C ≤ C^(j*(r+1)) := by
    calc
      C = C^1 := by simp
      _ ≤ C^(j*(r+1)) := Nat.pow_le_pow_right (by omega) hexp
  have hpow : C * (Q^j)^r ≤ (R^j)^(r+1) := by
    have he : (r+1)*j*r = r*j*(r+1) := by ring
    simpa only [Q, R, mul_pow, ← pow_mul, he] using
      Nat.mul_le_mul_right ((C+1)^(r*j*(r+1))) hcoef
  have hc : count A (Q^j) ≤ R^j :=
    (Nat.pow_le_pow_iff_left (by omega : r+1 ≠ 0)).mp ((hA (Q^j)).trans hpow)
  exact hc.trans (Nat.pow_le_pow_left hRQ j)

/-- A finite-model condition, allowing a different dimension and map for every finite subset. -/
def FinitelyThreeModelable (A : Set ℕ) : Prop :=
  ∀ S : Finset ℕ, (S : Set ℕ) ⊆ A → HasThreeModel S

theorem summable_of_finitely_three_modelable {A : Set ℕ}
    (hA : FinitelyThreeModelable A) : Summable (fun a : A ↦ 1 / (a : ℝ)) := by
  classical
  apply summable_of_polynomial_count_bound (C := 3^29 * 2^42) (r := 42) (by norm_num)
  intro N
  let S := (range N).filter (fun n ↦ n ∈ A)
  have hsA : (S : Set ℕ) ⊆ A := by
    intro x hx
    change x ∈ (range N).filter (fun n ↦ n ∈ A) at hx
    exact (mem_filter.mp hx).2
  have hsN : ∀ x ∈ S, x < N := fun x hx ↦ mem_range.mp (mem_filter.mp hx).1
  simpa only [count_eq_card, S] using modeled_card_in_range (hA S hsA) hsN

/-- Divergence forces a finite obstruction to every characteristic-three Freiman model. -/
theorem divergence_finite_model_obstruction {A : Set ℕ}
    (hA : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) :
    ∃ S : Finset ℕ, (S : Set ℕ) ⊆ A ∧ ¬ HasThreeModel S := by
  by_contra! h
  exact hA (summable_of_finitely_three_modelable h)

#print axioms modeled_card_le_doubling
#print axioms summable_of_finitely_three_modelable
#print axioms divergence_finite_model_obstruction
end Erdos3FreimanModelCase
