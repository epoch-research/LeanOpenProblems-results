import Submission.QuadraticRotationPairs

/-!
A finite, relation-preserving integer specialization of the formal rotation
model. The specialization is chosen after all finitely many nonzero pair
relations are known; no blanket small-base specialization is claimed, and
no quantitative height bound or asymptotic construction is inferred.
-/
namespace Erdos773.QuadraticRotationTrade
open Finset MvPolynomial
set_option maxHeartbeats 2500000
noncomputable section

lemma avoid_finite_in_box {n : ℕ} (P : Finset (MvPolynomial (Fin n) ℚ))
    (hP : ∀ p ∈ P, p ≠ 0) :
    ∃ x : Fin n → ℚ, (∀ i, 1 < x i ∧ x i < 4/3) ∧ ∀ p ∈ P, eval x p ≠ 0 := by
  have hp : (∏ p ∈ P, p) ≠ 0 := prod_ne_zero_iff.mpr hP
  have hex : ∃ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Ioo (1:ℚ) (4/3)),
      eval x (∏ p ∈ P, p) ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hp
    apply MvPolynomial.funext_set (fun _ : Fin n => Set.Ioo (1:ℚ) (4/3))
      (fun _ => Set.Ioo_infinite (by norm_num))
    intro x hx
    simpa using hn x hx
  obtain ⟨x, hx, hp⟩ := hex
  refine ⟨x, fun i => hx i (Set.mem_univ _), ?_⟩
  simpa only [map_prod, prod_ne_zero_iff] using hp

lemma finite_pair_specialization {n : ℕ} {ι : Type*} [Fintype ι]
    (P : ι → MvPolynomial (Fin n) ℚ) :
    ∃ x : Fin n → ℚ, (∀ i, 1 < x i ∧ x i < 4/3) ∧
      ∀ a b c d, eval x (P a+P b)=eval x (P c+P d) ↔ P a+P b=P c+P d := by
  classical
  let diff (t : ι × ι × ι × ι) := P t.1+P t.2.1-(P t.2.2.1+P t.2.2.2)
  let S := (univ.image diff).erase 0
  obtain ⟨x,hx,hS⟩ := avoid_finite_in_box S (fun _ h => (mem_erase.mp h).1)
  refine ⟨x,hx,fun a b c d => ⟨?_,fun h => congrArg (eval x) h⟩⟩
  intro h
  by_contra hn
  have hm : diff (a,b,c,d) ∈ S :=
    mem_erase.mpr ⟨sub_ne_zero.mpr hn, mem_image.mpr ⟨(a,b,c,d),mem_univ _,rfl⟩⟩
  apply hS _ hm
  simp only [diff,map_sub,h,sub_self]

lemma clear_positive_denominators {ι : Type*} [Fintype ι] (q : ι → ℚ)
    (hq : ∀ i, 0 < q i) :
    ∃ D : ℕ, 0 < D ∧ ∃ f : ι → ℕ, ∀ i, (f i : ℚ)=D*q i := by
  classical
  let D := ∏ i, (q i).den
  have hD : 0 < D := prod_pos (fun i _ => (q i).den_pos)
  let f : ι → ℕ := fun i => (q i).num.toNat*(D/(q i).den)
  refine ⟨D,hD,f,fun i => ?_⟩
  have hd : (q i).den ∣ D := dvd_prod_of_mem (fun i => (q i).den) (mem_univ i)
  obtain ⟨k,hk⟩ := hd
  have hn : (((q i).num.toNat : ℕ) : ℚ)=(q i).num := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hq i).le)
  dsimp only [f]
  rw [hk, Nat.mul_div_cancel_left k (q i).den_pos, Nat.cast_mul, hn, Nat.cast_mul]
  rw [mul_comm ((q i).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
  ring

/-- The finite model is positive and injective and preserves ALL square-pair
    relations in both directions. There is deliberately no height estimate. -/
theorem exists_integer_model (n : ℕ) :
    ∃ f : Root n → ℕ, (∀ u, 0 < f u) ∧ Function.Injective f ∧
      ∀ u v w z, f u^2+f v^2=f w^2+f z^2 ↔ value u+value v=value w+value z := by
  obtain ⟨x,hx,hpair⟩ := finite_pair_specialization (value (n := n))
  let q : Root n → ℚ := fun u => eval x (poly u)
  have hq : ∀ u, 0 < q u := by
    intro u
    cases u with
    | core a => dsimp [q,poly]; simp only [map_mul, map_ofNat, eval_X]; linarith [(hx a).1]
    | plus e => dsimp [q,poly]; simp only [map_add,map_mul,map_ofNat,eval_X]; linarith [(hx e.val.1).1,(hx e.val.2).1]
    | minus e => dsimp [q,poly]; simp only [map_sub,map_mul,map_ofNat,eval_X]; linarith [(hx e.val.1).1,(hx e.val.2).2]
  obtain ⟨D,hD,f,hf⟩ := clear_positive_denominators q hq
  have hDq : (0:ℚ) < D := by exact_mod_cast hD
  have hfpos : ∀ u, 0 < f u := by
    intro u
    have hh : (0:ℚ) < f u := by rw [hf]; exact mul_pos hDq (hq u)
    exact_mod_cast hh
  have hs (u v : Root n) : ((f u^2+f v^2 : ℕ) : ℚ) = D^2*eval x (value u+value v) := by
    push_cast
    rw [hf,hf]
    simp only [value,map_add,map_pow]
    dsimp only [q]
    ring
  have hequiv (u v w z : Root n) :
      f u^2+f v^2=f w^2+f z^2 ↔ value u+value v=value w+value z := by
    rw [← hpair u v w z]
    constructor
    · intro h
      have hc : ((f u^2+f v^2 : ℕ) : ℚ)=((f w^2+f z^2 : ℕ) : ℚ) := by rw [h]
      rw [hs,hs] at hc
      exact mul_left_cancel₀ (pow_ne_zero _ hDq.ne') hc
    · intro h
      have hc : ((f u^2+f v^2 : ℕ) : ℚ)=((f w^2+f z^2 : ℕ) : ℚ) := by rw [hs,hs,h]
      exact_mod_cast hc
  refine ⟨f,hfpos,?_,hequiv⟩
  intro u v huv
  have hh := (hequiv u u v v).mp (by rw [huv])
  apply value_injective
  apply mul_left_cancel₀ (show (2 : MvPolynomial (Fin n) ℚ) ≠ 0 by norm_num)
  simpa only [two_mul] using hh

#print axioms avoid_finite_in_box
#print axioms finite_pair_specialization
#print axioms clear_positive_denominators
#print axioms exists_integer_model
end
end Erdos773.QuadraticRotationTrade
