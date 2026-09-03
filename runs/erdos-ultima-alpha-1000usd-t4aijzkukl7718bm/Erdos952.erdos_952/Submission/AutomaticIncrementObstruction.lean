import Submission.LinearOrbitObstruction

/-! An injective Gaussian-prime sequence cannot have a finite base-q kernel of
increments, for any q ≥ 2. This excludes automatic increment constructions;
it does not imply that arbitrary bounded-step increments have a finite kernel. -/
namespace Erdos952Investigation
namespace AutomaticIncrementObstruction

open LinearOrbitObstruction
set_option maxHeartbeats 0

lemma block_sum_of_kernel {ι G : Type*} [AddCommMonoid G]
    (q : ℕ) (u : ι → ℕ → G) (t : ι → Fin q → ι)
    (ht : ∀ i n (r : Fin q), u i (q*n+r.val) = u (t i r) n) :
    ∀ n i, (∑ j ∈ Finset.range (q*n), u i j) =
      ∑ r : Fin q, ∑ j ∈ Finset.range n, u (t i r) j := by
  intro n
  induction n with
  | zero => intro i; simp
  | succ n ih =>
    intro i
    rw [show q*(n+1) = q*n+q by ring,Finset.sum_range_add,ih]
    have hb : (∑ j ∈ Finset.range q, u i (q*n+j)) =
        ∑ r : Fin q, u (t i r) n := by
      rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => u i (q*n+j))]
      apply Finset.sum_congr rfl
      intro r hr
      exact ht i n r
    rw [hb]
    simp only [Finset.sum_range_succ,Finset.sum_add_distrib]

abbrev States (ι : Type*) := (ι → ℤ) × (ι → ℤ)

def transitionMap {ι : Type*} (q : ℕ) (t : ι → Fin q → ι) :
    States ι →ₗ[ℤ] States ι where
  toFun v := (fun i => ∑ r : Fin q, v.1 (t i r), fun i => ∑ r : Fin q, v.2 (t i r))
  map_add' v w := by ext i <;> simp [Finset.sum_add_distrib]
  map_smul' c v := by ext i <;> simp [Finset.mul_sum]

def observe {ι : Type*} (i : ι) : States ι →ₗ[ℤ] GaussianInt where
  toFun v := ⟨v.1 i,v.2 i⟩
  map_add' v w := by apply Zsqrtd.ext <;> rfl
  map_smul' c v := by apply Zsqrtd.ext <;> simp [zsmul_eq_mul]

/-- A finite family closed under base-q subsequences cannot describe all the
increments of an injective Gaussian-prime sequence. -/
theorem no_finite_kernel_representation {ι : Type*} [Fintype ι]
    (x : ℕ → GaussianInt) (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (q : ℕ) (hq : 2 ≤ q) (i₀ : ι) (u : ι → ℕ → GaussianInt)
    (t : ι → Fin q → ι)
    (ht : ∀ i n (r : Fin q), u i (q*n+r.val) = u (t i r) n) :
    ¬ ∀ n, x (n+1)-x n = u i₀ n := by
  intro hinc
  let state : ℕ → States ι := fun n =>
    (fun i => ∑ j ∈ Finset.range (q^n), (u i j).re,
      fun i => ∑ j ∈ Finset.range (q^n), (u i j).im)
  have hstate (n : ℕ) : state (n+1) = transitionMap q t (state n) := by
    apply Prod.ext <;> funext i
    · change (∑ j ∈ Finset.range (q^(n+1)), (u i j).re) =
        ∑ r : Fin q, ∑ j ∈ Finset.range (q^n), (u (t i r) j).re
      rw [pow_succ']
      exact block_sum_of_kernel q (fun i j => (u i j).re) t
        (fun i j r => congrArg Zsqrtd.re (ht i j r)) (q^n) i
    · change (∑ j ∈ Finset.range (q^(n+1)), (u i j).im) =
        ∑ r : Fin q, ∑ j ∈ Finset.range (q^n), (u (t i r) j).im
      rw [pow_succ']
      exact block_sum_of_kernel q (fun i j => (u i j).im) t
        (fun i j r => congrArg Zsqrtd.im (ht i j r)) (q^n) i
  apply no_geometric_index_linear_state x hx hp q hq (transitionMap q t)
    (observe i₀) state (x 0) hstate
  intro n
  have hr : (∑ j ∈ Finset.range (q^n), (u i₀ j).re) = (x (q^n)).re-(x 0).re := by
    rw [← Finset.sum_range_sub (fun j => (x j).re) (q^n)]
    apply Finset.sum_congr rfl
    intro j hj
    exact (congrArg Zsqrtd.re (hinc j)).symm
  have hi : (∑ j ∈ Finset.range (q^n), (u i₀ j).im) = (x (q^n)).im-(x 0).im := by
    rw [← Finset.sum_range_sub (fun j => (x j).im) (q^n)]
    apply Finset.sum_congr rfl
    intro j hj
    exact (congrArg Zsqrtd.im (hinc j)).symm
  apply Zsqrtd.ext <;> simp only [observe,state,LinearMap.coe_mk,AddHom.coe_mk,Zsqrtd.re_add,
    Zsqrtd.im_add] <;> omega

/-- The base-q kernel is the family of subsequences obtained by fixing a suffix
of base-q digits in the index. -/
def Kernel (q : ℕ) (f : ℕ → GaussianInt) : Set (ℕ → GaussianInt) :=
  {g | ∃ k r : ℕ, r < q^k ∧ g = fun n => f (q^k*n+r)}

lemma self_mem_kernel (q : ℕ) (f : ℕ → GaussianInt) : f ∈ Kernel q f := by
  refine ⟨0,0,by simp,?_⟩
  funext n
  simp

lemma kernel_subsequence {q : ℕ} {f g : ℕ → GaussianInt}
    (hg : g ∈ Kernel q f) (r : Fin q) : (fun n => g (q*n+r.val)) ∈ Kernel q f := by
  obtain ⟨k,s,hs,hg⟩ := hg
  refine ⟨k+1,q^k*r.val+s,?_,?_⟩
  · have hh := Nat.mul_le_mul_left (q^k) (show r.val+1 ≤ q by omega)
    rw [pow_succ]
    nlinarith
  · funext n
    rw [hg]
    change f (q^k*(q*n+r.val)+s) = f (q^(k+1)*n+(q^k*r.val+s))
    congr 1
    ring

/-- In particular the increment word of a hypothetical Gaussian-prime ray is
not q-automatic for any q ≥ 2, in the finite-kernel characterization. -/
theorem increment_kernel_infinite (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (q : ℕ) (hq : 2 ≤ q) :
    (Kernel q (fun n => x (n+1)-x n)).Infinite := by
  classical
  intro hfinite
  let f : ℕ → GaussianInt := fun n => x (n+1)-x n
  let I := Kernel q f
  letI : Fintype I := hfinite.fintype
  let i₀ : I := ⟨f,self_mem_kernel q f⟩
  let t : I → Fin q → I := fun i r =>
    ⟨fun n => i.val (q*n+r.val),kernel_subsequence i.property r⟩
  apply no_finite_kernel_representation x hx hp q hq i₀ (fun i : I => i.val) t
    (fun i n r => rfl)
  intro n
  rfl

#print axioms no_finite_kernel_representation
#print axioms increment_kernel_infinite

end AutomaticIncrementObstruction
end Erdos952Investigation
