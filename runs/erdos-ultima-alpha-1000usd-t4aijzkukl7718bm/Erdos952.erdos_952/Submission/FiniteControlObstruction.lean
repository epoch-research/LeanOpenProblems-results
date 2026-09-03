import Submission.PiecewiseModularObstruction

/-! Finite internal memory does not repair the piecewise-modular construction
of a bounded-step prime ray. This excludes a specified class of controllers;
an arbitrary prime ray is not assumed to have such a controller. -/
namespace Erdos952Investigation
namespace FiniteControlObstruction
open PiecewiseModularObstruction
open RecurrentIncrementObstruction (residue)
open ModularSuccessorObstruction (increment)
set_option maxHeartbeats 0

lemma arbitrarily_long_constant_sign_blocks {ι : Type*} [Finite ι]
    (a b c : ι → ℝ) (hab : ∀ i, max |a i| |b i| = 1)
    (x : ℕ → GaussianInt) (C : ℤ) (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (increment x n).norm < C) (K N₀ : ℕ) :
    ∃ N ≥ N₀, ∀ n ≤ K, signs a b c (x (N+n)) = signs a b c (x N) := by
  classical
  let D : ℝ := 2*((max C 1 : ℤ) : ℝ)
  have hD : 0 ≤ D := by
    have hh : (0 : ℤ) ≤ max C 1 := (by norm_num : (0 : ℤ) ≤ 1).trans (le_max_right _ _)
    have hh' : (0 : ℝ) ≤ ((max C 1 : ℤ) : ℝ) := by exact_mod_cast hh
    dsimp [D]
    positivity
  obtain ⟨N,hN,hclear⟩ := prime_ray_avoids_finite_strips a b c hab x C hx h D hD K N₀
  have hsign (n : ℕ) (hn : n < K) :
      signs a b c (x (N+(n+1))) = signs a b c (x (N+n)) := by
    funext i
    have hfar := hclear n hn.le i
    have hstep := affine_step_bound (a i) (b i) (c i) (hab i) C (h (N+n)).2
    change |affine (a i) (b i) (c i) (x (N+n+1))-
      affine (a i) (b i) (c i) (x (N+n))| ≤ D at hstep
    rw [show N+n+1 = N+(n+1) by omega] at hstep
    have hb := abs_le.mp hstep
    by_cases hn0 : 0 ≤ affine (a i) (b i) (c i) (x (N+n))
    · rw [abs_of_nonneg hn0] at hfar
      have hn1 : 0 ≤ affine (a i) (b i) (c i) (x (N+(n+1))) := by linarith
      simp only [signs,hn0,hn1,decide_true]
    · have hn0' : affine (a i) (b i) (c i) (x (N+n)) < 0 := lt_of_not_ge hn0
      rw [abs_of_neg hn0'] at hfar
      have hn1 : ¬ 0 ≤ affine (a i) (b i) (c i) (x (N+(n+1))) := by linarith
      simp only [signs,hn0,hn1,decide_false]
  refine ⟨N,hN,?_⟩
  intro n hn
  induction n with
  | zero => simp
  | succ n ih => exact (hsign n (by omega)).trans (ih (by omega))

abbrev Observation (α ι : Type*) (M : ℕ) :=
  α × (ZMod M × ZMod M) × (ι → Bool)

/-- A deterministic controller may use finite memory, coordinate congruences,
and finitely many affine sign tests. It still cannot generate a prime ray.
No bound on outputs at unvisited observations is required. -/
theorem no_finite_control_prime_walk {α ι : Type*} [Finite α] [Finite ι]
    (a b c : ι → ℝ) (hab : ∀ i, max |a i| |b i| = 1)
    (M : ℕ) (hM : 0 < M)
    (output : Observation α ι M → GaussianInt)
    (transition : Observation α ι M → α)
    (x : ℕ → GaussianInt) (q : ℕ → α) (C : ℤ)
    (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (increment x n).norm < C)
    (ho : ∀ n, increment x n = output (q n,residue M (x n),signs a b c (x n)))
    (ht : ∀ n, q (n+1) = transition (q n,residue M (x n),signs a b c (x n))) :
    False := by
  letI : NeZero M := ⟨hM.ne'⟩
  let state : ℕ → Observation α ι M :=
    fun n => (q n,residue M (x n),signs a b c (x n))
  let T : Observation α ι M → Observation α ι M :=
    fun s => (transition s,s.2.1+residue M (output s),s.2.2)
  obtain ⟨K,hK⟩ := finite_state_prime_segment_bound T output C
  obtain ⟨N,_,hsign⟩ := arbitrarily_long_constant_sign_blocks a b c hab x C hx h K 0
  have hnext (n : ℕ) (hn : n < K) : state (N+(n+1)) = T (state (N+n)) := by
    apply Prod.ext
    · change q (N+(n+1)) = transition (q (N+n),residue M (x (N+n)),signs a b c (x (N+n)))
      simpa only [Nat.add_assoc] using ht (N+n)
    · apply Prod.ext
      · change residue M (x (N+(n+1))) = residue M (x (N+n))+
          residue M (output (q (N+n),residue M (x (N+n)),signs a b c (x (N+n))))
        rw [← ho]
        simp only [increment,map_sub,Nat.add_assoc]
        abel
      · exact (hsign (n+1) (by omega)).trans (hsign n hn.le).symm
  have hstate (n : ℕ) (hn : n ≤ K) : state (N+n) = (T^[n]) (state N) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hnext n (by omega),ih (by omega),Function.iterate_succ_apply']
  have hbad : K < K := by
    apply hK (state N) (fun n => x (N+n)) K
    · intro i _ j _ he
      exact Nat.add_left_cancel (hx he)
    · intro n _
      exact (h (N+n)).1
    · intro n _
      simpa only [increment,Nat.add_assoc] using (h (N+n)).2
    · intro n hn
      have he : increment x (N+n) = output (state (N+n)) := ho (N+n)
      rw [hstate n hn.le] at he
      simpa only [increment,Nat.add_assoc] using he
  omega

/-- The obstruction can be expressed without specifying a controller: the
observed finite state cannot determine both the increment and next memory. -/
theorem no_finite_control_determinism {α ι : Type*} [Finite α] [Finite ι]
    (a b c : ι → ℝ) (hab : ∀ i, max |a i| |b i| = 1)
    (M : ℕ) (hM : 0 < M) (x : ℕ → GaussianInt) (q : ℕ → α) (C : ℤ)
    (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (increment x n).norm < C) :
    ¬ ∀ i j, q i = q j → residue M (x i) = residue M (x j) →
      signs a b c (x i) = signs a b c (x j) →
      increment x i = increment x j ∧ q (i+1) = q (j+1) := by
  classical
  intro hdet
  let state : ℕ → Observation α ι M :=
    fun n => (q n,residue M (x n),signs a b c (x n))
  let next : Observation α ι M → GaussianInt × α := fun s =>
    if hs : ∃ n, state n = s then
      (increment x (Classical.choose hs),q (Classical.choose hs+1)) else (0,q 0)
  have hn (n : ℕ) : next (state n) = (increment x n,q (n+1)) := by
    dsimp only [next]
    split_ifs with hs
    · have he := Classical.choose_spec hs
      have hh := hdet (Classical.choose hs) n (congrArg Prod.fst he)
        (congrArg (fun s : Observation α ι M => s.2.1) he)
        (congrArg (fun s : Observation α ι M => s.2.2) he)
      exact Prod.ext hh.1 hh.2
    · exact (hs ⟨n,rfl⟩).elim
  apply no_finite_control_prime_walk a b c hab M hM
    (fun s => (next s).1) (fun s => (next s).2) x q C hx h
  · intro n
    exact (congrArg Prod.fst (hn n)).symm
  · intro n
    exact (congrArg Prod.snd (hn n)).symm

#print axioms arbitrarily_long_constant_sign_blocks
#print axioms no_finite_control_prime_walk
#print axioms no_finite_control_determinism
end FiniteControlObstruction
end Erdos952Investigation
