import Submission.UniformRealStrip
import Submission.ModularSuccessorObstruction

/-! An obstruction for finite-state increment rules with finitely many affine
sign tests. This is a restriction on constructions of prime walks, not a
settlement of the unrestricted Gaussian moat problem. -/
namespace Erdos952Investigation
namespace PiecewiseModularObstruction
open RecurrentIncrementObstruction (residue)
open ModularSuccessorObstruction (increment)
set_option maxHeartbeats 0

lemma periodic_increments_in_strip (x : ℕ → GaussianInt)
    (N k : ℕ) (hk : 0 < k)
    (hperiod : ∀ n ≥ N, increment x (n+k) = increment x n) :
    ∃ d : GaussianInt, d ≠ 0 ∧ ∃ B : ℕ,
      ∀ n, |(d*(x n-x 0)).im| ≤ (B : ℤ) := by
  let v := x (N+k)-x N
  have hshift (m : ℕ) : x (N+m+k)-x (N+m) = v := by
    induction m with
    | zero => simp [v]
    | succ m ih =>
      have hh := hperiod (N+m) (by omega)
      dsimp only [increment] at hh
      have he : N+(m+1)+k = N+m+k+1 := by omega
      rw [he,show N+(m+1) = N+m+1 by omega]
      calc
        _ = (x (N+m+k+1)-x (N+m+k)) +
          (x (N+m+k)-x (N+m)) - (x (N+m+1)-x (N+m)) := by abel
        _ = v := by rw [hh,ih]; abel
  let d : GaussianInt := if v = 0 then 1 else star v
  have hd : d ≠ 0 := by
    dsimp [d]
    split_ifs with hv
    · exact one_ne_zero
    · exact star_ne_zero.mpr hv
  have hdv : (d*v).im = 0 := by
    dsimp [d]
    split_ifs with hv
    · simp [hv]
    · simp only [Zsqrtd.re_star,Zsqrtd.im_star]
      ring
  let q : ℕ → ℤ := fun n => (d*(x n-x 0)).im
  have hqperiod (n : ℕ) (hn : N ≤ n) : q (n+k) = q n := by
    have hh := hshift (n-N)
    rw [show N+(n-N) = n by omega] at hh
    have he : (d*(x (n+k)-x n)).im = 0 := by rw [hh,hdv]
    dsimp only [q]
    simp only [mul_sub,Zsqrtd.im_sub] at he ⊢
    omega
  let B := (Finset.range (N+k)).sup (fun n => (q n).natAbs)
  have hB (n : ℕ) : (q n).natAbs ≤ B := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < N+k
      · exact Finset.le_sup (f := fun n => (q n).natAbs) (Finset.mem_range.mpr hn)
      · have hsub : N ≤ n-k := by omega
        have he : q n = q (n-k) := by
          rw [← hqperiod (n-k) hsub]
          congr 1
          omega
        rw [he]
        exact ih (n-k) (by omega)
  refine ⟨d,hd,B,fun n => ?_⟩
  have hh : ((q n).natAbs : ℤ) ≤ B := by exact_mod_cast hB n
  simpa only [Int.natCast_natAbs,q] using hh

def generatedWalk {α : Type*} (t : α → α) (d : α → GaussianInt)
    (s : α) : ℕ → GaussianInt
  | 0 => 0
  | n+1 => generatedWalk t d s n+d ((t^[n]) s)

lemma generatedWalk_increment {α : Type*} (t : α → α) (d : α → GaussianInt)
    (s : α) (n : ℕ) : increment (generatedWalk t d s) n = d ((t^[n]) s) := by
  simp [increment,generatedWalk]

/-- Uniformly in the starting state and the translation, finite-state machines
cannot produce arbitrarily long injective Gaussian-prime segments. -/
theorem finite_state_prime_segment_bound {α : Type*} [Finite α]
    (t : α → α) (d : α → GaussianInt) (C : ℤ) :
    ∃ K : ℕ, ∀ s : α, ∀ x : ℕ → GaussianInt, ∀ L : ℕ,
      Set.InjOn x (Set.Iic L) →
      (∀ n ≤ L, Prime (x n)) →
      (∀ n < L, (increment x n).norm < C) →
      (∀ n < L, increment x n = d ((t^[n]) s)) → L < K := by
  classical
  letI := Fintype.ofFinite α
  have hfixed (s : α) : ∃ K : ℕ, ∀ x : ℕ → GaussianInt, ∀ L : ℕ,
      Set.InjOn x (Set.Iic L) → (∀ n ≤ L, Prime (x n)) →
      (∀ n < L, (increment x n).norm < C) →
      (∀ n < L, increment x n = d ((t^[n]) s)) → L < K := by
    let y := generatedWalk t d s
    obtain ⟨N,k,hk,hp⟩ := ModularSuccessorObstruction.finite_state_increments_periodic
      y (fun n => (t^[n]) s)
      (by
        intro i j he
        simpa only [Function.iterate_succ_apply'] using congrArg t he)
      (by
        intro i j he
        simp only [y,generatedWalk_increment,he])
    obtain ⟨a,ha,B,hB⟩ := periodic_increments_in_strip y N k hk hp
    obtain ⟨K,hK⟩ := UniformRationalStrip.uniform_prime_segment_bound a ha C B
    refine ⟨K,?_⟩
    intro x L hx hprime hstep hword
    have he (n : ℕ) (hn : n ≤ L) : x n-x 0 = y n-y 0 := by
      induction n with
      | zero => simp
      | succ n ih =>
        have hh := hword n (by omega)
        have hy := generatedWalk_increment t d s n
        change increment y n = d ((t^[n]) s) at hy
        have hd : increment x n = increment y n := hh.trans hy.symm
        dsimp only [increment] at hd
        calc
          _ = (x (n+1)-x n)+(x n-x 0) := by abel
          _ = (y (n+1)-y n)+(y n-y 0) := by rw [hd,ih (by omega)]
          _ = _ := by abel
    apply hK x L hx hprime hstep
    intro n hn
    rw [he n hn]
    exact hB n
  choose k hk using hfixed
  refine ⟨Finset.univ.sup k,?_⟩
  intro s x L hx hp hs hw
  exact (hk s x L hx hp hs hw).trans_le (Finset.le_sup (Finset.mem_univ s))

def affine (a b c : ℝ) (z : GaussianInt) : ℝ :=
  a*(z.re : ℝ)+b*(z.im : ℝ)+c

lemma affine_difference (a b c : ℝ) (z w : GaussianInt) :
    affine a b c z-affine a b c w =
      a*((z-w).re : ℝ)+b*((z-w).im : ℝ) := by
  simp only [affine,Zsqrtd.re_sub,Zsqrtd.im_sub,Int.cast_sub]
  ring

lemma affine_step_bound (a b c : ℝ) (hab : max |a| |b| = 1)
    (C : ℤ) {z w : GaussianInt} (hs : (w-z).norm < C) :
    |affine a b c w-affine a b c z| ≤ 2*((max C 1 : ℤ) : ℝ) := by
  have hre : |(w-z).re| ≤ max C 1 :=
    (abs_re_le_gaussian_norm _).trans (hs.le.trans (le_max_left _ _))
  have him : |(w-z).im| ≤ max C 1 :=
    (ModularSuccessorObstruction.abs_im_le_norm _).trans (hs.le.trans (le_max_left _ _))
  have hre' : |((w-z).re : ℝ)| ≤ ((max C 1 : ℤ) : ℝ) := by exact_mod_cast hre
  have him' : |((w-z).im : ℝ)| ≤ ((max C 1 : ℤ) : ℝ) := by exact_mod_cast him
  have ha := (max_le_iff.mp hab.le).1
  have hb := (max_le_iff.mp hab.le).2
  have hr := mul_le_mul_of_nonneg_right ha (abs_nonneg ((w-z).re : ℝ))
  have hi := mul_le_mul_of_nonneg_right hb (abs_nonneg ((w-z).im : ℝ))
  rw [affine_difference]
  have ht := abs_add_le (a*((w-z).re : ℝ)) (b*((w-z).im : ℝ))
  rw [abs_mul,abs_mul] at ht
  nlinarith

lemma accumulated_step_bound (f : ℕ → ℝ) (D : ℝ)
    (hs : ∀ n, |f (n+1)-f n| ≤ D) (N j : ℕ) :
    |f (N+j)-f N| ≤ (j : ℝ)*D := by
  induction j with
  | zero => simp
  | succ j ih =>
    have ht := abs_sub_le (f (N+j+1)) (f (N+j)) (f N)
    have hh := hs (N+j)
    rw [show N+(j+1) = N+j+1 by omega]
    push_cast
    nlinarith

/-- Uniform escape from each fixed strip and bounded steps allow arbitrarily
long blocks outside any finite family of fixed strips simultaneously. -/
lemma finite_family_clear_block {ι : Type*} (f : ι → ℕ → ℝ) (D : ℝ)
    (hD : 0 ≤ D) (hs : ∀ i n, |f i (n+1)-f i n| ≤ D)
    (he : ∀ i B, ∃ K : ℕ, ∀ N, ∃ j ≤ K, B < |f i (N+j)-f i N|)
    (S : Finset ι) (B : ℝ) (hB : 0 ≤ B) (L N₀ : ℕ) :
    ∃ N ≥ N₀, ∀ j ≤ L, ∀ i ∈ S, B < |f i (N+j)| := by
  classical
  induction S using Finset.induction_on generalizing L N₀ with
  | empty => exact ⟨N₀,le_rfl,by simp⟩
  | @insert i S hi ih =>
    let W := B+(L : ℝ)*D
    have hW : 0 ≤ W := by dsimp [W]; positivity
    obtain ⟨K,hK⟩ := he i (2*W)
    obtain ⟨N,hN,hclear⟩ := ih (K+L) N₀
    obtain ⟨j,hj,hdiff⟩ := hK N
    have hlarge : W < |f i N| ∨ W < |f i (N+j)| := by
      by_contra! hn
      have ht := abs_sub_le (f i (N+j)) 0 (f i N)
      simp only [sub_zero,zero_sub,abs_neg] at ht
      linarith
    have hchoose : ∃ b ≤ K, W < |f i (N+b)| := by
      rcases hlarge with h | h
      · exact ⟨0,by omega,by simpa using h⟩
      · exact ⟨j,hj,h⟩
    obtain ⟨b,hb,hlarge⟩ := hchoose
    refine ⟨N+b,by omega,?_⟩
    intro t ht q hq
    rcases Finset.mem_insert.mp hq with heq | hq
    · subst q
      have hdelta := accumulated_step_bound (f i) D (hs i) (N+b) t
      have ht' : (t : ℝ) ≤ L := by exact_mod_cast ht
      have hm := mul_le_mul_of_nonneg_right ht' hD
      have hh := abs_sub_le (f i (N+b)) (f i (N+b+t)) 0
      simp only [sub_zero] at hh
      rw [abs_sub_comm (f i (N+b)) (f i (N+b+t))] at hh
      dsimp only [W] at hlarge
      nlinarith
    · simpa only [Nat.add_assoc] using hclear (b+t) (by omega) q hq

/-- An arbitrary hypothetical prime ray has arbitrarily long segments which
avoid a prescribed finite collection of translated real strips. -/
theorem prime_ray_avoids_finite_strips {ι : Type*} [Finite ι]
    (a b c : ι → ℝ) (hab : ∀ i, max |a i| |b i| = 1)
    (x : ℕ → GaussianInt) (C : ℤ) (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (increment x n).norm < C)
    (B : ℝ) (hB : 0 ≤ B) (L N₀ : ℕ) :
    ∃ N ≥ N₀, ∀ j ≤ L, ∀ i, B < |affine (a i) (b i) (c i) (x (N+j))| := by
  classical
  letI := Fintype.ofFinite ι
  let f : ι → ℕ → ℝ := fun i n => affine (a i) (b i) (c i) (x n)
  let D : ℝ := 2*((max C 1 : ℤ) : ℝ)
  have hD : 0 ≤ D := by
    have hh : (0 : ℤ) ≤ max C 1 := (by norm_num : (0 : ℤ) ≤ 1).trans (le_max_right _ _)
    have hh' : (0 : ℝ) ≤ ((max C 1 : ℤ) : ℝ) := by exact_mod_cast hh
    dsimp [D]
    positivity
  have hs (i : ι) (n : ℕ) : |f i (n+1)-f i n| ≤ D :=
    affine_step_bound (a i) (b i) (c i) (hab i) C (h n).2
  have he (i : ι) (W : ℝ) : ∃ K : ℕ, ∀ N, ∃ j ≤ K,
      W < |f i (N+j)-f i N| := by
    obtain ⟨K,hK⟩ := UniformRealStrip.uniform_escape_all_directions C W
    refine ⟨K,?_⟩
    intro N
    obtain ⟨j,hj,hd⟩ := hK x hx h N (a i) (b i) (hab i)
    exact ⟨j,hj,by simpa only [f,affine_difference] using hd⟩
  obtain ⟨N,hN,hclear⟩ := finite_family_clear_block f D hD hs he
    Finset.univ B hB L N₀
  exact ⟨N,hN,fun j hj i => hclear j hj i (Finset.mem_univ i)⟩

noncomputable def signs {ι : Type*} (a b c : ι → ℝ) (z : GaussianInt) : ι → Bool := by
  classical
  exact fun i => decide (0 ≤ affine (a i) (b i) (c i) z)

/-- No bounded-step injective prime walk has its increment determined by
coordinate congruences and a fixed finite collection of affine sign tests. -/
theorem no_piecewise_modular_increment_rule {ι : Type*} [Finite ι]
    (a b c : ι → ℝ) (hab : ∀ i, max |a i| |b i| = 1)
    (M : ℕ) (hM : 0 < M) (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (increment x n).norm < C) :
    ¬ ∀ i j, residue M (x i) = residue M (x j) →
      signs a b c (x i) = signs a b c (x j) → increment x i = increment x j := by
  classical
  intro hdet
  letI : NeZero M := ⟨hM.ne'⟩
  let A := (ZMod M × ZMod M) × (ι → Bool)
  let state : GaussianInt → A := fun z => (residue M z,signs a b c z)
  let d : A → GaussianInt := fun s =>
    if hs : ∃ n, state (x n) = s then increment x (Classical.choose hs) else 0
  have hd (n : ℕ) : d (state (x n)) = increment x n := by
    dsimp only [d]
    split_ifs with hs
    · have he := Classical.choose_spec hs
      exact hdet (Classical.choose hs) n (congrArg Prod.fst he) (congrArg Prod.snd he)
    · exact (hs ⟨n,rfl⟩).elim
  let T : A → A := fun s => (s.1+residue M (d s),s.2)
  obtain ⟨K,hK⟩ := finite_state_prime_segment_bound T d C
  let D : ℝ := 2*((max C 1 : ℤ) : ℝ)
  have hD : 0 ≤ D := by
    have hh : (0 : ℤ) ≤ max C 1 := (by norm_num : (0 : ℤ) ≤ 1).trans (le_max_right _ _)
    have hh' : (0 : ℝ) ≤ ((max C 1 : ℤ) : ℝ) := by exact_mod_cast hh
    dsimp [D]
    positivity
  obtain ⟨N,_,hclear⟩ := prime_ray_avoids_finite_strips a b c hab x C hx h D hD K 0
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
  have hnext (n : ℕ) (hn : n < K) :
      state (x (N+(n+1))) = T (state (x (N+n))) := by
    apply Prod.ext
    · change residue M (x (N+(n+1))) =
        residue M (x (N+n))+residue M (d (state (x (N+n))))
      rw [hd]
      simp only [increment,map_sub,Nat.add_assoc]
      abel
    · exact hsign n hn
  have hstate (n : ℕ) (hn : n ≤ K) :
      state (x (N+n)) = (T^[n]) (state (x N)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hnext n (by omega),ih (by omega),Function.iterate_succ_apply']
  have hbad : K < K := by
    apply hK (state (x N)) (fun n => x (N+n)) K
    · intro i _ j _ he
      exact Nat.add_left_cancel (hx he)
    · intro n _
      exact (h (N+n)).1
    · intro n _
      simpa only [increment,Nat.add_assoc] using (h (N+n)).2
    · intro n hn
      have he := hd (N+n)
      rw [hstate n hn.le] at he
      simpa only [increment,Nat.add_assoc] using he.symm
  omega

/-- Affine sign tests do not repair a modular successor rule. This assumes
bounded steps only along the orbit, and does not assume global prime preservation. -/
theorem no_piecewise_modular_prime_orbit {ι : Type*} [Finite ι]
    (a b c : ι → ℝ) (hab : ∀ i, max |a i| |b i| = 1)
    (M : ℕ) (hM : 0 < M) (F : GaussianInt → GaussianInt)
    (hF : ∀ z w, residue M z = residue M w → signs a b c z = signs a b c w →
      F z-z = F w-w)
    (x : ℕ → GaussianInt) (C : ℤ) (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (increment x n).norm < C)
    (horbit : ∀ n, x (n+1) = F (x n)) : False := by
  apply no_piecewise_modular_increment_rule a b c hab M hM x C hx h
  intro i j hres hsign
  simpa only [increment,horbit] using hF (x i) (x j) hres hsign

/-- Every tail has positions indistinguishable by the prescribed congruence
and affine tests but with different next increments. -/
theorem piecewise_modular_ambiguity_on_every_tail {ι : Type*} [Finite ι]
    (a b c : ι → ℝ) (hab : ∀ i, max |a i| |b i| = 1)
    (M : ℕ) (hM : 0 < M) (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (increment x n).norm < C) (N : ℕ) :
    ∃ i ≥ N, ∃ j ≥ N, residue M (x i) = residue M (x j) ∧
      signs a b c (x i) = signs a b c (x j) ∧ increment x i ≠ increment x j := by
  have hy : Function.Injective (fun n => x (N+n)) := by
    intro i j he
    exact Nat.add_left_cancel (hx he)
  have hh := no_piecewise_modular_increment_rule a b c hab M hM (fun n => x (N+n))
    C hy (fun n => by simpa only [increment,Nat.add_assoc] using h (N+n))
  push_neg at hh
  obtain ⟨i,j,hres,hsign,hne⟩ := hh
  refine ⟨N+i,by omega,N+j,by omega,hres,hsign,?_⟩
  simpa only [increment,Nat.add_assoc] using hne

#print axioms no_piecewise_modular_prime_orbit
#print axioms piecewise_modular_ambiguity_on_every_tail
#print axioms prime_ray_avoids_finite_strips
#print axioms periodic_increments_in_strip
#print axioms finite_state_prime_segment_bound
end PiecewiseModularObstruction
end Erdos952Investigation
