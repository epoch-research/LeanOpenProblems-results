import Submission.RecurrentIncrementObstruction

/-! An arithmetic obstruction to affine linear recurrences of Gaussian primes.
No bound on the step sizes is needed. This does not assert that an arbitrary
bounded-step path satisfies such a recurrence. -/
namespace Erdos952Investigation
namespace LinearRecurrenceObstruction

open RecurrentIncrementObstruction
set_option maxHeartbeats 0

/-- Backward uniqueness in a finite state space forces arbitrarily late
returns to the initial state. No explicit forward transition is needed. -/
lemma finite_backward_unique_returns {A : Type*} [Finite A] (f : ℕ → A)
    (hback : ∀ i j, f (i+1) = f (j+1) → f i = f j) :
    ∀ N : ℕ, ∃ n ≥ N, f n = f 0 := by
  have hpull : ∀ s i j : ℕ, f (i+s) = f (j+s) → f i = f j := by
    intro s
    induction s with
    | zero => intro i j h; simpa using h
    | succ s ih =>
      intro i j h
      apply ih i j
      apply hback (i+s) (j+s)
      simpa only [Nat.add_assoc] using h
  intro N
  obtain ⟨i,j,hij,he⟩ := Finite.exists_ne_map_eq_of_infinite (fun n => f ((N+1)*n))
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm he.symm (by omega)
  let d := (N+1)*(j-i)
  have hmul : (N+1)*i ≤ (N+1)*j := Nat.mul_le_mul_left _ hlt.le
  have hd : N ≤ d := (Nat.le_succ N).trans (Nat.le_mul_of_pos_right (N+1) (by omega))
  refine ⟨d,hd,?_⟩
  apply hpull ((N+1)*i) d 0
  simpa only [d,Nat.mul_sub,Nat.sub_add_cancel hmul,Nat.zero_add] using he.symm

lemma finite_recurrence_returns {G : Type*} [AddCommGroup G] [Finite G]
    (k : ℕ) (a : Fin (k+1) → ℤ)
    (ha : Function.Injective (fun v : G => a 0 • v)) (b : G)
    (x : ℕ → G)
    (hrec : ∀ n, x (n+k+1) = b+∑ i : Fin (k+1), a i • x (n+i.val)) :
    ∀ N : ℕ, ∃ n ≥ N, x n = x 0 := by
  let state : ℕ → (Fin (k+1) → G) := fun n i => x (n+i.val)
  have hback (n m : ℕ) (he : state (n+1) = state (m+1)) : state n = state m := by
    have he' (i : Fin (k+1)) : x (n+1+i.val) = x (m+1+i.val) := congrFun he i
    have hlast : x (n+k+1) = x (m+k+1) := by
      simpa only [Fin.val_last,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using he' (Fin.last k)
    have hsum : (∑ i : Fin (k+1), a i • x (n+i.val)) =
        ∑ i : Fin (k+1), a i • x (m+i.val) :=
      add_left_cancel ((hrec n).symm.trans (hlast.trans (hrec m)))
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ] at hsum
    have htail : (∑ i : Fin k, a i.succ • x (n+i.succ.val)) =
        ∑ i : Fin k, a i.succ • x (m+i.succ.val) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      simpa only [Fin.val_succ,Fin.val_castSucc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
        using he' i.castSucc
    rw [htail] at hsum
    have hzero : x n = x m := by
      apply ha
      simpa using add_right_cancel hsum
    funext i
    induction i using Fin.cases with
    | zero => simpa [state] using hzero
    | succ i =>
      simpa only [state,Fin.val_succ,Fin.val_castSucc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
        using he' i.castSucc
  intro N
  obtain ⟨n,hn,he⟩ := finite_backward_unique_returns state hback N
  exact ⟨n,hn,by simpa [state] using congrFun he 0⟩

/-- An injective sequence of Gaussian primes cannot eventually satisfy an
integer affine linear recurrence whose trailing coefficient is nonzero. -/
theorem no_eventually_affine_linear_recurrence (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (k N : ℕ) (a : Fin (k+1) → ℤ) (ha : a 0 ≠ 0) (b : GaussianInt) :
    ¬ ∀ n ≥ N, x (n+k+1) = b+∑ i : Fin (k+1), (a i : GaussianInt)*x (n+i.val) := by
  intro hrec
  obtain ⟨T₀,hT₀⟩ := injective_escapes_norm x hx ((a 0)^2)
  let T := max N T₀
  let y : ℕ → GaussianInt := fun n => x (T+n)
  have hy : Function.Injective y := by
    intro i j he
    exact Nat.add_left_cancel (hx he)
  have hyp (n : ℕ) : Prime (y n) := hp (T+n)
  have hylarge : (a 0)^2 < (y 0).norm := by
    exact hT₀ (T+0) (by dsimp [T]; omega)
  have hyrec (n : ℕ) : y (n+k+1) = b+∑ i : Fin (k+1), (a i : GaussianInt)*y (n+i.val) := by
    simpa only [y,Nat.add_assoc] using hrec (T+n) (by dsimp [T]; omega)
  have hn1 : (y 0).norm.natAbs ≠ 1 := by
    intro he
    have hnorm : (y 0).norm = 1 := by
      have ht := congrArg (fun n : ℕ => (n : ℤ)) he
      simpa using ht
    exact (hyp 0).not_unit
      ((Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) (y 0)).mp hnorm)
  obtain ⟨p,hprime,hpdiv⟩ := Nat.exists_prime_and_dvd hn1
  letI : Fact p.Prime := ⟨hprime⟩
  have hdiv : (p : ℤ) ∣ (y 0).norm := Int.natCast_dvd.mpr hpdiv
  have ha0 : (a 0 : ZMod p) ≠ 0 := by
    intro he
    have hd : (p : ℤ) ∣ a 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp he
    have hle := Int.le_of_dvd (abs_pos.mpr ha) ((dvd_abs _ _).mpr hd)
    have hsmall := prime_norm_divisor_bound (hyp 0) hprime hdiv
    have hp0 : (0 : ℤ) ≤ p := Int.natCast_nonneg p
    nlinarith [sq_abs (a 0)]
  have hai : Function.Injective (fun v : ZMod p × ZMod p => a 0 • v) := by
    intro u v he
    apply Prod.ext
    · have hh := congrArg Prod.fst he
      change a 0 • u.1 = a 0 • v.1 at hh
      simp only [zsmul_eq_mul] at hh
      exact mul_left_cancel₀ ha0 hh
    · have hh := congrArg Prod.snd he
      change a 0 • u.2 = a 0 • v.2 at hh
      simp only [zsmul_eq_mul] at hh
      exact mul_left_cancel₀ ha0 hh
  have hmul (c : ℤ) (z : GaussianInt) :
      residue p ((c : GaussianInt)*z) = c • residue p z := by
    rw [← zsmul_eq_mul,map_zsmul]
  have hrecmod (n : ℕ) : residue p (y (n+k+1)) =
      residue p b+∑ i : Fin (k+1), a i • residue p (y (n+i.val)) := by
    have hh := congrArg (residue p) (hyrec n)
    simpa only [map_add,map_sum,hmul] using hh
  obtain ⟨M,hM⟩ := injective_escapes_norm y hy ((p : ℤ)^2)
  obtain ⟨n,hn,he⟩ := finite_recurrence_returns k a hai (residue p b)
    (fun n => residue p (y n)) hrecmod M
  have he' := norm_cast_eq_of_residue_eq he
  have hzero : ((y n).norm : ZMod p) = 0 := by
    rw [he']
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdiv
  have hsmall := prime_norm_divisor_bound (hyp n) hprime
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hzero)
  have hlarge := hM n hn
  omega

/-- Zero trailing coefficients can be removed by shifting the sequence.
Thus no nontrivial order, including order zero, escapes the obstruction. -/
theorem no_eventual_affine_recurrence (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (k N : ℕ) (a : Fin k → ℤ) (b : GaussianInt) :
    ¬ ∀ n ≥ N, x (n+k) = b+∑ i : Fin k, (a i : GaussianInt)*x (n+i.val) := by
  induction k generalizing x N with
  | zero =>
    intro hrec
    have h0 := hrec N le_rfl
    have h1 := hrec (N+1) (by omega)
    simp only [Nat.add_zero,Fin.sum_univ_zero,add_zero] at h0 h1
    have hh := hx (h0.trans h1.symm)
    omega
  | succ k ih =>
    intro hrec
    by_cases ha : a 0 = 0
    · let y : ℕ → GaussianInt := fun n => x (n+1)
      have hy : Function.Injective y := by
        intro i j he
        exact Nat.add_right_cancel (hx he)
      have hyp (n : ℕ) : Prime (y n) := hp (n+1)
      apply ih y hy hyp N (fun i : Fin k => a i.succ)
      intro n hn
      have hh := hrec n hn
      rw [Fin.sum_univ_succ,ha] at hh
      simp only [Int.cast_zero,zero_mul,zero_add] at hh
      simpa only [y,Fin.val_succ,Nat.add_assoc] using hh
    · apply no_eventually_affine_linear_recurrence x hx hp k N a ha b
      intro n hn
      simpa only [Nat.add_assoc] using hrec n hn

#print axioms no_eventual_affine_recurrence
#print axioms finite_backward_unique_returns
#print axioms finite_recurrence_returns
#print axioms no_eventually_affine_linear_recurrence

end LinearRecurrenceObstruction
end Erdos952Investigation
