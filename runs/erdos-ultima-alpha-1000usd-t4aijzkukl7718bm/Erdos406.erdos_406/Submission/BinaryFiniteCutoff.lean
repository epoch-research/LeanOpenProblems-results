import Submission.BinaryCertificates

/-! A search-size reduction, not a certificate witness. A periodic modular
guard does not increase the transient length of a finite-state orbit. -/

namespace Erdos406BinaryCertificate

lemma periodic_of_iterate_eq {σ : Type*} (f : σ → σ) (s : σ)
    {i j k : ℕ} (hij : i < j) (hjk : j ≤ k) (he : f^[i] s = f^[j] s) :
    Function.IsPeriodicPt f (j - i) (f^[k] s) := by
  have hp : Function.IsPeriodicPt f (j - i) (f^[i] s) := by
    change f^[j - i] (f^[i] s) = f^[i] s
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega : i ≤ j)]
    exact he.symm
  have hh := hp.apply_iterate (k - i)
  rwa [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega : i ≤ k)] at hh

lemma late_orbit_periodic {σ : Type*} [Fintype σ] (f : σ → σ) (s : σ)
    {k : ℕ} (hk : Fintype.card σ ≤ k) :
    ∃ p : ℕ, 0 < p ∧ Function.IsPeriodicPt f p (f^[k] s) := by
  obtain ⟨i, j, hne, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Fintype.card σ + 1) => f^[i.val] s) (by simp)
  rcases lt_or_gt_of_ne hne with hij | hji
  · refine ⟨j.val - i.val, by omega, periodic_of_iterate_eq f s hij ?_ he⟩
    have hj := j.isLt
    omega
  · refine ⟨i.val - j.val, by omega, periodic_of_iterate_eq f s hji ?_ he.symm⟩
    have hi := i.isLt
    omega

/-- If a finite-state orbit, tested against an independent periodic guard,
passes only finitely many times, then it never passes after the state count.
The guard's period need not multiply the cutoff. -/
lemma finite_guarded_orbit_cutoff {σ β : Type*} [Fintype σ]
    (f : σ → σ) (s : σ) (A : Set σ) (g : ℕ → β) (P : β → Prop)
    {T : ℕ} (hT : 0 < T) (hg : Function.Periodic g T)
    (hfinite : {k | f^[k] s ∈ A ∧ P (g k)}.Finite)
    {k : ℕ} (hk : Fintype.card σ ≤ k) :
    ¬ (f^[k] s ∈ A ∧ P (g k)) := by
  rintro ⟨ha, hpg⟩
  obtain ⟨p, hp, hperiod⟩ := late_orbit_periodic f s hk
  obtain ⟨B, hB⟩ := hfinite.bddAbove
  let m := p * (B + 1) * T
  have hlarge : B < k + m := by
    have h1 : B + 1 ≤ p * (B + 1) := Nat.le_mul_of_pos_left _ hp
    have h2 : p * (B + 1) ≤ m := Nat.le_mul_of_pos_right _ hT
    omega
  have he : f^[k + m] s = f^[k] s := by
    have hh := hperiod.mul_const ((B + 1) * T)
    change f^[p * ((B + 1) * T)] (f^[k] s) = f^[k] s at hh
    rw [Nat.add_comm, Function.iterate_add_apply]
    simpa only [m, mul_assoc] using hh
  have hg' : g (k + m) = g k := hg.nat_mul (p * (B + 1)) k
  have hb : k + m ≤ B := hB ⟨he ▸ ha, hg' ▸ hpg⟩
  omega

lemma evalNat_two_pow_iterate {σ : Type*} (D : DFA ℕ σ) (k : ℕ) :
    evalNat D (2 ^ k) = (fun s => D.step s 0)^[k] (evalNat D 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', evalNat_twice D (by positivity), ih]
    rw [Function.iterate_succ_apply']

lemma finite_guarded_binary_powers_cutoff {σ : Type*} [Fintype σ]
    (D : DFA ℕ σ) (r : ℕ)
    (hfinite : {k | evalNat D (2 ^ k) ∈ D.accept ∧
      Nat.digits 3 (2 ^ k % 3 ^ r) ⊆ [0, 1]}.Finite)
    {k : ℕ} (hk : Fintype.card σ ≤ k) :
    ¬ (evalNat D (2 ^ k) ∈ D.accept ∧ Nat.digits 3 (2 ^ k % 3 ^ r) ⊆ [0, 1]) := by
  have hc : Nat.Coprime 2 (3 ^ r) := (by decide : Nat.Coprime 2 3).pow_right r
  have hT : 0 < (3 ^ r).totient := Nat.totient_pos.mpr (by positivity)
  have hg : Function.Periodic (fun k : ℕ => 2 ^ k % 3 ^ r) (3 ^ r).totient := by
    intro k
    simpa only [pow_add, mul_one] using (Nat.ModEq.pow_totient hc).mul_left (2 ^ k)
  have hf : {k | (fun s => D.step s 0)^[k] (evalNat D 1) ∈ D.accept ∧
      Nat.digits 3 (2 ^ k % 3 ^ r) ⊆ [0, 1]}.Finite := by
    simpa only [evalNat_two_pow_iterate] using hfinite
  simpa only [evalNat_two_pow_iterate] using finite_guarded_orbit_cutoff
    (fun s => D.step s 0) (evalNat D 1) D.accept (fun k => 2 ^ k % 3 ^ r)
    (fun n => Nat.digits 3 n ⊆ [0, 1]) hT hg hf hk

#print axioms finite_guarded_binary_powers_cutoff
end Erdos406BinaryCertificate
