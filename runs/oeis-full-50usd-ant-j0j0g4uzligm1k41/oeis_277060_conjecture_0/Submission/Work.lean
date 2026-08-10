import FormalConjectures.Util.ProblemImports
open Finset

def A277060 (n : ℕ) : ℕ :=
  (Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k * Nat.choose (n + k) (k + 1)) ^ 2) / 2

theorem sum_zmod_eq_sum_range (p : ℕ) [Fact p.Prime] {M : Type*} [AddCommMonoid M]
    (f : ZMod p → M) : ∑ x : ZMod p, f x = ∑ i ∈ range p, f (i : ZMod p) := by
  rw [Finset.sum_range fun i => f (i : ZMod p)]
  have he : Function.Bijective (fun i : Fin p => ((i : ℕ) : ZMod p)) := by
    refine ⟨fun a b hab => ?_, fun x => ⟨⟨x.val, ZMod.val_lt x⟩, by simp [ZMod.natCast_val, ZMod.cast_id]⟩⟩
    have := congrArg ZMod.val hab
    rwa [ZMod.val_cast_of_lt a.2, ZMod.val_cast_of_lt b.2, Fin.val_inj] at this
  exact (Fintype.sum_bijective _ he (fun i => f (i : ZMod p)) f (fun x => rfl)).symm

theorem sum_inv_pow_zero (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : k < p - 1) :
    ∑ i ∈ range p, ((i : ZMod p)⁻¹) ^ k = 0 := by
  rw [← sum_zmod_eq_sum_range p (fun x => x⁻¹ ^ k)]
  have hbij : Function.Bijective (fun x : ZMod p => x⁻¹) :=
    Function.Involutive.bijective inv_inv
  rw [Fintype.sum_bijective _ hbij (fun x => x⁻¹ ^ k) (fun x => x ^ k) (fun x => rfl)]
  have h := FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) k
  rw [ZMod.card] at h
  exact h hk

theorem term_id (n k : ℕ) :
    (n+1) * (n.choose k * (n+k).choose (k+1)) = n * ((n+1).choose (k+1) * (n+k).choose k) := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.succ_pos k)
  have hA : (n+k).choose (k+1) * (k+1) = (n+k).choose k * n := by
    rw [Nat.choose_succ_right_eq]; congr 1; omega
  have hB : (n+1) * n.choose k = (n+1).choose (k+1) * (k+1) := Nat.succ_mul_choose_eq n k
  calc (n+1) * (n.choose k * (n+k).choose (k+1)) * (k+1)
      = ((n+1) * n.choose k) * ((n+k).choose (k+1) * (k+1)) := by ring
    _ = ((n+1).choose (k+1) * (k+1)) * ((n+k).choose k * n) := by rw [hA, hB]
    _ = n * ((n+1).choose (k+1) * (n+k).choose k) * (k+1) := by ring

noncomputable def bb (p k : ℕ) : ℕ := (p-1).choose k * (p-1+k).choose (k+1)
noncomputable def cc (p k : ℕ) : ℕ := p.choose (k+1) * (p-1+k).choose k

theorem pb_eq {p : ℕ} (hp : 1 ≤ p) (k : ℕ) : p * bb p k = (p-1) * cc p k := by
  have h := term_id (p-1) k
  rw [Nat.sub_add_cancel hp] at h
  simpa [bb, cc] using h

theorem sq_identity {p : ℕ} (hp : 1 ≤ p) :
    p^2 * (∑ k ∈ range p, (bb p k)^2) = (p-1)^2 * (∑ k ∈ range p, (cc p k)^2) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have h := pb_eq hp k
  calc p^2 * (bb p k)^2 = (p * bb p k)^2 := by ring
    _ = ((p-1) * cc p k)^2 := by rw [h]
    _ = (p-1)^2 * (cc p k)^2 := by ring

theorem two_dvd_S {p : ℕ} (hp : Odd p) (hp1 : 1 ≤ p) :
    2 ∣ ∑ k ∈ range p, (bb p k)^2 := by
  have h4 : (4:ℕ) ∣ (p-1)^2 := by
    obtain ⟨m, hm⟩ := hp; have : p - 1 = 2 * m := by omega
    rw [this]; exact ⟨m^2, by ring⟩
  have hdvd : (4:ℕ) ∣ p^2 * (∑ k ∈ range p, (bb p k)^2) := by
    rw [sq_identity hp1]; exact Dvd.dvd.mul_right h4 _
  have h2 : Nat.Coprime 2 p := (Nat.coprime_two_left).mpr hp
  have hcop : Nat.Coprime 4 (p^2) := by
    have hh : Nat.Coprime (2^2) (p^2) := h2.pow 2 2
    rwa [show (2:ℕ)^2 = 4 from rfl] at hh
  exact dvd_trans (by norm_num) (Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd)

theorem A_eq {p : ℕ} (hp1 : 1 ≤ p) (hodd : Odd p) :
    2 * A277060 (p-1) = ∑ k ∈ range p, (bb p k)^2 := by
  have hSeq : A277060 (p-1) = (∑ k ∈ range p, (bb p k)^2) / 2 := by
    unfold A277060 bb
    rw [Nat.sub_add_cancel hp1]
  rw [hSeq, Nat.mul_div_cancel' (two_dvd_S hodd hp1)]

-- THE HARD PART
theorem core_sum {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    ((∑ k ∈ range p, (bb p k)^2 : ℕ) : ZMod (p^4)) = 2 := sorry

theorem c1 {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    A277060 (p-1) ≡ 1 [MOD p^4] := by
  have hp1 : 1 ≤ p := by omega
  have hodd : Odd p := (Fact.out (p := p.Prime)).odd_of_ne_two (by omega)
  rw [← ZMod.natCast_eq_natCast_iff]
  have hSc : ((∑ k ∈ range p, (bb p k)^2 : ℕ) : ZMod (p^4)) = 2 := core_sum hp5
  have h2A := A_eq hp1 hodd
  have key : (2 : ZMod (p^4)) * ((A277060 (p-1) : ℕ) : ZMod (p^4)) = 2 := by
    have h : (((2 * A277060 (p-1) : ℕ)) : ZMod (p^4)) = 2 := by rw [h2A]; exact hSc
    push_cast at h; exact h
  have hne : NeZero (p^4) := ⟨by positivity⟩
  have hu : IsUnit (2 : ZMod (p^4)) := by
    have hc : Nat.Coprime 2 (p^4) := by
      have h2 : Nat.Coprime 2 p := (Nat.coprime_two_left).mpr hodd
      simpa using h2.pow_right 4
    have := (ZMod.isUnit_iff_coprime 2 (p^4)).mpr hc
    simpa using this
  rw [Nat.cast_one]
  refine (hu.mul_right_inj).mp ?_
  rw [mul_one]; exact key
