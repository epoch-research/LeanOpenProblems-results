import FormalConjectures.Util.ProblemImports
import Submission.TestPrimality3

namespace R

open Finset

instance {n} [NeZero n] : DecidableEq (R n) := by delta R; infer_instance
instance {n} [NeZero n] : Fintype (R n) := by delta R; infer_instance

theorem M_le_p2_minus_one {n p M m : ℕ} [NeZero n] [NeZero p] (h : p ∣ n) (hp : 1 < p)
    (x : R n) (hM : M = 2 * (100943 * 3^m))
    (h_pow_M : pow x M = one)
    (inv2 : R n) (h_inv2 : mul inv2 (sub (pow x (M / 2)) one) = one)
    (inv3 : R n) (h_inv3 : mul inv3 (sub (pow x (M / 3)) one) = one)
    (invp : R n) (h_invp : mul invp (sub (pow x (M / 100943)) one) = one) :
    M + 1 ≤ p^2 := by
  have h_inj : ∀ i j, i < M → j < M → pow (cast h x) i = pow (cast h x) j → i = j := by
    intro i j hi hj heq
    obtain hle | hle := le_total i j
    · have h_pow_M_p : pow (cast h x) M = one := by
        rw [←cast_pow, h_pow_M, cast_one]
      have h_sub := pow_sub (cast h x) h_pow_M_p (by omega) hle heq
      by_contra! hne
      have h_pos : 0 < j - i := by omega
      have h_lt : j - i < M := by omega
      have := order_eq_M_rp h hp x hM h_pow_M inv2 h_inv2 inv3 h_inv3 invp h_invp (j - i) h_pos h_lt
      exact this h_sub
    · have h_pow_M_p : pow (cast h x) M = one := by
        rw [←cast_pow, h_pow_M, cast_one]
      have h_sub := pow_sub (cast h x) h_pow_M_p (by omega) hle heq.symm
      by_contra! hne
      have h_pos : 0 < i - j := by omega
      have h_lt : i - j < M := by omega
      have := order_eq_M_rp h hp x hM h_pow_M inv2 h_inv2 inv3 h_inv3 invp h_invp (i - j) h_pos h_lt
      exact this h_sub
  have h_nodup : (List.range M).map (pow (cast h x)) |>.Nodup := by
    rw [List.nodup_map_iff_inj_on List.nodup_range]
    intro i hi j hj heq
    rw [List.mem_range] at hi hj
    exact h_inj i j hi hj heq
  have h_len : ((List.range M).map (pow (cast h x))).length = M := by
    rw [List.length_map, List.length_range]
  have h_ne_zero : ∀ y ∈ (List.range M).map (pow (cast h x)), y ≠ zero := by
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    rw [List.mem_range] at hi
    have h_pow_M_p : pow (cast h x) M = one := by
      rw [←cast_pow, h_pow_M, cast_one]
    intro h_zero
    have : pow (cast h x) M = zero := by
      calc pow (cast h x) M = pow (cast h x) (i + (M - i)) := by rw [Nat.add_sub_of_le (by omega)]
        _ = mul (pow (cast h x) i) (pow (cast h x) (M - i)) := pow_add _ _ _
        _ = mul zero (pow (cast h x) (M - i)) := by rw [h_zero]
        _ = zero := zero_mul _
    rw [h_pow_M_p] at this
    exact one_ne_zero hp this
  let S := ((List.range M).map (pow (cast h x))).toFinset
  have h_card_S : S.card = M := by
    rw [List.toFinset_card_of_nodup h_nodup, h_len]
  have h_subset : S ⊆ Finset.univ.erase zero := by
    intro y hy
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    rw [List.mem_toFinset] at hy
    exact h_ne_zero y hy
  have h_le : S.card ≤ (Finset.univ.erase (zero : R p)).card :=
    Finset.card_le_card h_subset
  have h_card_univ : (Finset.univ : Finset (R p)).card = p^2 := by
    change Fintype.card (ZMod p × ZMod p) = p^2
    rw [Fintype.card_prod, ZMod.card p, sq]
  have h_erase : (Finset.univ.erase (zero : R p)).card = Finset.univ.card - 1 :=
    Finset.card_erase_of_mem (Finset.mem_univ (zero : R p))
  have h_card_erase : (Finset.univ.erase (zero : R p)).card = p^2 - 1 := by
    rw [h_erase, h_card_univ]
  rw [h_card_S, h_card_erase] at h_le
  have h_M_pos : 0 < M := by rw [hM]; positivity
  omega

theorem is_prime_of_cert {M N m : ℕ} [NeZero N]
    (hN : N = M - 1)
    (hM : M = 2 * (100943 * 3^m))
    (hm_pos : 0 < m)
    (x : R N)
    (h_pow_M : pow x M = one)
    (inv2 : R N) (h_inv2 : mul inv2 (sub (pow x (M / 2)) one) = one)
    (inv3 : R N) (h_inv3 : mul inv3 (sub (pow x (M / 3)) one) = one)
    (invp : R N) (h_invp : mul invp (sub (pow x (M / 100943)) one) = one) :
    Nat.Prime N := by
  have hM_pos : 0 < M := by rw [hM]; positivity
  have hM_gt_1 : 1 < M := by
    rw [hM]
    have : 3^1 ≤ 3^m := Nat.pow_le_pow_right (by omega) hm_pos
    norm_num at this
    nlinarith
  have hN_pos : 0 < N := by omega
  have hN_gt_1 : 1 < N := by omega
  by_contra h_not_prime
  set p := Nat.minFac N
  have hp_prime : Nat.Prime p := Nat.minFac_prime hN_gt_1.ne'
  have hp_gt_1 : 1 < p := hp_prime.one_lt
  have hp_dvd : p ∣ N := Nat.minFac_dvd N
  have h_p2_le : p^2 ≤ N := Nat.minFac_sq_le_self hN_pos h_not_prime
  haveI : NeZero p := ⟨by omega⟩
  have h_le := M_le_p2_minus_one hp_dvd hp_gt_1 x hM h_pow_M inv2 h_inv2 inv3 h_inv3 invp h_invp
  omega

end R
