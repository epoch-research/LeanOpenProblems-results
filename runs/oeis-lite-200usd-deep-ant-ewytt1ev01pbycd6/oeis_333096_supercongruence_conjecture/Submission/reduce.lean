import Submission.termdvd
import Submission.p1

open PowerSeries Finset

lemma gc_eq_gcoef (t : ℕ) : gc t = gcoef t := by
  unfold gc gcoef; rfl

theorem agen_eq_u (m : ℤ) (hm : m ≠ -1) (n : ℕ) :
    a_gen m n = u ((m + 2) * (n:ℤ)) n := by
  rw [closed_form m hm n]
  unfold u ℓ
  rw [coeffMul]
  -- RHS coefficient forms
  have hR : ∀ i, (PowerSeries.coeff i) (binomialSeries ℤ ((m + 2) * (n:ℤ)))
      * (PowerSeries.coeff (n - i)) Gser
      = Ring.choose ((m + 2) * (n:ℤ)) i * gc (n - i) := by
    intro i
    rw [binomialSeries_coeff, coeff_Gser, smul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl (fun i _ => hR i)]
  -- reflect the LHS sum
  have hrefl := Finset.sum_range_reflect
    (fun j => gcoef j * Ring.choose ((m + 2) * (n:ℤ)) (n - j)) (n + 1)
  simp only [Nat.add_sub_cancel] at hrefl
  rw [← hrefl]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hni : n - (n - i) = i := by omega
  rw [hni, gc_eq_gcoef, mul_comm]

theorem reduce_conj (m : ℤ) (hm : m ≠ -1) (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5)
    (n k : ℕ) (hn : n > 0) (hk : k > 0) :
    a_gen m (n * p ^ k) ≡ a_gen m (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)] := by
  have hp0 : 0 < p := hp.pos
  set M : ℕ := n * p ^ (k - 1) with hMdef
  have hMne : M ≠ 0 := by
    rw [hMdef]; exact Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))
  have hM0 : 0 < M := Nat.pos_of_ne_zero hMne
  have hMp : M * p = n * p ^ k := by
    have hk1 : k - 1 + 1 = k := by omega
    rw [hMdef, mul_assoc, ← pow_succ, hk1]
  -- express a_gens as u
  have hAlo : a_gen m M = u ((m + 2) * (M:ℤ)) M := agen_eq_u m hm M
  have hAhi : a_gen m (n * p ^ k) = u (((m + 2) * (M:ℤ)) * (p:ℤ)) (M * p) := by
    rw [← hMp, agen_eq_u m hm (M * p)]
    congr 1
    push_cast; ring
  -- main formula
  have hmf := main_formula p hp hp5 M ((m + 2) * (M:ℤ))
  -- difference as a sum
  have hdiff : a_gen m (n * p ^ k) - a_gen m M
      = ∑ j ∈ (range (M * p + 1)).filter (fun j => 3 ≤ j),
          Ring.choose ((m + 2) * (M:ℤ)) j * (p:ℤ) ^ j * ℓ (ψ p j) ((m + 2) * (M:ℤ)) M := by
    rw [hAhi, hAlo]; exact hmf
  -- divisibility of the difference
  have hdvdSum : (p:ℤ) ^ (3 * k) ∣ a_gen m (n * p ^ k) - a_gen m M := by
    rw [hdiff]
    apply Finset.dvd_sum
    intro j hj
    rw [Finset.mem_filter] at hj
    have hj3 : 3 ≤ j := hj.2
    have ht := termDvd p hp hp5 (m + 2) M hM0 j hj3
    have hpow : p ^ (k - 1) ∣ M := by rw [hMdef]; exact dvd_mul_left _ _
    have hle : k - 1 ≤ padicValNat p M := by
      have h := (Nat.Prime.pow_dvd_iff_le_factorization hp hMne).mp hpow
      rwa [Nat.factorization_def M hp] at h
    have hexp : 3 * k ≤ 3 * padicValNat p M + 3 := by omega
    exact dvd_trans (pow_dvd_pow (p:ℤ) hexp) ht
  -- conclude the congruence
  rw [Int.modEq_iff_dvd]
  have hneg : a_gen m M - a_gen m (n * p ^ k)
      = -(a_gen m (n * p ^ k) - a_gen m M) := by ring
  rw [hneg]
  exact dvd_neg.mpr hdvdSum

#print axioms agen_eq_u
#print axioms reduce_conj
