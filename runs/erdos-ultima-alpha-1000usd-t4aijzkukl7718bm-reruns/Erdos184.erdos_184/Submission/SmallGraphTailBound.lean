import Submission.PaddedGraphEncoding

/-! Isolated high labels force the unused binary edge digits to vanish. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.SmallGraphTailBound
open SmallGraphEncoding QuadrilateralOutsideData
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

lemma bound_from_zero_digits {lo hi code : ℕ} (hl : lo ≤ hi) (hc : code < 2^hi)
    (hz : ∀ k, lo ≤ k → k < hi → code / 2^k % 2 = 0) : code < 2^lo := by
  induction hi generalizing lo with
  | zero =>
    have : lo = 0 := by omega
    simpa [this] using hc
  | succ hi ih =>
    by_cases he : lo = hi+1
    · simpa [he] using hc
    have hz' := hz hi (by omega) (by omega)
    have hq : code / 2^hi < 2 := by
      apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
      simpa only [pow_succ,Nat.mul_comm] using hc
    rw [Nat.mod_eq_of_lt hq] at hz'
    have hc' : code < 2^hi := by
      have hh := (Nat.div_lt_iff_lt_mul (k := 2^hi) (x := code) (y := 1) (by positivity)).mp
        (by omega)
      simpa only [one_mul] using hh
    exact ih (by omega) hc' (fun k hk hk' => hz k hk (by omega))

lemma table7_indices : ∀ k : Fin 15,
    let p := table7.endpoints k
    p.1.val ≠ p.2.val ∧ p.1.val ≠ 0 ∧ p.2.val ≠ 0 ∧ edgeIndex p.1.val p.2.val = k.val := by
  decide +kernel

lemma table7_tail : ∀ n : Fin 8, ∀ k : Fin 15,
    (n.val-1)*(n.val-2)/2 ≤ k.val → n.val ≤ (table7.endpoints k).2.val := by
  decide +kernel

lemma tail_bound (code n : ℕ) (hn : n ≤ 7) (hc : code < 32768)
    (hz : ∀ i : Fin 7, n ≤ i.val → (graph 7 2 code).degree i = 0) :
    code < 2^((n-1)*(n-2)/2) := by
  apply bound_from_zero_digits (hi := 15)
  · interval_cases n <;> norm_num
  · exact hc
  intro k hk hkhi
  let i := (table7.endpoints ⟨k,hkhi⟩).1
  let j := (table7.endpoints ⟨k,hkhi⟩).2
  have hjn : n ≤ j.val := table7_tail ⟨n,by omega⟩ ⟨k,hkhi⟩ hk
  have hjzero := hz j hjn
  have ha : ¬(graph 7 2 code).Adj i j := by
    intro hij
    have hp := ((graph 7 2 code).degree_pos_iff_exists_adj j).mpr ⟨i,hij.symm⟩
    omega
  have ht := table7_indices ⟨k,hkhi⟩
  change ¬starAdj 2 code i.val j.val = true at ha
  have hne : i.val ≠ j.val := ht.1
  have hi0 : i.val ≠ 0 := ht.2.1
  have hj0 : j.val ≠ 0 := ht.2.2.1
  have hidx : edgeIndex i.val j.val = k := ht.2.2.2
  simp only [starAdj,if_neg hne,if_neg hi0,if_neg hj0,hidx,decide_eq_true_eq] at ha
  have hm := Nat.mod_lt (code / 2^k) (by decide : 0 < 2)
  omega

end Erdos184.SmallGraphTailBound
