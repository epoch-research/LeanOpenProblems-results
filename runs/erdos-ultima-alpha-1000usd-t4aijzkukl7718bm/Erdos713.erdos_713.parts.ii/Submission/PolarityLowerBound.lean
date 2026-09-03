import FormalConjecturesUtil
import Submission.RestrictedPolarity

/-! A uniform C4 lower bound, used to separate restricted polarity graph
families from the actual extremal-number function. -/
open SimpleGraph
namespace Erdos713PolarityLowerBound
set_option maxHeartbeats 1000000

lemma free_map_of_no_isolates {W V U : Type*} {H : SimpleGraph W}
    {G : SimpleGraph V} (hH : ∀ w, ∃ z, H.Adj w z) (hfree : H.Free G) (e : V ↪ U) :
    H.Free (G.map e) := by
  classical
  rintro ⟨f⟩
  have hpre (w : W) : ∃ v : V, e v = f w := by
    obtain ⟨z, hwz⟩ := hH w
    obtain ⟨v, _, _, hv, _⟩ := (map_adj e G _ _).mp (f.toHom.map_adj hwz)
    exact ⟨v, hv⟩
  choose k hk using hpre
  apply hfree
  refine ⟨⟨⟨k, ?_⟩, ?_⟩⟩
  · intro a b hab
    obtain ⟨v, w, hvw, hv, hw⟩ := (map_adj e G _ _).mp (f.toHom.map_adj hab)
    have hvk : v = k a := e.injective (hv.trans (hk a).symm)
    have hwk : w = k b := e.injective (hw.trans (hk b).symm)
    simpa only [hvk, hwk] using hvw
  · intro a b hab
    apply f.injective
    change f a = f b
    change k a = k b at hab
    rw [← hk a, ← hk b, hab]

open scoped Classical in
lemma edge_le_extremal_larger {W : Type*} {H : SimpleGraph W}
    (hH : ∀ w, ∃ z, H.Adj w z) {m n : ℕ} (hmn : m ≤ n)
    (G : SimpleGraph (Fin m)) (hfree : H.Free G) :
    Nat.card G.edgeSet ≤ extremalNumber n H := by
  let e := Fin.castLEEmb hmn
  have h := card_edgeFinset_le_extremalNumber (free_map_of_no_isolates hH hfree e)
  rw [Fintype.card_fin] at h
  have he := card_edgeFinset_map e G
  simp only [edgeFinset_card, ← Nat.card_eq_fintype_card] at h he
  rwa [he] at h

/-- A deliberately non-sharp numerical constant in the C4 lower bound. -/
lemma c4_lower_squared (n : ℕ) (hn : 4 ≤ n) :
    (n : ℝ) ^ 3 ≤ 4096 * (extremalNumber n (cycleGraph 4) : ℝ) ^ 2 := by
  classical
  let s := Nat.sqrt n
  have hs : 2 ≤ s := Nat.le_sqrt'.mpr hn
  let k := Nat.log 2 s
  let q := 2 ^ k
  have hk : k ≠ 0 := (Nat.log_pos (by norm_num) hs).ne'
  have hqle : q ≤ s := Nat.pow_log_le_self 2 (by omega)
  have hsqlt : s < 2 * q := by
    simpa only [Nat.pow_succ, mul_comm] using Nat.lt_pow_succ_log_self
      (by norm_num : (1 : ℕ) < 2) s
  have hq : 2 ≤ q := by omega
  have hqn : q ^ 2 ≤ n := (Nat.pow_le_pow_left hqle 2).trans (Nat.sqrt_le' n)
  have hnq : n < 4 * q ^ 2 := by
    have h := Nat.lt_succ_sqrt' n
    have hsq : s + 1 ≤ 2 * q := by omega
    have hp := Nat.pow_le_pow_left hsq 2
    dsimp [s] at hsq
    nlinarith
  let K := GaloisField 2 k
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = q := by
    simpa only [← Nat.card_eq_fintype_card, K, q] using GaloisField.card 2 k hk
  have hd : q - 1 < Fintype.card K := by rw [hcard]; omega
  have hg := Erdos713RestrictedPolarity.exists_regular_c4_free (K := K) (q - 1) hd
  rw [hcard] at hg
  obtain ⟨G, hfree, _, he⟩ := hg
  have hE : Nat.card G.edgeSet ≤ extremalNumber n (cycleGraph 4) :=
    edge_le_extremal_larger (by decide : ∀ v : Fin 4, ∃ w, (cycleGraph 4).Adj v w)
      (show (q - 1) * q ≤ n by nlinarith [Nat.sub_le q 1]) G hfree
  simp only [edgeFinset_card, ← Nat.card_eq_fintype_card] at he
  have heR : 2 * (Nat.card G.edgeSet : ℝ) = ((q : ℝ) - 1) ^ 2 * q := by
    have hcast : 2 * (Nat.card G.edgeSet : ℝ) = ((q - 1 : ℕ) : ℝ) ^ 2 * q := by
      exact_mod_cast he
    simpa only [Nat.cast_sub (show 1 ≤ q by omega), Nat.cast_one] using hcast
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hnqR : (n : ℝ) ≤ 4 * (q : ℝ) ^ 2 := by exact_mod_cast hnq.le
  have hqsq : (q : ℝ) ^ 2 ≤ 4 * ((q : ℝ) - 1) ^ 2 := by nlinarith
  have hqcube : (q : ℝ) ^ 3 ≤ 8 * (Nat.card G.edgeSet : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hqsq (show (0 : ℝ) ≤ q by positivity)
    nlinarith [heR]
  calc
    (n : ℝ) ^ 3 ≤ (4 * (q : ℝ) ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) hnqR 3
    _ = 64 * ((q : ℝ) ^ 3) ^ 2 := by ring
    _ ≤ 64 * (8 * (Nat.card G.edgeSet : ℝ)) ^ 2 := by
      gcongr
    _ = 4096 * (Nat.card G.edgeSet : ℝ) ^ 2 := by ring
    _ ≤ 4096 * (extremalNumber n (cycleGraph 4) : ℝ) ^ 2 := by
      gcongr

lemma c4_lower_power (n : ℕ) (hn : 4 ≤ n) :
    (n : ℝ) ^ (3 / 2 : ℝ) / 64 ≤ (extremalNumber n (cycleGraph 4) : ℝ) := by
  have hp : ((n : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = (n : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  have h := c4_lower_squared n hn
  have hnn : (0 : ℝ) ≤ extremalNumber n (cycleGraph 4) := Nat.cast_nonneg _
  nlinarith [Real.rpow_nonneg (Nat.cast_nonneg n) (3 / 2 : ℝ)]

#print axioms free_map_of_no_isolates
#print axioms edge_le_extremal_larger
#print axioms c4_lower_squared
#print axioms c4_lower_power
end Erdos713PolarityLowerBound
