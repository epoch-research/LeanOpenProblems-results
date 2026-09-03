import FormalConjecturesUtil

/-! Arithmetic for a parameterized chain/ring obstruction.
These lemmas do not assert the graph-theoretic transport or a disproof of Erdős184.
`localExcess` is the cost beyond one singleton per independent-side vertex
of the elementary K_(3,a) packing. -/
namespace Erdos184Work.ChainRingArithmetic
set_option maxHeartbeats 400000

def localExcess (a : ℕ) : ℕ := if a = 1 then 2 else (a + 2) / 3

lemma localExcess_zero : localExcess 0 = 0 := by decide
lemma localExcess_two : localExcess 2 = 1 := by decide

lemma localExcess_le (q a : ℕ) (hq : 1 ≤ q) (ha : a ≤ 6 * q) :
    localExcess a ≤ 2 * q := by
  unfold localExcess
  split_ifs <;> omega

/-- Number of leaves used in a row by t global cycles. A global cycle uses
one or two leaves in that row. Avoid leaving exactly one leaf when possible. -/
def consume (t a : ℕ) : ℕ :=
  if a ≤ 2 * t then a else if a = 2 * t + 1 then 2 * t - 1 else 2 * t

lemma consume_bounds {t a : ℕ} (ht : 1 ≤ t) (ha : t ≤ a) :
    t ≤ consume t a ∧ consume t a ≤ 2 * t ∧ consume t a ≤ a := by
  unfold consume
  split_ifs <;> omega

lemma consume_all {t a : ℕ} (ha : a ≤ 2 * t) : consume t a = a := by
  simp [consume,ha]

lemma consume_excess {q t a : ℕ} (ht : 1 ≤ t) (htq : t ≤ 3 * q)
    (hta : t ≤ a) (ha : a ≤ 6 * q) :
    localExcess (a - consume t a) ≤ (6 * q - 2 * t + 2) / 3 := by
  unfold consume localExcess
  split_ifs <;> omega

lemma global_cost_bound {q t : ℕ} (ht : 1 ≤ t) (htq : t ≤ 3 * q) :
    t + 2 * ((6 * q - 2 * t + 2) / 3) ≤ 4 * q + 1 := by
  omega

def minimumCount (a b c : ℕ) := min a (min b c)
def globalCount (a b c : ℕ) := (minimumCount a b c + 1) / 2

def ringExcess (a b c : ℕ) : ℕ :=
  if minimumCount a b c = 0 then localExcess a + localExcess b + localExcess c
  else
    let t := globalCount a b c
    t + localExcess (a - consume t a) + localExcess (b - consume t b) +
      localExcess (c - consume t c)

lemma positive_ring_excess {q a b c : ℕ} (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c)
    (ha : a ≤ 6 * q) (hb : b ≤ 6 * q) (hc : c ≤ 6 * q) :
    ringExcess a b c ≤ 4 * q + 1 := by
  let m := minimumCount a b c
  let t := globalCount a b c
  have hm : m = min a (min b c) := rfl
  have ht : t = (m + 1) / 2 := rfl
  have hmpos : 0 < m := by omega
  have htpos : 1 ≤ t := by omega
  have htq : t ≤ 3 * q := by omega
  have hta : t ≤ a := by omega
  have htb : t ≤ b := by omega
  have htc : t ≤ c := by omega
  have hA := consume_excess htpos htq hta ha
  have hB := consume_excess htpos htq htb hb
  have hC := consume_excess htpos htq htc hc
  have hz : localExcess (a - consume t a) = 0 ∨
      localExcess (b - consume t b) = 0 ∨ localExcess (c - consume t c) = 0 := by
    have hm2 : m ≤ 2 * t := by omega
    have hmcase : a = m ∨ b = m ∨ c = m := by omega
    rcases hmcase with h | h | h
    · left
      rw [h,consume_all hm2,Nat.sub_self,localExcess_zero]
    · right; left
      rw [h,consume_all hm2,Nat.sub_self,localExcess_zero]
    · right; right
      rw [h,consume_all hm2,Nat.sub_self,localExcess_zero]
  have hnum := global_cost_bound htpos htq
  unfold ringExcess
  rw [if_neg (show minimumCount a b c ≠ 0 by change m ≠ 0; omega)]
  change t + localExcess (a - consume t a) + localExcess (b - consume t b) +
      localExcess (c - consume t c) ≤ _
  omega

/-- Rank contributed by the hubs of the active rows. Each nonempty row adds
2 in a chain. In a ring with all three rows active the total is instead 5. -/
def chainHubRank (a b c : ℕ) : ℕ :=
  (if a = 0 then 0 else 2) + (if b = 0 then 0 else 2) + (if c = 0 then 0 else 2)
def ringHubRank (a b c : ℕ) : ℕ :=
  if minimumCount a b c = 0 then chainHubRank a b c else 5

lemma chain_excess_bound {q a b c : ℕ} (hq : 1 ≤ q)
    (ha : a ≤ 6 * q) (hb : b ≤ 6 * q) (hc : c ≤ 6 * q) :
    localExcess a + localExcess b + localExcess c ≤ chainHubRank a b c + (6 * q - 6) := by
  have hA := localExcess_le q a hq ha
  have hB := localExcess_le q b hq hb
  have hC := localExcess_le q c hq hc
  unfold chainHubRank
  split_ifs <;> subst_vars <;> simp only [localExcess_zero] at * <;> omega

lemma ring_excess_bound {q a b c : ℕ} (hq : 1 ≤ q)
    (ha : a ≤ 6 * q) (hb : b ≤ 6 * q) (hc : c ≤ 6 * q) :
    ringExcess a b c ≤ ringHubRank a b c + (4 * q - 4) := by
  by_cases hm : minimumCount a b c = 0
  · rw [ringExcess,if_pos hm,ringHubRank,if_pos hm]
    have hA := localExcess_le q a hq ha
    have hB := localExcess_le q b hq hb
    have hC := localExcess_le q c hq hc
    unfold minimumCount at hm
    unfold chainHubRank
    split_ifs <;> subst_vars <;> simp only [localExcess_zero] at * <;> omega
  · have ha0 : 0 < a := by unfold minimumCount at hm; omega
    have hb0 : 0 < b := by unfold minimumCount at hm; omega
    have hc0 : 0 < c := by unfold minimumCount at hm; omega
    have h := positive_ring_excess ha0 hb0 hc0 ha hb hc
    rw [ringHubRank,if_neg hm]
    omega

lemma parameter_gap {q : ℕ} (hq : 1 ≤ q) :
    (22 * q + 2) + (2 * q - 1) = 24 * q + 1 := by omega

end Erdos184Work.ChainRingArithmetic
#print axioms Erdos184Work.ChainRingArithmetic.ring_excess_bound
#print axioms Erdos184Work.ChainRingArithmetic.chain_excess_bound
