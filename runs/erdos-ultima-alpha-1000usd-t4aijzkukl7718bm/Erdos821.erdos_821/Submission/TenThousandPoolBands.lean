import Submission.CertifiedPoolBands

/-!
# Ten thousand kernel-certified retained-pool bands

The cutoff is 15586310/40000020. This improves a fixed multiplicity
exponent, not the unrestricted conjecture.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

/-- A uniformly spaced, rounded partition; it is constant after its last point. -/
def tenThousandPoolEndpoint (i : ℕ) : ℕ :=
  7793155 + (2206852 * min i 10000)/10000

def tenThousandPoolB (i : Fin 10000) : ℕ :=
  999999999999999 / tenThousandPoolEndpoint (i.val+1)

def tenThousandPoolL (i : Fin 10000) : ℕ := 2*tenThousandPoolB i-100000000+1

private def tenThousandPoolBudgetAt (i : ℕ) : ℕ :=
  poolBandCertificate 10000000000 (tenThousandPoolEndpoint i)
    (tenThousandPoolEndpoint (i+1))
    (999999999999999 / tenThousandPoolEndpoint (i+1))

def tenThousandPoolBudgetNat (i : Fin 10000) : ℕ :=
  tenThousandPoolBudgetAt i.val

noncomputable def tenThousandPoolBudget (i : Fin 10000) : ℝ :=
  (tenThousandPoolBudgetNat i : ℝ)/10000000000

lemma tenThousandPool_band_parameters (i : Fin 10000) :
    1 ≤ tenThousandPoolEndpoint i.val ∧
    tenThousandPoolEndpoint i.val ≤ tenThousandPoolEndpoint (i.val+1) ∧
    tenThousandPoolEndpoint (i.val+1) ≤ 10000007 ∧
    20000011 ≤ 3*tenThousandPoolEndpoint i.val ∧
    1 ≤ tenThousandPoolB i ∧ tenThousandPoolB i < 200000000 ∧
    1 ≤ tenThousandPoolL i ∧ 2*tenThousandPoolB i+1 ≤ tenThousandPoolL i+100000000 ∧
    tenThousandPoolL i*tenThousandPoolEndpoint (i.val+1) <
      100000000*(20000009-tenThousandPoolEndpoint (i.val+1)) ∧
    tenThousandPoolB i*tenThousandPoolEndpoint (i.val+1) < 100000000*10000000 := by
  let u := tenThousandPoolEndpoint i.val
  let v := tenThousandPoolEndpoint (i.val+1)
  let B := tenThousandPoolB i
  let L := tenThousandPoolL i
  have hu : 7793155 ≤ u := Nat.le_add_right _ _
  have huv : u ≤ v := by
    apply Nat.add_le_add_left
    apply Nat.div_le_div_right
    apply Nat.mul_le_mul_left
    exact min_le_min_right _ (Nat.le_succ _)
  have hv : v ≤ 10000007 := by
    have h := Nat.div_le_div_right (Nat.mul_le_mul_left 2206852
      (min_le_right (i.val+1) 10000)) (c := 10000)
    norm_num at h
    dsimp [v,tenThousandPoolEndpoint]
    omega
  have hv0 : 0 < v := by omega
  have hBv : B*v ≤ 999999999999999 := Nat.div_mul_le_self _ _
  have hBlo : 90000000 ≤ B := by
    apply (Nat.le_div_iff_mul_le hv0).mpr
    omega
  have hBhi : B < 200000000 := by
    apply (Nat.div_lt_iff_lt_mul hv0).mpr
    omega
  have hL : L+100000000=2*B+1 := by
    dsimp [L,tenThousandPoolL]
    change 2*B-100000000+1+100000000=2*B+1
    omega
  have hLv : L*v+100000000*v=(2*B+1)*v := by
    rw [← Nat.add_mul,hL]
  have hsub : 20000009-v+v=20000009 := by omega
  have hsubv : 100000000*(20000009-v)+100000000*v=2000000900000000 := by
    rw [← Nat.mul_add,hsub]
  change 1 ≤ u ∧ u ≤ v ∧ v ≤ 10000007 ∧ 20000011 ≤ 3*u ∧
    1 ≤ B ∧ B < 200000000 ∧ 1 ≤ L ∧ 2*B+1 ≤ L+100000000 ∧
    L*v < 100000000*(20000009-v) ∧ B*v < 100000000*10000000
  refine ⟨by omega,huv,hv,by omega,by omega,hBhi,by omega,by omega,?_,by omega⟩
  nlinarith only [hLv,hsubv,hBv,hv]

lemma tenThousandPool_band_limit (i : Fin 10000) :
    scaledProductLongLimit (poolBandCoefficient (tenThousandPoolB i))
      (tenThousandPoolEndpoint i.val) (tenThousandPoolEndpoint (i.val+1)) < tenThousandPoolBudget i := by
  obtain ⟨hu,huv,_,_,hb,_⟩ := tenThousandPool_band_parameters i
  exact poolBandLimit_lt_certificate 10000000000 _ _ _ (by decide) hu huv hb

private lemma tenThousandPool_prefix_0 :
    (∑ i ∈ range 0, tenThousandPoolBudgetAt i) = 0 := by simp

private lemma tenThousandPool_prefix_1 :
    (∑ i ∈ range 100, tenThousandPoolBudgetAt i) = 113331445 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (0+i)) = 113331445 := by
    decide
  change (∑ i ∈ range (0+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_0,hb]

private lemma tenThousandPool_prefix_2 :
    (∑ i ∈ range 200, tenThousandPoolBudgetAt i) = 226348432 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (100+i)) = 113016987 := by
    decide
  change (∑ i ∈ range (100+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_1,hb]

private lemma tenThousandPool_prefix_3 :
    (∑ i ∈ range 300, tenThousandPoolBudgetAt i) = 339042515 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (200+i)) = 112694083 := by
    decide
  change (∑ i ∈ range (200+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_2,hb]

private lemma tenThousandPool_prefix_4 :
    (∑ i ∈ range 400, tenThousandPoolBudgetAt i) = 451425697 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (300+i)) = 112383182 := by
    decide
  change (∑ i ∈ range (300+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_3,hb]

private lemma tenThousandPool_prefix_5 :
    (∑ i ∈ range 500, tenThousandPoolBudgetAt i) = 563489552 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (400+i)) = 112063855 := by
    decide
  change (∑ i ∈ range (400+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_4,hb]

private lemma tenThousandPool_prefix_6 :
    (∑ i ∈ range 600, tenThousandPoolBudgetAt i) = 675245991 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (500+i)) = 111756439 := by
    decide
  change (∑ i ∈ range (500+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_5,hb]

private lemma tenThousandPool_prefix_7 :
    (∑ i ∈ range 700, tenThousandPoolBudgetAt i) = 786686628 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (600+i)) = 111440637 := by
    decide
  change (∑ i ∈ range (600+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_6,hb]

private lemma tenThousandPool_prefix_8 :
    (∑ i ∈ range 800, tenThousandPoolBudgetAt i) = 897823281 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (700+i)) = 111136653 := by
    decide
  change (∑ i ∈ range (700+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_7,hb]

private lemma tenThousandPool_prefix_9 :
    (∑ i ∈ range 900, tenThousandPoolBudgetAt i) = 1008647591 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (800+i)) = 110824310 := by
    decide
  change (∑ i ∈ range (800+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_8,hb]

private lemma tenThousandPool_prefix_10 :
    (∑ i ∈ range 1000, tenThousandPoolBudgetAt i) = 1119171296 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (900+i)) = 110523705 := by
    decide
  change (∑ i ∈ range (900+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_9,hb]

private lemma tenThousandPool_prefix_11 :
    (∑ i ∈ range 1100, tenThousandPoolBudgetAt i) = 1229386064 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (1000+i)) = 110214768 := by
    decide
  change (∑ i ∈ range (1000+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_10,hb]

private lemma tenThousandPool_prefix_12 :
    (∑ i ∈ range 1200, tenThousandPoolBudgetAt i) = 1339303548 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (1100+i)) = 109917484 := by
    decide
  change (∑ i ∈ range (1100+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_11,hb]

private lemma tenThousandPool_prefix_13 :
    (∑ i ∈ range 1300, tenThousandPoolBudgetAt i) = 1448915438 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (1200+i)) = 109611890 := by
    decide
  change (∑ i ∈ range (1200+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_12,hb]

private lemma tenThousandPool_prefix_14 :
    (∑ i ∈ range 1400, tenThousandPoolBudgetAt i) = 1558233307 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (1300+i)) = 109317869 := by
    decide
  change (∑ i ∈ range (1300+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_13,hb]

private lemma tenThousandPool_prefix_15 :
    (∑ i ∈ range 1500, tenThousandPoolBudgetAt i) = 1667248876 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (1400+i)) = 109015569 := by
    decide
  change (∑ i ∈ range (1400+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_14,hb]

private lemma tenThousandPool_prefix_16 :
    (∑ i ∈ range 1600, tenThousandPoolBudgetAt i) = 1775973643 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (1500+i)) = 108724767 := by
    decide
  change (∑ i ∈ range (1500+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_15,hb]

private lemma tenThousandPool_prefix_17 :
    (∑ i ∈ range 1700, tenThousandPoolBudgetAt i) = 1884399349 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (1600+i)) = 108425706 := by
    decide
  change (∑ i ∈ range (1600+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_16,hb]

private lemma tenThousandPool_prefix_18 :
    (∑ i ∈ range 1800, tenThousandPoolBudgetAt i) = 1992537408 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (1700+i)) = 108138059 := by
    decide
  change (∑ i ∈ range (1700+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_17,hb]

private lemma tenThousandPool_prefix_19 :
    (∑ i ∈ range 1900, tenThousandPoolBudgetAt i) = 2100379591 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (1800+i)) = 107842183 := by
    decide
  change (∑ i ∈ range (1800+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_18,hb]

private lemma tenThousandPool_prefix_20 :
    (∑ i ∈ range 2000, tenThousandPoolBudgetAt i) = 2207937245 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (1900+i)) = 107557654 := by
    decide
  change (∑ i ∈ range (1900+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_19,hb]

private lemma tenThousandPool_prefix_21 :
    (∑ i ∈ range 2100, tenThousandPoolBudgetAt i) = 2315202159 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (2000+i)) = 107264914 := by
    decide
  change (∑ i ∈ range (2000+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_20,hb]

private lemma tenThousandPool_prefix_22 :
    (∑ i ∈ range 2200, tenThousandPoolBudgetAt i) = 2422185599 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (2100+i)) = 106983440 := by
    decide
  change (∑ i ∈ range (2100+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_21,hb]

private lemma tenThousandPool_prefix_23 :
    (∑ i ∈ range 2300, tenThousandPoolBudgetAt i) = 2528879397 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (2200+i)) = 106693798 := by
    decide
  change (∑ i ∈ range (2200+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_22,hb]

private lemma tenThousandPool_prefix_24 :
    (∑ i ∈ range 2400, tenThousandPoolBudgetAt i) = 2635294731 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (2300+i)) = 106415334 := by
    decide
  change (∑ i ∈ range (2300+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_23,hb]

private lemma tenThousandPool_prefix_25 :
    (∑ i ∈ range 2500, tenThousandPoolBudgetAt i) = 2741428259 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (2400+i)) = 106133528 := by
    decide
  change (∑ i ∈ range (2400+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_24,hb]

private lemma tenThousandPool_prefix_26 :
    (∑ i ∈ range 2600, tenThousandPoolBudgetAt i) = 2847276691 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (2500+i)) = 105848432 := by
    decide
  change (∑ i ∈ range (2500+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_25,hb]

private lemma tenThousandPool_prefix_27 :
    (∑ i ∈ range 2700, tenThousandPoolBudgetAt i) = 2952851079 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (2600+i)) = 105574388 := by
    decide
  change (∑ i ∈ range (2600+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_26,hb]

private lemma tenThousandPool_prefix_28 :
    (∑ i ∈ range 2800, tenThousandPoolBudgetAt i) = 3058143323 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (2700+i)) = 105292244 := by
    decide
  change (∑ i ∈ range (2700+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_27,hb]

private lemma tenThousandPool_prefix_29 :
    (∑ i ∈ range 2900, tenThousandPoolBudgetAt i) = 3163164424 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (2800+i)) = 105021101 := by
    decide
  change (∑ i ∈ range (2800+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_28,hb]

private lemma tenThousandPool_prefix_30 :
    (∑ i ∈ range 3000, tenThousandPoolBudgetAt i) = 3267906313 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (2900+i)) = 104741889 := by
    decide
  change (∑ i ∈ range (2900+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_29,hb]

private lemma tenThousandPool_prefix_31 :
    (∑ i ∈ range 3100, tenThousandPoolBudgetAt i) = 3372379903 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (3000+i)) = 104473590 := by
    decide
  change (∑ i ∈ range (3000+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_30,hb]

private lemma tenThousandPool_prefix_32 :
    (∑ i ∈ range 3200, tenThousandPoolBudgetAt i) = 3476577150 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (3100+i)) = 104197247 := by
    decide
  change (∑ i ∈ range (3100+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_31,hb]

private lemma tenThousandPool_prefix_33 :
    (∑ i ∈ range 3300, tenThousandPoolBudgetAt i) = 3580508900 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (3200+i)) = 103931750 := by
    decide
  change (∑ i ∈ range (3200+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_32,hb]

private lemma tenThousandPool_prefix_34 :
    (∑ i ∈ range 3400, tenThousandPoolBudgetAt i) = 3684167142 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (3300+i)) = 103658242 := by
    decide
  change (∑ i ∈ range (3300+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_33,hb]

private lemma tenThousandPool_prefix_35 :
    (∑ i ∈ range 3500, tenThousandPoolBudgetAt i) = 3787562655 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (3400+i)) = 103395513 := by
    decide
  change (∑ i ∈ range (3400+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_34,hb]

private lemma tenThousandPool_prefix_36 :
    (∑ i ∈ range 3600, tenThousandPoolBudgetAt i) = 3890687442 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (3500+i)) = 103124787 := by
    decide
  change (∑ i ∈ range (3500+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_35,hb]

private lemma tenThousandPool_prefix_37 :
    (∑ i ∈ range 3700, tenThousandPoolBudgetAt i) = 3993552211 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (3600+i)) = 102864769 := by
    decide
  change (∑ i ∈ range (3600+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_36,hb]

private lemma tenThousandPool_prefix_38 :
    (∑ i ∈ range 3800, tenThousandPoolBudgetAt i) = 4096149002 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (3700+i)) = 102596791 := by
    decide
  change (∑ i ∈ range (3700+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_37,hb]

private lemma tenThousandPool_prefix_39 :
    (∑ i ∈ range 3900, tenThousandPoolBudgetAt i) = 4198488455 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (3800+i)) = 102339453 := by
    decide
  change (∑ i ∈ range (3800+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_38,hb]

private lemma tenThousandPool_prefix_40 :
    (∑ i ∈ range 4000, tenThousandPoolBudgetAt i) = 4300562633 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (3900+i)) = 102074178 := by
    decide
  change (∑ i ∈ range (3900+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_39,hb]

private lemma tenThousandPool_prefix_41 :
    (∑ i ∈ range 4100, tenThousandPoolBudgetAt i) = 4402382111 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (4000+i)) = 101819478 := by
    decide
  change (∑ i ∈ range (4000+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_40,hb]

private lemma tenThousandPool_prefix_42 :
    (∑ i ∈ range 4200, tenThousandPoolBudgetAt i) = 4503938970 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (4100+i)) = 101556859 := by
    decide
  change (∑ i ∈ range (4100+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_41,hb]

private lemma tenThousandPool_prefix_43 :
    (∑ i ∈ range 4300, tenThousandPoolBudgetAt i) = 4605243727 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (4200+i)) = 101304757 := by
    decide
  change (∑ i ∈ range (4200+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_42,hb]

private lemma tenThousandPool_prefix_44 :
    (∑ i ∈ range 4400, tenThousandPoolBudgetAt i) = 4706288491 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (4300+i)) = 101044764 := by
    decide
  change (∑ i ∈ range (4300+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_43,hb]

private lemma tenThousandPool_prefix_45 :
    (∑ i ∈ range 4500, tenThousandPoolBudgetAt i) = 4807083700 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (4400+i)) = 100795209 := by
    decide
  change (∑ i ∈ range (4400+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_44,hb]

private lemma tenThousandPool_prefix_46 :
    (∑ i ∈ range 4600, tenThousandPoolBudgetAt i) = 4907621499 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (4500+i)) = 100537799 := by
    decide
  change (∑ i ∈ range (4500+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_45,hb]

private lemma tenThousandPool_prefix_47 :
    (∑ i ∈ range 4700, tenThousandPoolBudgetAt i) = 5007912264 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (4600+i)) = 100290765 := by
    decide
  change (∑ i ∈ range (4600+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_46,hb]

private lemma tenThousandPool_prefix_48 :
    (∑ i ∈ range 4800, tenThousandPoolBudgetAt i) = 5107948174 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (4700+i)) = 100035910 := by
    decide
  change (∑ i ∈ range (4700+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_47,hb]

private lemma tenThousandPool_prefix_49 :
    (∑ i ∈ range 4900, tenThousandPoolBudgetAt i) = 5207739521 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (4800+i)) = 99791347 := by
    decide
  change (∑ i ∈ range (4800+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_48,hb]

private lemma tenThousandPool_prefix_50 :
    (∑ i ∈ range 5000, tenThousandPoolBudgetAt i) = 5307283015 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (4900+i)) = 99543494 := by
    decide
  change (∑ i ∈ range (4900+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_49,hb]

private lemma tenThousandPool_prefix_51 :
    (∑ i ∈ range 5100, tenThousandPoolBudgetAt i) = 5406575385 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (5000+i)) = 99292370 := by
    decide
  change (∑ i ∈ range (5000+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_50,hb]

private lemma tenThousandPool_prefix_52 :
    (∑ i ∈ range 5200, tenThousandPoolBudgetAt i) = 5505626852 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (5100+i)) = 99051467 := by
    decide
  change (∑ i ∈ range (5100+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_51,hb]

private lemma tenThousandPool_prefix_53 :
    (∑ i ∈ range 5300, tenThousandPoolBudgetAt i) = 5604429646 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (5200+i)) = 98802794 := by
    decide
  change (∑ i ∈ range (5200+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_52,hb]

private lemma tenThousandPool_prefix_54 :
    (∑ i ∈ range 5400, tenThousandPoolBudgetAt i) = 5702993930 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (5300+i)) = 98564284 := by
    decide
  change (∑ i ∈ range (5300+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_53,hb]

private lemma tenThousandPool_prefix_55 :
    (∑ i ∈ range 5500, tenThousandPoolBudgetAt i) = 5801311963 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (5400+i)) = 98318033 := by
    decide
  change (∑ i ∈ range (5400+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_54,hb]

private lemma tenThousandPool_prefix_56 :
    (∑ i ∈ range 5600, tenThousandPoolBudgetAt i) = 5899393835 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (5500+i)) = 98081872 := by
    decide
  change (∑ i ∈ range (5500+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_55,hb]

private lemma tenThousandPool_prefix_57 :
    (∑ i ∈ range 5700, tenThousandPoolBudgetAt i) = 5997231833 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (5600+i)) = 97837998 := by
    decide
  change (∑ i ∈ range (5600+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_56,hb]

private lemma tenThousandPool_prefix_58 :
    (∑ i ∈ range 5800, tenThousandPoolBudgetAt i) = 6094835990 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (5700+i)) = 97604157 := by
    decide
  change (∑ i ∈ range (5700+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_57,hb]

private lemma tenThousandPool_prefix_59 :
    (∑ i ∈ range 5900, tenThousandPoolBudgetAt i) = 6192198619 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (5800+i)) = 97362629 := by
    decide
  change (∑ i ∈ range (5800+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_58,hb]

private lemma tenThousandPool_prefix_60 :
    (∑ i ∈ range 6000, tenThousandPoolBudgetAt i) = 6289329690 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (5900+i)) = 97131071 := by
    decide
  change (∑ i ∈ range (5900+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_59,hb]

private lemma tenThousandPool_prefix_61 :
    (∑ i ∈ range 6100, tenThousandPoolBudgetAt i) = 6386221546 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (6000+i)) = 96891856 := by
    decide
  change (∑ i ∈ range (6000+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_60,hb]

private lemma tenThousandPool_prefix_62 :
    (∑ i ∈ range 6200, tenThousandPoolBudgetAt i) = 6482884093 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (6100+i)) = 96662547 := by
    decide
  change (∑ i ∈ range (6100+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_61,hb]

private lemma tenThousandPool_prefix_63 :
    (∑ i ∈ range 6300, tenThousandPoolBudgetAt i) = 6579309704 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (6200+i)) = 96425611 := by
    decide
  change (∑ i ∈ range (6200+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_62,hb]

private lemma tenThousandPool_prefix_64 :
    (∑ i ∈ range 6400, tenThousandPoolBudgetAt i) = 6675508236 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (6300+i)) = 96198532 := by
    decide
  change (∑ i ∈ range (6300+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_63,hb]

private lemma tenThousandPool_prefix_65 :
    (∑ i ∈ range 6500, tenThousandPoolBudgetAt i) = 6771472070 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (6400+i)) = 95963834 := by
    decide
  change (∑ i ∈ range (6400+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_64,hb]

private lemma tenThousandPool_prefix_66 :
    (∑ i ∈ range 6600, tenThousandPoolBudgetAt i) = 6867211012 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (6500+i)) = 95738942 := by
    decide
  change (∑ i ∈ range (6500+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_65,hb]

private lemma tenThousandPool_prefix_67 :
    (∑ i ∈ range 6700, tenThousandPoolBudgetAt i) = 6962717470 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (6600+i)) = 95506458 := by
    decide
  change (∑ i ∈ range (6600+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_66,hb]

private lemma tenThousandPool_prefix_68 :
    (∑ i ∈ range 6800, tenThousandPoolBudgetAt i) = 7058001188 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (6700+i)) = 95283718 := by
    decide
  change (∑ i ∈ range (6700+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_67,hb]

private lemma tenThousandPool_prefix_69 :
    (∑ i ∈ range 6900, tenThousandPoolBudgetAt i) = 7153054614 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (6800+i)) = 95053426 := by
    decide
  change (∑ i ∈ range (6800+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_68,hb]

private lemma tenThousandPool_prefix_70 :
    (∑ i ∈ range 7000, tenThousandPoolBudgetAt i) = 7247887428 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (6900+i)) = 94832814 := by
    decide
  change (∑ i ∈ range (6900+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_69,hb]

private lemma tenThousandPool_prefix_71 :
    (∑ i ∈ range 7100, tenThousandPoolBudgetAt i) = 7342492097 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (7000+i)) = 94604669 := by
    decide
  change (∑ i ∈ range (7000+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_70,hb]

private lemma tenThousandPool_prefix_72 :
    (∑ i ∈ range 7200, tenThousandPoolBudgetAt i) = 7436878251 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (7100+i)) = 94386154 := by
    decide
  change (∑ i ∈ range (7100+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_71,hb]

private lemma tenThousandPool_prefix_73 :
    (∑ i ∈ range 7300, tenThousandPoolBudgetAt i) = 7531038380 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (7200+i)) = 94160129 := by
    decide
  change (∑ i ∈ range (7200+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_72,hb]

private lemma tenThousandPool_prefix_74 :
    (∑ i ∈ range 7400, tenThousandPoolBudgetAt i) = 7624982059 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (7300+i)) = 93943679 := by
    decide
  change (∑ i ∈ range (7300+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_73,hb]

private lemma tenThousandPool_prefix_75 :
    (∑ i ∈ range 7500, tenThousandPoolBudgetAt i) = 7718706049 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (7400+i)) = 93723990 := by
    decide
  change (∑ i ∈ range (7400+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_74,hb]

private lemma tenThousandPool_prefix_76 :
    (∑ i ∈ range 7600, tenThousandPoolBudgetAt i) = 7812207140 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (7500+i)) = 93501091 := by
    decide
  change (∑ i ∈ range (7500+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_75,hb]

private lemma tenThousandPool_prefix_77 :
    (∑ i ∈ range 7700, tenThousandPoolBudgetAt i) = 7905494831 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (7600+i)) = 93287691 := by
    decide
  change (∑ i ∈ range (7600+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_76,hb]

private lemma tenThousandPool_prefix_78 :
    (∑ i ∈ range 7800, tenThousandPoolBudgetAt i) = 7998561668 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (7700+i)) = 93066837 := by
    decide
  change (∑ i ∈ range (7700+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_77,hb]

private lemma tenThousandPool_prefix_79 :
    (∑ i ∈ range 7900, tenThousandPoolBudgetAt i) = 8091417100 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (7800+i)) = 92855432 := by
    decide
  change (∑ i ∈ range (7800+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_78,hb]

private lemma tenThousandPool_prefix_80 :
    (∑ i ∈ range 8000, tenThousandPoolBudgetAt i) = 8184053703 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (7900+i)) = 92636603 := by
    decide
  change (∑ i ∈ range (7900+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_79,hb]

private lemma tenThousandPool_prefix_81 :
    (∑ i ∈ range 8100, tenThousandPoolBudgetAt i) = 8276480857 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (8000+i)) = 92427154 := by
    decide
  change (∑ i ∈ range (8000+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_80,hb]

private lemma tenThousandPool_prefix_82 :
    (∑ i ∈ range 8200, tenThousandPoolBudgetAt i) = 8368691179 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (8100+i)) = 92210322 := by
    decide
  change (∑ i ∈ range (8100+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_81,hb]

private lemma tenThousandPool_prefix_83 :
    (∑ i ∈ range 8300, tenThousandPoolBudgetAt i) = 8460693998 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (8200+i)) = 92002819 := by
    decide
  change (∑ i ∈ range (8200+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_82,hb]

private lemma tenThousandPool_prefix_84 :
    (∑ i ∈ range 8400, tenThousandPoolBudgetAt i) = 8552481940 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (8300+i)) = 91787942 := by
    decide
  change (∑ i ∈ range (8300+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_83,hb]

private lemma tenThousandPool_prefix_85 :
    (∑ i ∈ range 8500, tenThousandPoolBudgetAt i) = 8644064296 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (8400+i)) = 91582356 := by
    decide
  change (∑ i ∈ range (8400+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_84,hb]

private lemma tenThousandPool_prefix_86 :
    (∑ i ∈ range 8600, tenThousandPoolBudgetAt i) = 8735433725 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (8500+i)) = 91369429 := by
    decide
  change (∑ i ∈ range (8500+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_85,hb]

private lemma tenThousandPool_prefix_87 :
    (∑ i ∈ range 8700, tenThousandPoolBudgetAt i) = 8826599449 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (8600+i)) = 91165724 := by
    decide
  change (∑ i ∈ range (8600+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_86,hb]

private lemma tenThousandPool_prefix_88 :
    (∑ i ∈ range 8800, tenThousandPoolBudgetAt i) = 8917554151 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (8700+i)) = 90954702 := by
    decide
  change (∑ i ∈ range (8700+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_87,hb]

private lemma tenThousandPool_prefix_89 :
    (∑ i ∈ range 8900, tenThousandPoolBudgetAt i) = 9008307012 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (8800+i)) = 90752861 := by
    decide
  change (∑ i ∈ range (8800+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_88,hb]

private lemma tenThousandPool_prefix_90 :
    (∑ i ∈ range 9000, tenThousandPoolBudgetAt i) = 9098850742 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (8900+i)) = 90543730 := by
    decide
  change (∑ i ∈ range (8900+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_89,hb]

private lemma tenThousandPool_prefix_91 :
    (∑ i ∈ range 9100, tenThousandPoolBudgetAt i) = 9189194468 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (9000+i)) = 90343726 := by
    decide
  change (∑ i ∈ range (9000+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_90,hb]

private lemma tenThousandPool_prefix_92 :
    (∑ i ∈ range 9200, tenThousandPoolBudgetAt i) = 9279330915 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (9100+i)) = 90136447 := by
    decide
  change (∑ i ∈ range (9100+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_91,hb]

private lemma tenThousandPool_prefix_93 :
    (∑ i ∈ range 9300, tenThousandPoolBudgetAt i) = 9369269171 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (9200+i)) = 89938256 := by
    decide
  change (∑ i ∈ range (9200+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_92,hb]

private lemma tenThousandPool_prefix_94 :
    (∑ i ∈ range 9400, tenThousandPoolBudgetAt i) = 9459001989 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (9300+i)) = 89732818 := by
    decide
  change (∑ i ∈ range (9300+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_93,hb]

private lemma tenThousandPool_prefix_95 :
    (∑ i ∈ range 9500, tenThousandPoolBudgetAt i) = 9548538405 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (9400+i)) = 89536416 := by
    decide
  change (∑ i ∈ range (9400+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_94,hb]

private lemma tenThousandPool_prefix_96 :
    (∑ i ∈ range 9600, tenThousandPoolBudgetAt i) = 9637871196 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (9500+i)) = 89332791 := by
    decide
  change (∑ i ∈ range (9500+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_95,hb]

private lemma tenThousandPool_prefix_97 :
    (∑ i ∈ range 9700, tenThousandPoolBudgetAt i) = 9727009347 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (9600+i)) = 89138151 := by
    decide
  change (∑ i ∈ range (9600+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_96,hb]

private lemma tenThousandPool_prefix_98 :
    (∑ i ∈ range 9800, tenThousandPoolBudgetAt i) = 9815945655 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (9700+i)) = 88936308 := by
    decide
  change (∑ i ∈ range (9700+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_97,hb]

private lemma tenThousandPool_prefix_99 :
    (∑ i ∈ range 9900, tenThousandPoolBudgetAt i) = 9904689061 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (9800+i)) = 88743406 := by
    decide
  change (∑ i ∈ range (9800+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_98,hb]

private lemma tenThousandPool_prefix_100 :
    (∑ i ∈ range 10000, tenThousandPoolBudgetAt i) = 9993236399 := by
  have hb : (∑ i ∈ range 100, tenThousandPoolBudgetAt (9900+i)) = 88547338 := by
    decide
  change (∑ i ∈ range (9900+100), tenThousandPoolBudgetAt i) = _
  rw [sum_range_add,tenThousandPool_prefix_99,hb]

lemma tenThousandPool_budgetNat_sum :
    (∑ i : Fin 10000, tenThousandPoolBudgetNat i) = 9993236399 := by
  change (∑ i : Fin 10000, tenThousandPoolBudgetAt i.val) = _
  rw [Fin.sum_univ_eq_sum_range]
  exact tenThousandPool_prefix_100

lemma tenThousandPool_budget_sum :
    (∑ i : Fin 10000, tenThousandPoolBudget i) = 9993236399/10000000000 := by
  unfold tenThousandPoolBudget
  rw [← sum_div,← Nat.cast_sum,tenThousandPool_budgetNat_sum]
  norm_num

lemma eventually_all_ten_thousand_pool_bands :
    ∀ᶠ m : ℕ in atTop, ∀ i : Fin 10000, ∀ X : ℕ,
      independentN 40000020 m ≤ X → X ≤ independentN 40000021 m →
      Real.log (X : ℝ)*(∑ c ∈ widePairPool 10000000 m,
        ((hyperbolicPrimePairPool c (X/c)
          (2^(128*tenThousandPoolEndpoint i.val*m))
          (2^(128*tenThousandPoolEndpoint (i.val+1)*m))).card : ℝ)) ≤
            tenThousandPoolBudget i*(X : ℝ)*poolTotientMass (widePairPool 10000000 m) := by
  rw [Filter.eventually_all]
  intro i
  obtain ⟨hu,huv,hv,hu3,hb,hbt,hl,hlevel,hscale,hrough⟩ := tenThousandPool_band_parameters i
  exact eventually_pool_band_rejection_bound _ _ _ _ hu huv hv hu3 hb hbt hl hlevel hscale hrough _
    (tenThousandPool_band_limit i)

end Erdos821.AnalyticSieve
