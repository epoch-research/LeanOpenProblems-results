import Submission.Rec
open Finset BigOperators Nat

def Gnat (m : ℕ) : ℕ := (2*m).choose m * (3*m+1).choose m
noncomputable def gq (m : ℕ) : ℚ := (-1:ℚ)^m * (Gnat m : ℚ)

theorem hGrec (m : ℕ) :
    ((m:ℚ)+1)^2*(2*(m:ℚ)+3)*(Gnat (m+1):ℚ) = 3*(2*(m:ℚ)+1)*(3*(m:ℚ)+2)*(3*(m:ℚ)+4)*(Gnat m:ℚ) := by
  have hm : (Nat.factorial m : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h2m1 : (Nat.factorial (2*m+1) : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hmp1 : ((m:ℚ)+1) ≠ 0 := by positivity
  have fA : ((2*m+2).factorial:ℚ)=(2*(m:ℚ)+2)*(2*(m:ℚ)+1)*((2*m).factorial) := by
    rw [show 2*m+2=(2*m+1)+1 from by ring, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have fB : ((m+1).factorial:ℚ)=((m:ℚ)+1)*(m.factorial) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have fC : ((3*m+4).factorial:ℚ)=(3*(m:ℚ)+4)*(3*(m:ℚ)+3)*(3*(m:ℚ)+2)*((3*m+1).factorial) := by
    rw [show 3*m+4=(3*m+3)+1 from by ring, Nat.factorial_succ, show 3*m+3=(3*m+2)+1 from by ring, Nat.factorial_succ, show 3*m+2=(3*m+1)+1 from by ring, Nat.factorial_succ]; push_cast; ring
  have fD : ((2*m+3).factorial:ℚ)=(2*(m:ℚ)+3)*(2*(m:ℚ)+2)*((2*m+1).factorial) := by
    rw [show 2*m+3=(2*m+2)+1 from by ring, Nat.factorial_succ, show 2*m+2=(2*m+1)+1 from by ring, Nat.factorial_succ]; push_cast; ring
  simp only [Gnat]
  push_cast
  rw [Nat.cast_choose ℚ (show m ≤ 2*m by omega), Nat.cast_choose ℚ (show m ≤ 3*m+1 by omega),
      Nat.cast_choose ℚ (show m+1 ≤ 2*(m+1) by omega), Nat.cast_choose ℚ (show m+1 ≤ 3*(m+1)+1 by omega)]
  rw [show 2*m-m = m from by omega, show 3*m+1-m = 2*m+1 from by omega,
      show 2*(m+1) = 2*m+2 from by ring, show 2*m+2-(m+1) = m+1 from by omega,
      show 3*(m+1)+1 = 3*m+4 from by ring, show 3*m+4-(m+1) = 2*m+3 from by omega]
  rw [fA, fB, fC, fD]
  field_simp

noncomputable def AA (m:ℕ):ℚ := -(cc0 (↑(2*m+1)) * cc0 (↑(2*m+2)) * cc1 (↑(2*m+3)))
noncomputable def BB (m:ℕ):ℚ := cc1 (↑(2*m+1)) * cc1 (↑(2*m+2)) * cc1 (↑(2*m+3)) - cc2 (↑(2*m+1)) * cc0 (↑(2*m+2)) * cc1 (↑(2*m+3)) - cc1 (↑(2*m+1)) * cc2 (↑(2*m+2)) * cc0 (↑(2*m+3))
noncomputable def CC (m:ℕ):ℚ := -(cc1 (↑(2*m+1)) * cc2 (↑(2*m+2)) * cc2 (↑(2*m+3)))

theorem aaq1 : aaq 1 = 1 := by
  rw [aaq]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Fq]
theorem aaq2 : aaq 2 = 1 := by
  rw [aaq]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Fq]
theorem aaq3 : aaq 3 = -8 := by
  rw [aaq]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Fq]

theorem nrec1 : cc0 ((1:ℕ):ℚ) * aaq 1 + cc1 ((1:ℕ):ℚ) * aaq 2 + cc2 ((1:ℕ):ℚ) * aaq 3 = 0 := by
  rw [aaq1, aaq2, aaq3]; simp only [cc0, cc1, cc2]; norm_num

theorem nrec_ge1 (n:ℕ) (hn:1≤n) :
    cc0 (n:ℚ)*aaq n + cc1 (n:ℚ)*aaq (n+1) + cc2 (n:ℚ)*aaq (n+2) = 0 := by
  rcases lt_or_ge n 2 with h | h
  · interval_cases n
    exact nrec1
  · exact nrec n h

theorem Rrec (m:ℕ) : AA m * aaq (2*m+1) + BB m * aaq (2*m+3) + CC m * aaq (2*m+5) = 0 := by
  have E0 := nrec_ge1 (2*m+1) (by omega)
  have E1 := nrec_ge1 (2*m+2) (by omega)
  have E2 := nrec_ge1 (2*m+3) (by omega)
  rw [show 2*m+1+1=2*m+2 from by ring, show 2*m+1+2=2*m+3 from by ring] at E0
  rw [show 2*m+2+1=2*m+3 from by ring, show 2*m+2+2=2*m+4 from by ring] at E1
  rw [show 2*m+3+1=2*m+4 from by ring, show 2*m+3+2=2*m+5 from by ring] at E2
  simp only [AA, BB, CC]
  linear_combination (cc1 (↑(2*m+1)) * cc1 (↑(2*m+3))) * E1 - (cc0 (↑(2*m+2)) * cc1 (↑(2*m+3))) * E0 - (cc2 (↑(2*m+2)) * cc1 (↑(2*m+1))) * E2

set_option maxHeartbeats 4000000 in
theorem hGid (m:ℕ) : AA m * (Gnat m:ℚ) - BB m * (Gnat (m+1):ℚ) + CC m * (Gnat (m+2):ℚ) = 0 := by
  have hr0 := hGrec m
  have hr1 := hGrec (m+1)
  rw [show m+1+1 = m+2 from rfl] at hr1
  push_cast at hr1
  have hP : (((m:ℚ)+1)^2*(2*(m:ℚ)+3)) * (((m:ℚ)+2)^2*(2*(m:ℚ)+5)) ≠ 0 := by positivity
  have hcl : (((m:ℚ)+1)^2*(2*(m:ℚ)+3)) * (((m:ℚ)+2)^2*(2*(m:ℚ)+5)) * (AA m * (Gnat m:ℚ) - BB m * (Gnat (m+1):ℚ) + CC m * (Gnat (m+2):ℚ)) = 0 := by
    simp only [AA, BB, CC, cc0, cc1, cc2]
    push_cast
    linear_combination ((-1146617856)*(m:ℚ)^19 + (-28474343424)*(m:ℚ)^18 + (-331133681664)*(m:ℚ)^17 + (-2396118122496)*(m:ℚ)^16 + (-12089996181504)*(m:ℚ)^15 + (-45170402181120)*(m:ℚ)^14 + (-129508542554112)*(m:ℚ)^13 + (-291348258582528)*(m:ℚ)^12 + (-521333734053888)*(m:ℚ)^11 + (-747532339236864)*(m:ℚ)^10 + (-860923362030336)*(m:ℚ)^9 + (-794437996953600)*(m:ℚ)^8 + (-582963271929216)*(m:ℚ)^7 + (-335525377024512)*(m:ℚ)^6 + (-148109323373568)*(m:ℚ)^5 + (-48373417460736)*(m:ℚ)^4 + (-11004553040256)*(m:ℚ)^3 + (-1555425400320)*(m:ℚ)^2 + (-102745843200)*(m:ℚ)) * hr0 + ((42467328)*(m:ℚ)^19 + (1054605312)*(m:ℚ)^18 + (12276006912)*(m:ℚ)^17 + (89042780160)*(m:ℚ)^16 + (451239051264)*(m:ℚ)^15 + (1697667465216)*(m:ℚ)^14 + (4917797462016)*(m:ℚ)^13 + (11225614036992)*(m:ℚ)^12 + (20491840026624)*(m:ℚ)^11 + (30180357642240)*(m:ℚ)^10 + (36012629971200)*(m:ℚ)^9 + (34816955661312)*(m:ℚ)^8 + (27161531303040)*(m:ℚ)^7 + (16948802339328)*(m:ℚ)^6 + (8336190147072)*(m:ℚ)^5 + (3158052235776)*(m:ℚ)^4 + (888553079424)*(m:ℚ)^3 + (174744843264)*(m:ℚ)^2 + (21423813120)*(m:ℚ) + (1231718400)) * hr1
  exact (mul_eq_zero.mp hcl).resolve_left hP

theorem Rg (m:ℕ) : AA m * gq m + BB m * gq (m+1) + CC m * gq (m+2) = 0 := by
  have key := hGid m
  have hs1 : (-1:ℚ)^(m+1) = (-1)^m * (-1) := pow_succ (-1) m
  have hs2 : (-1:ℚ)^(m+2) = (-1)^m := by rw [show m+2 = m+1+1 from rfl, pow_succ, pow_succ]; ring
  simp only [gq]
  rw [hs1, hs2]
  linear_combination ((-1:ℚ)^m) * key

theorem CCne (m:ℕ) : CC m ≠ 0 := by
  have h1 : (0:ℚ) < (↑(2*m+1):ℚ) := by positivity
  have h2 : (0:ℚ) < (↑(2*m+2):ℚ) := by positivity
  have h3 : (0:ℚ) < (↑(2*m+3):ℚ) := by positivity
  have hc1 : cc1 (↑(2*m+1):ℚ) ≠ 0 := by
    have hcube : (0:ℚ) < 6*(↑(2*m+1):ℚ)^3+12*(↑(2*m+1))^2+5*(↑(2*m+1))+1 := by positivity
    have hpos := mul_pos (mul_pos (by norm_num : (0:ℚ)<6) h1) hcube
    have : cc1 (↑(2*m+1):ℚ) < 0 := by simp only [cc1]; nlinarith [hpos]
    linarith
  have hc2 : cc2 (↑(2*m+2):ℚ) ≠ 0 := by
    have hq : (0:ℚ) < 3*(↑(2*m+2):ℚ)^2-2*(↑(2*m+2))+1 := by nlinarith [sq_nonneg (3*(↑(2*m+2):ℚ)-1)]
    have hpos : (0:ℚ) < (↑(2*m+2):ℚ)^2*((↑(2*m+2):ℚ)+2)^2*(3*(↑(2*m+2):ℚ)^2-2*(↑(2*m+2))+1) :=
      mul_pos (mul_pos (by positivity) (by positivity)) hq
    have : cc2 (↑(2*m+2):ℚ) < 0 := by simp only [cc2]; nlinarith [hpos]
    linarith
  have hc3 : cc2 (↑(2*m+3):ℚ) ≠ 0 := by
    have hq : (0:ℚ) < 3*(↑(2*m+3):ℚ)^2-2*(↑(2*m+3))+1 := by nlinarith [sq_nonneg (3*(↑(2*m+3):ℚ)-1)]
    have hpos : (0:ℚ) < (↑(2*m+3):ℚ)^2*((↑(2*m+3):ℚ)+2)^2*(3*(↑(2*m+3):ℚ)^2-2*(↑(2*m+3))+1) :=
      mul_pos (mul_pos (by positivity) (by positivity)) hq
    have : cc2 (↑(2*m+3):ℚ) < 0 := by simp only [cc2]; nlinarith [hpos]
    linarith
  simp only [CC, neg_ne_zero]
  exact mul_ne_zero (mul_ne_zero hc1 hc2) hc3

theorem gq0 : gq 0 = 1 := by norm_num [gq, Gnat]
theorem gq1 : gq 1 = -8 := by norm_num [gq, Gnat, Nat.choose]

theorem closed_pair : ∀ m, aaq (2*m+1) = gq m ∧ aaq (2*(m+1)+1) = gq (m+1) := by
  intro m
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · show aaq 1 = gq 0; rw [aaq1, gq0]
    · show aaq 3 = gq 1; rw [aaq3, gq1]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have h2' : aaq (2*k+3) = gq (k+1) := by rw [show 2*k+3 = 2*(k+1)+1 from by ring]; exact h2
    refine ⟨?_, ?_⟩
    · rw [show 2*(k+1)+1 = 2*k+3 from by ring]; exact h2'
    · have hR := Rrec k
      have hG := Rg k
      have hCne := CCne k
      have e : CC k * aaq (2*k+5) = CC k * gq (k+2) := by
        rw [h1, h2'] at hR
        linear_combination hR - hG
      rw [show 2*(k+1+1)+1 = 2*k+5 from by ring]
      exact mul_left_cancel₀ hCne e

theorem closedform (m:ℕ) : aaq (2*m+1) = gq m := (closed_pair m).1
