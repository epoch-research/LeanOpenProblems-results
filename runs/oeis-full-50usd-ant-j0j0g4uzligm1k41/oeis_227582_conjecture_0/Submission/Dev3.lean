import FormalConjectures.Util.ProblemImports
open Real
noncomputable def s3 (x : ℝ) : ℝ := 1/(2*x) - 1/(12*x^2) + 1/(120*x^4)
noncomputable def s4 (x : ℝ) : ℝ := s3 x - 1/(252*x^6)
noncomputable def sden (N : ℝ) : ℝ := (N+1)*(2*N-1)
noncomputable def LTlo (N : ℝ) : ℝ := 2*((N-1)/sden N + ((N-1)/sden N)^3/3)
noncomputable def LThi (N : ℝ) : ℝ := LTlo N + (N-1)^5/(2*N^2*(N^2+N-1)*(sden N)^3)
noncomputable def psiMlo (N : ℝ) : ℝ := 1/(2*(N^2+N-1)) - 1/(12*(N^2+N-1)^2)
noncomputable def Dhi (N : ℝ) : ℝ := 2*s3 N - psiMlo N - LTlo N
noncomputable def Dlo (N : ℝ) : ℝ := 2*s4 N - s3 (N^2+N-1) - LThi N

lemma ratI5 (N : ℝ) (hN : 1 ≤ N) : ((6*N^2+6*N+(-5))/5) * Dhi N ≤ 1 := by
  obtain ⟨e, rfl⟩ : ∃ e, N = 1 + e := ⟨N-1, by ring⟩
  have he : 0 ≤ e := by linarith
  rw [← sub_nonneg]
  have hid : 1 - ((6*(1+e)^2+6*(1+e)+(-5))/5) * Dhi (1+e) = ((944) + (15240)*e + (108524)*e^2 + (450082)*e^3 + (1208830)*e^4 + (2211299)*e^5 + (2820338)*e^6 + (2523110)*e^7 + (1569534)*e^8 + (661856)*e^9 + (179728)*e^10 + (28268)*e^11 + (1952)*e^12) / (300*(e + 1)^4*(e + 2)^3*(2*e + 1)^3*(e^2 + 3*e + 1)^2) := by
    simp only [Dhi, s3, psiMlo, LTlo, sden]
    rw [show ((1:ℝ)+e)^2+(1+e)-1 = e^2+3*e+1 from by ring,
        show (1:ℝ)+e+1 = e+2 from by ring,
        show (2:ℝ)*(1+e)-1 = 2*e+1 from by ring]
    have q1 : (1:ℝ)+e ≠ 0 := by positivity
    have q2 : (e:ℝ)+2 ≠ 0 := by positivity
    have q3 : (2:ℝ)*e+1 ≠ 0 := by positivity
    have q4 : (e:ℝ)^2+3*e+1 ≠ 0 := by positivity
    field_simp
    ring
  rw [hid]
  positivity

lemma ratII5 (N : ℝ) (hN : 1 ≤ N) : 1 < ((6*N^2+6*N+(-5))/5 + 1) * Dlo N := by
  obtain ⟨e, rfl⟩ : ∃ e, N = 1 + e := ⟨N-1, by ring⟩
  have he : 0 ≤ e := by linarith
  rw [← sub_pos]
  have hid : ((6*(1+e)^2+6*(1+e)+(-5))/5 + 1) * Dlo (1+e) - 1 = ((8) + (996)*e + (15302)*e^2 + (115115)*e^3 + (539334)*e^4 + (1729919)*e^5 + (3970228)*e^6 + (6658089)*e^7 + (8231758)*e^8 + (7519367)*e^9 + (5066430)*e^10 + (2509178)*e^11 + (909860)*e^12 + (240144)*e^13 + (45116)*e^14 + (5544)*e^15 + (336)*e^16) / (2100*(e + 1)^5*(e + 2)^2*(2*e + 1)^3*(e^2 + 3*e + 1)^4) := by
    simp only [Dlo, s4, s3, LThi, LTlo, sden]
    rw [show ((1:ℝ)+e)^2+(1+e)-1 = e^2+3*e+1 from by ring,
        show (1:ℝ)+e+1 = e+2 from by ring,
        show (2:ℝ)*(1+e)-1 = 2*e+1 from by ring]
    have q1 : (1:ℝ)+e ≠ 0 := by positivity
    have q2 : (e:ℝ)+2 ≠ 0 := by positivity
    have q3 : (2:ℝ)*e+1 ≠ 0 := by positivity
    have q4 : (e:ℝ)^2+3*e+1 ≠ 0 := by positivity
    field_simp
    ring
  rw [hid]
  positivity

lemma ratI2 (N : ℝ) (hN : 1 ≤ N) : ((6*N^2+6*N+(-2))/5) * Dhi N ≤ 1 := by
  obtain ⟨e, rfl⟩ : ∃ e, N = 1 + e := ⟨N-1, by ring⟩
  have he : 0 ≤ e := by linarith
  rw [← sub_nonneg]
  have hid : 1 - ((6*(1+e)^2+6*(1+e)+(-2))/5) * Dhi (1+e) = ((160) + (2688)*e + (19624)*e^2 + (82748)*e^3 + (224936)*e^4 + (415375)*e^5 + (533815)*e^6 + (480367)*e^7 + (300054)*e^8 + (126856)*e^9 + (34502)*e^10 + (5434)*e^11 + (376)*e^12) / (150*(e + 1)^4*(e + 2)^3*(2*e + 1)^3*(e^2 + 3*e + 1)^2) := by
    simp only [Dhi, s3, psiMlo, LTlo, sden]
    rw [show ((1:ℝ)+e)^2+(1+e)-1 = e^2+3*e+1 from by ring,
        show (1:ℝ)+e+1 = e+2 from by ring,
        show (2:ℝ)*(1+e)-1 = 2*e+1 from by ring]
    have q1 : (1:ℝ)+e ≠ 0 := by positivity
    have q2 : (e:ℝ)+2 ≠ 0 := by positivity
    have q3 : (2:ℝ)*e+1 ≠ 0 := by positivity
    have q4 : (e:ℝ)^2+3*e+1 ≠ 0 := by positivity
    field_simp
    ring
  rw [hid]
  positivity

lemma ratII2 (N : ℝ) (hN : 1 ≤ N) : 1 < ((6*N^2+6*N+(-2))/5 + 1) * Dlo N := by
  obtain ⟨e, rfl⟩ : ∃ e, N = 1 + e := ⟨N-1, by ring⟩
  have he : 0 ≤ e := by linarith
  rw [← sub_pos]
  have hid : ((6*(1+e)^2+6*(1+e)+(-2))/5 + 1) * Dlo (1+e) - 1 = ((8440) + (206628)*e + (2310602)*e^2 + (15720079)*e^3 + (72974164)*e^4 + (245417429)*e^5 + (619334522)*e^6 + (1198351651)*e^7 + (1801097980)*e^8 + (2117500561)*e^9 + (1951535468)*e^10 + (1406611604)*e^11 + (787215628)*e^12 + (337615036)*e^13 + (108597464)*e^14 + (25304604)*e^15 + (4026976)*e^16 + (391104)*e^17 + (17472)*e^18) / (4200*(e + 1)^6*(e + 2)^3*(2*e + 1)^3*(e^2 + 3*e + 1)^4) := by
    simp only [Dlo, s4, s3, LThi, LTlo, sden]
    rw [show ((1:ℝ)+e)^2+(1+e)-1 = e^2+3*e+1 from by ring,
        show (1:ℝ)+e+1 = e+2 from by ring,
        show (2:ℝ)*(1+e)-1 = 2*e+1 from by ring]
    have q1 : (1:ℝ)+e ≠ 0 := by positivity
    have q2 : (e:ℝ)+2 ≠ 0 := by positivity
    have q3 : (2:ℝ)*e+1 ≠ 0 := by positivity
    have q4 : (e:ℝ)^2+3*e+1 ≠ 0 := by positivity
    field_simp
    ring
  rw [hid]
  positivity

lemma ratI1 (N : ℝ) (hN : 1 ≤ N) : ((6*N^2+6*N+(-1))/5) * Dhi N ≤ 1 := by
  obtain ⟨e, rfl⟩ : ∃ e, N = 1 + e := ⟨N-1, by ring⟩
  have he : 0 ≤ e := by linarith
  rw [← sub_nonneg]
  have hid : 1 - ((6*(1+e)^2+6*(1+e)+(-1))/5) * Dhi (1+e) = ((112) + (2088)*e + (16156)*e^2 + (70634)*e^3 + (196886)*e^4 + (370567)*e^5 + (483394)*e^6 + (439942)*e^7 + (276966)*e^8 + (117664)*e^9 + (32096)*e^10 + (5068)*e^11 + (352)*e^12) / (300*(e + 1)^4*(e + 2)^3*(2*e + 1)^3*(e^2 + 3*e + 1)^2) := by
    simp only [Dhi, s3, psiMlo, LTlo, sden]
    rw [show ((1:ℝ)+e)^2+(1+e)-1 = e^2+3*e+1 from by ring,
        show (1:ℝ)+e+1 = e+2 from by ring,
        show (2:ℝ)*(1+e)-1 = 2*e+1 from by ring]
    have q1 : (1:ℝ)+e ≠ 0 := by positivity
    have q2 : (e:ℝ)+2 ≠ 0 := by positivity
    have q3 : (2:ℝ)*e+1 ≠ 0 := by positivity
    have q4 : (e:ℝ)^2+3*e+1 ≠ 0 := by positivity
    field_simp
    ring
  rw [hid]
  positivity

lemma ratII1 (N : ℝ) (hN : 1 ≤ N) : 1 < ((6*N^2+6*N+(-1))/5 + 1) * Dlo N := by
  obtain ⟨e, rfl⟩ : ∃ e, N = 1 + e := ⟨N-1, by ring⟩
  have he : 0 ≤ e := by linarith
  rw [← sub_pos]
  have hid : ((6*(1+e)^2+6*(1+e)+(-1))/5 + 1) * Dlo (1+e) - 1 = ((16864) + (411240)*e + (4587604)*e^2 + (31163026)*e^3 + (144509013)*e^4 + (485641903)*e^5 + (1224999497)*e^6 + (2369746521)*e^7 + (3561787949)*e^8 + (4188609025)*e^9 + (3862148217)*e^10 + (2785486195)*e^11 + (1560017572)*e^12 + (669511026)*e^13 + (215474404)*e^14 + (50222628)*e^15 + (7991532)*e^16 + (775656)*e^17 + (34608)*e^18) / (6300*(e + 1)^6*(e + 2)^3*(2*e + 1)^3*(e^2 + 3*e + 1)^4) := by
    simp only [Dlo, s4, s3, LThi, LTlo, sden]
    rw [show ((1:ℝ)+e)^2+(1+e)-1 = e^2+3*e+1 from by ring,
        show (1:ℝ)+e+1 = e+2 from by ring,
        show (2:ℝ)*(1+e)-1 = 2*e+1 from by ring]
    have q1 : (1:ℝ)+e ≠ 0 := by positivity
    have q2 : (e:ℝ)+2 ≠ 0 := by positivity
    have q3 : (2:ℝ)*e+1 ≠ 0 := by positivity
    have q4 : (e:ℝ)^2+3*e+1 ≠ 0 := by positivity
    field_simp
    ring
  rw [hid]
  positivity


lemma artanh_lower (N : ℝ) (hN : 1 ≤ N) :
    LTlo N ≤ Real.log (N^2+N-1) - 2*Real.log N := by
  have hN0 : 0 < N := by linarith
  have hsd : 0 < sden N := by simp only [sden]; nlinarith
  have hs0 : 0 ≤ (N-1)/sden N := div_nonneg (by linarith) hsd.le
  have hs1 : (N-1)/sden N < 1 := by
    rw [div_lt_one hsd]; simp only [sden]; nlinarith
  have hM : 0 < N^2+N-1 := by nlinarith
  have hd : (1:ℝ) - (N-1)/sden N ≠ 0 := by linarith
  have hN2 : (N:ℝ)^2 ≠ 0 := by positivity
  have hratio : (1 + (N-1)/sden N)/(1 - (N-1)/sden N) = (N^2+N-1)/N^2 := by
    rw [div_eq_div_iff hd hN2]; field_simp [hsd.ne']; rw [sden]; ring
  have hlog := Real.sum_range_le_log_div hs0 hs1 2
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at hlog
  rw [hratio, Real.log_div (ne_of_gt hM) hN2, Real.log_pow] at hlog
  simp only [LTlo]
  nlinarith [hlog]

lemma artanh_upper (N : ℝ) (hN : 1 ≤ N) :
    Real.log (N^2+N-1) - 2*Real.log N ≤ LThi N := by
  have hN0 : 0 < N := by linarith
  have hsd : 0 < sden N := by simp only [sden]; nlinarith
  have hMne : (N:ℝ)^2+N-1 ≠ 0 := by nlinarith
  have hs0 : 0 ≤ (N-1)/sden N := div_nonneg (by linarith) hsd.le
  have hs1 : (N-1)/sden N < 1 := by
    rw [div_lt_one hsd]; simp only [sden]; nlinarith
  have hM : 0 < N^2+N-1 := by nlinarith
  have hd : (1:ℝ) - (N-1)/sden N ≠ 0 := by linarith
  have hN2 : (N:ℝ)^2 ≠ 0 := by positivity
  have hratio : (1 + (N-1)/sden N)/(1 - (N-1)/sden N) = (N^2+N-1)/N^2 := by
    rw [div_eq_div_iff hd hN2]; field_simp [hsd.ne']; rw [sden]; ring
  have hlog := Real.log_div_le_sum_range_add hs0 hs1 2
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at hlog
  rw [hratio, Real.log_div (ne_of_gt hM) hN2, Real.log_pow] at hlog
  have hs2val : (1:ℝ) - ((N-1)/sden N)^2 = (4*N^2*(N^2+N-1))/(sden N)^2 := by
    field_simp [hsd.ne']; rw [sden]; ring
  have herr : 2 * (((N-1)/sden N)^5/(1 - ((N-1)/sden N)^2))
      = (N-1)^5/(2*N^2*(N^2+N-1)*(sden N)^3) := by
    rw [hs2val, div_pow, div_div_div_eq]; field_simp [hsd.ne']; ring
  simp only [LThi, LTlo]
  nlinarith [hlog, herr]
