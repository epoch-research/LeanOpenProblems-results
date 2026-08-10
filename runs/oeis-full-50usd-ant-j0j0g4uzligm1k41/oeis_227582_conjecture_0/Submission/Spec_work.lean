import FormalConjectures.Util.ProblemImports

open BigOperators LinearRecurrence Real Filter Topology

def A227582_base (n : ℕ) : ℤ :=
  let order := 7
  let coeffs : Fin order → ℤ := ![1, -2, 1, 0, 0, -1, 2]
  let init : Fin order → ℤ := ![2, 7, 14, 23, 35, 50, 67]
  let E : LinearRecurrence ℤ := { order := order, coeffs := coeffs }
  E.mkSol init n

noncomputable def a (n : ℕ) : ℕ :=
  if h : 0 < n then
    (A227582_base (n - 1)).toNat
  else
    0

noncomputable def E : LinearRecurrence ℤ := { order := 7, coeffs := ![1, -2, 1, 0, 0, -1, 2] }
noncomputable def init7 : Fin 7 → ℤ := ![2, 7, 14, 23, 35, 50, 67]
lemma base_val (j : Fin 7) : A227582_base (j : ℕ) = init7 j := by
  have := E.mkSol_eq_init init7 j
  simpa [A227582_base, E] using this

-- recurrence
lemma base_rec (n : ℕ) : A227582_base (n + 7) =
    A227582_base n - 2 * A227582_base (n+1) + A227582_base (n+2)
      - A227582_base (n+5) + 2 * A227582_base (n+6) := by
  have h2 : E.mkSol init7 (n+7) = ∑ i : Fin 7, E.coeffs i * E.mkSol init7 (n + (i:ℕ)) :=
    E.is_sol_mkSol init7 n
  have e : ∀ k, A227582_base k = E.mkSol init7 k := fun k => rfl
  rw [e (n+7), e n, e (n+1), e (n+2), e (n+5), e (n+6)]
  rw [h2, Fin.sum_univ_seven]
  simp only [E, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Fin.isValue, Fin.val_zero, Fin.val_one, Nat.add_zero]
  norm_num
  ring

/-- The period-5 correction in the closed form `5 * base m = 6 m² + 18 m + cc (m % 5)`. -/
def cc (r : ℕ) : ℤ := if r = 0 then 10 else if r = 1 then 11 else if r = 2 then 10 else 7

lemma bv0 : A227582_base 0 = 2 := by have := base_val ⟨0, by decide⟩; simpa [init7] using this
lemma bv1 : A227582_base 1 = 7 := by have := base_val ⟨1, by decide⟩; simpa [init7] using this
lemma bv2 : A227582_base 2 = 14 := by have := base_val ⟨2, by decide⟩; simpa [init7] using this
lemma bv3 : A227582_base 3 = 23 := by have := base_val ⟨3, by decide⟩; simpa [init7] using this
lemma bv4 : A227582_base 4 = 35 := by have := base_val ⟨4, by decide⟩; simpa [init7] using this
lemma bv5 : A227582_base 5 = 50 := by have := base_val ⟨5, by decide⟩; simpa [init7] using this
lemma bv6 : A227582_base 6 = 67 := by have := base_val ⟨6, by decide⟩; simpa [init7] using this

lemma closed (m : ℕ) : 5 * A227582_base m = 6 * (m : ℤ)^2 + 18 * m + cc (m % 5) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases lt_or_ge m 7 with hm | hm
    · interval_cases m <;>
        simp only [bv0, bv1, bv2, bv3, bv4, bv5, bv6, cc] <;> norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 7 := ⟨m - 7, by omega⟩
      have h0 := ih k (by omega)
      have h1 := ih (k+1) (by omega)
      have h2 := ih (k+2) (by omega)
      have h5 := ih (k+5) (by omega)
      have h6 := ih (k+6) (by omega)
      have e5 : (k+5) % 5 = k % 5 := by omega
      have e6 : (k+6) % 5 = (k+1) % 5 := by omega
      have e7 : (k+7) % 5 = (k+2) % 5 := by omega
      rw [e5] at h5
      rw [e6] at h6
      rw [base_rec k, e7]
      push_cast at h0 h1 h2 h5 h6 ⊢
      linear_combination h0 - 2*h1 + h2 - h5 + 2*h6

lemma ineqP (K : ℝ) (hK : 1 ≤ K) :
    2*(1/(2*K+1) + (1/(2*K+1))^3/3 + (1/(2*K+1))^5/5
        + (1/(2*K+1))^7/(1-(1/(2*K+1))^2))
    < (1/(K+1) - (1/(2*(K+1))-1/(2*K)) + (1/(12*(K+1)^2)-1/(12*K^2))
        - (1/(120*(K+1)^4)-1/(120*K^4))) := by
  have hK0 : 0 < K := by linarith
  have h1 : 0 < K + 1 := by linarith
  have h2 : 0 < 2*K+1 := by linarith
  have h3 : (1 - (1/(2*K+1))^2) = 4*K*(K+1)/(2*K+1)^2 := by
    field_simp; ring
  have hnum : 0 < (40*K^6+120*K^5+182*K^4+164*K^3+76*K^2+14*K+1) := by positivity
  have key : (1/(K+1) - (1/(2*(K+1))-1/(2*K)) + (1/(12*(K+1)^2)-1/(12*K^2))
        - (1/(120*(K+1)^4)-1/(120*K^4)))
      - 2*(1/(2*K+1) + (1/(2*K+1))^3/3 + (1/(2*K+1))^5/5
        + (1/(2*K+1))^7/(1-(1/(2*K+1))^2))
      = (40*K^6+120*K^5+182*K^4+164*K^3+76*K^2+14*K+1)
          / (120*K^4*(K+1)^4*(2*K+1)^5) := by
    rw [h3]
    field_simp
    ring
  have hden : 0 < 120*K^4*(K+1)^4*(2*K+1)^5 := by positivity
  nlinarith [div_pos hnum hden, key]

-- Rational inequality for Q-monotonicity (artanh lower bound, 4 terms)
lemma ineqQ (K : ℝ) (hK : 1 ≤ K) :
    (1/(K+1) - (1/(2*(K+1))-1/(2*K)) + (1/(12*(K+1)^2)-1/(12*K^2))
        - (1/(120*(K+1)^4)-1/(120*K^4))
        + (1/(252*(K+1)^6)-1/(252*K^6)))
    < 2*(1/(2*K+1) + (1/(2*K+1))^3/3 + (1/(2*K+1))^5/5 + (1/(2*K+1))^7/7) := by
  have hK0 : 0 < K := by linarith
  have h1 : 0 < K + 1 := by linarith
  have h2 : 0 < 2*K+1 := by linarith
  have hnum : 0 < (10612*K^10+53060*K^9+119322*K^8+158928*K^7+138774*K^6+82926*K^5
      +34317*K^4+9720*K^3+1809*K^2+200*K+10) := by positivity
  have key : 2*(1/(2*K+1) + (1/(2*K+1))^3/3 + (1/(2*K+1))^5/5 + (1/(2*K+1))^7/7)
      - (1/(K+1) - (1/(2*(K+1))-1/(2*K)) + (1/(12*(K+1)^2)-1/(12*K^2))
        - (1/(120*(K+1)^4)-1/(120*K^4)) + (1/(252*(K+1)^6)-1/(252*K^6)))
      = (10612*K^10+53060*K^9+119322*K^8+158928*K^7+138774*K^6+82926*K^5
          +34317*K^4+9720*K^3+1809*K^2+200*K+10)
          / (2520*K^6*(K+1)^6*(2*K+1)^7) := by
    field_simp
    ring
  have hden : 0 < 2520*K^6*(K+1)^6*(2*K+1)^7 := by positivity
  nlinarith [div_pos hnum hden, key]

-- log upper bound via artanh, 3 terms
lemma logbound_P (K : ℝ) (hK : 1 ≤ K) :
    Real.log ((K+1)/K) < (1/(K+1) - (1/(2*(K+1))-1/(2*K)) + (1/(12*(K+1)^2)-1/(12*K^2))
        - (1/(120*(K+1)^4)-1/(120*K^4))) := by
  have hK0 : 0 < K := by linarith
  have h2 : 0 < 2*K+1 := by linarith
  have hx0 : (0:ℝ) ≤ 1/(2*K+1) := by positivity
  have hx1 : (1:ℝ)/(2*K+1) < 1 := by rw [div_lt_one h2]; linarith
  have hlog := Real.log_div_le_sum_range_add hx0 hx1 3
  have hd : (1:ℝ) - 1/(2*K+1) ≠ 0 := by
    have : (0:ℝ) < 1 - 1/(2*K+1) := by rw [sub_pos]; exact hx1
    linarith
  have hratio : (1 + 1/(2*K+1))/(1 - 1/(2*K+1)) = (K+1)/K := by
    rw [div_eq_div_iff hd hK0.ne']; field_simp; ring
  rw [hratio, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero] at hlog
  have hub : Real.log ((K+1)/K) ≤ 2*(1/(2*K+1) + (1/(2*K+1))^3/3 + (1/(2*K+1))^5/5
        + (1/(2*K+1))^7/(1-(1/(2*K+1))^2)) := by
    nlinarith [hlog]
  exact lt_of_le_of_lt hub (ineqP K hK)

-- log lower bound via artanh, 4 terms
lemma logbound_Q (K : ℝ) (hK : 1 ≤ K) :
    (1/(K+1) - (1/(2*(K+1))-1/(2*K)) + (1/(12*(K+1)^2)-1/(12*K^2))
        - (1/(120*(K+1)^4)-1/(120*K^4)) + (1/(252*(K+1)^6)-1/(252*K^6)))
    < Real.log ((K+1)/K) := by
  have hK0 : 0 < K := by linarith
  have h2 : 0 < 2*K+1 := by linarith
  have hx0 : (0:ℝ) ≤ 1/(2*K+1) := by positivity
  have hx1 : (1:ℝ)/(2*K+1) < 1 := by rw [div_lt_one h2]; linarith
  have hlog := Real.sum_range_le_log_div hx0 hx1 4
  have hd : (1:ℝ) - 1/(2*K+1) ≠ 0 := by
    have : (0:ℝ) < 1 - 1/(2*K+1) := by rw [sub_pos]; exact hx1
    linarith
  have hratio : (1 + 1/(2*K+1))/(1 - 1/(2*K+1)) = (K+1)/K := by
    rw [div_eq_div_iff hd hK0.ne']; field_simp; ring
  rw [hratio, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero] at hlog
  have hlb : 2*(1/(2*K+1) + (1/(2*K+1))^3/3 + (1/(2*K+1))^5/5 + (1/(2*K+1))^7/7)
      ≤ Real.log ((K+1)/K) := by
    nlinarith [hlog]
  exact lt_of_lt_of_le (ineqQ K hK) hlb

noncomputable def Pseq (n : ℕ) : ℝ :=
  (harmonic n : ℝ) - Real.log n - 1/(2*n) + 1/(12*n^2) - 1/(120*n^4)

noncomputable def Qseq (n : ℕ) : ℝ := Pseq n + 1/(252*n^6)

lemma Pseq_step (k : ℕ) (hk : 1 ≤ k) : Pseq k < Pseq (k+1) := by
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hk0 : ((k:ℝ)) ≠ 0 := by positivity
  have hk1' : ((k:ℝ)+1) ≠ 0 := by positivity
  have hh : (harmonic (k+1) : ℝ) = (harmonic k : ℝ) + 1/((k:ℝ)+1) := by
    rw [harmonic_succ]; push_cast; ring
  have hl : Real.log (((k:ℝ)+1)/(k:ℝ)) = Real.log ((k:ℝ)+1) - Real.log (k:ℝ) :=
    Real.log_div hk1' hk0
  have key := logbound_P (k:ℝ) hk1
  have hP : Pseq (k+1) - Pseq k =
      (1/((k:ℝ)+1) - (1/(2*((k:ℝ)+1))-1/(2*(k:ℝ))) + (1/(12*((k:ℝ)+1)^2)-1/(12*(k:ℝ)^2))
        - (1/(120*((k:ℝ)+1)^4)-1/(120*(k:ℝ)^4))) - Real.log (((k:ℝ)+1)/(k:ℝ)) := by
    simp only [Pseq]
    push_cast [hh]
    rw [hl]
    ring
  linarith [hP, key]

lemma Qseq_step (k : ℕ) (hk : 1 ≤ k) : Qseq (k+1) < Qseq k := by
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hk0 : ((k:ℝ)) ≠ 0 := by positivity
  have hk1' : ((k:ℝ)+1) ≠ 0 := by positivity
  have hh : (harmonic (k+1) : ℝ) = (harmonic k : ℝ) + 1/((k:ℝ)+1) := by
    rw [harmonic_succ]; push_cast; ring
  have hl : Real.log (((k:ℝ)+1)/(k:ℝ)) = Real.log ((k:ℝ)+1) - Real.log (k:ℝ) :=
    Real.log_div hk1' hk0
  have key := logbound_Q (k:ℝ) hk1
  have hQ : Qseq (k+1) - Qseq k =
      (1/((k:ℝ)+1) - (1/(2*((k:ℝ)+1))-1/(2*(k:ℝ))) + (1/(12*((k:ℝ)+1)^2)-1/(12*(k:ℝ)^2))
        - (1/(120*((k:ℝ)+1)^4)-1/(120*(k:ℝ)^4)) + (1/(252*((k:ℝ)+1)^6)-1/(252*(k:ℝ)^6)))
        - Real.log (((k:ℝ)+1)/(k:ℝ)) := by
    simp only [Qseq, Pseq]
    push_cast [hh]
    rw [hl]
    ring
  linarith [hQ, key]

open Filter Topology in
lemma tendsto_Pseq : Tendsto Pseq atTop (𝓝 Real.eulerMascheroniConstant) := by
  have t1 : Filter.Tendsto (fun n:ℕ => 1/(n:ℝ)) Filter.atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hcont : Continuous (fun t:ℝ => -t/2 + t^2/12 - t^4/120) := by fun_prop
  have hc0 := (hcont.tendsto (0:ℝ)).comp t1
  rw [show (-0/2 + 0^2/12 - 0^4/120 : ℝ) = 0 by norm_num] at hc0
  have hsum := Real.tendsto_harmonic_sub_log.add hc0
  rw [add_zero] at hsum
  apply hsum.congr
  intro n
  simp only [Pseq, Function.comp]
  ring

open Filter Topology in
lemma tendsto_Qseq : Tendsto Qseq atTop (𝓝 Real.eulerMascheroniConstant) := by
  have t1 : Filter.Tendsto (fun n:ℕ => 1/(n:ℝ)) Filter.atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hcont : Continuous (fun t:ℝ => -t/2 + t^2/12 - t^4/120 + t^6/252) := by fun_prop
  have hc0 := (hcont.tendsto (0:ℝ)).comp t1
  rw [show (-0/2 + 0^2/12 - 0^4/120 + 0^6/252 : ℝ) = 0 by norm_num] at hc0
  have hsum := Real.tendsto_harmonic_sub_log.add hc0
  rw [add_zero] at hsum
  apply hsum.congr
  intro n
  simp only [Qseq, Pseq, Function.comp]
  ring

open Filter Topology in
lemma Pseq_lt_g (n : ℕ) (hn : 1 ≤ n) : Pseq n < Real.eulerMascheroniConstant := by
  have hmono : Monotone (fun m => Pseq (m+1)) :=
    monotone_nat_of_le_succ (fun m => (Pseq_step (m+1) (Nat.le_add_left 1 m)).le)
  have htend : Tendsto (fun m => Pseq (m+1)) atTop (𝓝 Real.eulerMascheroniConstant) :=
    tendsto_Pseq.comp (tendsto_add_atTop_nat 1)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n-1, by omega⟩
  have h1 : Pseq (m+1) < Pseq (m+2) := Pseq_step (m+1) (Nat.le_add_left 1 m)
  have h2 : Pseq (m+2) ≤ Real.eulerMascheroniConstant := hmono.ge_of_tendsto htend (m+1)
  linarith

open Filter Topology in
lemma g_lt_Qseq (n : ℕ) (hn : 1 ≤ n) : Real.eulerMascheroniConstant < Qseq n := by
  have hanti : Antitone (fun m => Qseq (m+1)) :=
    antitone_nat_of_succ_le (fun m => (Qseq_step (m+1) (Nat.le_add_left 1 m)).le)
  have htend : Tendsto (fun m => Qseq (m+1)) atTop (𝓝 Real.eulerMascheroniConstant) :=
    tendsto_Qseq.comp (tendsto_add_atTop_nat 1)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n-1, by omega⟩
  have h1 : Qseq (m+2) < Qseq (m+1) := Qseq_step (m+1) (Nat.le_add_left 1 m)
  have h2 : Real.eulerMascheroniConstant ≤ Qseq (m+2) := hanti.le_of_tendsto htend (m+1)
  linarith

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

----------------------------------------------------------------
-- Gluing: ψ bounds, D bounds, and the final floor computation.
----------------------------------------------------------------

lemma psiMlo_lt_s4 (x : ℝ) (hx : 1 ≤ x) : 1/(2*x) - 1/(12*x^2) < s4 x := by
  have hx0 : 0 < x := by linarith
  have hdiff : s4 x - (1/(2*x) - 1/(12*x^2)) = 1/(120*x^4) - 1/(252*x^6) := by
    simp only [s4, s3]; field_simp; ring
  have hpos : 0 < 1/(120*x^4) - 1/(252*x^6) := by
    rw [sub_pos, one_div_lt_one_div (by positivity) (by positivity)]
    have h1 : (0:ℝ) ≤ x^4*(x^2-1) := mul_nonneg (by positivity) (by nlinarith)
    nlinarith [h1, pow_pos hx0 4]
  linarith [hdiff, hpos]

lemma s3M_lt_psiMhi (x : ℝ) (hx : 1 ≤ x) : s3 x < 1/(2*x) := by
  have hx0 : 0 < x := by linarith
  have hdiff : 1/(2*x) - s3 x = 1/(12*x^2) - 1/(120*x^4) := by
    simp only [s3]; field_simp; ring
  have hpos : 0 < 1/(12*x^2) - 1/(120*x^4) := by
    rw [sub_pos, one_div_lt_one_div (by positivity) (by positivity)]
    have h1 : (0:ℝ) ≤ x^2*(x^2-1) := mul_nonneg (by positivity) (by nlinarith)
    nlinarith [h1, pow_pos hx0 2]
  linarith [hdiff, hpos]

lemma D_lt_Dhi (n : ℕ) (hn : 1 ≤ n) :
    2*(harmonic n:ℝ) - (harmonic (n*n+n-1):ℝ) - Real.eulerMascheroniConstant
      < Dhi (n:ℝ) := by
  have hN1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hmm : 1*1 ≤ n*n := Nat.mul_le_mul hn hn
  have hMge : 1 ≤ n*n+n-1 := by omega
  have hMr : ((n*n+n-1:ℕ):ℝ) = (n:ℝ)^2+(n:ℝ)-1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hMr1 : (1:ℝ) ≤ ((n*n+n-1:ℕ):ℝ) := by exact_mod_cast hMge
  -- f1 : ψ(n) < s3 N
  have f1 : (harmonic n:ℝ) - Real.log n - Real.eulerMascheroniConstant < s3 (n:ℝ) := by
    have h := Pseq_lt_g n hn
    simp only [Pseq, s3] at h ⊢; linarith
  -- hpsiM : 1/(2M)-1/(12M²) < ψ(M)
  have hpsiM : 1/(2*((n*n+n-1:ℕ):ℝ)) - 1/(12*((n*n+n-1:ℕ):ℝ)^2)
      < (harmonic (n*n+n-1):ℝ) - Real.log ((n*n+n-1:ℕ):ℝ)
          - Real.eulerMascheroniConstant := by
    have hq := g_lt_Qseq (n*n+n-1) hMge
    have hs4 := psiMlo_lt_s4 ((n*n+n-1:ℕ):ℝ) hMr1
    simp only [Qseq, Pseq, s4, s3] at hq hs4 ⊢; linarith
  -- f3 : LTlo ≤ LM - 2 Ln
  have f3 : LTlo (n:ℝ) ≤ Real.log ((n*n+n-1:ℕ):ℝ) - 2*Real.log n := by
    have h := artanh_lower (n:ℝ) hN1
    rw [← hMr] at h; exact h
  simp only [Dhi, psiMlo]
  rw [← hMr]
  linarith [f1, hpsiM, f3]

lemma D_gt_Dlo (n : ℕ) (hn : 1 ≤ n) :
    Dlo (n:ℝ) <
      2*(harmonic n:ℝ) - (harmonic (n*n+n-1):ℝ) - Real.eulerMascheroniConstant := by
  have hN1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hmm : 1*1 ≤ n*n := Nat.mul_le_mul hn hn
  have hMge : 1 ≤ n*n+n-1 := by omega
  have hMr : ((n*n+n-1:ℕ):ℝ) = (n:ℝ)^2+(n:ℝ)-1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hMr1 : (1:ℝ) ≤ ((n*n+n-1:ℕ):ℝ) := by exact_mod_cast hMge
  -- g1 : ψ(n) > s4 N
  have g1 : s4 (n:ℝ) < (harmonic n:ℝ) - Real.log n - Real.eulerMascheroniConstant := by
    have h := g_lt_Qseq n hn
    simp only [Qseq, Pseq, s4, s3] at h ⊢; linarith
  -- g2 : ψ(M) < s3 M
  have g2 : (harmonic (n*n+n-1):ℝ) - Real.log ((n*n+n-1:ℕ):ℝ)
        - Real.eulerMascheroniConstant
      < s3 ((n*n+n-1:ℕ):ℝ) := by
    have h := Pseq_lt_g (n*n+n-1) hMge
    simp only [Pseq, s3] at h ⊢; linarith
  -- g3 : LM - 2 Ln ≤ LThi
  have g3 : Real.log ((n*n+n-1:ℕ):ℝ) - 2*Real.log n ≤ LThi (n:ℝ) := by
    have h := artanh_upper (n:ℝ) hN1
    rw [← hMr] at h; exact h
  simp only [Dlo]
  rw [← hMr]
  linarith [g1, g2, g3]

lemma final_step (D ar dlo dhi : ℝ) (K : ℤ)
    (har : (K:ℝ) = ar) (harpos : 0 ≤ ar)
    (hDhi : D < dhi) (hDlo : dlo < D)
    (hI : ar * dhi ≤ 1) (hII : 1 < (ar+1) * dlo) :
    K.toNat = (Int.floor (1/D)).toNat := by
  have hap : 0 ≤ ar + 1 := by linarith
  have hDlo0 : 0 < dlo := by
    by_contra h
    push_neg at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hap h]
  have hD0 : 0 < D := lt_trans hDlo0 hDlo
  have hfl : Int.floor (1/D) = K := by
    rw [Int.floor_eq_iff]
    constructor
    · rw [har, le_div_iff₀ hD0]
      nlinarith [harpos, hDhi, hI]
    · rw [har, div_lt_iff₀ hD0]
      nlinarith [hap, hDlo, hII]
  rw [hfl]

theorem oeis_227582_conjecture_0 (n : ℕ) (hn : 0 < n) :
    a n = (Int.floor
      (1 / (2 * (↑(harmonic n) : ℝ) -
            (↑(harmonic (n * n + n - 1)) : ℝ) -
            Real.eulerMascheroniConstant))).toNat := by
  have hn1 : 1 ≤ n := hn
  set N := (n:ℝ) with hNdef
  have hN1 : (1:ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hn1
  set D := 2 * (harmonic n:ℝ) - (harmonic (n*n+n-1):ℝ) - Real.eulerMascheroniConstant
    with hDdef
  have hDhi : D < Dhi N := D_lt_Dhi n hn1
  have hDlo : Dlo N < D := D_gt_Dlo n hn1
  have ha_eq : a n = (A227582_base (n-1)).toNat := by simp only [a, dif_pos hn]
  rw [ha_eq]
  -- general base value as a real
  have hc : ((n-1:ℕ):ℝ) = N - 1 := by rw [hNdef, Nat.cast_sub hn1]; push_cast; ring
  have hbaseR : (A227582_base (n-1):ℝ)
      = (6*N^2+6*N + ((cc ((n-1)%5):ℝ) - 12))/5 := by
    have h := closed (n-1)
    have hR : (5:ℝ) * (A227582_base (n-1):ℝ)
        = 6*((n-1:ℕ):ℝ)^2+18*((n-1:ℕ):ℝ)+(cc ((n-1)%5):ℝ) := by
      exact_mod_cast h
    rw [hc] at hR
    rw [eq_div_iff (by norm_num : (5:ℝ) ≠ 0)]
    linear_combination hR
  -- case split on n % 5
  have hmod : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases hmod with h0 | h1 | h2 | h3 | h4
  · -- n%5=0, (n-1)%5=4, cc=7, q=-5
    have hm : (n-1)%5 = 4 := by omega
    have har : (A227582_base (n-1):ℝ) = (6*N^2+6*N+(-5))/5 := by
      rw [hbaseR, hm]; simp only [cc]; norm_num
    have harpos : (0:ℝ) ≤ (6*N^2+6*N+(-5))/5 := by nlinarith [hN1]
    exact final_step D _ (Dlo N) (Dhi N) _ har harpos hDhi hDlo
      (ratI5 N hN1) (ratII5 N hN1)
  · -- n%5=1, (n-1)%5=0, cc=10, q=-2
    have hm : (n-1)%5 = 0 := by omega
    have har : (A227582_base (n-1):ℝ) = (6*N^2+6*N+(-2))/5 := by
      rw [hbaseR, hm]; simp only [cc]; norm_num
    have harpos : (0:ℝ) ≤ (6*N^2+6*N+(-2))/5 := by nlinarith [hN1]
    exact final_step D _ (Dlo N) (Dhi N) _ har harpos hDhi hDlo
      (ratI2 N hN1) (ratII2 N hN1)
  · -- n%5=2, (n-1)%5=1, cc=11, q=-1
    have hm : (n-1)%5 = 1 := by omega
    have har : (A227582_base (n-1):ℝ) = (6*N^2+6*N+(-1))/5 := by
      rw [hbaseR, hm]; simp only [cc]; norm_num
    have harpos : (0:ℝ) ≤ (6*N^2+6*N+(-1))/5 := by nlinarith [hN1]
    exact final_step D _ (Dlo N) (Dhi N) _ har harpos hDhi hDlo
      (ratI1 N hN1) (ratII1 N hN1)
  · -- n%5=3, (n-1)%5=2, cc=10, q=-2
    have hm : (n-1)%5 = 2 := by omega
    have har : (A227582_base (n-1):ℝ) = (6*N^2+6*N+(-2))/5 := by
      rw [hbaseR, hm]; simp only [cc]; norm_num
    have harpos : (0:ℝ) ≤ (6*N^2+6*N+(-2))/5 := by nlinarith [hN1]
    exact final_step D _ (Dlo N) (Dhi N) _ har harpos hDhi hDlo
      (ratI2 N hN1) (ratII2 N hN1)
  · -- n%5=4, (n-1)%5=3, cc=7, q=-5
    have hm : (n-1)%5 = 3 := by omega
    have har : (A227582_base (n-1):ℝ) = (6*N^2+6*N+(-5))/5 := by
      rw [hbaseR, hm]; simp only [cc]; norm_num
    have harpos : (0:ℝ) ≤ (6*N^2+6*N+(-5))/5 := by nlinarith [hN1]
    exact final_step D _ (Dlo N) (Dhi N) _ har harpos hDhi hDlo
      (ratI5 N hN1) (ratII5 N hN1)
