import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix
open scoped BigOperators

/--
A228304: The sequence $a(n)$ is defined by the alternating sum of fourth powers of binomial coefficients.
$$a(n) = \sum_{k=0}^n \binom{n}{k}^4 (-1)^k$$
-/
def a (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k => ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 4)

/--
A228304 c(n) sequence:
$$c(n) = \sum_{k=0}^n (-1)^k \binom{n}{k}^2 \binom{2k}{k} \binom{2(n-k)}{n-k}$$
-/
def c (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k =>
    ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 2) * (choose (2 * k) k : ℤ) * (choose (2 * (n - k)) (n - k) : ℤ)

namespace A228304Proof

-- The formal proof is assembled from elementary Lucas congruences and an anti-triangular
-- determinant evaluation.  Helper lemmas are kept in this namespace.

lemma zmod_natCast_ne_zero_of_pos_lt (p a : ℕ) (ha0 : 0 < a) (hap : a < p) :
    (a : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ a := by
    rwa [ZMod.natCast_eq_zero_iff] at h
  exact (Nat.not_dvd_of_pos_of_lt ha0 hap) hdvd

lemma choose_p_add_small (p r s : ℕ) (hp : Nat.Prime p) (hr : r < p) (hs : s < p) :
    ((Nat.choose (p + r) s : ℕ) : ZMod p) = (Nat.choose r s : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := (Choose.choose_modEq_choose_mod_mul_choose_div (n := p + r) (k := s) (p := p))
  rw [← ZMod.intCast_eq_intCast_iff] at h
  norm_num at h
  simpa [Nat.add_mod, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs, Nat.div_eq_of_lt hs,
    Nat.add_div_right _ (Nat.pos_of_ne_zero hp.ne_zero)] using h

lemma choose_p_add_big (p r s : ℕ) (hp : Nat.Prime p) (hr : r < p) (hs : s < p) :
    ((Nat.choose (p + r) (p + s) : ℕ) : ZMod p) = (Nat.choose r s : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := (Choose.choose_modEq_choose_mod_mul_choose_div (n := p + r) (k := p + s) (p := p))
  rw [← ZMod.intCast_eq_intCast_iff] at h
  norm_num at h
  have hp0 : 0 < p := Nat.pos_of_ne_zero hp.ne_zero
  have hdivr : (p + r) / p = 1 := by
    rw [Nat.add_comm, Nat.add_div_right _ hp0, Nat.div_eq_of_lt hr, zero_add]
  have hdivs : (p + s) / p = 1 := by
    rw [Nat.add_comm, Nat.add_div_right _ hp0, Nat.div_eq_of_lt hs, zero_add]
  simpa [Nat.add_mod, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs, hdivr, hdivs] using h

lemma central_large_zero (p u : ℕ) (hp : Nat.Prime p) (hu : u < p) (hlarge : p ≤ 2*u) :
    ((Nat.choose (2*u) u : ℕ) : ZMod p) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := (Choose.choose_modEq_choose_mod_mul_choose_div (n := 2*u) (k := u) (p := p))
  rw [← ZMod.intCast_eq_intCast_iff] at h
  have humod : u % p = u := Nat.mod_eq_of_lt hu
  have hudiv : u / p = 0 := Nat.div_eq_of_lt hu
  have hlow : (2*u) % p < u := by
    rw [Nat.mod_eq_sub_mod hlarge]
    have h2ult : 2*u < 2*p := by omega
    have hsub : 2*u - p < p := by omega
    rw [Nat.mod_eq_of_lt hsub]
    omega
  have hchoose : Nat.choose ((2*u) % p) (u % p) = 0 := by
    rw [humod]
    exact Nat.choose_eq_zero_of_lt hlow
  rw [hchoose] at h
  simpa [hudiv] using h

lemma central_p_add (p u : ℕ) (hp : Nat.Prime p) (hu : u < p) :
    ((Nat.choose (2*(p+u)) (p+u) : ℕ) : ZMod p) = 2 * (Nat.choose (2*u) u : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hsmall : 2*u < p
  · have h1 := (Choose.choose_modEq_choose_mod_mul_choose_div (n := 2*(p+u)) (k := p+u) (p := p))
    rw [← ZMod.intCast_eq_intCast_iff] at h1
    have hp0 : 0 < p := Nat.pos_of_ne_zero hp.ne_zero
    have hu_mod : u % p = u := Nat.mod_eq_of_lt hu
    have hu_div : u / p = 0 := Nat.div_eq_of_lt hu
    have hpudiv : (p+u)/p = 1 := by
      rw [Nat.add_comm, Nat.add_div_right _ hp0, hu_div, zero_add]
    have hpumod : (p+u)%p = u := by simp [hu_mod]
    have h2u_mod : (2*u)%p = 2*u := Nat.mod_eq_of_lt hsmall
    have h2u_div : (2*u)/p = 0 := Nat.div_eq_of_lt hsmall
    have hn_mod : (2*(p+u))%p = 2*u := by
      have : 2*(p+u) = 2*p + 2*u := by ring
      rw [this]
      simp [Nat.add_mod, h2u_mod]
    have hn_div : (2*(p+u))/p = 2 := by
      have : 2*(p+u) = 2*u + 2*p := by ring
      rw [this, Nat.add_mul_div_right _ 2 hp0, h2u_div, zero_add]
    have hn_mod' : ((p+u)*2)%p = u*2 := by simpa [Nat.mul_comm] using hn_mod
    have hn_div' : ((p+u)*2)/p = 2 := by simpa [Nat.mul_comm] using hn_div
    have h2u_mod' : (u*2)%p = u*2 := by simpa [Nat.mul_comm] using h2u_mod
    have h2u_div' : (u*2)/p = 0 := by simpa [Nat.mul_comm] using h2u_div
    simpa [hn_mod', hpumod, hn_div', hpudiv, h2u_mod', hu_mod, h2u_div', hu_div, mul_comm] using h1
  · have hlarge : p ≤ 2*u := by omega
    have hzero : (Nat.choose (2*u) u : ZMod p) = 0 := central_large_zero p u hp hu hlarge
    rw [hzero, mul_zero]
    have h1 := (Choose.choose_modEq_choose_mod_mul_choose_div (n := 2*(p+u)) (k := p+u) (p := p))
    rw [← ZMod.intCast_eq_intCast_iff] at h1
    have hp0 : 0 < p := Nat.pos_of_ne_zero hp.ne_zero
    have hu_mod : u % p = u := Nat.mod_eq_of_lt hu
    have hu_div : u / p = 0 := Nat.div_eq_of_lt hu
    have hpudiv : (p+u)/p = 1 := by
      rw [Nat.add_comm, Nat.add_div_right _ hp0, hu_div, zero_add]
    have hpumod : (p+u)%p = u := by simp [hu_mod]
    have hn_mod_lt : (2*(p+u))%p < u := by
      have htwolt : 2*u < 2*p := by omega
      have : (2*(p+u))%p = (2*u)%p := by
        have heq : 2*(p+u) = 2*p + 2*u := by ring
        rw [heq]
        simp [Nat.add_mod]
      rw [this]
      rw [Nat.mod_eq_sub_mod hlarge]
      have hsub : 2*u - p < p := by omega
      rw [Nat.mod_eq_of_lt hsub]
      omega
    have hchoose : Nat.choose ((2*(p+u))%p) ((p+u)%p) = 0 := by
      rw [hpumod]
      exact Nat.choose_eq_zero_of_lt hn_mod_lt
    rw [hchoose] at h1
    simpa [hpudiv] using h1

lemma choose_pred_cast (p k : ℕ) (hp : Nat.Prime p) (hk : k < p) :
    (Nat.choose (p-1) k : ZMod p) = (-1 : ZMod p)^k := by
  haveI : Fact p.Prime := ⟨hp⟩
  induction k with
  | zero => simp
  | succ k ih =>
      have hklt : k < p := by omega
      have hksucc : k + 1 < p := hk
      have ih' := ih hklt
      have hrecNat := Nat.choose_succ_right_eq (p-1) k
      have hrec : (Nat.choose (p-1) (k+1) : ZMod p) * (k+1 : ZMod p) =
          (Nat.choose (p-1) k : ZMod p) * ((p : ZMod p) - 1 - (k : ZMod p)) := by
        have h := congrArg (fun n : ℕ => (n : ZMod p)) hrecNat
        have hkp : k+1 ≤ p := by omega
        have hsubn : (p - 1) - k = p - (k+1) := by omega
        have hcastsub_add : ((p - (k+1) : ℕ) : ZMod p) + (k+1 : ZMod p) = (p : ZMod p) := by
          have hh := congrArg (fun n : ℕ => (n : ZMod p)) (Nat.sub_add_cancel hkp)
          simpa [Nat.cast_add] using hh
        have hcastsub : ((p - (k+1) : ℕ) : ZMod p) = (p : ZMod p) - (k+1 : ZMod p) := by
          exact eq_sub_of_add_eq hcastsub_add
        simpa [Nat.cast_mul, Nat.cast_add, hsubn, hcastsub, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
      have hnonzero : (k+1 : ZMod p) ≠ 0 := by
        simpa [Nat.cast_add] using zmod_natCast_ne_zero_of_pos_lt p (k+1) (by omega) hksucc
      apply mul_right_cancel₀ hnonzero
      calc
        (Nat.choose (p - 1) (k + 1) : ZMod p) * (k + 1 : ZMod p)
            = (Nat.choose (p-1) k : ZMod p) * ((p : ZMod p) - 1 - (k : ZMod p)) := hrec
        _ = ((-1 : ZMod p)^k) * (-(k+1 : ZMod p)) := by
          rw [ih']; simp; ring
        _ = ((-1 : ZMod p)^(k+1)) * (k+1 : ZMod p) := by
          rw [pow_succ]; ring

lemma sum_neg_one_pow_odd {R : Type*} [Ring R] (m : ℕ) :
    (∑ k ∈ range (2*m+1), (-1 : R)^k) = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2*(m+1)+1 = (2*m+1)+2 by ring]
      rw [Finset.sum_range_add]
      simp [ih, pow_add, pow_mul]

lemma a_p_add_eq_zero (p r : ℕ) (hp : Nat.Prime p) (hodd : p ≠ 2) (hr : r < p) :
    (a (p + r) : ZMod p) = 0 := by
  have hpoddZ : ((-1 : ZMod p) ^ p) = -1 := by
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two hodd
    rw [hm]
    simp [pow_succ, pow_mul]
  let F : ℕ → ZMod p := fun k => (-1 : ZMod p)^k * ((Nat.choose (p+r) k : ZMod p)^4)
  have hcast : (a (p+r) : ZMod p) = ∑ k ∈ range (p+r+1), F k := by
    simp [a, F]
  rw [hcast]
  have hsplit : ∑ k ∈ range (p+r+1), F k = ∑ k ∈ range p, F k + ∑ s ∈ range (r+1), F (p+s) := by
    have hlen : p + (r+1) = p+r+1 := by omega
    rw [← hlen]
    exact Finset.sum_range_add F p (r+1)
  rw [hsplit]
  have hfirst : ∑ k ∈ range p, F k = ∑ k ∈ range (r+1), F k := by
    have hlen : r + 1 + (p - (r + 1)) = p := by omega
    calc
      ∑ k ∈ range p, F k = ∑ k ∈ range (r+1 + (p-(r+1))), F k := by rw [hlen]
      _ = ∑ k ∈ range (r+1), F k + ∑ x ∈ range (p-(r+1)), F ((r+1)+x) := by rw [Finset.sum_range_add]
      _ = ∑ k ∈ range (r+1), F k := by
        suffices (∑ x ∈ range (p - (r + 1)), F (r + 1 + x)) = 0 by simp [this]
        apply Finset.sum_eq_zero
        intro x hx
        simp only [mem_range] at hx
        have hxlt : r + 1 + x < p := by omega
        have hltchoose : r < r + 1 + x := by
          have hpos : 0 < 1 + x := by omega
          have hlt' : r < r + (1 + x) := Nat.lt_add_of_pos_right hpos
          simpa [Nat.add_assoc] using hlt'
        have hchoose : (Nat.choose r (r+1+x) : ZMod p) = 0 := by
          rw [Nat.choose_eq_zero_of_lt hltchoose]
          simp
        unfold F
        rw [choose_p_add_small p r (r+1+x) hp hr hxlt, hchoose]
        simp
  rw [hfirst]
  have hpair : (∑ k ∈ range (r+1), F k) + (∑ s ∈ range (r+1), F (p+s)) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro s hs
    simp only [mem_range] at hs
    have hsltp : s < p := by omega
    unfold F
    rw [choose_p_add_small p r s hp hr hsltp, choose_p_add_big p r s hp hr hsltp]
    have hpow : (-1 : ZMod p) ^ (p + s) = - ((-1 : ZMod p) ^ s) := by
      rw [pow_add, hpoddZ]
      ring
    rw [hpow]
    ring
  simpa using hpair

lemma c_p_add_eq_zero (p r : ℕ) (hp : Nat.Prime p) (hodd : p ≠ 2) (hr : r < p) :
    (c (p + r) : ZMod p) = 0 := by
  have hpoddZ : ((-1 : ZMod p) ^ p) = -1 := by
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two hodd
    rw [hm]
    simp [pow_succ, pow_mul]
  let B : ℕ → ZMod p := fun t => (Nat.choose (2*t) t : ZMod p)
  let G : ℕ → ZMod p := fun k => (-1 : ZMod p)^k * ((Nat.choose (p+r) k : ZMod p)^2) * B k * B ((p+r)-k)
  have hcast : (c (p+r) : ZMod p) = ∑ k ∈ range (p+r+1), G k := by
    simp [c, G, B]
  rw [hcast]
  have hsplit : ∑ k ∈ range (p+r+1), G k = ∑ k ∈ range p, G k + ∑ s ∈ range (r+1), G (p+s) := by
    have hlen : p + (r+1) = p+r+1 := by omega
    rw [← hlen]
    exact Finset.sum_range_add G p (r+1)
  rw [hsplit]
  have hfirst : ∑ k ∈ range p, G k = ∑ k ∈ range (r+1), G k := by
    have hlen : r + 1 + (p - (r + 1)) = p := by omega
    calc
      ∑ k ∈ range p, G k = ∑ k ∈ range (r+1 + (p-(r+1))), G k := by rw [hlen]
      _ = ∑ k ∈ range (r+1), G k + ∑ x ∈ range (p-(r+1)), G ((r+1)+x) := by rw [Finset.sum_range_add]
      _ = ∑ k ∈ range (r+1), G k := by
        suffices (∑ x ∈ range (p - (r + 1)), G (r + 1 + x)) = 0 by simp [this]
        apply Finset.sum_eq_zero
        intro x hx
        simp only [mem_range] at hx
        have hxlt : r + 1 + x < p := by omega
        have hltchoose : r < r + 1 + x := by
          have hpos : 0 < 1 + x := by omega
          have hlt' : r < r + (1 + x) := Nat.lt_add_of_pos_right hpos
          simpa [Nat.add_assoc] using hlt'
        have hchoose : (Nat.choose r (r+1+x) : ZMod p) = 0 := by
          rw [Nat.choose_eq_zero_of_lt hltchoose]
          simp
        unfold G
        rw [choose_p_add_small p r (r+1+x) hp hr hxlt, hchoose]
        simp
  rw [hfirst]
  have hpair : (∑ k ∈ range (r+1), G k) + (∑ s ∈ range (r+1), G (p+s)) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro s hs
    simp only [mem_range] at hs
    have hsltp : s < p := by omega
    have hrsublt : r - s < p := by omega
    have hsub1 : (p+r) - s = p + (r-s) := by omega
    have hsub2 : (p+r) - (p+s) = r-s := by omega
    unfold G B
    rw [choose_p_add_small p r s hp hr hsltp, choose_p_add_big p r s hp hr hsltp]
    rw [hsub1, hsub2]
    rw [central_p_add p (r-s) hp hrsublt, central_p_add p s hp hsltp]
    have hpow : (-1 : ZMod p) ^ (p + s) = - ((-1 : ZMod p) ^ s) := by
      rw [pow_add, hpoddZ]
      ring
    rw [hpow]
    ring
  simpa using hpair

lemma det_antidiagonal_const {R : Type*} [CommRing R] (n : ℕ) [NeZero n] (M : Matrix (Fin n) (Fin n) R)
    (hzero : ∀ i j : Fin n, j < i → M i (Fin.rev j) = 0)
    (hdiag : ∀ i : Fin n, M i (Fin.rev i) = M 0 (Fin.rev 0)) :
    M.det = ((Fin.revPerm (n:=n)).sign : R) * (M 0 (Fin.rev 0)) ^ n := by
  let B : Matrix (Fin n) (Fin n) R := M.submatrix id (Fin.revPerm (n:=n))
  have htri : B.BlockTriangular id := by
    intro i j hij
    exact hzero i j hij
  have hdetB : B.det = (M 0 (Fin.rev 0)) ^ n := by
    rw [Matrix.det_of_upperTriangular htri]
    simp [B, hdiag, Finset.prod_const, Fintype.card_fin]
  have hperm : B.det = ((Fin.revPerm (n:=n)).sign : R) * M.det := by
    simpa [B] using (Matrix.det_permute' (Fin.revPerm (n:=n)) M)
  have hsignsq : (((Fin.revPerm (n:=n)).sign : R) * ((Fin.revPerm (n:=n)).sign : R)) = 1 := by
    rw [← Int.cast_mul]
    change (((((Fin.revPerm (n:=n)).sign * (Fin.revPerm (n:=n)).sign : ℤˣ) : ℤ) : R) = 1)
    simp
  calc
    M.det = (((Fin.revPerm (n:=n)).sign : R) * ((Fin.revPerm (n:=n)).sign : R)) * M.det := by rw [hsignsq, one_mul]
    _ = ((Fin.revPerm (n:=n)).sign : R) * B.det := by rw [hperm, mul_assoc]
    _ = ((Fin.revPerm (n:=n)).sign : R) * (M 0 (Fin.rev 0)) ^ n := by rw [hdetB]


lemma a_pred_cast (p : ℕ) (hp : Nat.Prime p) (hodd : p ≠ 2) :
    (a (p-1) : ZMod p) = 1 := by
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hodd
  have hcast : (a (p-1) : ZMod p) = ∑ k ∈ range p, (-1 : ZMod p)^k * ((Nat.choose (p-1) k : ZMod p)^4) := by
    have : p - 1 + 1 = p := by omega
    simp [a, this]
  rw [hcast]
  calc
    (∑ k ∈ range p, (-1 : ZMod p)^k * ((Nat.choose (p-1) k : ZMod p)^4))
        = ∑ k ∈ range p, (-1 : ZMod p)^k := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [mem_range] at hk
      rw [choose_pred_cast p k hp hk]
      have h4 : ((-1 : ZMod p)^k)^4 = 1 := by
        rw [← pow_mul]
        have : k * 4 = 2 * (2*k) := by ring
        rw [this, pow_mul]
        simp
      rw [h4]
      simp
    _ = 1 := by
      rw [hm]
      simpa using (sum_neg_one_pow_odd (R := ZMod p) m)

lemma c_pred_cast (p : ℕ) (hp : Nat.Prime p) (hodd : p ≠ 2) :
    (c (p-1) : ZMod p) = (-1 : ZMod p)^((p-1)/2) := by
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hodd
  have hmdiv : (p-1)/2 = m := by omega
  have hcast : (c (p-1) : ZMod p) = ∑ k ∈ range p,
      (-1 : ZMod p)^k * ((Nat.choose (p-1) k : ZMod p)^2) *
        (Nat.choose (2*k) k : ZMod p) * (Nat.choose (2*((p-1)-k)) ((p-1)-k) : ZMod p) := by
    have : p - 1 + 1 = p := by omega
    simp [c, this]
  rw [hcast]
  have hsingle : (∑ k ∈ range p,
      (-1 : ZMod p)^k * ((Nat.choose (p-1) k : ZMod p)^2) *
        (Nat.choose (2*k) k : ZMod p) * (Nat.choose (2*((p-1)-k)) ((p-1)-k) : ZMod p))
      = (-1 : ZMod p)^m * ((Nat.choose (p-1) m : ZMod p)^2) *
        (Nat.choose (2*m) m : ZMod p) * (Nat.choose (2*((p-1)-m)) ((p-1)-m) : ZMod p) := by
    apply Finset.sum_eq_single m
    · intro b hb hbm
      simp only [mem_range] at hb
      by_cases hlt : b < m
      · have hLlt : (p-1)-b < p := by omega
        have hlarge : p ≤ 2*((p-1)-b) := by omega
        have hz := central_large_zero p ((p-1)-b) hp hLlt hlarge
        rw [hz]
        ring
      · have hlarge : p ≤ 2*b := by omega
        have hz := central_large_zero p b hp hb hlarge
        rw [hz]
        ring
    · intro hmnot
      simp at hmnot
      omega
  rw [hsingle]
  have hpm : (p-1) = 2*m := by omega
  have hsubm : (p-1)-m = m := by omega
  have hchoosem : (Nat.choose (p-1) m : ZMod p) = (-1 : ZMod p)^m := by
    apply choose_pred_cast
    · exact hp
    · omega
  have hcentral : (Nat.choose (2*m) m : ZMod p) = (-1 : ZMod p)^m := by
    simpa [hpm] using hchoosem
  rw [hchoosem, hcentral, hsubm, hcentral, hmdiv]
  let x : ZMod p := (-1 : ZMod p)^m
  change x * x^2 * x * x = x
  have hx4 : x^4 = 1 := by
    dsimp [x]
    rw [← pow_mul]
    have : m * 4 = 2 * (2*m) := by ring
    rw [this, pow_mul]
    simp
  calc
    x * x^2 * x * x = x * x^4 := by ring
    _ = x := by rw [hx4]; ring

lemma sign_revPerm (n : ℕ) : (Fin.revPerm (n:=n)).sign = (-1 : ℤˣ) ^ (n * (n-1) / 2) := by
  calc
    (Fin.revPerm (n:=n)).sign = ∏ j : Fin n, ∏ i ∈ Finset.Iio j, (-1 : ℤˣ) := by
      rw [Equiv.Perm.sign_eq_prod_prod_Iio]
      apply Finset.prod_congr rfl
      intro j hj
      apply Finset.prod_congr rfl
      intro i hi
      have hij : i < j := by simpa using hi
      have hnot : ¬ Fin.rev i < Fin.rev j := by
        exact not_lt.mpr (Fin.rev_le_rev.mpr (le_of_lt hij))
      simp [Fin.revPerm, hnot]
    _ = (-1 : ℤˣ) ^ (n * (n-1) / 2) := by
      calc
        (∏ j : Fin n, ∏ i ∈ Finset.Iio j, (-1 : ℤˣ)) = ∏ j : Fin n, (-1 : ℤˣ) ^ (j : ℕ) := by
          apply Finset.prod_congr rfl
          intro j hj
          rw [Finset.prod_const]
          simp
        _ = (-1 : ℤˣ) ^ (∑ j : Fin n, (j : ℕ)) := by rw [Finset.prod_pow_eq_pow_sum]
        _ = (-1 : ℤˣ) ^ (n * (n-1) / 2) := by
          congr 1
          rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n]
          exact Finset.sum_range_id n

end A228304Proof

open A228304Proof

/--
A228304 Conjecture: Let p be any odd prime, and let A(p) be the p X p determinant with (i,j)-entry equal to a(i+j) for all i,j = 0,...,p-1. Then A(p) == (-1)^{(p-1)/2} (mod p). Similarly, if c(n) = sum_{k=0}^n (-1)^k*C(n,k)^2*C(2k,k)*C(2(n-k),n-k) and C(p) is the p X p determinant with (i,j)-entry equal to c(i+j) for all i,j = 0,...,p-1, then we have C(p) == 1 (mod p).
-/
theorem oeis_228304_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (h_odd : p ≠ 2) :
    let N := Fin p
    let half_minus_one := (p - 1) / 2
    -- A(p) is the p x p matrix with entries a(i+j)
    let A : Matrix N N ℤ := fun i j => a (i.val + j.val)
    -- C(p) is the p x p matrix with entries c(i+j)
    let C : Matrix N N ℤ := fun i j => c (i.val + j.val)
    (Matrix.det A ≡ (-1 : ℤ) ^ half_minus_one [ZMOD p]) ∧ (Matrix.det C ≡ 1 [ZMOD p]) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  dsimp
  constructor
  · rw [← ZMod.intCast_eq_intCast_iff]
    let Az : Matrix (Fin p) (Fin p) (ZMod p) := fun i j => (a (i.val + j.val) : ZMod p)
    have hdet : ((Matrix.det (fun i j : Fin p => a (i.val + j.val)) : ℤ) : ZMod p) = Az.det := by
      change (Int.castRingHom (ZMod p)) (Matrix.det (fun i j : Fin p => a (i.val + j.val))) = Az.det
      rw [Matrix.det_apply, Matrix.det_apply]
      simp [Az, map_sum, map_prod]
    rw [hdet]
    have hzero : ∀ i j : Fin p, j < i → Az i (Fin.rev j) = 0 := by
      intro i j hij
      unfold Az
      have hlt : i.val + (Fin.rev j).val - p < p := by
        simp [Fin.val_rev]
        omega
      have hsum : i.val + (Fin.rev j).val = p + (i.val + (Fin.rev j).val - p) := by
        simp [Fin.val_rev]
        omega
      rw [hsum]
      exact a_p_add_eq_zero p (i.val + (Fin.rev j).val - p) hp h_odd hlt
    have hdiag : ∀ i : Fin p, Az i (Fin.rev i) = Az 0 (Fin.rev 0) := by
      intro i
      unfold Az
      apply congrArg (fun n => (a n : ZMod p))
      simp [Fin.val_rev]
      omega
    have hanti := det_antidiagonal_const p Az hzero hdiag
    rw [hanti, sign_revPerm]
    have ha : Az 0 (Fin.rev 0) = (1 : ZMod p) := by
      unfold Az
      have hval : (Fin.rev (0 : Fin p)).val = p-1 := by rfl
      rw [hval]
      simpa using a_pred_cast p hp h_odd
    rw [ha]
    simp
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two h_odd
    have hmhalf : (p - 1) / 2 = m := by omega
    rw [hmhalf, hm]
    rw [show 2 * m + 1 - 1 = 2*m by omega]
    have hexp : (2 * m + 1) * (2 * m) / 2 = (2 * m + 1) * m := by
      rw [show (2 * m + 1) * (2 * m) = ((2 * m + 1) * m) * 2 by ring]
      rw [mul_comm (((2 * m + 1) * m)) 2]
      exact Nat.mul_div_right ((2 * m + 1) * m) (by norm_num : 0 < 2)
    rw [hexp, mul_comm (2*m+1) m, pow_mul]
    rw [pow_add, pow_mul]
    have hx2 : ((-1 : ZMod (2*m+1))^m)^2 = 1 := by
      rw [← pow_mul]
      have : m * 2 = 2*m := by ring
      rw [this, pow_mul]
      simp
    rw [hx2]
    simp
  · rw [← ZMod.intCast_eq_intCast_iff]
    let Cz : Matrix (Fin p) (Fin p) (ZMod p) := fun i j => (c (i.val + j.val) : ZMod p)
    have hdet : ((Matrix.det (fun i j : Fin p => c (i.val + j.val)) : ℤ) : ZMod p) = Cz.det := by
      change (Int.castRingHom (ZMod p)) (Matrix.det (fun i j : Fin p => c (i.val + j.val))) = Cz.det
      rw [Matrix.det_apply, Matrix.det_apply]
      simp [Cz, map_sum, map_prod]
    rw [hdet]
    have hzero : ∀ i j : Fin p, j < i → Cz i (Fin.rev j) = 0 := by
      intro i j hij
      unfold Cz
      have hlt : i.val + (Fin.rev j).val - p < p := by
        simp [Fin.val_rev]
        omega
      have hsum : i.val + (Fin.rev j).val = p + (i.val + (Fin.rev j).val - p) := by
        simp [Fin.val_rev]
        omega
      rw [hsum]
      exact c_p_add_eq_zero p (i.val + (Fin.rev j).val - p) hp h_odd hlt
    have hdiag : ∀ i : Fin p, Cz i (Fin.rev i) = Cz 0 (Fin.rev 0) := by
      intro i
      unfold Cz
      apply congrArg (fun n => (c n : ZMod p))
      simp [Fin.val_rev]
      omega
    have hanti := det_antidiagonal_const p Cz hzero hdiag
    rw [hanti, sign_revPerm]
    have hc : Cz 0 (Fin.rev 0) = (-1 : ZMod p)^((p-1)/2) := by
      unfold Cz
      have hval : (Fin.rev (0 : Fin p)).val = p-1 := by rfl
      rw [hval]
      simpa using c_pred_cast p hp h_odd
    rw [hc]
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two h_odd
    have hmhalf : (p - 1) / 2 = m := by omega
    rw [hmhalf, hm]
    rw [show 2 * m + 1 - 1 = 2*m by omega]
    have hexp : (2 * m + 1) * (2 * m) / 2 = (2 * m + 1) * m := by
      rw [show (2 * m + 1) * (2 * m) = ((2 * m + 1) * m) * 2 by ring]
      rw [mul_comm (((2 * m + 1) * m)) 2]
      exact Nat.mul_div_right ((2 * m + 1) * m) (by norm_num : 0 < 2)
    rw [hexp]
    have hunitcast : ((((-1 : ℤˣ) ^ ((2*m+1)*m) : ℤˣ) : ZMod (2*m+1))) = (-1 : ZMod (2*m+1))^((2*m+1)*m) := by
      simp
    rw [hunitcast]
    rw [mul_comm (2*m+1) m]
    have hpowdiag : (((-1 : ZMod (2*m+1))^m) ^ (2*m+1)) = (-1 : ZMod (2*m+1)) ^ (m*(2*m+1)) := by
      rw [← pow_mul]
    rw [hpowdiag]
    have hsquare : ((-1 : ZMod (2*m+1)) ^ (m * (2 * m + 1))) * ((-1 : ZMod (2*m+1)) ^ (m * (2 * m + 1))) = 1 := by
      rw [← pow_add]
      have : m * (2 * m + 1) + m * (2 * m + 1) = 2 * (m * (2 * m + 1)) := by ring
      rw [this, pow_mul]
      simp
    simpa using hsquare
