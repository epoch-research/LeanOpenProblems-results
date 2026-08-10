import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix
open scoped BigOperators

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
    have h2 := (Choose.choose_modEq_choose_mod_mul_choose_div (n := 2*u) (k := u) (p := p))
    rw [← ZMod.intCast_eq_intCast_iff] at h2
    have hp0 : 0 < p := Nat.pos_of_ne_zero hp.ne_zero
    have hu_mod : u % p = u := Nat.mod_eq_of_lt hu
    have hu_div : u / p = 0 := Nat.div_eq_of_lt hu
    have hpudiv : (p+u)/p = 1 := by
      rw [Nat.add_comm, Nat.add_div_right _ hp0, hu_div, zero_add]
    have hpumod : (p+u)%p = u := by simp [Nat.add_mod, hu_mod]
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
    have hpumod : (p+u)%p = u := by simp [Nat.add_mod, hu_mod]
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


def c (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k =>
    ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 2) * (choose (2 * k) k : ℤ) * (choose (2 * (n - k)) (n - k) : ℤ)

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

lemma c_p_add_eq_zero (p r : ℕ) (hp : Nat.Prime p) (hodd : p ≠ 2) (hr : r < p) :
    (c (p + r) : ZMod p) = 0 := by
  have hp0 : 0 < p := Nat.pos_of_ne_zero hp.ne_zero
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
      _ = ∑ k ∈ range (r+1), G k + ∑ x ∈ range (p-(r+1)), G ((r+1)+x) := by
        rw [Finset.sum_range_add]
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
    have hsle : s ≤ r := by omega
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
