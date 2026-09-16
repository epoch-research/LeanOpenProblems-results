import FormalConjectures.Util.ProblemImports

def pow_mod (base exp m : ℕ) : ℕ :=
  if h : exp = 0 then 1
  else
    have : exp / 2 < exp := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
    let half := pow_mod base (exp / 2) m
    let half_sq := (half * half) % m
    if exp % 2 == 1 then (half_sq * base) % m else half_sq
termination_by exp

def inv (a p mod_val mod_e : ℕ) : ℕ :=
  let phi := p^(mod_e - 1) * (p - 1)
  pow_mod a (phi - 1) mod_val

def loop (n p mod_e : ℕ) : ℕ × ℤ :=
  Id.run do
    let mod_val := p^mod_e
    let mut val : ℤ := 0
    let mut unit : ℕ := 0
      
    for i in [1:n+1] do
      let mut v_i := 0
      let mut u_i := i
      while u_i % p == 0 do
        v_i := v_i + 1
        u_i := u_i / p
        
      let term_u := inv u_i p mod_val mod_e
      let term_v : ℤ := - (v_i : ℤ)
      
      if unit == 0 then
        val := term_v
        unit := term_u
      else
        let min_v := min val term_v
        
        let p_val := p^(val - min_v).toNat % mod_val
        let p_term := p^(term_v - min_v).toNat % mod_val
        
        let mut new_unit := (unit * p_val + term_u * p_term) % mod_val
        let mut min_v_mut := min_v
        
        while new_unit > 0 && new_unit % p == 0 && min_v_mut < mod_e do
          new_unit := new_unit / p
          min_v_mut := min_v_mut + 1
          
        if new_unit == 0 then
          val := mod_e
          unit := 0
        else
          val := min_v_mut
          unit := new_unit
    return (unit, val)

#eval! loop 283686647 16843 3
