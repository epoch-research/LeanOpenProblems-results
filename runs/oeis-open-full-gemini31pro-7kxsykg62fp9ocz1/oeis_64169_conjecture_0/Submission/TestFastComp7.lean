import FormalConjectures.Util.ProblemImports

def inv (a m : ℕ) : ℕ :=
  let (x, _) := Nat.xgcd a m
  ((x % (m : ℤ)) + (m : ℤ)) % (m : ℤ) |>.toNat

def loop (n p mod_val mod_e : ℕ) : ℕ × ℤ :=
  Id.run do
    let mut val : ℤ := 0
    let mut unit : ℕ := 0
    for i in [1:n+1] do
      let mut v_i := 0
      let mut u_i := i
      while u_i % p == 0 do
        v_i := v_i + 1
        u_i := u_i / p
      
      let term_u := inv u_i mod_val
      let term_v : ℤ := - (v_i : ℤ)
      
      if unit == 0 then
        val := term_v
        unit := term_u
      else
        let min_v := min val term_v
        
        let mut p_val := 1
        for _ in [0:(val - min_v).toNat] do p_val := (p_val * p) % mod_val
        
        let mut p_term := 1
        for _ in [0:(term_v - min_v).toNat] do p_term := (p_term * p) % mod_val
        
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

#eval! loop 283686647 16843 4778931189407 3
