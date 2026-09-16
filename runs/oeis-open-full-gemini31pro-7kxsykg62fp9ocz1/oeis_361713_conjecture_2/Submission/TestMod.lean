import Submission.InvTable

def M : ℕ := 1341068619663964900807

def extract_7 (x : ℕ) : ℕ × ℕ :=
  if x % 117649 == 0 then (6, x / 117649)
  else if x % 16807 == 0 then (5, x / 16807)
  else if x % 2401 == 0 then (4, x / 2401)
  else if x % 343 == 0 then (3, x / 343)
  else if x % 49 == 0 then (2, x / 49)
  else if x % 7 == 0 then (1, x / 7)
  else (0, x)

def step_mod (n : ℕ) (st : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let (k, c1_v, c1_u, c2_v, c2_u, acc) := st
  if k < n then
    let c1 := if c1_v >= 25 then 0 else (c1_u * (7^c1_v)) % M
    let c2 := if c2_v >= 25 then 0 else (c2_u * (7^c2_v)) % M
    let acc' := (acc + c1^2 * c2^2) % M
    
    let (v1, u1) := extract_7 (n - k)
    let (v2, u2) := extract_7 (k + 1)
    let c1_v' := c1_v + v1 - v2
    let c1_u' := (c1_u * u1 * modinv_table u2) % M
    
    let (v3, u3) := extract_7 (n + k)
    let c2_v' := c2_v + v3 - v2
    let c2_u' := (c2_u * u3 * modinv_table u2) % M
    
    (k + 1, c1_v', c1_u', c2_v', c2_u', acc')
  else
    st

def step_mod_1000 (n : ℕ) (st : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  match 1000 with
  | 0 => st
  | _ => st -- wait, I can just use a loop

def loop_mod (n : ℕ) (fuel : ℕ) (st : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  match fuel with
  | 0 => st
  | f + 1 => loop_mod n f (step_mod n st)

set_option maxHeartbeats 0
set_option maxRecDepth 2000000

theorem test_mod : loop_mod 117649 1000 (0, 0, 1, 0, 1, 0) = (1000, 6, 1300851660100734796944, 6, 926692386075322006538, 862386337684943465605) := by
  decide
