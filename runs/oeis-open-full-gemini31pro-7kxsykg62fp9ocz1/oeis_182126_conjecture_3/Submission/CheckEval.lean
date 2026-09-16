import Mathlib

open Nat

def p_n (k : ℕ) : ℕ :=
  if k = 1 then 2
  else if k = 2 then 3
  else if k = 3 then 5
  else if k = 4 then 7
  else if k = 5 then 11
  else if k = 6 then 13
  else if k = 7 then 17
  else if k = 8 then 19
  else if k = 9 then 23
  else if k = 10 then 29
  else if k = 11 then 31
  else if k = 12 then 37
  else if k = 13 then 41
  else if k = 14 then 43
  else if k = 15 then 47
  else if k = 16 then 53
  else if k = 17 then 59
  else if k = 18 then 61
  else if k = 19 then 67
  else if k = 20 then 71
  else if k = 21 then 73
  else if k = 22 then 79
  else if k = 23 then 83
  else if k = 24 then 89
  else if k = 25 then 97
  else if k = 26 then 101
  else if k = 27 then 103
  else if k = 28 then 107
  else if k = 29 then 109
  else if k = 30 then 113
  else if k = 31 then 127
  else if k = 32 then 131
  else if k = 33 then 137
  else if k = 34 then 139
  else if k = 35 then 149
  else if k = 36 then 151
  else if k = 37 then 157
  else if k = 38 then 163
  else if k = 39 then 167
  else if k = 40 then 173
  else if k = 41 then 179
  else if k = 42 then 181
  else if k = 43 then 191
  else if k = 44 then 193
  else if k = 45 then 197
  else if k = 46 then 199
  else if k = 47 then 211
  else if k = 48 then 223
  else if k = 49 then 227
  else if k = 50 then 229
  else if k = 51 then 233
  else if k = 52 then 239
  else if k = 53 then 241
  else if k = 54 then 251
  else if k = 55 then 257
  else if k = 56 then 263
  else if k = 57 then 269
  else if k = 58 then 271
  else if k = 59 then 277
  else if k = 60 then 281
  else if k = 61 then 283
  else if k = 62 then 293
  else if k = 63 then 307
  else 0

def my_a (n : ℕ) : ℕ := (p_n n * p_n (n + 1)) % p_n (n + 2)

#eval my_a 1
#eval my_a 3
#eval my_a 5
#eval my_a 8
#eval my_a 10
#eval my_a 14
#eval my_a 15
#eval my_a 61

