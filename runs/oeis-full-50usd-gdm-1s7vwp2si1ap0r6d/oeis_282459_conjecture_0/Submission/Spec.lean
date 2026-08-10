import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

/--
A282459: Number of composite numbers of the form $2n - 2^k + 1$ ($k > 0, 2^k < 2n + 1$).
-/
def A282459 (n : ℕ) : ℕ :=
  -- The upper bound for k is $\lfloor \log_2(2n+1) \rfloor$.
  let upper_k : ℕ := log 2 (2 * n + 1)
  -- The set of $k$ values is $1 \le k \le \lfloor \log_2(2n+1) \rfloor$.
  let s := Finset.Icc 1 upper_k

  -- A natural number $m$ is composite if $m > 1$ and $m$ is not a prime.
  -- We must use Nat.Prime explicitly in this context.
  let is_composite (m : ℕ) : Prop := 1 < m ∧ ¬ Nat.Prime m

  -- The value we are checking for compositeness. The subtraction is safe since $2^k \le 2n+1$.
  -- The subtraction is safe because $k \le \log_2(2n+1)$, which implies $2^k \le 2n+1$.
  let seq_val (k : ℕ) : ℕ := 2 * n + 1 - 2 ^ k

  -- We count how many $k$ in the set $s$ make `seq_val k` composite.
  Finset.card (Finset.filter (fun k : ℕ => is_composite (seq_val k)) s)

lemma A282459_pos_of_exists (n : ℕ) (k : ℕ) (hk : k ∈ Finset.Icc 1 (log 2 (2 * n + 1)))
    (h_comp : 1 < 2 * n + 1 - 2 ^ k ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ k)) : A282459 n > 0 := by
  have h_comp_aux : (1 < 2 * n + 1 - 2 ^ k ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ k)) := h_comp
  unfold A282459
  dsimp
  have hk_filter : k ∈ Finset.filter (fun k => (1 < 2 * n + 1 - 2 ^ k ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ k))) (Finset.Icc 1 (log 2 (2 * n + 1))) := by
    rw [Finset.mem_filter]
    exact ⟨hk, h_comp_aux⟩
  have h_nonempty : (Finset.filter (fun k => (1 < 2 * n + 1 - 2 ^ k ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ k))) (Finset.Icc 1 (log 2 (2 * n + 1)))).Nonempty := by
    exact ⟨k, hk_filter⟩
  exact Finset.card_pos.mpr h_nonempty

lemma k_in_Icc (n k : ℕ) (hk1 : 1 ≤ k) (hk2 : 2^k ≤ 2*n+1) : k ∈ Finset.Icc 1 (log 2 (2*n+1)) := by
  rw [Finset.mem_Icc]
  refine ⟨hk1, ?_⟩
  exact Nat.le_log_of_pow_le Nat.one_lt_two hk2

lemma dvd_of_mod_eq (N k p : ℕ) (hN : N % p = 2^k % p) (hk : 2^k ≤ N) : p ∣ N - 2^k := by
  have h_modeq : 2^k ≡ N [MOD p] := by
    exact hN.symm
  exact (Nat.modEq_iff_dvd' hk).mp h_modeq

lemma composite_of_dvd (N : ℕ) (k : ℕ) (p : ℕ) (hp : p.Prime) (hdvd : p ∣ N - 2^k) (hgt : p < N - 2^k) (h1 : 1 < N - 2^k) :
    1 < N - 2^k ∧ ¬ Nat.Prime (N - 2^k) := by
  refine ⟨h1, ?_⟩
  intro h_prime
  have h_dvd_eq : p = N - 2^k := by
    exact ((Nat.Prime.dvd_iff_eq h_prime hp.ne_one).mp hdvd).symm
  omega

lemma composite_of_proper_divisor (N : ℕ) (k : ℕ) (d : ℕ) (hd1 : 1 < d) (hd2 : d < N - 2^k) (hdvd : d ∣ N - 2^k) :
    1 < N - 2^k ∧ ¬ Nat.Prime (N - 2^k) := by
  refine ⟨by omega, ?_⟩
  intro h_prime
  have h_dvd_eq : d = 1 ∨ d = N - 2^k := Nat.Prime.eq_one_or_self_of_dvd h_prime d hdvd
  rcases h_dvd_eq with h_eq1 | h_eq2
  · omega
  · omega

lemma hk_of_ge (A B bound_A bound_B : ℕ) (hA : A ≥ bound_A) (hB : B ≤ bound_B) (h_bound : bound_B ≤ bound_A) : B ≤ A := by
  omega

lemma gt_of_ge (A B C bound_A bound_B bound_C : ℕ) (hA : A ≥ bound_A) (hB : B ≤ bound_B) (hC : C ≤ bound_C) (h_bound : bound_B + bound_C < bound_A) : C < A - B := by
  omega

lemma h1_of_ge (A B bound_A bound_B : ℕ) (hA : A ≥ bound_A) (hB : B ≤ bound_B) (h_bound : bound_B + 1 < bound_A) : 1 < A - B := by
  omega

lemma hp3 : Nat.Prime 3 := Nat.prime_three
lemma hp5 : Nat.Prime 5 := by decide
lemma hp7 : Nat.Prime 7 := by decide
lemma hp11 : Nat.Prime 11 := by decide
lemma hp13 : Nat.Prime 13 := by decide
lemma hp17 : Nat.Prime 17 := by decide
lemma hp19 : Nat.Prime 19 := by decide
lemma hp23 : Nat.Prime 23 := by decide
lemma hp29 : Nat.Prime 29 := by decide
lemma hp31 : Nat.Prime 31 := by decide
lemma hp37 : Nat.Prime 37 := by decide
lemma hp41 : Nat.Prime 41 := by decide
lemma hp43 : Nat.Prime 43 := by decide
lemma hp47 : Nat.Prime 47 := by decide
lemma hp53 : Nat.Prime 53 := by decide
lemma hp59 : Nat.Prime 59 := by decide
lemma hp73 : Nat.Prime 73 := by decide

def certificate_k_block_0 (n : ℕ) : ℕ :=
  (if n ≤ 102 then (if n ≤ 77 then (if n ≤ 65 then (if n ≤ 59 then (if n ≤ 56 then (if n ≤ 54 then (if n ≤ 53 then 1 else 2) else (if n ≤ 55 then 4 else 1)) else (if n ≤ 58 then (if n ≤ 57 then 2 else 1) else 1)) else (if n ≤ 62 then (if n ≤ 61 then (if n ≤ 60 then 2 else 3) else 1) else (if n ≤ 64 then (if n ≤ 63 then 2 else 2) else 1))) else (if n ≤ 71 then (if n ≤ 68 then (if n ≤ 67 then (if n ≤ 66 then 2 else 1) else 1) else (if n ≤ 70 then (if n ≤ 69 then 2 else 4) else 1)) else (if n ≤ 74 then (if n ≤ 73 then (if n ≤ 72 then 2 else 1) else 1) else (if n ≤ 76 then (if n ≤ 75 then 2 else 3) else 1)))) else (if n ≤ 90 then (if n ≤ 84 then (if n ≤ 81 then (if n ≤ 79 then (if n ≤ 78 then 2 else 2) else (if n ≤ 80 then 1 else 2)) else (if n ≤ 83 then (if n ≤ 82 then 2 else 1) else 2)) else (if n ≤ 87 then (if n ≤ 86 then (if n ≤ 85 then 4 else 1) else 2) else (if n ≤ 89 then (if n ≤ 88 then 1 else 1) else 2))) else (if n ≤ 96 then (if n ≤ 93 then (if n ≤ 92 then (if n ≤ 91 then 3 else 1) else 2) else (if n ≤ 95 then (if n ≤ 94 then 2 else 1) else 2)) else (if n ≤ 99 then (if n ≤ 98 then (if n ≤ 97 then 3 else 1) else 2) else (if n ≤ 101 then (if n ≤ 100 then 4 else 1) else 2))))) else (if n ≤ 127 then (if n ≤ 115 then (if n ≤ 109 then (if n ≤ 106 then (if n ≤ 104 then (if n ≤ 103 then 1 else 1) else (if n ≤ 105 then 2 else 3)) else (if n ≤ 108 then (if n ≤ 107 then 1 else 2) else 2)) else (if n ≤ 112 then (if n ≤ 111 then (if n ≤ 110 then 1 else 2) else 3) else (if n ≤ 114 then (if n ≤ 113 then 1 else 2) else 4))) else (if n ≤ 121 then (if n ≤ 118 then (if n ≤ 117 then (if n ≤ 116 then 1 else 2) else 1) else (if n ≤ 120 then (if n ≤ 119 then 1 else 2) else 3)) else (if n ≤ 124 then (if n ≤ 123 then (if n ≤ 122 then 1 else 2) else 2) else (if n ≤ 126 then (if n ≤ 125 then 1 else 2) else 1)))) else (if n ≤ 140 then (if n ≤ 134 then (if n ≤ 131 then (if n ≤ 129 then (if n ≤ 128 then 1 else 2) else (if n ≤ 130 then 4 else 1)) else (if n ≤ 133 then (if n ≤ 132 then 2 else 1) else 1)) else (if n ≤ 137 then (if n ≤ 136 then (if n ≤ 135 then 2 else 3) else 1) else (if n ≤ 139 then (if n ≤ 138 then 2 else 2) else 1))) else (if n ≤ 146 then (if n ≤ 143 then (if n ≤ 142 then (if n ≤ 141 then 2 else 5) else 1) else (if n ≤ 145 then (if n ≤ 144 then 2 else 4) else 1)) else (if n ≤ 149 then (if n ≤ 148 then (if n ≤ 147 then 2 else 1) else 1) else (if n ≤ 151 then (if n ≤ 150 then 2 else 3) else 1))))))

def certificate_k_block_1 (n : ℕ) : ℕ :=
  (if n ≤ 202 then (if n ≤ 177 then (if n ≤ 165 then (if n ≤ 159 then (if n ≤ 156 then (if n ≤ 154 then (if n ≤ 153 then 2 else 2) else (if n ≤ 155 then 1 else 2)) else (if n ≤ 158 then (if n ≤ 157 then 7 else 1) else 2)) else (if n ≤ 162 then (if n ≤ 161 then (if n ≤ 160 then 4 else 1) else 2) else (if n ≤ 164 then (if n ≤ 163 then 1 else 1) else 2))) else (if n ≤ 171 then (if n ≤ 168 then (if n ≤ 167 then (if n ≤ 166 then 3 else 1) else 2) else (if n ≤ 170 then (if n ≤ 169 then 2 else 1) else 2)) else (if n ≤ 174 then (if n ≤ 173 then (if n ≤ 172 then 1 else 1) else 2) else (if n ≤ 176 then (if n ≤ 175 then 4 else 1) else 2)))) else (if n ≤ 190 then (if n ≤ 184 then (if n ≤ 181 then (if n ≤ 179 then (if n ≤ 178 then 1 else 1) else (if n ≤ 180 then 2 else 3)) else (if n ≤ 183 then (if n ≤ 182 then 1 else 2) else 2)) else (if n ≤ 187 then (if n ≤ 186 then (if n ≤ 185 then 1 else 2) else 2) else (if n ≤ 189 then (if n ≤ 188 then 1 else 2) else 4))) else (if n ≤ 196 then (if n ≤ 193 then (if n ≤ 192 then (if n ≤ 191 then 1 else 2) else 1) else (if n ≤ 195 then (if n ≤ 194 then 1 else 2) else 3)) else (if n ≤ 199 then (if n ≤ 198 then (if n ≤ 197 then 1 else 2) else 2) else (if n ≤ 201 then (if n ≤ 200 then 1 else 2) else 6))))) else (if n ≤ 227 then (if n ≤ 215 then (if n ≤ 209 then (if n ≤ 206 then (if n ≤ 204 then (if n ≤ 203 then 1 else 2) else (if n ≤ 205 then 4 else 1)) else (if n ≤ 208 then (if n ≤ 207 then 2 else 1) else 1)) else (if n ≤ 212 then (if n ≤ 211 then (if n ≤ 210 then 2 else 3) else 1) else (if n ≤ 214 then (if n ≤ 213 then 2 else 2) else 1))) else (if n ≤ 221 then (if n ≤ 218 then (if n ≤ 217 then (if n ≤ 216 then 2 else 3) else 1) else (if n ≤ 220 then (if n ≤ 219 then 2 else 4) else 1)) else (if n ≤ 224 then (if n ≤ 223 then (if n ≤ 222 then 2 else 1) else 1) else (if n ≤ 226 then (if n ≤ 225 then 2 else 3) else 1)))) else (if n ≤ 240 then (if n ≤ 234 then (if n ≤ 231 then (if n ≤ 229 then (if n ≤ 228 then 2 else 2) else (if n ≤ 230 then 1 else 2)) else (if n ≤ 233 then (if n ≤ 232 then 8 else 1) else 2)) else (if n ≤ 237 then (if n ≤ 236 then (if n ≤ 235 then 4 else 1) else 2) else (if n ≤ 239 then (if n ≤ 238 then 1 else 1) else 2))) else (if n ≤ 246 then (if n ≤ 243 then (if n ≤ 242 then (if n ≤ 241 then 3 else 1) else 2) else (if n ≤ 245 then (if n ≤ 244 then 2 else 1) else 2)) else (if n ≤ 249 then (if n ≤ 248 then (if n ≤ 247 then 1 else 1) else 2) else (if n ≤ 251 then (if n ≤ 250 then 4 else 1) else 2))))))

def certificate_k_block_2 (n : ℕ) : ℕ :=
  (if n ≤ 302 then (if n ≤ 277 then (if n ≤ 265 then (if n ≤ 259 then (if n ≤ 256 then (if n ≤ 254 then (if n ≤ 253 then 1 else 1) else (if n ≤ 255 then 2 else 3)) else (if n ≤ 258 then (if n ≤ 257 then 1 else 2) else 2)) else (if n ≤ 262 then (if n ≤ 261 then (if n ≤ 260 then 1 else 2) else 3) else (if n ≤ 264 then (if n ≤ 263 then 1 else 2) else 4))) else (if n ≤ 271 then (if n ≤ 268 then (if n ≤ 267 then (if n ≤ 266 then 1 else 2) else 1) else (if n ≤ 270 then (if n ≤ 269 then 1 else 2) else 3)) else (if n ≤ 274 then (if n ≤ 273 then (if n ≤ 272 then 1 else 2) else 2) else (if n ≤ 276 then (if n ≤ 275 then 1 else 2) else 1)))) else (if n ≤ 290 then (if n ≤ 284 then (if n ≤ 281 then (if n ≤ 279 then (if n ≤ 278 then 1 else 2) else (if n ≤ 280 then 4 else 1)) else (if n ≤ 283 then (if n ≤ 282 then 2 else 1) else 1)) else (if n ≤ 287 then (if n ≤ 286 then (if n ≤ 285 then 2 else 3) else 1) else (if n ≤ 289 then (if n ≤ 288 then 2 else 2) else 1))) else (if n ≤ 296 then (if n ≤ 293 then (if n ≤ 292 then (if n ≤ 291 then 2 else 2) else 1) else (if n ≤ 295 then (if n ≤ 294 then 2 else 4) else 1)) else (if n ≤ 299 then (if n ≤ 298 then (if n ≤ 297 then 2 else 1) else 1) else (if n ≤ 301 then (if n ≤ 300 then 2 else 3) else 1))))) else (if n ≤ 327 then (if n ≤ 315 then (if n ≤ 309 then (if n ≤ 306 then (if n ≤ 304 then (if n ≤ 303 then 2 else 2) else (if n ≤ 305 then 1 else 2)) else (if n ≤ 308 then (if n ≤ 307 then 5 else 1) else 2)) else (if n ≤ 312 then (if n ≤ 311 then (if n ≤ 310 then 4 else 1) else 2) else (if n ≤ 314 then (if n ≤ 313 then 1 else 1) else 2))) else (if n ≤ 321 then (if n ≤ 318 then (if n ≤ 317 then (if n ≤ 316 then 3 else 1) else 2) else (if n ≤ 320 then (if n ≤ 319 then 2 else 1) else 2)) else (if n ≤ 324 then (if n ≤ 323 then (if n ≤ 322 then 3 else 1) else 2) else (if n ≤ 326 then (if n ≤ 325 then 4 else 1) else 2)))) else (if n ≤ 340 then (if n ≤ 334 then (if n ≤ 331 then (if n ≤ 329 then (if n ≤ 328 then 1 else 1) else (if n ≤ 330 then 2 else 3)) else (if n ≤ 333 then (if n ≤ 332 then 1 else 2) else 2)) else (if n ≤ 337 then (if n ≤ 336 then (if n ≤ 335 then 1 else 2) else 2) else (if n ≤ 339 then (if n ≤ 338 then 1 else 2) else 4))) else (if n ≤ 346 then (if n ≤ 343 then (if n ≤ 342 then (if n ≤ 341 then 1 else 2) else 1) else (if n ≤ 345 then (if n ≤ 344 then 1 else 2) else 3)) else (if n ≤ 349 then (if n ≤ 348 then (if n ≤ 347 then 1 else 2) else 2) else (if n ≤ 351 then (if n ≤ 350 then 1 else 2) else 4))))))

def certificate_k_block_3 (n : ℕ) : ℕ :=
  (if n ≤ 402 then (if n ≤ 377 then (if n ≤ 365 then (if n ≤ 359 then (if n ≤ 356 then (if n ≤ 354 then (if n ≤ 353 then 1 else 2) else (if n ≤ 355 then 4 else 1)) else (if n ≤ 358 then (if n ≤ 357 then 2 else 1) else 1)) else (if n ≤ 362 then (if n ≤ 361 then (if n ≤ 360 then 2 else 3) else 1) else (if n ≤ 364 then (if n ≤ 363 then 2 else 2) else 1))) else (if n ≤ 371 then (if n ≤ 368 then (if n ≤ 367 then (if n ≤ 366 then 2 else 6) else 1) else (if n ≤ 370 then (if n ≤ 369 then 2 else 4) else 1)) else (if n ≤ 374 then (if n ≤ 373 then (if n ≤ 372 then 2 else 1) else 1) else (if n ≤ 376 then (if n ≤ 375 then 2 else 3) else 1)))) else (if n ≤ 390 then (if n ≤ 384 then (if n ≤ 381 then (if n ≤ 379 then (if n ≤ 378 then 2 else 2) else (if n ≤ 380 then 1 else 2)) else (if n ≤ 383 then (if n ≤ 382 then 1 else 1) else 2)) else (if n ≤ 387 then (if n ≤ 386 then (if n ≤ 385 then 4 else 1) else 2) else (if n ≤ 389 then (if n ≤ 388 then 1 else 1) else 2))) else (if n ≤ 396 then (if n ≤ 393 then (if n ≤ 392 then (if n ≤ 391 then 3 else 1) else 2) else (if n ≤ 395 then (if n ≤ 394 then 2 else 1) else 2)) else (if n ≤ 399 then (if n ≤ 398 then (if n ≤ 397 then 2 else 1) else 2) else (if n ≤ 401 then (if n ≤ 400 then 4 else 1) else 2))))) else (if n ≤ 427 then (if n ≤ 415 then (if n ≤ 409 then (if n ≤ 406 then (if n ≤ 404 then (if n ≤ 403 then 1 else 1) else (if n ≤ 405 then 2 else 3)) else (if n ≤ 408 then (if n ≤ 407 then 1 else 2) else 2)) else (if n ≤ 412 then (if n ≤ 411 then (if n ≤ 410 then 1 else 2) else 5) else (if n ≤ 414 then (if n ≤ 413 then 1 else 2) else 4))) else (if n ≤ 421 then (if n ≤ 418 then (if n ≤ 417 then (if n ≤ 416 then 1 else 2) else 1) else (if n ≤ 420 then (if n ≤ 419 then 1 else 2) else 3)) else (if n ≤ 424 then (if n ≤ 423 then (if n ≤ 422 then 1 else 2) else 2) else (if n ≤ 426 then (if n ≤ 425 then 1 else 2) else 3)))) else (if n ≤ 440 then (if n ≤ 434 then (if n ≤ 431 then (if n ≤ 429 then (if n ≤ 428 then 1 else 2) else (if n ≤ 430 then 4 else 1)) else (if n ≤ 433 then (if n ≤ 432 then 2 else 1) else 1)) else (if n ≤ 437 then (if n ≤ 436 then (if n ≤ 435 then 2 else 3) else 1) else (if n ≤ 439 then (if n ≤ 438 then 2 else 2) else 1))) else (if n ≤ 446 then (if n ≤ 443 then (if n ≤ 442 then (if n ≤ 441 then 2 else 4) else 1) else (if n ≤ 445 then (if n ≤ 444 then 2 else 4) else 1)) else (if n ≤ 449 then (if n ≤ 448 then (if n ≤ 447 then 2 else 1) else 1) else (if n ≤ 451 then (if n ≤ 450 then 2 else 3) else 1))))))

def certificate_k_block_4 (n : ℕ) : ℕ :=
  (if n ≤ 502 then (if n ≤ 477 then (if n ≤ 465 then (if n ≤ 459 then (if n ≤ 456 then (if n ≤ 454 then (if n ≤ 453 then 2 else 2) else (if n ≤ 455 then 1 else 2)) else (if n ≤ 458 then (if n ≤ 457 then 1 else 1) else 2)) else (if n ≤ 462 then (if n ≤ 461 then (if n ≤ 460 then 4 else 1) else 2) else (if n ≤ 464 then (if n ≤ 463 then 1 else 1) else 2))) else (if n ≤ 471 then (if n ≤ 468 then (if n ≤ 467 then (if n ≤ 466 then 3 else 1) else 2) else (if n ≤ 470 then (if n ≤ 469 then 2 else 1) else 2)) else (if n ≤ 474 then (if n ≤ 473 then (if n ≤ 472 then 5 else 1) else 2) else (if n ≤ 476 then (if n ≤ 475 then 4 else 1) else 2)))) else (if n ≤ 490 then (if n ≤ 484 then (if n ≤ 481 then (if n ≤ 479 then (if n ≤ 478 then 1 else 1) else (if n ≤ 480 then 2 else 3)) else (if n ≤ 483 then (if n ≤ 482 then 1 else 2) else 2)) else (if n ≤ 487 then (if n ≤ 486 then (if n ≤ 485 then 1 else 2) else 1) else (if n ≤ 489 then (if n ≤ 488 then 1 else 2) else 4))) else (if n ≤ 496 then (if n ≤ 493 then (if n ≤ 492 then (if n ≤ 491 then 1 else 2) else 1) else (if n ≤ 495 then (if n ≤ 494 then 1 else 2) else 3)) else (if n ≤ 499 then (if n ≤ 498 then (if n ≤ 497 then 1 else 2) else 2) else (if n ≤ 501 then (if n ≤ 500 then 1 else 2) else 2))))) else (if n ≤ 527 then (if n ≤ 515 then (if n ≤ 509 then (if n ≤ 506 then (if n ≤ 504 then (if n ≤ 503 then 1 else 2) else (if n ≤ 505 then 4 else 1)) else (if n ≤ 508 then (if n ≤ 507 then 2 else 1) else 1)) else (if n ≤ 512 then (if n ≤ 511 then (if n ≤ 510 then 2 else 3) else 1) else (if n ≤ 514 then (if n ≤ 513 then 2 else 2) else 1))) else (if n ≤ 521 then (if n ≤ 518 then (if n ≤ 517 then (if n ≤ 516 then 2 else 3) else 1) else (if n ≤ 520 then (if n ≤ 519 then 2 else 4) else 1)) else (if n ≤ 524 then (if n ≤ 523 then (if n ≤ 522 then 2 else 1) else 1) else (if n ≤ 526 then (if n ≤ 525 then 2 else 3) else 1)))) else (if n ≤ 540 then (if n ≤ 534 then (if n ≤ 531 then (if n ≤ 529 then (if n ≤ 528 then 2 else 2) else (if n ≤ 530 then 1 else 2)) else (if n ≤ 533 then (if n ≤ 532 then 3 else 1) else 2)) else (if n ≤ 537 then (if n ≤ 536 then (if n ≤ 535 then 4 else 1) else 2) else (if n ≤ 539 then (if n ≤ 538 then 1 else 1) else 2))) else (if n ≤ 546 then (if n ≤ 543 then (if n ≤ 542 then (if n ≤ 541 then 3 else 1) else 2) else (if n ≤ 545 then (if n ≤ 544 then 2 else 1) else 2)) else (if n ≤ 549 then (if n ≤ 548 then (if n ≤ 547 then 9 else 1) else 2) else (if n ≤ 551 then (if n ≤ 550 then 4 else 1) else 2))))))

def certificate_k_block_5 (n : ℕ) : ℕ :=
  (if n ≤ 602 then (if n ≤ 577 then (if n ≤ 565 then (if n ≤ 559 then (if n ≤ 556 then (if n ≤ 554 then (if n ≤ 553 then 1 else 1) else (if n ≤ 555 then 2 else 3)) else (if n ≤ 558 then (if n ≤ 557 then 1 else 2) else 2)) else (if n ≤ 562 then (if n ≤ 561 then (if n ≤ 560 then 1 else 2) else 8) else (if n ≤ 564 then (if n ≤ 563 then 1 else 2) else 4))) else (if n ≤ 571 then (if n ≤ 568 then (if n ≤ 567 then (if n ≤ 566 then 1 else 2) else 1) else (if n ≤ 570 then (if n ≤ 569 then 1 else 2) else 3)) else (if n ≤ 574 then (if n ≤ 573 then (if n ≤ 572 then 1 else 2) else 2) else (if n ≤ 576 then (if n ≤ 575 then 1 else 2) else 7)))) else (if n ≤ 590 then (if n ≤ 584 then (if n ≤ 581 then (if n ≤ 579 then (if n ≤ 578 then 1 else 2) else (if n ≤ 580 then 4 else 1)) else (if n ≤ 583 then (if n ≤ 582 then 2 else 1) else 1)) else (if n ≤ 587 then (if n ≤ 586 then (if n ≤ 585 then 2 else 3) else 1) else (if n ≤ 589 then (if n ≤ 588 then 2 else 2) else 1))) else (if n ≤ 596 then (if n ≤ 593 then (if n ≤ 592 then (if n ≤ 591 then 2 else 1) else 1) else (if n ≤ 595 then (if n ≤ 594 then 2 else 4) else 1)) else (if n ≤ 599 then (if n ≤ 598 then (if n ≤ 597 then 2 else 1) else 1) else (if n ≤ 601 then (if n ≤ 600 then 2 else 3) else 1))))) else (if n ≤ 627 then (if n ≤ 615 then (if n ≤ 609 then (if n ≤ 606 then (if n ≤ 604 then (if n ≤ 603 then 2 else 2) else (if n ≤ 605 then 1 else 2)) else (if n ≤ 608 then (if n ≤ 607 then 2 else 1) else 2)) else (if n ≤ 612 then (if n ≤ 611 then (if n ≤ 610 then 4 else 1) else 2) else (if n ≤ 614 then (if n ≤ 613 then 1 else 1) else 2))) else (if n ≤ 621 then (if n ≤ 618 then (if n ≤ 617 then (if n ≤ 616 then 3 else 1) else 2) else (if n ≤ 620 then (if n ≤ 619 then 2 else 1) else 2)) else (if n ≤ 624 then (if n ≤ 623 then (if n ≤ 622 then 1 else 1) else 2) else (if n ≤ 626 then (if n ≤ 625 then 4 else 1) else 2)))) else (if n ≤ 640 then (if n ≤ 634 then (if n ≤ 631 then (if n ≤ 629 then (if n ≤ 628 then 1 else 1) else (if n ≤ 630 then 2 else 3)) else (if n ≤ 633 then (if n ≤ 632 then 1 else 2) else 2)) else (if n ≤ 637 then (if n ≤ 636 then (if n ≤ 635 then 1 else 2) else 3) else (if n ≤ 639 then (if n ≤ 638 then 1 else 2) else 4))) else (if n ≤ 646 then (if n ≤ 643 then (if n ≤ 642 then (if n ≤ 641 then 1 else 2) else 1) else (if n ≤ 645 then (if n ≤ 644 then 1 else 2) else 3)) else (if n ≤ 649 then (if n ≤ 648 then (if n ≤ 647 then 1 else 2) else 2) else (if n ≤ 651 then (if n ≤ 650 then 1 else 2) else 7))))))

def certificate_k_block_6 (n : ℕ) : ℕ :=
  (if n ≤ 702 then (if n ≤ 677 then (if n ≤ 665 then (if n ≤ 659 then (if n ≤ 656 then (if n ≤ 654 then (if n ≤ 653 then 1 else 2) else (if n ≤ 655 then 4 else 1)) else (if n ≤ 658 then (if n ≤ 657 then 2 else 1) else 1)) else (if n ≤ 662 then (if n ≤ 661 then (if n ≤ 660 then 2 else 3) else 1) else (if n ≤ 664 then (if n ≤ 663 then 2 else 2) else 1))) else (if n ≤ 671 then (if n ≤ 668 then (if n ≤ 667 then (if n ≤ 666 then 2 else 2) else 1) else (if n ≤ 670 then (if n ≤ 669 then 2 else 4) else 1)) else (if n ≤ 674 then (if n ≤ 673 then (if n ≤ 672 then 2 else 1) else 1) else (if n ≤ 676 then (if n ≤ 675 then 2 else 3) else 1)))) else (if n ≤ 690 then (if n ≤ 684 then (if n ≤ 681 then (if n ≤ 679 then (if n ≤ 678 then 2 else 2) else (if n ≤ 680 then 1 else 2)) else (if n ≤ 683 then (if n ≤ 682 then 10 else 1) else 2)) else (if n ≤ 687 then (if n ≤ 686 then (if n ≤ 685 then 4 else 1) else 2) else (if n ≤ 689 then (if n ≤ 688 then 1 else 1) else 2))) else (if n ≤ 696 then (if n ≤ 693 then (if n ≤ 692 then (if n ≤ 691 then 3 else 1) else 2) else (if n ≤ 695 then (if n ≤ 694 then 2 else 1) else 2)) else (if n ≤ 699 then (if n ≤ 698 then (if n ≤ 697 then 1 else 1) else 2) else (if n ≤ 701 then (if n ≤ 700 then 4 else 1) else 2))))) else (if n ≤ 727 then (if n ≤ 715 then (if n ≤ 709 then (if n ≤ 706 then (if n ≤ 704 then (if n ≤ 703 then 1 else 1) else (if n ≤ 705 then 2 else 3)) else (if n ≤ 708 then (if n ≤ 707 then 1 else 2) else 2)) else (if n ≤ 712 then (if n ≤ 711 then (if n ≤ 710 then 1 else 2) else 2) else (if n ≤ 714 then (if n ≤ 713 then 1 else 2) else 4))) else (if n ≤ 721 then (if n ≤ 718 then (if n ≤ 717 then (if n ≤ 716 then 1 else 2) else 1) else (if n ≤ 720 then (if n ≤ 719 then 1 else 2) else 3)) else (if n ≤ 724 then (if n ≤ 723 then (if n ≤ 722 then 1 else 2) else 2) else (if n ≤ 726 then (if n ≤ 725 then 1 else 2) else 8)))) else (if n ≤ 740 then (if n ≤ 734 then (if n ≤ 731 then (if n ≤ 729 then (if n ≤ 728 then 1 else 2) else (if n ≤ 730 then 4 else 1)) else (if n ≤ 733 then (if n ≤ 732 then 2 else 1) else 1)) else (if n ≤ 737 then (if n ≤ 736 then (if n ≤ 735 then 2 else 3) else 1) else (if n ≤ 739 then (if n ≤ 738 then 2 else 2) else 1))) else (if n ≤ 746 then (if n ≤ 743 then (if n ≤ 742 then (if n ≤ 741 then 2 else 3) else 1) else (if n ≤ 745 then (if n ≤ 744 then 2 else 4) else 1)) else (if n ≤ 749 then (if n ≤ 748 then (if n ≤ 747 then 2 else 1) else 1) else (if n ≤ 751 then (if n ≤ 750 then 2 else 3) else 1))))))

def certificate_k_block_7 (n : ℕ) : ℕ :=
  (if n ≤ 802 then (if n ≤ 777 then (if n ≤ 765 then (if n ≤ 759 then (if n ≤ 756 then (if n ≤ 754 then (if n ≤ 753 then 2 else 2) else (if n ≤ 755 then 1 else 2)) else (if n ≤ 758 then (if n ≤ 757 then 3 else 1) else 2)) else (if n ≤ 762 then (if n ≤ 761 then (if n ≤ 760 then 4 else 1) else 2) else (if n ≤ 764 then (if n ≤ 763 then 1 else 1) else 2))) else (if n ≤ 771 then (if n ≤ 768 then (if n ≤ 767 then (if n ≤ 766 then 3 else 1) else 2) else (if n ≤ 770 then (if n ≤ 769 then 2 else 1) else 2)) else (if n ≤ 774 then (if n ≤ 773 then (if n ≤ 772 then 4 else 1) else 2) else (if n ≤ 776 then (if n ≤ 775 then 4 else 1) else 2)))) else (if n ≤ 790 then (if n ≤ 784 then (if n ≤ 781 then (if n ≤ 779 then (if n ≤ 778 then 1 else 1) else (if n ≤ 780 then 2 else 3)) else (if n ≤ 783 then (if n ≤ 782 then 1 else 2) else 2)) else (if n ≤ 787 then (if n ≤ 786 then (if n ≤ 785 then 1 else 2) else 1) else (if n ≤ 789 then (if n ≤ 788 then 1 else 2) else 4))) else (if n ≤ 796 then (if n ≤ 793 then (if n ≤ 792 then (if n ≤ 791 then 1 else 2) else 1) else (if n ≤ 795 then (if n ≤ 794 then 1 else 2) else 3)) else (if n ≤ 799 then (if n ≤ 798 then (if n ≤ 797 then 1 else 2) else 2) else (if n ≤ 801 then (if n ≤ 800 then 1 else 2) else 1))))) else (if n ≤ 827 then (if n ≤ 815 then (if n ≤ 809 then (if n ≤ 806 then (if n ≤ 804 then (if n ≤ 803 then 1 else 2) else (if n ≤ 805 then 4 else 1)) else (if n ≤ 808 then (if n ≤ 807 then 2 else 1) else 1)) else (if n ≤ 812 then (if n ≤ 811 then (if n ≤ 810 then 2 else 3) else 1) else (if n ≤ 814 then (if n ≤ 813 then 2 else 2) else 1))) else (if n ≤ 821 then (if n ≤ 818 then (if n ≤ 817 then (if n ≤ 816 then 2 else 2) else 1) else (if n ≤ 820 then (if n ≤ 819 then 2 else 4) else 1)) else (if n ≤ 824 then (if n ≤ 823 then (if n ≤ 822 then 2 else 1) else 1) else (if n ≤ 826 then (if n ≤ 825 then 2 else 3) else 1)))) else (if n ≤ 840 then (if n ≤ 834 then (if n ≤ 831 then (if n ≤ 829 then (if n ≤ 828 then 2 else 2) else (if n ≤ 830 then 1 else 2)) else (if n ≤ 833 then (if n ≤ 832 then 2 else 1) else 2)) else (if n ≤ 837 then (if n ≤ 836 then (if n ≤ 835 then 4 else 1) else 2) else (if n ≤ 839 then (if n ≤ 838 then 1 else 1) else 2))) else (if n ≤ 846 then (if n ≤ 843 then (if n ≤ 842 then (if n ≤ 841 then 3 else 1) else 2) else (if n ≤ 845 then (if n ≤ 844 then 2 else 1) else 2)) else (if n ≤ 849 then (if n ≤ 848 then (if n ≤ 847 then 3 else 1) else 2) else (if n ≤ 851 then (if n ≤ 850 then 4 else 1) else 2))))))

def certificate_k_block_8 (n : ℕ) : ℕ :=
  (if n ≤ 902 then (if n ≤ 877 then (if n ≤ 865 then (if n ≤ 859 then (if n ≤ 856 then (if n ≤ 854 then (if n ≤ 853 then 1 else 1) else (if n ≤ 855 then 2 else 3)) else (if n ≤ 858 then (if n ≤ 857 then 1 else 2) else 2)) else (if n ≤ 862 then (if n ≤ 861 then (if n ≤ 860 then 1 else 2) else 6) else (if n ≤ 864 then (if n ≤ 863 then 1 else 2) else 4))) else (if n ≤ 871 then (if n ≤ 868 then (if n ≤ 867 then (if n ≤ 866 then 1 else 2) else 1) else (if n ≤ 870 then (if n ≤ 869 then 1 else 2) else 3)) else (if n ≤ 874 then (if n ≤ 873 then (if n ≤ 872 then 1 else 2) else 2) else (if n ≤ 876 then (if n ≤ 875 then 1 else 2) else 9)))) else (if n ≤ 890 then (if n ≤ 884 then (if n ≤ 881 then (if n ≤ 879 then (if n ≤ 878 then 1 else 2) else (if n ≤ 880 then 4 else 1)) else (if n ≤ 883 then (if n ≤ 882 then 2 else 1) else 1)) else (if n ≤ 887 then (if n ≤ 886 then (if n ≤ 885 then 2 else 3) else 1) else (if n ≤ 889 then (if n ≤ 888 then 2 else 2) else 1))) else (if n ≤ 896 then (if n ≤ 893 then (if n ≤ 892 then (if n ≤ 891 then 2 else 8) else 1) else (if n ≤ 895 then (if n ≤ 894 then 2 else 4) else 1)) else (if n ≤ 899 then (if n ≤ 898 then (if n ≤ 897 then 2 else 1) else 1) else (if n ≤ 901 then (if n ≤ 900 then 2 else 3) else 1))))) else (if n ≤ 927 then (if n ≤ 915 then (if n ≤ 909 then (if n ≤ 906 then (if n ≤ 904 then (if n ≤ 903 then 2 else 2) else (if n ≤ 905 then 1 else 2)) else (if n ≤ 908 then (if n ≤ 907 then 1 else 1) else 2)) else (if n ≤ 912 then (if n ≤ 911 then (if n ≤ 910 then 4 else 1) else 2) else (if n ≤ 914 then (if n ≤ 913 then 1 else 1) else 2))) else (if n ≤ 921 then (if n ≤ 918 then (if n ≤ 917 then (if n ≤ 916 then 3 else 1) else 2) else (if n ≤ 920 then (if n ≤ 919 then 2 else 1) else 2)) else (if n ≤ 924 then (if n ≤ 923 then (if n ≤ 922 then 2 else 1) else 2) else (if n ≤ 926 then (if n ≤ 925 then 4 else 1) else 2)))) else (if n ≤ 940 then (if n ≤ 934 then (if n ≤ 931 then (if n ≤ 929 then (if n ≤ 928 then 1 else 1) else (if n ≤ 930 then 2 else 3)) else (if n ≤ 933 then (if n ≤ 932 then 1 else 2) else 2)) else (if n ≤ 937 then (if n ≤ 936 then (if n ≤ 935 then 1 else 2) else 4) else (if n ≤ 939 then (if n ≤ 938 then 1 else 2) else 4))) else (if n ≤ 946 then (if n ≤ 943 then (if n ≤ 942 then (if n ≤ 941 then 1 else 2) else 1) else (if n ≤ 945 then (if n ≤ 944 then 1 else 2) else 3)) else (if n ≤ 949 then (if n ≤ 948 then (if n ≤ 947 then 1 else 2) else 2) else (if n ≤ 951 then (if n ≤ 950 then 1 else 2) else 3))))))

def certificate_k_block_9 (n : ℕ) : ℕ :=
  (if n ≤ 1002 then (if n ≤ 977 then (if n ≤ 965 then (if n ≤ 959 then (if n ≤ 956 then (if n ≤ 954 then (if n ≤ 953 then 1 else 2) else (if n ≤ 955 then 4 else 1)) else (if n ≤ 958 then (if n ≤ 957 then 2 else 1) else 1)) else (if n ≤ 962 then (if n ≤ 961 then (if n ≤ 960 then 2 else 3) else 1) else (if n ≤ 964 then (if n ≤ 963 then 2 else 2) else 1))) else (if n ≤ 971 then (if n ≤ 968 then (if n ≤ 967 then (if n ≤ 966 then 2 else 5) else 1) else (if n ≤ 970 then (if n ≤ 969 then 2 else 4) else 1)) else (if n ≤ 974 then (if n ≤ 973 then (if n ≤ 972 then 2 else 1) else 1) else (if n ≤ 976 then (if n ≤ 975 then 2 else 3) else 1)))) else (if n ≤ 990 then (if n ≤ 984 then (if n ≤ 981 then (if n ≤ 979 then (if n ≤ 978 then 2 else 2) else (if n ≤ 980 then 1 else 2)) else (if n ≤ 983 then (if n ≤ 982 then 7 else 1) else 2)) else (if n ≤ 987 then (if n ≤ 986 then (if n ≤ 985 then 4 else 1) else 2) else (if n ≤ 989 then (if n ≤ 988 then 1 else 1) else 2))) else (if n ≤ 996 then (if n ≤ 993 then (if n ≤ 992 then (if n ≤ 991 then 3 else 1) else 2) else (if n ≤ 995 then (if n ≤ 994 then 2 else 1) else 2)) else (if n ≤ 999 then (if n ≤ 998 then (if n ≤ 997 then 2 else 1) else 2) else (if n ≤ 1001 then (if n ≤ 1000 then 4 else 1) else 2))))) else (if n ≤ 1027 then (if n ≤ 1015 then (if n ≤ 1009 then (if n ≤ 1006 then (if n ≤ 1004 then (if n ≤ 1003 then 1 else 1) else (if n ≤ 1005 then 2 else 3)) else (if n ≤ 1008 then (if n ≤ 1007 then 1 else 2) else 2)) else (if n ≤ 1012 then (if n ≤ 1011 then (if n ≤ 1010 then 1 else 2) else 1) else (if n ≤ 1014 then (if n ≤ 1013 then 1 else 2) else 4))) else (if n ≤ 1021 then (if n ≤ 1018 then (if n ≤ 1017 then (if n ≤ 1016 then 1 else 2) else 1) else (if n ≤ 1020 then (if n ≤ 1019 then 1 else 2) else 3)) else (if n ≤ 1024 then (if n ≤ 1023 then (if n ≤ 1022 then 1 else 2) else 2) else (if n ≤ 1026 then (if n ≤ 1025 then 1 else 2) else 2)))) else (if n ≤ 1040 then (if n ≤ 1034 then (if n ≤ 1031 then (if n ≤ 1029 then (if n ≤ 1028 then 1 else 2) else (if n ≤ 1030 then 4 else 1)) else (if n ≤ 1033 then (if n ≤ 1032 then 2 else 1) else 1)) else (if n ≤ 1037 then (if n ≤ 1036 then (if n ≤ 1035 then 2 else 3) else 1) else (if n ≤ 1039 then (if n ≤ 1038 then 2 else 2) else 1))) else (if n ≤ 1046 then (if n ≤ 1043 then (if n ≤ 1042 then (if n ≤ 1041 then 2 else 9) else 1) else (if n ≤ 1045 then (if n ≤ 1044 then 2 else 4) else 1)) else (if n ≤ 1049 then (if n ≤ 1048 then (if n ≤ 1047 then 2 else 1) else 1) else (if n ≤ 1051 then (if n ≤ 1050 then 2 else 3) else 1))))))

def certificate_k_block_10 (n : ℕ) : ℕ :=
  (if n ≤ 1102 then (if n ≤ 1077 then (if n ≤ 1065 then (if n ≤ 1059 then (if n ≤ 1056 then (if n ≤ 1054 then (if n ≤ 1053 then 2 else 2) else (if n ≤ 1055 then 1 else 2)) else (if n ≤ 1058 then (if n ≤ 1057 then 3 else 1) else 2)) else (if n ≤ 1062 then (if n ≤ 1061 then (if n ≤ 1060 then 4 else 1) else 2) else (if n ≤ 1064 then (if n ≤ 1063 then 1 else 1) else 2))) else (if n ≤ 1071 then (if n ≤ 1068 then (if n ≤ 1067 then (if n ≤ 1066 then 3 else 1) else 2) else (if n ≤ 1070 then (if n ≤ 1069 then 2 else 1) else 2)) else (if n ≤ 1074 then (if n ≤ 1073 then (if n ≤ 1072 then 10 else 1) else 2) else (if n ≤ 1076 then (if n ≤ 1075 then 4 else 1) else 2)))) else (if n ≤ 1090 then (if n ≤ 1084 then (if n ≤ 1081 then (if n ≤ 1079 then (if n ≤ 1078 then 1 else 1) else (if n ≤ 1080 then 2 else 3)) else (if n ≤ 1083 then (if n ≤ 1082 then 1 else 2) else 2)) else (if n ≤ 1087 then (if n ≤ 1086 then (if n ≤ 1085 then 1 else 2) else 3) else (if n ≤ 1089 then (if n ≤ 1088 then 1 else 2) else 4))) else (if n ≤ 1096 then (if n ≤ 1093 then (if n ≤ 1092 then (if n ≤ 1091 then 1 else 2) else 1) else (if n ≤ 1095 then (if n ≤ 1094 then 1 else 2) else 3)) else (if n ≤ 1099 then (if n ≤ 1098 then (if n ≤ 1097 then 1 else 2) else 2) else (if n ≤ 1101 then (if n ≤ 1100 then 1 else 2) else 4))))) else (if n ≤ 1127 then (if n ≤ 1115 then (if n ≤ 1109 then (if n ≤ 1106 then (if n ≤ 1104 then (if n ≤ 1103 then 1 else 2) else (if n ≤ 1105 then 4 else 1)) else (if n ≤ 1108 then (if n ≤ 1107 then 2 else 1) else 1)) else (if n ≤ 1112 then (if n ≤ 1111 then (if n ≤ 1110 then 2 else 3) else 1) else (if n ≤ 1114 then (if n ≤ 1113 then 2 else 2) else 1))) else (if n ≤ 1121 then (if n ≤ 1118 then (if n ≤ 1117 then (if n ≤ 1116 then 2 else 1) else 1) else (if n ≤ 1120 then (if n ≤ 1119 then 2 else 4) else 1)) else (if n ≤ 1124 then (if n ≤ 1123 then (if n ≤ 1122 then 2 else 1) else 1) else (if n ≤ 1126 then (if n ≤ 1125 then 2 else 3) else 1)))) else (if n ≤ 1140 then (if n ≤ 1134 then (if n ≤ 1131 then (if n ≤ 1129 then (if n ≤ 1128 then 2 else 2) else (if n ≤ 1130 then 1 else 2)) else (if n ≤ 1133 then (if n ≤ 1132 then 2 else 1) else 2)) else (if n ≤ 1137 then (if n ≤ 1136 then (if n ≤ 1135 then 4 else 1) else 2) else (if n ≤ 1139 then (if n ≤ 1138 then 1 else 1) else 2))) else (if n ≤ 1146 then (if n ≤ 1143 then (if n ≤ 1142 then (if n ≤ 1141 then 3 else 1) else 2) else (if n ≤ 1145 then (if n ≤ 1144 then 2 else 1) else 2)) else (if n ≤ 1149 then (if n ≤ 1148 then (if n ≤ 1147 then 7 else 1) else 2) else (if n ≤ 1151 then (if n ≤ 1150 then 4 else 1) else 2))))))

def certificate_k_block_11 (n : ℕ) : ℕ :=
  (if n ≤ 1202 then (if n ≤ 1177 then (if n ≤ 1165 then (if n ≤ 1159 then (if n ≤ 1156 then (if n ≤ 1154 then (if n ≤ 1153 then 1 else 1) else (if n ≤ 1155 then 2 else 3)) else (if n ≤ 1158 then (if n ≤ 1157 then 1 else 2) else 2)) else (if n ≤ 1162 then (if n ≤ 1161 then (if n ≤ 1160 then 1 else 2) else 3) else (if n ≤ 1164 then (if n ≤ 1163 then 1 else 2) else 4))) else (if n ≤ 1171 then (if n ≤ 1168 then (if n ≤ 1167 then (if n ≤ 1166 then 1 else 2) else 1) else (if n ≤ 1170 then (if n ≤ 1169 then 1 else 2) else 3)) else (if n ≤ 1174 then (if n ≤ 1173 then (if n ≤ 1172 then 1 else 2) else 2) else (if n ≤ 1176 then (if n ≤ 1175 then 1 else 2) else 10)))) else (if n ≤ 1190 then (if n ≤ 1184 then (if n ≤ 1181 then (if n ≤ 1179 then (if n ≤ 1178 then 1 else 2) else (if n ≤ 1180 then 4 else 1)) else (if n ≤ 1183 then (if n ≤ 1182 then 2 else 1) else 1)) else (if n ≤ 1187 then (if n ≤ 1186 then (if n ≤ 1185 then 2 else 3) else 1) else (if n ≤ 1189 then (if n ≤ 1188 then 2 else 2) else 1))) else (if n ≤ 1196 then (if n ≤ 1193 then (if n ≤ 1192 then (if n ≤ 1191 then 2 else 6) else 1) else (if n ≤ 1195 then (if n ≤ 1194 then 2 else 4) else 1)) else (if n ≤ 1199 then (if n ≤ 1198 then (if n ≤ 1197 then 2 else 1) else 1) else (if n ≤ 1201 then (if n ≤ 1200 then 2 else 3) else 1))))) else (if n ≤ 1227 then (if n ≤ 1215 then (if n ≤ 1209 then (if n ≤ 1206 then (if n ≤ 1204 then (if n ≤ 1203 then 2 else 2) else (if n ≤ 1205 then 1 else 2)) else (if n ≤ 1208 then (if n ≤ 1207 then 9 else 1) else 2)) else (if n ≤ 1212 then (if n ≤ 1211 then (if n ≤ 1210 then 4 else 1) else 2) else (if n ≤ 1214 then (if n ≤ 1213 then 1 else 1) else 2))) else (if n ≤ 1221 then (if n ≤ 1218 then (if n ≤ 1217 then (if n ≤ 1216 then 3 else 1) else 2) else (if n ≤ 1220 then (if n ≤ 1219 then 2 else 1) else 2)) else (if n ≤ 1224 then (if n ≤ 1223 then (if n ≤ 1222 then 1 else 1) else 2) else (if n ≤ 1226 then (if n ≤ 1225 then 4 else 1) else 2)))) else (if n ≤ 1240 then (if n ≤ 1234 then (if n ≤ 1231 then (if n ≤ 1229 then (if n ≤ 1228 then 1 else 1) else (if n ≤ 1230 then 2 else 3)) else (if n ≤ 1233 then (if n ≤ 1232 then 1 else 2) else 2)) else (if n ≤ 1237 then (if n ≤ 1236 then (if n ≤ 1235 then 1 else 2) else 2) else (if n ≤ 1239 then (if n ≤ 1238 then 1 else 2) else 4))) else (if n ≤ 1246 then (if n ≤ 1243 then (if n ≤ 1242 then (if n ≤ 1241 then 1 else 2) else 1) else (if n ≤ 1245 then (if n ≤ 1244 then 1 else 2) else 3)) else (if n ≤ 1249 then (if n ≤ 1248 then (if n ≤ 1247 then 1 else 2) else 2) else (if n ≤ 1251 then (if n ≤ 1250 then 1 else 2) else 3))))))

def certificate_k_block_12 (n : ℕ) : ℕ :=
  (if n ≤ 1302 then (if n ≤ 1277 then (if n ≤ 1265 then (if n ≤ 1259 then (if n ≤ 1256 then (if n ≤ 1254 then (if n ≤ 1253 then 1 else 2) else (if n ≤ 1255 then 4 else 1)) else (if n ≤ 1258 then (if n ≤ 1257 then 2 else 1) else 1)) else (if n ≤ 1262 then (if n ≤ 1261 then (if n ≤ 1260 then 2 else 3) else 1) else (if n ≤ 1264 then (if n ≤ 1263 then 2 else 2) else 1))) else (if n ≤ 1271 then (if n ≤ 1268 then (if n ≤ 1267 then (if n ≤ 1266 then 2 else 3) else 1) else (if n ≤ 1270 then (if n ≤ 1269 then 2 else 4) else 1)) else (if n ≤ 1274 then (if n ≤ 1273 then (if n ≤ 1272 then 2 else 1) else 1) else (if n ≤ 1276 then (if n ≤ 1275 then 2 else 3) else 1)))) else (if n ≤ 1290 then (if n ≤ 1284 then (if n ≤ 1281 then (if n ≤ 1279 then (if n ≤ 1278 then 2 else 2) else (if n ≤ 1280 then 1 else 2)) else (if n ≤ 1283 then (if n ≤ 1282 then 1 else 1) else 2)) else (if n ≤ 1287 then (if n ≤ 1286 then (if n ≤ 1285 then 4 else 1) else 2) else (if n ≤ 1289 then (if n ≤ 1288 then 1 else 1) else 2))) else (if n ≤ 1296 then (if n ≤ 1293 then (if n ≤ 1292 then (if n ≤ 1291 then 3 else 1) else 2) else (if n ≤ 1295 then (if n ≤ 1294 then 2 else 1) else 2)) else (if n ≤ 1299 then (if n ≤ 1298 then (if n ≤ 1297 then 5 else 1) else 2) else (if n ≤ 1301 then (if n ≤ 1300 then 4 else 1) else 2))))) else (if n ≤ 1327 then (if n ≤ 1315 then (if n ≤ 1309 then (if n ≤ 1306 then (if n ≤ 1304 then (if n ≤ 1303 then 1 else 1) else (if n ≤ 1305 then 2 else 3)) else (if n ≤ 1308 then (if n ≤ 1307 then 1 else 2) else 2)) else (if n ≤ 1312 then (if n ≤ 1311 then (if n ≤ 1310 then 1 else 2) else 7) else (if n ≤ 1314 then (if n ≤ 1313 then 1 else 2) else 4))) else (if n ≤ 1321 then (if n ≤ 1318 then (if n ≤ 1317 then (if n ≤ 1316 then 1 else 2) else 1) else (if n ≤ 1320 then (if n ≤ 1319 then 1 else 2) else 3)) else (if n ≤ 1324 then (if n ≤ 1323 then (if n ≤ 1322 then 1 else 2) else 2) else (if n ≤ 1326 then (if n ≤ 1325 then 1 else 2) else 1)))) else (if n ≤ 1340 then (if n ≤ 1334 then (if n ≤ 1331 then (if n ≤ 1329 then (if n ≤ 1328 then 1 else 2) else (if n ≤ 1330 then 4 else 1)) else (if n ≤ 1333 then (if n ≤ 1332 then 2 else 1) else 1)) else (if n ≤ 1337 then (if n ≤ 1336 then (if n ≤ 1335 then 2 else 3) else 1) else (if n ≤ 1339 then (if n ≤ 1338 then 2 else 2) else 1))) else (if n ≤ 1346 then (if n ≤ 1343 then (if n ≤ 1342 then (if n ≤ 1341 then 2 else 2) else 1) else (if n ≤ 1345 then (if n ≤ 1344 then 2 else 4) else 1)) else (if n ≤ 1349 then (if n ≤ 1348 then (if n ≤ 1347 then 2 else 1) else 1) else (if n ≤ 1351 then (if n ≤ 1350 then 2 else 3) else 1))))))

def certificate_k_block_13 (n : ℕ) : ℕ :=
  (if n ≤ 1402 then (if n ≤ 1377 then (if n ≤ 1365 then (if n ≤ 1359 then (if n ≤ 1356 then (if n ≤ 1354 then (if n ≤ 1353 then 2 else 2) else (if n ≤ 1355 then 1 else 2)) else (if n ≤ 1358 then (if n ≤ 1357 then 6 else 1) else 2)) else (if n ≤ 1362 then (if n ≤ 1361 then (if n ≤ 1360 then 4 else 1) else 2) else (if n ≤ 1364 then (if n ≤ 1363 then 1 else 1) else 2))) else (if n ≤ 1371 then (if n ≤ 1368 then (if n ≤ 1367 then (if n ≤ 1366 then 3 else 1) else 2) else (if n ≤ 1370 then (if n ≤ 1369 then 2 else 1) else 2)) else (if n ≤ 1374 then (if n ≤ 1373 then (if n ≤ 1372 then 3 else 1) else 2) else (if n ≤ 1376 then (if n ≤ 1375 then 4 else 1) else 2)))) else (if n ≤ 1390 then (if n ≤ 1384 then (if n ≤ 1381 then (if n ≤ 1379 then (if n ≤ 1378 then 1 else 1) else (if n ≤ 1380 then 2 else 3)) else (if n ≤ 1383 then (if n ≤ 1382 then 1 else 2) else 2)) else (if n ≤ 1387 then (if n ≤ 1386 then (if n ≤ 1385 then 1 else 2) else 8) else (if n ≤ 1389 then (if n ≤ 1388 then 1 else 2) else 4))) else (if n ≤ 1396 then (if n ≤ 1393 then (if n ≤ 1392 then (if n ≤ 1391 then 1 else 2) else 1) else (if n ≤ 1395 then (if n ≤ 1394 then 1 else 2) else 3)) else (if n ≤ 1399 then (if n ≤ 1398 then (if n ≤ 1397 then 1 else 2) else 2) else (if n ≤ 1401 then (if n ≤ 1400 then 1 else 2) else 10))))) else (if n ≤ 1427 then (if n ≤ 1415 then (if n ≤ 1409 then (if n ≤ 1406 then (if n ≤ 1404 then (if n ≤ 1403 then 1 else 2) else (if n ≤ 1405 then 4 else 1)) else (if n ≤ 1408 then (if n ≤ 1407 then 2 else 1) else 1)) else (if n ≤ 1412 then (if n ≤ 1411 then (if n ≤ 1410 then 2 else 3) else 1) else (if n ≤ 1414 then (if n ≤ 1413 then 2 else 2) else 1))) else (if n ≤ 1421 then (if n ≤ 1418 then (if n ≤ 1417 then (if n ≤ 1416 then 2 else 3) else 1) else (if n ≤ 1420 then (if n ≤ 1419 then 2 else 4) else 1)) else (if n ≤ 1424 then (if n ≤ 1423 then (if n ≤ 1422 then 2 else 1) else 1) else (if n ≤ 1426 then (if n ≤ 1425 then 2 else 3) else 1)))) else (if n ≤ 1440 then (if n ≤ 1434 then (if n ≤ 1431 then (if n ≤ 1429 then (if n ≤ 1428 then 2 else 2) else (if n ≤ 1430 then 1 else 2)) else (if n ≤ 1433 then (if n ≤ 1432 then 1 else 1) else 2)) else (if n ≤ 1437 then (if n ≤ 1436 then (if n ≤ 1435 then 4 else 1) else 2) else (if n ≤ 1439 then (if n ≤ 1438 then 1 else 1) else 2))) else (if n ≤ 1446 then (if n ≤ 1443 then (if n ≤ 1442 then (if n ≤ 1441 then 3 else 1) else 2) else (if n ≤ 1445 then (if n ≤ 1444 then 2 else 1) else 2)) else (if n ≤ 1449 then (if n ≤ 1448 then (if n ≤ 1447 then 2 else 1) else 2) else (if n ≤ 1451 then (if n ≤ 1450 then 4 else 1) else 2))))))

def certificate_k_block_14 (n : ℕ) : ℕ :=
  (if n ≤ 1502 then (if n ≤ 1477 then (if n ≤ 1465 then (if n ≤ 1459 then (if n ≤ 1456 then (if n ≤ 1454 then (if n ≤ 1453 then 1 else 1) else (if n ≤ 1455 then 2 else 3)) else (if n ≤ 1458 then (if n ≤ 1457 then 1 else 2) else 2)) else (if n ≤ 1462 then (if n ≤ 1461 then (if n ≤ 1460 then 1 else 2) else 5) else (if n ≤ 1464 then (if n ≤ 1463 then 1 else 2) else 4))) else (if n ≤ 1471 then (if n ≤ 1468 then (if n ≤ 1467 then (if n ≤ 1466 then 1 else 2) else 1) else (if n ≤ 1470 then (if n ≤ 1469 then 1 else 2) else 3)) else (if n ≤ 1474 then (if n ≤ 1473 then (if n ≤ 1472 then 1 else 2) else 2) else (if n ≤ 1476 then (if n ≤ 1475 then 1 else 2) else 3)))) else (if n ≤ 1490 then (if n ≤ 1484 then (if n ≤ 1481 then (if n ≤ 1479 then (if n ≤ 1478 then 1 else 2) else (if n ≤ 1480 then 4 else 1)) else (if n ≤ 1483 then (if n ≤ 1482 then 2 else 1) else 1)) else (if n ≤ 1487 then (if n ≤ 1486 then (if n ≤ 1485 then 2 else 3) else 1) else (if n ≤ 1489 then (if n ≤ 1488 then 2 else 2) else 1))) else (if n ≤ 1496 then (if n ≤ 1493 then (if n ≤ 1492 then (if n ≤ 1491 then 2 else 2) else 1) else (if n ≤ 1495 then (if n ≤ 1494 then 2 else 4) else 1)) else (if n ≤ 1499 then (if n ≤ 1498 then (if n ≤ 1497 then 2 else 1) else 1) else (if n ≤ 1501 then (if n ≤ 1500 then 2 else 3) else 1))))) else (if n ≤ 1527 then (if n ≤ 1515 then (if n ≤ 1509 then (if n ≤ 1506 then (if n ≤ 1504 then (if n ≤ 1503 then 2 else 2) else (if n ≤ 1505 then 1 else 2)) else (if n ≤ 1508 then (if n ≤ 1507 then 10 else 1) else 2)) else (if n ≤ 1512 then (if n ≤ 1511 then (if n ≤ 1510 then 4 else 1) else 2) else (if n ≤ 1514 then (if n ≤ 1513 then 1 else 1) else 2))) else (if n ≤ 1521 then (if n ≤ 1518 then (if n ≤ 1517 then (if n ≤ 1516 then 3 else 1) else 2) else (if n ≤ 1520 then (if n ≤ 1519 then 2 else 1) else 2)) else (if n ≤ 1524 then (if n ≤ 1523 then (if n ≤ 1522 then 6 else 1) else 2) else (if n ≤ 1526 then (if n ≤ 1525 then 4 else 1) else 2)))) else (if n ≤ 1540 then (if n ≤ 1534 then (if n ≤ 1531 then (if n ≤ 1529 then (if n ≤ 1528 then 1 else 1) else (if n ≤ 1530 then 2 else 3)) else (if n ≤ 1533 then (if n ≤ 1532 then 1 else 2) else 2)) else (if n ≤ 1537 then (if n ≤ 1536 then (if n ≤ 1535 then 1 else 2) else 1) else (if n ≤ 1539 then (if n ≤ 1538 then 1 else 2) else 4))) else (if n ≤ 1546 then (if n ≤ 1543 then (if n ≤ 1542 then (if n ≤ 1541 then 1 else 2) else 1) else (if n ≤ 1545 then (if n ≤ 1544 then 1 else 2) else 3)) else (if n ≤ 1549 then (if n ≤ 1548 then (if n ≤ 1547 then 1 else 2) else 2) else (if n ≤ 1551 then (if n ≤ 1550 then 1 else 2) else 2))))))

def certificate_k_block_15 (n : ℕ) : ℕ :=
  (if n ≤ 1602 then (if n ≤ 1577 then (if n ≤ 1565 then (if n ≤ 1559 then (if n ≤ 1556 then (if n ≤ 1554 then (if n ≤ 1553 then 1 else 2) else (if n ≤ 1555 then 4 else 1)) else (if n ≤ 1558 then (if n ≤ 1557 then 2 else 1) else 1)) else (if n ≤ 1562 then (if n ≤ 1561 then (if n ≤ 1560 then 2 else 3) else 1) else (if n ≤ 1564 then (if n ≤ 1563 then 2 else 2) else 1))) else (if n ≤ 1571 then (if n ≤ 1568 then (if n ≤ 1567 then (if n ≤ 1566 then 2 else 1) else 1) else (if n ≤ 1570 then (if n ≤ 1569 then 2 else 4) else 1)) else (if n ≤ 1574 then (if n ≤ 1573 then (if n ≤ 1572 then 2 else 1) else 1) else (if n ≤ 1576 then (if n ≤ 1575 then 2 else 3) else 1)))) else (if n ≤ 1590 then (if n ≤ 1584 then (if n ≤ 1581 then (if n ≤ 1579 then (if n ≤ 1578 then 2 else 2) else (if n ≤ 1580 then 1 else 2)) else (if n ≤ 1583 then (if n ≤ 1582 then 3 else 1) else 2)) else (if n ≤ 1587 then (if n ≤ 1586 then (if n ≤ 1585 then 4 else 1) else 2) else (if n ≤ 1589 then (if n ≤ 1588 then 1 else 1) else 2))) else (if n ≤ 1596 then (if n ≤ 1593 then (if n ≤ 1592 then (if n ≤ 1591 then 3 else 1) else 2) else (if n ≤ 1595 then (if n ≤ 1594 then 2 else 1) else 2)) else (if n ≤ 1599 then (if n ≤ 1598 then (if n ≤ 1597 then 4 else 1) else 2) else (if n ≤ 1601 then (if n ≤ 1600 then 4 else 1) else 2))))) else (if n ≤ 1627 then (if n ≤ 1615 then (if n ≤ 1609 then (if n ≤ 1606 then (if n ≤ 1604 then (if n ≤ 1603 then 1 else 1) else (if n ≤ 1605 then 2 else 3)) else (if n ≤ 1608 then (if n ≤ 1607 then 1 else 2) else 2)) else (if n ≤ 1612 then (if n ≤ 1611 then (if n ≤ 1610 then 1 else 2) else 1) else (if n ≤ 1614 then (if n ≤ 1613 then 1 else 2) else 4))) else (if n ≤ 1621 then (if n ≤ 1618 then (if n ≤ 1617 then (if n ≤ 1616 then 1 else 2) else 1) else (if n ≤ 1620 then (if n ≤ 1619 then 1 else 2) else 3)) else (if n ≤ 1624 then (if n ≤ 1623 then (if n ≤ 1622 then 1 else 2) else 2) else (if n ≤ 1626 then (if n ≤ 1625 then 1 else 2) else 5)))) else (if n ≤ 1640 then (if n ≤ 1634 then (if n ≤ 1631 then (if n ≤ 1629 then (if n ≤ 1628 then 1 else 2) else (if n ≤ 1630 then 4 else 1)) else (if n ≤ 1633 then (if n ≤ 1632 then 2 else 1) else 1)) else (if n ≤ 1637 then (if n ≤ 1636 then (if n ≤ 1635 then 2 else 3) else 1) else (if n ≤ 1639 then (if n ≤ 1638 then 2 else 2) else 1))) else (if n ≤ 1646 then (if n ≤ 1643 then (if n ≤ 1642 then (if n ≤ 1641 then 2 else 1) else 1) else (if n ≤ 1645 then (if n ≤ 1644 then 2 else 4) else 1)) else (if n ≤ 1649 then (if n ≤ 1648 then (if n ≤ 1647 then 2 else 1) else 1) else (if n ≤ 1651 then (if n ≤ 1650 then 2 else 3) else 1))))))

def certificate_k_block_16 (n : ℕ) : ℕ :=
  (if n ≤ 1702 then (if n ≤ 1677 then (if n ≤ 1665 then (if n ≤ 1659 then (if n ≤ 1656 then (if n ≤ 1654 then (if n ≤ 1653 then 2 else 2) else (if n ≤ 1655 then 1 else 2)) else (if n ≤ 1658 then (if n ≤ 1657 then 2 else 1) else 2)) else (if n ≤ 1662 then (if n ≤ 1661 then (if n ≤ 1660 then 4 else 1) else 2) else (if n ≤ 1664 then (if n ≤ 1663 then 1 else 1) else 2))) else (if n ≤ 1671 then (if n ≤ 1668 then (if n ≤ 1667 then (if n ≤ 1666 then 3 else 1) else 2) else (if n ≤ 1670 then (if n ≤ 1669 then 2 else 1) else 2)) else (if n ≤ 1674 then (if n ≤ 1673 then (if n ≤ 1672 then 10 else 1) else 2) else (if n ≤ 1676 then (if n ≤ 1675 then 4 else 1) else 2)))) else (if n ≤ 1690 then (if n ≤ 1684 then (if n ≤ 1681 then (if n ≤ 1679 then (if n ≤ 1678 then 1 else 1) else (if n ≤ 1680 then 2 else 3)) else (if n ≤ 1683 then (if n ≤ 1682 then 1 else 2) else 2)) else (if n ≤ 1687 then (if n ≤ 1686 then (if n ≤ 1685 then 1 else 2) else 3) else (if n ≤ 1689 then (if n ≤ 1688 then 1 else 2) else 4))) else (if n ≤ 1696 then (if n ≤ 1693 then (if n ≤ 1692 then (if n ≤ 1691 then 1 else 2) else 1) else (if n ≤ 1695 then (if n ≤ 1694 then 1 else 2) else 3)) else (if n ≤ 1699 then (if n ≤ 1698 then (if n ≤ 1697 then 1 else 2) else 2) else (if n ≤ 1701 then (if n ≤ 1700 then 1 else 2) else 9))))) else (if n ≤ 1727 then (if n ≤ 1715 then (if n ≤ 1709 then (if n ≤ 1706 then (if n ≤ 1704 then (if n ≤ 1703 then 1 else 2) else (if n ≤ 1705 then 4 else 1)) else (if n ≤ 1708 then (if n ≤ 1707 then 2 else 1) else 1)) else (if n ≤ 1712 then (if n ≤ 1711 then (if n ≤ 1710 then 2 else 3) else 1) else (if n ≤ 1714 then (if n ≤ 1713 then 2 else 2) else 1))) else (if n ≤ 1721 then (if n ≤ 1718 then (if n ≤ 1717 then (if n ≤ 1716 then 2 else 8) else 1) else (if n ≤ 1720 then (if n ≤ 1719 then 2 else 4) else 1)) else (if n ≤ 1724 then (if n ≤ 1723 then (if n ≤ 1722 then 2 else 1) else 1) else (if n ≤ 1726 then (if n ≤ 1725 then 2 else 3) else 1)))) else (if n ≤ 1740 then (if n ≤ 1734 then (if n ≤ 1731 then (if n ≤ 1729 then (if n ≤ 1728 then 2 else 2) else (if n ≤ 1730 then 1 else 2)) else (if n ≤ 1733 then (if n ≤ 1732 then 11 else 1) else 2)) else (if n ≤ 1737 then (if n ≤ 1736 then (if n ≤ 1735 then 4 else 1) else 2) else (if n ≤ 1739 then (if n ≤ 1738 then 1 else 1) else 2))) else (if n ≤ 1746 then (if n ≤ 1743 then (if n ≤ 1742 then (if n ≤ 1741 then 3 else 1) else 2) else (if n ≤ 1745 then (if n ≤ 1744 then 2 else 1) else 2)) else (if n ≤ 1749 then (if n ≤ 1748 then (if n ≤ 1747 then 1 else 1) else 2) else (if n ≤ 1751 then (if n ≤ 1750 then 4 else 1) else 2))))))

def certificate_k_block_17 (n : ℕ) : ℕ :=
  (if n ≤ 1802 then (if n ≤ 1777 then (if n ≤ 1765 then (if n ≤ 1759 then (if n ≤ 1756 then (if n ≤ 1754 then (if n ≤ 1753 then 1 else 1) else (if n ≤ 1755 then 2 else 3)) else (if n ≤ 1758 then (if n ≤ 1757 then 1 else 2) else 2)) else (if n ≤ 1762 then (if n ≤ 1761 then (if n ≤ 1760 then 1 else 2) else 2) else (if n ≤ 1764 then (if n ≤ 1763 then 1 else 2) else 4))) else (if n ≤ 1771 then (if n ≤ 1768 then (if n ≤ 1767 then (if n ≤ 1766 then 1 else 2) else 1) else (if n ≤ 1770 then (if n ≤ 1769 then 1 else 2) else 3)) else (if n ≤ 1774 then (if n ≤ 1773 then (if n ≤ 1772 then 1 else 2) else 2) else (if n ≤ 1776 then (if n ≤ 1775 then 1 else 2) else 1)))) else (if n ≤ 1790 then (if n ≤ 1784 then (if n ≤ 1781 then (if n ≤ 1779 then (if n ≤ 1778 then 1 else 2) else (if n ≤ 1780 then 4 else 1)) else (if n ≤ 1783 then (if n ≤ 1782 then 2 else 1) else 1)) else (if n ≤ 1787 then (if n ≤ 1786 then (if n ≤ 1785 then 2 else 3) else 1) else (if n ≤ 1789 then (if n ≤ 1788 then 2 else 2) else 1))) else (if n ≤ 1796 then (if n ≤ 1793 then (if n ≤ 1792 then (if n ≤ 1791 then 2 else 3) else 1) else (if n ≤ 1795 then (if n ≤ 1794 then 2 else 4) else 1)) else (if n ≤ 1799 then (if n ≤ 1798 then (if n ≤ 1797 then 2 else 1) else 1) else (if n ≤ 1801 then (if n ≤ 1800 then 2 else 3) else 1))))) else (if n ≤ 1827 then (if n ≤ 1815 then (if n ≤ 1809 then (if n ≤ 1806 then (if n ≤ 1804 then (if n ≤ 1803 then 2 else 2) else (if n ≤ 1805 then 1 else 2)) else (if n ≤ 1808 then (if n ≤ 1807 then 7 else 1) else 2)) else (if n ≤ 1812 then (if n ≤ 1811 then (if n ≤ 1810 then 4 else 1) else 2) else (if n ≤ 1814 then (if n ≤ 1813 then 1 else 1) else 2))) else (if n ≤ 1821 then (if n ≤ 1818 then (if n ≤ 1817 then (if n ≤ 1816 then 3 else 1) else 2) else (if n ≤ 1820 then (if n ≤ 1819 then 2 else 1) else 2)) else (if n ≤ 1824 then (if n ≤ 1823 then (if n ≤ 1822 then 2 else 1) else 2) else (if n ≤ 1826 then (if n ≤ 1825 then 4 else 1) else 2)))) else (if n ≤ 1840 then (if n ≤ 1834 then (if n ≤ 1831 then (if n ≤ 1829 then (if n ≤ 1828 then 1 else 1) else (if n ≤ 1830 then 2 else 3)) else (if n ≤ 1833 then (if n ≤ 1832 then 1 else 2) else 2)) else (if n ≤ 1837 then (if n ≤ 1836 then (if n ≤ 1835 then 1 else 2) else 10) else (if n ≤ 1839 then (if n ≤ 1838 then 1 else 2) else 4))) else (if n ≤ 1846 then (if n ≤ 1843 then (if n ≤ 1842 then (if n ≤ 1841 then 1 else 2) else 1) else (if n ≤ 1845 then (if n ≤ 1844 then 1 else 2) else 3)) else (if n ≤ 1849 then (if n ≤ 1848 then (if n ≤ 1847 then 1 else 2) else 2) else (if n ≤ 1851 then (if n ≤ 1850 then 1 else 2) else 1))))))

def certificate_k_block_18 (n : ℕ) : ℕ :=
  (if n ≤ 1902 then (if n ≤ 1877 then (if n ≤ 1865 then (if n ≤ 1859 then (if n ≤ 1856 then (if n ≤ 1854 then (if n ≤ 1853 then 1 else 2) else (if n ≤ 1855 then 4 else 1)) else (if n ≤ 1858 then (if n ≤ 1857 then 2 else 1) else 1)) else (if n ≤ 1862 then (if n ≤ 1861 then (if n ≤ 1860 then 2 else 3) else 1) else (if n ≤ 1864 then (if n ≤ 1863 then 2 else 2) else 1))) else (if n ≤ 1871 then (if n ≤ 1868 then (if n ≤ 1867 then (if n ≤ 1866 then 2 else 2) else 1) else (if n ≤ 1870 then (if n ≤ 1869 then 2 else 4) else 1)) else (if n ≤ 1874 then (if n ≤ 1873 then (if n ≤ 1872 then 2 else 1) else 1) else (if n ≤ 1876 then (if n ≤ 1875 then 2 else 3) else 1)))) else (if n ≤ 1890 then (if n ≤ 1884 then (if n ≤ 1881 then (if n ≤ 1879 then (if n ≤ 1878 then 2 else 2) else (if n ≤ 1880 then 1 else 2)) else (if n ≤ 1883 then (if n ≤ 1882 then 8 else 1) else 2)) else (if n ≤ 1887 then (if n ≤ 1886 then (if n ≤ 1885 then 4 else 1) else 2) else (if n ≤ 1889 then (if n ≤ 1888 then 1 else 1) else 2))) else (if n ≤ 1896 then (if n ≤ 1893 then (if n ≤ 1892 then (if n ≤ 1891 then 3 else 1) else 2) else (if n ≤ 1895 then (if n ≤ 1894 then 2 else 1) else 2)) else (if n ≤ 1899 then (if n ≤ 1898 then (if n ≤ 1897 then 3 else 1) else 2) else (if n ≤ 1901 then (if n ≤ 1900 then 4 else 1) else 2))))) else (if n ≤ 1927 then (if n ≤ 1915 then (if n ≤ 1909 then (if n ≤ 1906 then (if n ≤ 1904 then (if n ≤ 1903 then 1 else 1) else (if n ≤ 1905 then 2 else 3)) else (if n ≤ 1908 then (if n ≤ 1907 then 1 else 2) else 2)) else (if n ≤ 1912 then (if n ≤ 1911 then (if n ≤ 1910 then 1 else 2) else 3) else (if n ≤ 1914 then (if n ≤ 1913 then 1 else 2) else 4))) else (if n ≤ 1921 then (if n ≤ 1918 then (if n ≤ 1917 then (if n ≤ 1916 then 1 else 2) else 1) else (if n ≤ 1920 then (if n ≤ 1919 then 1 else 2) else 3)) else (if n ≤ 1924 then (if n ≤ 1923 then (if n ≤ 1922 then 1 else 2) else 2) else (if n ≤ 1926 then (if n ≤ 1925 then 1 else 2) else 4)))) else (if n ≤ 1940 then (if n ≤ 1934 then (if n ≤ 1931 then (if n ≤ 1929 then (if n ≤ 1928 then 1 else 2) else (if n ≤ 1930 then 4 else 1)) else (if n ≤ 1933 then (if n ≤ 1932 then 2 else 1) else 1)) else (if n ≤ 1937 then (if n ≤ 1936 then (if n ≤ 1935 then 2 else 3) else 1) else (if n ≤ 1939 then (if n ≤ 1938 then 2 else 2) else 1))) else (if n ≤ 1946 then (if n ≤ 1943 then (if n ≤ 1942 then (if n ≤ 1941 then 2 else 1) else 1) else (if n ≤ 1945 then (if n ≤ 1944 then 2 else 4) else 1)) else (if n ≤ 1949 then (if n ≤ 1948 then (if n ≤ 1947 then 2 else 1) else 1) else (if n ≤ 1951 then (if n ≤ 1950 then 2 else 3) else 1))))))

def certificate_k_block_19 (n : ℕ) : ℕ :=
  (if n ≤ 2002 then (if n ≤ 1977 then (if n ≤ 1965 then (if n ≤ 1959 then (if n ≤ 1956 then (if n ≤ 1954 then (if n ≤ 1953 then 2 else 2) else (if n ≤ 1955 then 1 else 2)) else (if n ≤ 1958 then (if n ≤ 1957 then 1 else 1) else 2)) else (if n ≤ 1962 then (if n ≤ 1961 then (if n ≤ 1960 then 4 else 1) else 2) else (if n ≤ 1964 then (if n ≤ 1963 then 1 else 1) else 2))) else (if n ≤ 1971 then (if n ≤ 1968 then (if n ≤ 1967 then (if n ≤ 1966 then 3 else 1) else 2) else (if n ≤ 1970 then (if n ≤ 1969 then 2 else 1) else 2)) else (if n ≤ 1974 then (if n ≤ 1973 then (if n ≤ 1972 then 2 else 1) else 2) else (if n ≤ 1976 then (if n ≤ 1975 then 4 else 1) else 2)))) else (if n ≤ 1990 then (if n ≤ 1984 then (if n ≤ 1981 then (if n ≤ 1979 then (if n ≤ 1978 then 1 else 1) else (if n ≤ 1980 then 2 else 3)) else (if n ≤ 1983 then (if n ≤ 1982 then 1 else 2) else 2)) else (if n ≤ 1987 then (if n ≤ 1986 then (if n ≤ 1985 then 1 else 2) else 2) else (if n ≤ 1989 then (if n ≤ 1988 then 1 else 2) else 4))) else (if n ≤ 1996 then (if n ≤ 1993 then (if n ≤ 1992 then (if n ≤ 1991 then 1 else 2) else 1) else (if n ≤ 1995 then (if n ≤ 1994 then 1 else 2) else 3)) else (if n ≤ 1999 then (if n ≤ 1998 then (if n ≤ 1997 then 1 else 2) else 2) else (if n ≤ 2001 then (if n ≤ 2000 then 1 else 2) else 3))))) else (if n ≤ 2027 then (if n ≤ 2015 then (if n ≤ 2009 then (if n ≤ 2006 then (if n ≤ 2004 then (if n ≤ 2003 then 1 else 2) else (if n ≤ 2005 then 4 else 1)) else (if n ≤ 2008 then (if n ≤ 2007 then 2 else 1) else 1)) else (if n ≤ 2012 then (if n ≤ 2011 then (if n ≤ 2010 then 2 else 3) else 1) else (if n ≤ 2014 then (if n ≤ 2013 then 2 else 2) else 1))) else (if n ≤ 2021 then (if n ≤ 2018 then (if n ≤ 2017 then (if n ≤ 2016 then 2 else 6) else 1) else (if n ≤ 2020 then (if n ≤ 2019 then 2 else 4) else 1)) else (if n ≤ 2024 then (if n ≤ 2023 then (if n ≤ 2022 then 2 else 1) else 1) else (if n ≤ 2026 then (if n ≤ 2025 then 2 else 3) else 1)))) else (if n ≤ 2040 then (if n ≤ 2034 then (if n ≤ 2031 then (if n ≤ 2029 then (if n ≤ 2028 then 2 else 2) else (if n ≤ 2030 then 1 else 2)) else (if n ≤ 2033 then (if n ≤ 2032 then 9 else 1) else 2)) else (if n ≤ 2037 then (if n ≤ 2036 then (if n ≤ 2035 then 4 else 1) else 2) else (if n ≤ 2039 then (if n ≤ 2038 then 1 else 1) else 2))) else (if n ≤ 2046 then (if n ≤ 2043 then (if n ≤ 2042 then (if n ≤ 2041 then 3 else 1) else 2) else (if n ≤ 2045 then (if n ≤ 2044 then 2 else 1) else 2)) else (if n ≤ 2049 then (if n ≤ 2048 then (if n ≤ 2047 then 8 else 1) else 2) else (if n ≤ 2051 then (if n ≤ 2050 then 4 else 1) else 2))))))

def certificate_k_block_20 (n : ℕ) : ℕ :=
  (if n ≤ 2053 then 1 else 1)

def certificate_d_block_0 (n : ℕ) : ℕ :=
  (if n ≤ 102 then (if n ≤ 77 then (if n ≤ 65 then (if n ≤ 59 then (if n ≤ 56 then (if n ≤ 54 then (if n ≤ 53 then 3 else 3) else (if n ≤ 55 then 5 else 3)) else (if n ≤ 58 then (if n ≤ 57 then 3 else 5) else 3)) else (if n ≤ 62 then (if n ≤ 61 then (if n ≤ 60 then 3 else 5) else 3) else (if n ≤ 64 then (if n ≤ 63 then 3 else 5) else 3))) else (if n ≤ 71 then (if n ≤ 68 then (if n ≤ 67 then (if n ≤ 66 then 3 else 7) else 3) else (if n ≤ 70 then (if n ≤ 69 then 3 else 5) else 3)) else (if n ≤ 74 then (if n ≤ 73 then (if n ≤ 72 then 3 else 5) else 3) else (if n ≤ 76 then (if n ≤ 75 then 3 else 5) else 3)))) else (if n ≤ 90 then (if n ≤ 84 then (if n ≤ 81 then (if n ≤ 79 then (if n ≤ 78 then 3 else 5) else (if n ≤ 80 then 3 else 3)) else (if n ≤ 83 then (if n ≤ 82 then 7 else 3) else 3)) else (if n ≤ 87 then (if n ≤ 86 then (if n ≤ 85 then 5 else 3) else 3) else (if n ≤ 89 then (if n ≤ 88 then 5 else 3) else 3))) else (if n ≤ 96 then (if n ≤ 93 then (if n ≤ 92 then (if n ≤ 91 then 5 else 3) else 3) else (if n ≤ 95 then (if n ≤ 94 then 5 else 3) else 3)) else (if n ≤ 99 then (if n ≤ 98 then (if n ≤ 97 then 11 else 3) else 3) else (if n ≤ 101 then (if n ≤ 100 then 5 else 3) else 3))))) else (if n ≤ 127 then (if n ≤ 115 then (if n ≤ 109 then (if n ≤ 106 then (if n ≤ 104 then (if n ≤ 103 then 5 else 3) else (if n ≤ 105 then 3 else 5)) else (if n ≤ 108 then (if n ≤ 107 then 3 else 3) else 5)) else (if n ≤ 112 then (if n ≤ 111 then (if n ≤ 110 then 3 else 3) else 7) else (if n ≤ 114 then (if n ≤ 113 then 3 else 3) else 5))) else (if n ≤ 121 then (if n ≤ 118 then (if n ≤ 117 then (if n ≤ 116 then 3 else 3) else 5) else (if n ≤ 120 then (if n ≤ 119 then 3 else 3) else 5)) else (if n ≤ 124 then (if n ≤ 123 then (if n ≤ 122 then 3 else 3) else 5) else (if n ≤ 126 then (if n ≤ 125 then 3 else 3) else 11)))) else (if n ≤ 140 then (if n ≤ 134 then (if n ≤ 131 then (if n ≤ 129 then (if n ≤ 128 then 3 else 3) else (if n ≤ 130 then 5 else 3)) else (if n ≤ 133 then (if n ≤ 132 then 3 else 5) else 3)) else (if n ≤ 137 then (if n ≤ 136 then (if n ≤ 135 then 3 else 5) else 3) else (if n ≤ 139 then (if n ≤ 138 then 3 else 5) else 3))) else (if n ≤ 146 then (if n ≤ 143 then (if n ≤ 142 then (if n ≤ 141 then 3 else 11) else 3) else (if n ≤ 145 then (if n ≤ 144 then 3 else 5) else 3)) else (if n ≤ 149 then (if n ≤ 148 then (if n ≤ 147 then 3 else 5) else 3) else (if n ≤ 151 then (if n ≤ 150 then 3 else 5) else 3))))))

def certificate_d_block_1 (n : ℕ) : ℕ :=
  (if n ≤ 202 then (if n ≤ 177 then (if n ≤ 165 then (if n ≤ 159 then (if n ≤ 156 then (if n ≤ 154 then (if n ≤ 153 then 3 else 5) else (if n ≤ 155 then 3 else 3)) else (if n ≤ 158 then (if n ≤ 157 then 11 else 3) else 3)) else (if n ≤ 162 then (if n ≤ 161 then (if n ≤ 160 then 5 else 3) else 3) else (if n ≤ 164 then (if n ≤ 163 then 5 else 3) else 3))) else (if n ≤ 171 then (if n ≤ 168 then (if n ≤ 167 then (if n ≤ 166 then 5 else 3) else 3) else (if n ≤ 170 then (if n ≤ 169 then 5 else 3) else 3)) else (if n ≤ 174 then (if n ≤ 173 then (if n ≤ 172 then 7 else 3) else 3) else (if n ≤ 176 then (if n ≤ 175 then 5 else 3) else 3)))) else (if n ≤ 190 then (if n ≤ 184 then (if n ≤ 181 then (if n ≤ 179 then (if n ≤ 178 then 5 else 3) else (if n ≤ 180 then 3 else 5)) else (if n ≤ 183 then (if n ≤ 182 then 3 else 3) else 5)) else (if n ≤ 187 then (if n ≤ 186 then (if n ≤ 185 then 3 else 3) else 7) else (if n ≤ 189 then (if n ≤ 188 then 3 else 3) else 5))) else (if n ≤ 196 then (if n ≤ 193 then (if n ≤ 192 then (if n ≤ 191 then 3 else 3) else 5) else (if n ≤ 195 then (if n ≤ 194 then 3 else 3) else 5)) else (if n ≤ 199 then (if n ≤ 198 then (if n ≤ 197 then 3 else 3) else 5) else (if n ≤ 201 then (if n ≤ 200 then 3 else 3) else 11))))) else (if n ≤ 227 then (if n ≤ 215 then (if n ≤ 209 then (if n ≤ 206 then (if n ≤ 204 then (if n ≤ 203 then 3 else 3) else (if n ≤ 205 then 5 else 3)) else (if n ≤ 208 then (if n ≤ 207 then 3 else 5) else 3)) else (if n ≤ 212 then (if n ≤ 211 then (if n ≤ 210 then 3 else 5) else 3) else (if n ≤ 214 then (if n ≤ 213 then 3 else 5) else 3))) else (if n ≤ 221 then (if n ≤ 218 then (if n ≤ 217 then (if n ≤ 216 then 3 else 7) else 3) else (if n ≤ 220 then (if n ≤ 219 then 3 else 5) else 3)) else (if n ≤ 224 then (if n ≤ 223 then (if n ≤ 222 then 3 else 5) else 3) else (if n ≤ 226 then (if n ≤ 225 then 3 else 5) else 3)))) else (if n ≤ 240 then (if n ≤ 234 then (if n ≤ 231 then (if n ≤ 229 then (if n ≤ 228 then 3 else 5) else (if n ≤ 230 then 3 else 3)) else (if n ≤ 233 then (if n ≤ 232 then 11 else 3) else 3)) else (if n ≤ 237 then (if n ≤ 236 then (if n ≤ 235 then 5 else 3) else 3) else (if n ≤ 239 then (if n ≤ 238 then 5 else 3) else 3))) else (if n ≤ 246 then (if n ≤ 243 then (if n ≤ 242 then (if n ≤ 241 then 5 else 3) else 3) else (if n ≤ 245 then (if n ≤ 244 then 5 else 3) else 3)) else (if n ≤ 249 then (if n ≤ 248 then (if n ≤ 247 then 17 else 3) else 3) else (if n ≤ 251 then (if n ≤ 250 then 5 else 3) else 3))))))

def certificate_d_block_2 (n : ℕ) : ℕ :=
  (if n ≤ 302 then (if n ≤ 277 then (if n ≤ 265 then (if n ≤ 259 then (if n ≤ 256 then (if n ≤ 254 then (if n ≤ 253 then 5 else 3) else (if n ≤ 255 then 3 else 5)) else (if n ≤ 258 then (if n ≤ 257 then 3 else 3) else 5)) else (if n ≤ 262 then (if n ≤ 261 then (if n ≤ 260 then 3 else 3) else 11) else (if n ≤ 264 then (if n ≤ 263 then 3 else 3) else 5))) else (if n ≤ 271 then (if n ≤ 268 then (if n ≤ 267 then (if n ≤ 266 then 3 else 3) else 5) else (if n ≤ 270 then (if n ≤ 269 then 3 else 3) else 5)) else (if n ≤ 274 then (if n ≤ 273 then (if n ≤ 272 then 3 else 3) else 5) else (if n ≤ 276 then (if n ≤ 275 then 3 else 3) else 7)))) else (if n ≤ 290 then (if n ≤ 284 then (if n ≤ 281 then (if n ≤ 279 then (if n ≤ 278 then 3 else 3) else (if n ≤ 280 then 5 else 3)) else (if n ≤ 283 then (if n ≤ 282 then 3 else 5) else 3)) else (if n ≤ 287 then (if n ≤ 286 then (if n ≤ 285 then 3 else 5) else 3) else (if n ≤ 289 then (if n ≤ 288 then 3 else 5) else 3))) else (if n ≤ 296 then (if n ≤ 293 then (if n ≤ 292 then (if n ≤ 291 then 3 else 7) else 3) else (if n ≤ 295 then (if n ≤ 294 then 3 else 5) else 3)) else (if n ≤ 299 then (if n ≤ 298 then (if n ≤ 297 then 3 else 5) else 3) else (if n ≤ 301 then (if n ≤ 300 then 3 else 5) else 3))))) else (if n ≤ 327 then (if n ≤ 315 then (if n ≤ 309 then (if n ≤ 306 then (if n ≤ 304 then (if n ≤ 303 then 3 else 5) else (if n ≤ 305 then 3 else 3)) else (if n ≤ 308 then (if n ≤ 307 then 11 else 3) else 3)) else (if n ≤ 312 then (if n ≤ 311 then (if n ≤ 310 then 5 else 3) else 3) else (if n ≤ 314 then (if n ≤ 313 then 5 else 3) else 3))) else (if n ≤ 321 then (if n ≤ 318 then (if n ≤ 317 then (if n ≤ 316 then 5 else 3) else 3) else (if n ≤ 320 then (if n ≤ 319 then 5 else 3) else 3)) else (if n ≤ 324 then (if n ≤ 323 then (if n ≤ 322 then 7 else 3) else 3) else (if n ≤ 326 then (if n ≤ 325 then 5 else 3) else 3)))) else (if n ≤ 340 then (if n ≤ 334 then (if n ≤ 331 then (if n ≤ 329 then (if n ≤ 328 then 5 else 3) else (if n ≤ 330 then 3 else 5)) else (if n ≤ 333 then (if n ≤ 332 then 3 else 3) else 5)) else (if n ≤ 337 then (if n ≤ 336 then (if n ≤ 335 then 3 else 3) else 11) else (if n ≤ 339 then (if n ≤ 338 then 3 else 3) else 5))) else (if n ≤ 346 then (if n ≤ 343 then (if n ≤ 342 then (if n ≤ 341 then 3 else 3) else 5) else (if n ≤ 345 then (if n ≤ 344 then 3 else 3) else 5)) else (if n ≤ 349 then (if n ≤ 348 then (if n ≤ 347 then 3 else 3) else 5) else (if n ≤ 351 then (if n ≤ 350 then 3 else 3) else 13))))))

def certificate_d_block_3 (n : ℕ) : ℕ :=
  (if n ≤ 402 then (if n ≤ 377 then (if n ≤ 365 then (if n ≤ 359 then (if n ≤ 356 then (if n ≤ 354 then (if n ≤ 353 then 3 else 3) else (if n ≤ 355 then 5 else 3)) else (if n ≤ 358 then (if n ≤ 357 then 3 else 5) else 3)) else (if n ≤ 362 then (if n ≤ 361 then (if n ≤ 360 then 3 else 5) else 3) else (if n ≤ 364 then (if n ≤ 363 then 3 else 5) else 3))) else (if n ≤ 371 then (if n ≤ 368 then (if n ≤ 367 then (if n ≤ 366 then 3 else 11) else 3) else (if n ≤ 370 then (if n ≤ 369 then 3 else 5) else 3)) else (if n ≤ 374 then (if n ≤ 373 then (if n ≤ 372 then 3 else 5) else 3) else (if n ≤ 376 then (if n ≤ 375 then 3 else 5) else 3)))) else (if n ≤ 390 then (if n ≤ 384 then (if n ≤ 381 then (if n ≤ 379 then (if n ≤ 378 then 3 else 5) else (if n ≤ 380 then 3 else 3)) else (if n ≤ 383 then (if n ≤ 382 then 7 else 3) else 3)) else (if n ≤ 387 then (if n ≤ 386 then (if n ≤ 385 then 5 else 3) else 3) else (if n ≤ 389 then (if n ≤ 388 then 5 else 3) else 3))) else (if n ≤ 396 then (if n ≤ 393 then (if n ≤ 392 then (if n ≤ 391 then 5 else 3) else 3) else (if n ≤ 395 then (if n ≤ 394 then 5 else 3) else 3)) else (if n ≤ 399 then (if n ≤ 398 then (if n ≤ 397 then 7 else 3) else 3) else (if n ≤ 401 then (if n ≤ 400 then 5 else 3) else 3))))) else (if n ≤ 427 then (if n ≤ 415 then (if n ≤ 409 then (if n ≤ 406 then (if n ≤ 404 then (if n ≤ 403 then 5 else 3) else (if n ≤ 405 then 3 else 5)) else (if n ≤ 408 then (if n ≤ 407 then 3 else 3) else 5)) else (if n ≤ 412 then (if n ≤ 411 then (if n ≤ 410 then 3 else 3) else 13) else (if n ≤ 414 then (if n ≤ 413 then 3 else 3) else 5))) else (if n ≤ 421 then (if n ≤ 418 then (if n ≤ 417 then (if n ≤ 416 then 3 else 3) else 5) else (if n ≤ 420 then (if n ≤ 419 then 3 else 3) else 5)) else (if n ≤ 424 then (if n ≤ 423 then (if n ≤ 422 then 3 else 3) else 5) else (if n ≤ 426 then (if n ≤ 425 then 3 else 3) else 7)))) else (if n ≤ 440 then (if n ≤ 434 then (if n ≤ 431 then (if n ≤ 429 then (if n ≤ 428 then 3 else 3) else (if n ≤ 430 then 5 else 3)) else (if n ≤ 433 then (if n ≤ 432 then 3 else 5) else 3)) else (if n ≤ 437 then (if n ≤ 436 then (if n ≤ 435 then 3 else 5) else 3) else (if n ≤ 439 then (if n ≤ 438 then 3 else 5) else 3))) else (if n ≤ 446 then (if n ≤ 443 then (if n ≤ 442 then (if n ≤ 441 then 3 else 11) else 3) else (if n ≤ 445 then (if n ≤ 444 then 3 else 5) else 3)) else (if n ≤ 449 then (if n ≤ 448 then (if n ≤ 447 then 3 else 5) else 3) else (if n ≤ 451 then (if n ≤ 450 then 3 else 5) else 3))))))

def certificate_d_block_4 (n : ℕ) : ℕ :=
  (if n ≤ 502 then (if n ≤ 477 then (if n ≤ 465 then (if n ≤ 459 then (if n ≤ 456 then (if n ≤ 454 then (if n ≤ 453 then 3 else 5) else (if n ≤ 455 then 3 else 3)) else (if n ≤ 458 then (if n ≤ 457 then 11 else 3) else 3)) else (if n ≤ 462 then (if n ≤ 461 then (if n ≤ 460 then 5 else 3) else 3) else (if n ≤ 464 then (if n ≤ 463 then 5 else 3) else 3))) else (if n ≤ 471 then (if n ≤ 468 then (if n ≤ 467 then (if n ≤ 466 then 5 else 3) else 3) else (if n ≤ 470 then (if n ≤ 469 then 5 else 3) else 3)) else (if n ≤ 474 then (if n ≤ 473 then (if n ≤ 472 then 11 else 3) else 3) else (if n ≤ 476 then (if n ≤ 475 then 5 else 3) else 3)))) else (if n ≤ 490 then (if n ≤ 484 then (if n ≤ 481 then (if n ≤ 479 then (if n ≤ 478 then 5 else 3) else (if n ≤ 480 then 3 else 5)) else (if n ≤ 483 then (if n ≤ 482 then 3 else 3) else 5)) else (if n ≤ 487 then (if n ≤ 486 then (if n ≤ 485 then 3 else 3) else 7) else (if n ≤ 489 then (if n ≤ 488 then 3 else 3) else 5))) else (if n ≤ 496 then (if n ≤ 493 then (if n ≤ 492 then (if n ≤ 491 then 3 else 3) else 5) else (if n ≤ 495 then (if n ≤ 494 then 3 else 3) else 5)) else (if n ≤ 499 then (if n ≤ 498 then (if n ≤ 497 then 3 else 3) else 5) else (if n ≤ 501 then (if n ≤ 500 then 3 else 3) else 7))))) else (if n ≤ 527 then (if n ≤ 515 then (if n ≤ 509 then (if n ≤ 506 then (if n ≤ 504 then (if n ≤ 503 then 3 else 3) else (if n ≤ 505 then 5 else 3)) else (if n ≤ 508 then (if n ≤ 507 then 3 else 5) else 3)) else (if n ≤ 512 then (if n ≤ 511 then (if n ≤ 510 then 3 else 5) else 3) else (if n ≤ 514 then (if n ≤ 513 then 3 else 5) else 3))) else (if n ≤ 521 then (if n ≤ 518 then (if n ≤ 517 then (if n ≤ 516 then 3 else 13) else 3) else (if n ≤ 520 then (if n ≤ 519 then 3 else 5) else 3)) else (if n ≤ 524 then (if n ≤ 523 then (if n ≤ 522 then 3 else 5) else 3) else (if n ≤ 526 then (if n ≤ 525 then 3 else 5) else 3)))) else (if n ≤ 540 then (if n ≤ 534 then (if n ≤ 531 then (if n ≤ 529 then (if n ≤ 528 then 3 else 5) else (if n ≤ 530 then 3 else 3)) else (if n ≤ 533 then (if n ≤ 532 then 7 else 3) else 3)) else (if n ≤ 537 then (if n ≤ 536 then (if n ≤ 535 then 5 else 3) else 3) else (if n ≤ 539 then (if n ≤ 538 then 5 else 3) else 3))) else (if n ≤ 546 then (if n ≤ 543 then (if n ≤ 542 then (if n ≤ 541 then 5 else 3) else 3) else (if n ≤ 545 then (if n ≤ 544 then 5 else 3) else 3)) else (if n ≤ 549 then (if n ≤ 548 then (if n ≤ 547 then 11 else 3) else 3) else (if n ≤ 551 then (if n ≤ 550 then 5 else 3) else 3))))))

def certificate_d_block_5 (n : ℕ) : ℕ :=
  (if n ≤ 602 then (if n ≤ 577 then (if n ≤ 565 then (if n ≤ 559 then (if n ≤ 556 then (if n ≤ 554 then (if n ≤ 553 then 5 else 3) else (if n ≤ 555 then 3 else 5)) else (if n ≤ 558 then (if n ≤ 557 then 3 else 3) else 5)) else (if n ≤ 562 then (if n ≤ 561 then (if n ≤ 560 then 3 else 3) else 11) else (if n ≤ 564 then (if n ≤ 563 then 3 else 3) else 5))) else (if n ≤ 571 then (if n ≤ 568 then (if n ≤ 567 then (if n ≤ 566 then 3 else 3) else 5) else (if n ≤ 570 then (if n ≤ 569 then 3 else 3) else 5)) else (if n ≤ 574 then (if n ≤ 573 then (if n ≤ 572 then 3 else 3) else 5) else (if n ≤ 576 then (if n ≤ 575 then 3 else 3) else 13)))) else (if n ≤ 590 then (if n ≤ 584 then (if n ≤ 581 then (if n ≤ 579 then (if n ≤ 578 then 3 else 3) else (if n ≤ 580 then 5 else 3)) else (if n ≤ 583 then (if n ≤ 582 then 3 else 5) else 3)) else (if n ≤ 587 then (if n ≤ 586 then (if n ≤ 585 then 3 else 5) else 3) else (if n ≤ 589 then (if n ≤ 588 then 3 else 5) else 3))) else (if n ≤ 596 then (if n ≤ 593 then (if n ≤ 592 then (if n ≤ 591 then 3 else 7) else 3) else (if n ≤ 595 then (if n ≤ 594 then 3 else 5) else 3)) else (if n ≤ 599 then (if n ≤ 598 then (if n ≤ 597 then 3 else 5) else 3) else (if n ≤ 601 then (if n ≤ 600 then 3 else 5) else 3))))) else (if n ≤ 627 then (if n ≤ 615 then (if n ≤ 609 then (if n ≤ 606 then (if n ≤ 604 then (if n ≤ 603 then 3 else 5) else (if n ≤ 605 then 3 else 3)) else (if n ≤ 608 then (if n ≤ 607 then 7 else 3) else 3)) else (if n ≤ 612 then (if n ≤ 611 then (if n ≤ 610 then 5 else 3) else 3) else (if n ≤ 614 then (if n ≤ 613 then 5 else 3) else 3))) else (if n ≤ 621 then (if n ≤ 618 then (if n ≤ 617 then (if n ≤ 616 then 5 else 3) else 3) else (if n ≤ 620 then (if n ≤ 619 then 5 else 3) else 3)) else (if n ≤ 624 then (if n ≤ 623 then (if n ≤ 622 then 11 else 3) else 3) else (if n ≤ 626 then (if n ≤ 625 then 5 else 3) else 3)))) else (if n ≤ 640 then (if n ≤ 634 then (if n ≤ 631 then (if n ≤ 629 then (if n ≤ 628 then 5 else 3) else (if n ≤ 630 then 3 else 5)) else (if n ≤ 633 then (if n ≤ 632 then 3 else 3) else 5)) else (if n ≤ 637 then (if n ≤ 636 then (if n ≤ 635 then 3 else 3) else 7) else (if n ≤ 639 then (if n ≤ 638 then 3 else 3) else 5))) else (if n ≤ 646 then (if n ≤ 643 then (if n ≤ 642 then (if n ≤ 641 then 3 else 3) else 5) else (if n ≤ 645 then (if n ≤ 644 then 3 else 3) else 5)) else (if n ≤ 649 then (if n ≤ 648 then (if n ≤ 647 then 3 else 3) else 5) else (if n ≤ 651 then (if n ≤ 650 then 3 else 3) else 11))))))

def certificate_d_block_6 (n : ℕ) : ℕ :=
  (if n ≤ 702 then (if n ≤ 677 then (if n ≤ 665 then (if n ≤ 659 then (if n ≤ 656 then (if n ≤ 654 then (if n ≤ 653 then 3 else 3) else (if n ≤ 655 then 5 else 3)) else (if n ≤ 658 then (if n ≤ 657 then 3 else 5) else 3)) else (if n ≤ 662 then (if n ≤ 661 then (if n ≤ 660 then 3 else 5) else 3) else (if n ≤ 664 then (if n ≤ 663 then 3 else 5) else 3))) else (if n ≤ 671 then (if n ≤ 668 then (if n ≤ 667 then (if n ≤ 666 then 3 else 11) else 3) else (if n ≤ 670 then (if n ≤ 669 then 3 else 5) else 3)) else (if n ≤ 674 then (if n ≤ 673 then (if n ≤ 672 then 3 else 5) else 3) else (if n ≤ 676 then (if n ≤ 675 then 3 else 5) else 3)))) else (if n ≤ 690 then (if n ≤ 684 then (if n ≤ 681 then (if n ≤ 679 then (if n ≤ 678 then 3 else 5) else (if n ≤ 680 then 3 else 3)) else (if n ≤ 683 then (if n ≤ 682 then 11 else 3) else 3)) else (if n ≤ 687 then (if n ≤ 686 then (if n ≤ 685 then 5 else 3) else 3) else (if n ≤ 689 then (if n ≤ 688 then 5 else 3) else 3))) else (if n ≤ 696 then (if n ≤ 693 then (if n ≤ 692 then (if n ≤ 691 then 5 else 3) else 3) else (if n ≤ 695 then (if n ≤ 694 then 5 else 3) else 3)) else (if n ≤ 699 then (if n ≤ 698 then (if n ≤ 697 then 7 else 3) else 3) else (if n ≤ 701 then (if n ≤ 700 then 5 else 3) else 3))))) else (if n ≤ 727 then (if n ≤ 715 then (if n ≤ 709 then (if n ≤ 706 then (if n ≤ 704 then (if n ≤ 703 then 5 else 3) else (if n ≤ 705 then 3 else 5)) else (if n ≤ 708 then (if n ≤ 707 then 3 else 3) else 5)) else (if n ≤ 712 then (if n ≤ 711 then (if n ≤ 710 then 3 else 3) else 7) else (if n ≤ 714 then (if n ≤ 713 then 3 else 3) else 5))) else (if n ≤ 721 then (if n ≤ 718 then (if n ≤ 717 then (if n ≤ 716 then 3 else 3) else 5) else (if n ≤ 720 then (if n ≤ 719 then 3 else 3) else 5)) else (if n ≤ 724 then (if n ≤ 723 then (if n ≤ 722 then 3 else 3) else 5) else (if n ≤ 726 then (if n ≤ 725 then 3 else 3) else 11)))) else (if n ≤ 740 then (if n ≤ 734 then (if n ≤ 731 then (if n ≤ 729 then (if n ≤ 728 then 3 else 3) else (if n ≤ 730 then 5 else 3)) else (if n ≤ 733 then (if n ≤ 732 then 3 else 5) else 3)) else (if n ≤ 737 then (if n ≤ 736 then (if n ≤ 735 then 3 else 5) else 3) else (if n ≤ 739 then (if n ≤ 738 then 3 else 5) else 3))) else (if n ≤ 746 then (if n ≤ 743 then (if n ≤ 742 then (if n ≤ 741 then 3 else 7) else 3) else (if n ≤ 745 then (if n ≤ 744 then 3 else 5) else 3)) else (if n ≤ 749 then (if n ≤ 748 then (if n ≤ 747 then 3 else 5) else 3) else (if n ≤ 751 then (if n ≤ 750 then 3 else 5) else 3))))))

def certificate_d_block_7 (n : ℕ) : ℕ :=
  (if n ≤ 802 then (if n ≤ 777 then (if n ≤ 765 then (if n ≤ 759 then (if n ≤ 756 then (if n ≤ 754 then (if n ≤ 753 then 3 else 5) else (if n ≤ 755 then 3 else 3)) else (if n ≤ 758 then (if n ≤ 757 then 11 else 3) else 3)) else (if n ≤ 762 then (if n ≤ 761 then (if n ≤ 760 then 5 else 3) else 3) else (if n ≤ 764 then (if n ≤ 763 then 5 else 3) else 3))) else (if n ≤ 771 then (if n ≤ 768 then (if n ≤ 767 then (if n ≤ 766 then 5 else 3) else 3) else (if n ≤ 770 then (if n ≤ 769 then 5 else 3) else 3)) else (if n ≤ 774 then (if n ≤ 773 then (if n ≤ 772 then 11 else 3) else 3) else (if n ≤ 776 then (if n ≤ 775 then 5 else 3) else 3)))) else (if n ≤ 790 then (if n ≤ 784 then (if n ≤ 781 then (if n ≤ 779 then (if n ≤ 778 then 5 else 3) else (if n ≤ 780 then 3 else 5)) else (if n ≤ 783 then (if n ≤ 782 then 3 else 3) else 5)) else (if n ≤ 787 then (if n ≤ 786 then (if n ≤ 785 then 3 else 3) else 11) else (if n ≤ 789 then (if n ≤ 788 then 3 else 3) else 5))) else (if n ≤ 796 then (if n ≤ 793 then (if n ≤ 792 then (if n ≤ 791 then 3 else 3) else 5) else (if n ≤ 795 then (if n ≤ 794 then 3 else 3) else 5)) else (if n ≤ 799 then (if n ≤ 798 then (if n ≤ 797 then 3 else 3) else 5) else (if n ≤ 801 then (if n ≤ 800 then 3 else 3) else 7))))) else (if n ≤ 827 then (if n ≤ 815 then (if n ≤ 809 then (if n ≤ 806 then (if n ≤ 804 then (if n ≤ 803 then 3 else 3) else (if n ≤ 805 then 5 else 3)) else (if n ≤ 808 then (if n ≤ 807 then 3 else 5) else 3)) else (if n ≤ 812 then (if n ≤ 811 then (if n ≤ 810 then 3 else 5) else 3) else (if n ≤ 814 then (if n ≤ 813 then 3 else 5) else 3))) else (if n ≤ 821 then (if n ≤ 818 then (if n ≤ 817 then (if n ≤ 816 then 3 else 7) else 3) else (if n ≤ 820 then (if n ≤ 819 then 3 else 5) else 3)) else (if n ≤ 824 then (if n ≤ 823 then (if n ≤ 822 then 3 else 5) else 3) else (if n ≤ 826 then (if n ≤ 825 then 3 else 5) else 3)))) else (if n ≤ 840 then (if n ≤ 834 then (if n ≤ 831 then (if n ≤ 829 then (if n ≤ 828 then 3 else 5) else (if n ≤ 830 then 3 else 3)) else (if n ≤ 833 then (if n ≤ 832 then 11 else 3) else 3)) else (if n ≤ 837 then (if n ≤ 836 then (if n ≤ 835 then 5 else 3) else 3) else (if n ≤ 839 then (if n ≤ 838 then 5 else 3) else 3))) else (if n ≤ 846 then (if n ≤ 843 then (if n ≤ 842 then (if n ≤ 841 then 5 else 3) else 3) else (if n ≤ 845 then (if n ≤ 844 then 5 else 3) else 3)) else (if n ≤ 849 then (if n ≤ 848 then (if n ≤ 847 then 7 else 3) else 3) else (if n ≤ 851 then (if n ≤ 850 then 5 else 3) else 3))))))

def certificate_d_block_8 (n : ℕ) : ℕ :=
  (if n ≤ 902 then (if n ≤ 877 then (if n ≤ 865 then (if n ≤ 859 then (if n ≤ 856 then (if n ≤ 854 then (if n ≤ 853 then 5 else 3) else (if n ≤ 855 then 3 else 5)) else (if n ≤ 858 then (if n ≤ 857 then 3 else 3) else 5)) else (if n ≤ 862 then (if n ≤ 861 then (if n ≤ 860 then 3 else 3) else 11) else (if n ≤ 864 then (if n ≤ 863 then 3 else 3) else 5))) else (if n ≤ 871 then (if n ≤ 868 then (if n ≤ 867 then (if n ≤ 866 then 3 else 3) else 5) else (if n ≤ 870 then (if n ≤ 869 then 3 else 3) else 5)) else (if n ≤ 874 then (if n ≤ 873 then (if n ≤ 872 then 3 else 3) else 5) else (if n ≤ 876 then (if n ≤ 875 then 3 else 3) else 11)))) else (if n ≤ 890 then (if n ≤ 884 then (if n ≤ 881 then (if n ≤ 879 then (if n ≤ 878 then 3 else 3) else (if n ≤ 880 then 5 else 3)) else (if n ≤ 883 then (if n ≤ 882 then 3 else 5) else 3)) else (if n ≤ 887 then (if n ≤ 886 then (if n ≤ 885 then 3 else 5) else 3) else (if n ≤ 889 then (if n ≤ 888 then 3 else 5) else 3))) else (if n ≤ 896 then (if n ≤ 893 then (if n ≤ 892 then (if n ≤ 891 then 3 else 11) else 3) else (if n ≤ 895 then (if n ≤ 894 then 3 else 5) else 3)) else (if n ≤ 899 then (if n ≤ 898 then (if n ≤ 897 then 3 else 5) else 3) else (if n ≤ 901 then (if n ≤ 900 then 3 else 5) else 3))))) else (if n ≤ 927 then (if n ≤ 915 then (if n ≤ 909 then (if n ≤ 906 then (if n ≤ 904 then (if n ≤ 903 then 3 else 5) else (if n ≤ 905 then 3 else 3)) else (if n ≤ 908 then (if n ≤ 907 then 7 else 3) else 3)) else (if n ≤ 912 then (if n ≤ 911 then (if n ≤ 910 then 5 else 3) else 3) else (if n ≤ 914 then (if n ≤ 913 then 5 else 3) else 3))) else (if n ≤ 921 then (if n ≤ 918 then (if n ≤ 917 then (if n ≤ 916 then 5 else 3) else 3) else (if n ≤ 920 then (if n ≤ 919 then 5 else 3) else 3)) else (if n ≤ 924 then (if n ≤ 923 then (if n ≤ 922 then 7 else 3) else 3) else (if n ≤ 926 then (if n ≤ 925 then 5 else 3) else 3)))) else (if n ≤ 940 then (if n ≤ 934 then (if n ≤ 931 then (if n ≤ 929 then (if n ≤ 928 then 5 else 3) else (if n ≤ 930 then 3 else 5)) else (if n ≤ 933 then (if n ≤ 932 then 3 else 3) else 5)) else (if n ≤ 937 then (if n ≤ 936 then (if n ≤ 935 then 3 else 3) else 11) else (if n ≤ 939 then (if n ≤ 938 then 3 else 3) else 5))) else (if n ≤ 946 then (if n ≤ 943 then (if n ≤ 942 then (if n ≤ 941 then 3 else 3) else 5) else (if n ≤ 945 then (if n ≤ 944 then 3 else 3) else 5)) else (if n ≤ 949 then (if n ≤ 948 then (if n ≤ 947 then 3 else 3) else 5) else (if n ≤ 951 then (if n ≤ 950 then 3 else 3) else 7))))))

def certificate_d_block_9 (n : ℕ) : ℕ :=
  (if n ≤ 1002 then (if n ≤ 977 then (if n ≤ 965 then (if n ≤ 959 then (if n ≤ 956 then (if n ≤ 954 then (if n ≤ 953 then 3 else 3) else (if n ≤ 955 then 5 else 3)) else (if n ≤ 958 then (if n ≤ 957 then 3 else 5) else 3)) else (if n ≤ 962 then (if n ≤ 961 then (if n ≤ 960 then 3 else 5) else 3) else (if n ≤ 964 then (if n ≤ 963 then 3 else 5) else 3))) else (if n ≤ 971 then (if n ≤ 968 then (if n ≤ 967 then (if n ≤ 966 then 3 else 11) else 3) else (if n ≤ 970 then (if n ≤ 969 then 3 else 5) else 3)) else (if n ≤ 974 then (if n ≤ 973 then (if n ≤ 972 then 3 else 5) else 3) else (if n ≤ 976 then (if n ≤ 975 then 3 else 5) else 3)))) else (if n ≤ 990 then (if n ≤ 984 then (if n ≤ 981 then (if n ≤ 979 then (if n ≤ 978 then 3 else 5) else (if n ≤ 980 then 3 else 3)) else (if n ≤ 983 then (if n ≤ 982 then 11 else 3) else 3)) else (if n ≤ 987 then (if n ≤ 986 then (if n ≤ 985 then 5 else 3) else 3) else (if n ≤ 989 then (if n ≤ 988 then 5 else 3) else 3))) else (if n ≤ 996 then (if n ≤ 993 then (if n ≤ 992 then (if n ≤ 991 then 5 else 3) else 3) else (if n ≤ 995 then (if n ≤ 994 then 5 else 3) else 3)) else (if n ≤ 999 then (if n ≤ 998 then (if n ≤ 997 then 11 else 3) else 3) else (if n ≤ 1001 then (if n ≤ 1000 then 5 else 3) else 3))))) else (if n ≤ 1027 then (if n ≤ 1015 then (if n ≤ 1009 then (if n ≤ 1006 then (if n ≤ 1004 then (if n ≤ 1003 then 5 else 3) else (if n ≤ 1005 then 3 else 5)) else (if n ≤ 1008 then (if n ≤ 1007 then 3 else 3) else 5)) else (if n ≤ 1012 then (if n ≤ 1011 then (if n ≤ 1010 then 3 else 3) else 7) else (if n ≤ 1014 then (if n ≤ 1013 then 3 else 3) else 5))) else (if n ≤ 1021 then (if n ≤ 1018 then (if n ≤ 1017 then (if n ≤ 1016 then 3 else 3) else 5) else (if n ≤ 1020 then (if n ≤ 1019 then 3 else 3) else 5)) else (if n ≤ 1024 then (if n ≤ 1023 then (if n ≤ 1022 then 3 else 3) else 5) else (if n ≤ 1026 then (if n ≤ 1025 then 3 else 3) else 7)))) else (if n ≤ 1040 then (if n ≤ 1034 then (if n ≤ 1031 then (if n ≤ 1029 then (if n ≤ 1028 then 3 else 3) else (if n ≤ 1030 then 5 else 3)) else (if n ≤ 1033 then (if n ≤ 1032 then 3 else 5) else 3)) else (if n ≤ 1037 then (if n ≤ 1036 then (if n ≤ 1035 then 3 else 5) else 3) else (if n ≤ 1039 then (if n ≤ 1038 then 3 else 5) else 3))) else (if n ≤ 1046 then (if n ≤ 1043 then (if n ≤ 1042 then (if n ≤ 1041 then 3 else 11) else 3) else (if n ≤ 1045 then (if n ≤ 1044 then 3 else 5) else 3)) else (if n ≤ 1049 then (if n ≤ 1048 then (if n ≤ 1047 then 3 else 5) else 3) else (if n ≤ 1051 then (if n ≤ 1050 then 3 else 5) else 3))))))

def certificate_d_block_10 (n : ℕ) : ℕ :=
  (if n ≤ 1102 then (if n ≤ 1077 then (if n ≤ 1065 then (if n ≤ 1059 then (if n ≤ 1056 then (if n ≤ 1054 then (if n ≤ 1053 then 3 else 5) else (if n ≤ 1055 then 3 else 3)) else (if n ≤ 1058 then (if n ≤ 1057 then 7 else 3) else 3)) else (if n ≤ 1062 then (if n ≤ 1061 then (if n ≤ 1060 then 5 else 3) else 3) else (if n ≤ 1064 then (if n ≤ 1063 then 5 else 3) else 3))) else (if n ≤ 1071 then (if n ≤ 1068 then (if n ≤ 1067 then (if n ≤ 1066 then 5 else 3) else 3) else (if n ≤ 1070 then (if n ≤ 1069 then 5 else 3) else 3)) else (if n ≤ 1074 then (if n ≤ 1073 then (if n ≤ 1072 then 19 else 3) else 3) else (if n ≤ 1076 then (if n ≤ 1075 then 5 else 3) else 3)))) else (if n ≤ 1090 then (if n ≤ 1084 then (if n ≤ 1081 then (if n ≤ 1079 then (if n ≤ 1078 then 5 else 3) else (if n ≤ 1080 then 3 else 5)) else (if n ≤ 1083 then (if n ≤ 1082 then 3 else 3) else 5)) else (if n ≤ 1087 then (if n ≤ 1086 then (if n ≤ 1085 then 3 else 3) else 11) else (if n ≤ 1089 then (if n ≤ 1088 then 3 else 3) else 5))) else (if n ≤ 1096 then (if n ≤ 1093 then (if n ≤ 1092 then (if n ≤ 1091 then 3 else 3) else 5) else (if n ≤ 1095 then (if n ≤ 1094 then 3 else 3) else 5)) else (if n ≤ 1099 then (if n ≤ 1098 then (if n ≤ 1097 then 3 else 3) else 5) else (if n ≤ 1101 then (if n ≤ 1100 then 3 else 3) else 11))))) else (if n ≤ 1127 then (if n ≤ 1115 then (if n ≤ 1109 then (if n ≤ 1106 then (if n ≤ 1104 then (if n ≤ 1103 then 3 else 3) else (if n ≤ 1105 then 5 else 3)) else (if n ≤ 1108 then (if n ≤ 1107 then 3 else 5) else 3)) else (if n ≤ 1112 then (if n ≤ 1111 then (if n ≤ 1110 then 3 else 5) else 3) else (if n ≤ 1114 then (if n ≤ 1113 then 3 else 5) else 3))) else (if n ≤ 1121 then (if n ≤ 1118 then (if n ≤ 1117 then (if n ≤ 1116 then 3 else 7) else 3) else (if n ≤ 1120 then (if n ≤ 1119 then 3 else 5) else 3)) else (if n ≤ 1124 then (if n ≤ 1123 then (if n ≤ 1122 then 3 else 5) else 3) else (if n ≤ 1126 then (if n ≤ 1125 then 3 else 5) else 3)))) else (if n ≤ 1140 then (if n ≤ 1134 then (if n ≤ 1131 then (if n ≤ 1129 then (if n ≤ 1128 then 3 else 5) else (if n ≤ 1130 then 3 else 3)) else (if n ≤ 1133 then (if n ≤ 1132 then 7 else 3) else 3)) else (if n ≤ 1137 then (if n ≤ 1136 then (if n ≤ 1135 then 5 else 3) else 3) else (if n ≤ 1139 then (if n ≤ 1138 then 5 else 3) else 3))) else (if n ≤ 1146 then (if n ≤ 1143 then (if n ≤ 1142 then (if n ≤ 1141 then 5 else 3) else 3) else (if n ≤ 1145 then (if n ≤ 1144 then 5 else 3) else 3)) else (if n ≤ 1149 then (if n ≤ 1148 then (if n ≤ 1147 then 11 else 3) else 3) else (if n ≤ 1151 then (if n ≤ 1150 then 5 else 3) else 3))))))

def certificate_d_block_11 (n : ℕ) : ℕ :=
  (if n ≤ 1202 then (if n ≤ 1177 then (if n ≤ 1165 then (if n ≤ 1159 then (if n ≤ 1156 then (if n ≤ 1154 then (if n ≤ 1153 then 5 else 3) else (if n ≤ 1155 then 3 else 5)) else (if n ≤ 1158 then (if n ≤ 1157 then 3 else 3) else 5)) else (if n ≤ 1162 then (if n ≤ 1161 then (if n ≤ 1160 then 3 else 3) else 7) else (if n ≤ 1164 then (if n ≤ 1163 then 3 else 3) else 5))) else (if n ≤ 1171 then (if n ≤ 1168 then (if n ≤ 1167 then (if n ≤ 1166 then 3 else 3) else 5) else (if n ≤ 1170 then (if n ≤ 1169 then 3 else 3) else 5)) else (if n ≤ 1174 then (if n ≤ 1173 then (if n ≤ 1172 then 3 else 3) else 5) else (if n ≤ 1176 then (if n ≤ 1175 then 3 else 3) else 11)))) else (if n ≤ 1190 then (if n ≤ 1184 then (if n ≤ 1181 then (if n ≤ 1179 then (if n ≤ 1178 then 3 else 3) else (if n ≤ 1180 then 5 else 3)) else (if n ≤ 1183 then (if n ≤ 1182 then 3 else 5) else 3)) else (if n ≤ 1187 then (if n ≤ 1186 then (if n ≤ 1185 then 3 else 5) else 3) else (if n ≤ 1189 then (if n ≤ 1188 then 3 else 5) else 3))) else (if n ≤ 1196 then (if n ≤ 1193 then (if n ≤ 1192 then (if n ≤ 1191 then 3 else 11) else 3) else (if n ≤ 1195 then (if n ≤ 1194 then 3 else 5) else 3)) else (if n ≤ 1199 then (if n ≤ 1198 then (if n ≤ 1197 then 3 else 5) else 3) else (if n ≤ 1201 then (if n ≤ 1200 then 3 else 5) else 3))))) else (if n ≤ 1227 then (if n ≤ 1215 then (if n ≤ 1209 then (if n ≤ 1206 then (if n ≤ 1204 then (if n ≤ 1203 then 3 else 5) else (if n ≤ 1205 then 3 else 3)) else (if n ≤ 1208 then (if n ≤ 1207 then 11 else 3) else 3)) else (if n ≤ 1212 then (if n ≤ 1211 then (if n ≤ 1210 then 5 else 3) else 3) else (if n ≤ 1214 then (if n ≤ 1213 then 5 else 3) else 3))) else (if n ≤ 1221 then (if n ≤ 1218 then (if n ≤ 1217 then (if n ≤ 1216 then 5 else 3) else 3) else (if n ≤ 1220 then (if n ≤ 1219 then 5 else 3) else 3)) else (if n ≤ 1224 then (if n ≤ 1223 then (if n ≤ 1222 then 7 else 3) else 3) else (if n ≤ 1226 then (if n ≤ 1225 then 5 else 3) else 3)))) else (if n ≤ 1240 then (if n ≤ 1234 then (if n ≤ 1231 then (if n ≤ 1229 then (if n ≤ 1228 then 5 else 3) else (if n ≤ 1230 then 3 else 5)) else (if n ≤ 1233 then (if n ≤ 1232 then 3 else 3) else 5)) else (if n ≤ 1237 then (if n ≤ 1236 then (if n ≤ 1235 then 3 else 3) else 7) else (if n ≤ 1239 then (if n ≤ 1238 then 3 else 3) else 5))) else (if n ≤ 1246 then (if n ≤ 1243 then (if n ≤ 1242 then (if n ≤ 1241 then 3 else 3) else 5) else (if n ≤ 1245 then (if n ≤ 1244 then 3 else 3) else 5)) else (if n ≤ 1249 then (if n ≤ 1248 then (if n ≤ 1247 then 3 else 3) else 5) else (if n ≤ 1251 then (if n ≤ 1250 then 3 else 3) else 11))))))

def certificate_d_block_12 (n : ℕ) : ℕ :=
  (if n ≤ 1302 then (if n ≤ 1277 then (if n ≤ 1265 then (if n ≤ 1259 then (if n ≤ 1256 then (if n ≤ 1254 then (if n ≤ 1253 then 3 else 3) else (if n ≤ 1255 then 5 else 3)) else (if n ≤ 1258 then (if n ≤ 1257 then 3 else 5) else 3)) else (if n ≤ 1262 then (if n ≤ 1261 then (if n ≤ 1260 then 3 else 5) else 3) else (if n ≤ 1264 then (if n ≤ 1263 then 3 else 5) else 3))) else (if n ≤ 1271 then (if n ≤ 1268 then (if n ≤ 1267 then (if n ≤ 1266 then 3 else 7) else 3) else (if n ≤ 1270 then (if n ≤ 1269 then 3 else 5) else 3)) else (if n ≤ 1274 then (if n ≤ 1273 then (if n ≤ 1272 then 3 else 5) else 3) else (if n ≤ 1276 then (if n ≤ 1275 then 3 else 5) else 3)))) else (if n ≤ 1290 then (if n ≤ 1284 then (if n ≤ 1281 then (if n ≤ 1279 then (if n ≤ 1278 then 3 else 5) else (if n ≤ 1280 then 3 else 3)) else (if n ≤ 1283 then (if n ≤ 1282 then 11 else 3) else 3)) else (if n ≤ 1287 then (if n ≤ 1286 then (if n ≤ 1285 then 5 else 3) else 3) else (if n ≤ 1289 then (if n ≤ 1288 then 5 else 3) else 3))) else (if n ≤ 1296 then (if n ≤ 1293 then (if n ≤ 1292 then (if n ≤ 1291 then 5 else 3) else 3) else (if n ≤ 1295 then (if n ≤ 1294 then 5 else 3) else 3)) else (if n ≤ 1299 then (if n ≤ 1298 then (if n ≤ 1297 then 11 else 3) else 3) else (if n ≤ 1301 then (if n ≤ 1300 then 5 else 3) else 3))))) else (if n ≤ 1327 then (if n ≤ 1315 then (if n ≤ 1309 then (if n ≤ 1306 then (if n ≤ 1304 then (if n ≤ 1303 then 5 else 3) else (if n ≤ 1305 then 3 else 5)) else (if n ≤ 1308 then (if n ≤ 1307 then 3 else 3) else 5)) else (if n ≤ 1312 then (if n ≤ 1311 then (if n ≤ 1310 then 3 else 3) else 11) else (if n ≤ 1314 then (if n ≤ 1313 then 3 else 3) else 5))) else (if n ≤ 1321 then (if n ≤ 1318 then (if n ≤ 1317 then (if n ≤ 1316 then 3 else 3) else 5) else (if n ≤ 1320 then (if n ≤ 1319 then 3 else 3) else 5)) else (if n ≤ 1324 then (if n ≤ 1323 then (if n ≤ 1322 then 3 else 3) else 5) else (if n ≤ 1326 then (if n ≤ 1325 then 3 else 3) else 7)))) else (if n ≤ 1340 then (if n ≤ 1334 then (if n ≤ 1331 then (if n ≤ 1329 then (if n ≤ 1328 then 3 else 3) else (if n ≤ 1330 then 5 else 3)) else (if n ≤ 1333 then (if n ≤ 1332 then 3 else 5) else 3)) else (if n ≤ 1337 then (if n ≤ 1336 then (if n ≤ 1335 then 3 else 5) else 3) else (if n ≤ 1339 then (if n ≤ 1338 then 3 else 5) else 3))) else (if n ≤ 1346 then (if n ≤ 1343 then (if n ≤ 1342 then (if n ≤ 1341 then 3 else 7) else 3) else (if n ≤ 1345 then (if n ≤ 1344 then 3 else 5) else 3)) else (if n ≤ 1349 then (if n ≤ 1348 then (if n ≤ 1347 then 3 else 5) else 3) else (if n ≤ 1351 then (if n ≤ 1350 then 3 else 5) else 3))))))

def certificate_d_block_13 (n : ℕ) : ℕ :=
  (if n ≤ 1402 then (if n ≤ 1377 then (if n ≤ 1365 then (if n ≤ 1359 then (if n ≤ 1356 then (if n ≤ 1354 then (if n ≤ 1353 then 3 else 5) else (if n ≤ 1355 then 3 else 3)) else (if n ≤ 1358 then (if n ≤ 1357 then 11 else 3) else 3)) else (if n ≤ 1362 then (if n ≤ 1361 then (if n ≤ 1360 then 5 else 3) else 3) else (if n ≤ 1364 then (if n ≤ 1363 then 5 else 3) else 3))) else (if n ≤ 1371 then (if n ≤ 1368 then (if n ≤ 1367 then (if n ≤ 1366 then 5 else 3) else 3) else (if n ≤ 1370 then (if n ≤ 1369 then 5 else 3) else 3)) else (if n ≤ 1374 then (if n ≤ 1373 then (if n ≤ 1372 then 7 else 3) else 3) else (if n ≤ 1376 then (if n ≤ 1375 then 5 else 3) else 3)))) else (if n ≤ 1390 then (if n ≤ 1384 then (if n ≤ 1381 then (if n ≤ 1379 then (if n ≤ 1378 then 5 else 3) else (if n ≤ 1380 then 3 else 5)) else (if n ≤ 1383 then (if n ≤ 1382 then 3 else 3) else 5)) else (if n ≤ 1387 then (if n ≤ 1386 then (if n ≤ 1385 then 3 else 3) else 11) else (if n ≤ 1389 then (if n ≤ 1388 then 3 else 3) else 5))) else (if n ≤ 1396 then (if n ≤ 1393 then (if n ≤ 1392 then (if n ≤ 1391 then 3 else 3) else 5) else (if n ≤ 1395 then (if n ≤ 1394 then 3 else 3) else 5)) else (if n ≤ 1399 then (if n ≤ 1398 then (if n ≤ 1397 then 3 else 3) else 5) else (if n ≤ 1401 then (if n ≤ 1400 then 3 else 3) else 13))))) else (if n ≤ 1427 then (if n ≤ 1415 then (if n ≤ 1409 then (if n ≤ 1406 then (if n ≤ 1404 then (if n ≤ 1403 then 3 else 3) else (if n ≤ 1405 then 5 else 3)) else (if n ≤ 1408 then (if n ≤ 1407 then 3 else 5) else 3)) else (if n ≤ 1412 then (if n ≤ 1411 then (if n ≤ 1410 then 3 else 5) else 3) else (if n ≤ 1414 then (if n ≤ 1413 then 3 else 5) else 3))) else (if n ≤ 1421 then (if n ≤ 1418 then (if n ≤ 1417 then (if n ≤ 1416 then 3 else 11) else 3) else (if n ≤ 1420 then (if n ≤ 1419 then 3 else 5) else 3)) else (if n ≤ 1424 then (if n ≤ 1423 then (if n ≤ 1422 then 3 else 5) else 3) else (if n ≤ 1426 then (if n ≤ 1425 then 3 else 5) else 3)))) else (if n ≤ 1440 then (if n ≤ 1434 then (if n ≤ 1431 then (if n ≤ 1429 then (if n ≤ 1428 then 3 else 5) else (if n ≤ 1430 then 3 else 3)) else (if n ≤ 1433 then (if n ≤ 1432 then 7 else 3) else 3)) else (if n ≤ 1437 then (if n ≤ 1436 then (if n ≤ 1435 then 5 else 3) else 3) else (if n ≤ 1439 then (if n ≤ 1438 then 5 else 3) else 3))) else (if n ≤ 1446 then (if n ≤ 1443 then (if n ≤ 1442 then (if n ≤ 1441 then 5 else 3) else 3) else (if n ≤ 1445 then (if n ≤ 1444 then 5 else 3) else 3)) else (if n ≤ 1449 then (if n ≤ 1448 then (if n ≤ 1447 then 7 else 3) else 3) else (if n ≤ 1451 then (if n ≤ 1450 then 5 else 3) else 3))))))

def certificate_d_block_14 (n : ℕ) : ℕ :=
  (if n ≤ 1502 then (if n ≤ 1477 then (if n ≤ 1465 then (if n ≤ 1459 then (if n ≤ 1456 then (if n ≤ 1454 then (if n ≤ 1453 then 5 else 3) else (if n ≤ 1455 then 3 else 5)) else (if n ≤ 1458 then (if n ≤ 1457 then 3 else 3) else 5)) else (if n ≤ 1462 then (if n ≤ 1461 then (if n ≤ 1460 then 3 else 3) else 11) else (if n ≤ 1464 then (if n ≤ 1463 then 3 else 3) else 5))) else (if n ≤ 1471 then (if n ≤ 1468 then (if n ≤ 1467 then (if n ≤ 1466 then 3 else 3) else 5) else (if n ≤ 1470 then (if n ≤ 1469 then 3 else 3) else 5)) else (if n ≤ 1474 then (if n ≤ 1473 then (if n ≤ 1472 then 3 else 3) else 5) else (if n ≤ 1476 then (if n ≤ 1475 then 3 else 3) else 7)))) else (if n ≤ 1490 then (if n ≤ 1484 then (if n ≤ 1481 then (if n ≤ 1479 then (if n ≤ 1478 then 3 else 3) else (if n ≤ 1480 then 5 else 3)) else (if n ≤ 1483 then (if n ≤ 1482 then 3 else 5) else 3)) else (if n ≤ 1487 then (if n ≤ 1486 then (if n ≤ 1485 then 3 else 5) else 3) else (if n ≤ 1489 then (if n ≤ 1488 then 3 else 5) else 3))) else (if n ≤ 1496 then (if n ≤ 1493 then (if n ≤ 1492 then (if n ≤ 1491 then 3 else 11) else 3) else (if n ≤ 1495 then (if n ≤ 1494 then 3 else 5) else 3)) else (if n ≤ 1499 then (if n ≤ 1498 then (if n ≤ 1497 then 3 else 5) else 3) else (if n ≤ 1501 then (if n ≤ 1500 then 3 else 5) else 3))))) else (if n ≤ 1527 then (if n ≤ 1515 then (if n ≤ 1509 then (if n ≤ 1506 then (if n ≤ 1504 then (if n ≤ 1503 then 3 else 5) else (if n ≤ 1505 then 3 else 3)) else (if n ≤ 1508 then (if n ≤ 1507 then 11 else 3) else 3)) else (if n ≤ 1512 then (if n ≤ 1511 then (if n ≤ 1510 then 5 else 3) else 3) else (if n ≤ 1514 then (if n ≤ 1513 then 5 else 3) else 3))) else (if n ≤ 1521 then (if n ≤ 1518 then (if n ≤ 1517 then (if n ≤ 1516 then 5 else 3) else 3) else (if n ≤ 1520 then (if n ≤ 1519 then 5 else 3) else 3)) else (if n ≤ 1524 then (if n ≤ 1523 then (if n ≤ 1522 then 11 else 3) else 3) else (if n ≤ 1526 then (if n ≤ 1525 then 5 else 3) else 3)))) else (if n ≤ 1540 then (if n ≤ 1534 then (if n ≤ 1531 then (if n ≤ 1529 then (if n ≤ 1528 then 5 else 3) else (if n ≤ 1530 then 3 else 5)) else (if n ≤ 1533 then (if n ≤ 1532 then 3 else 3) else 5)) else (if n ≤ 1537 then (if n ≤ 1536 then (if n ≤ 1535 then 3 else 3) else 7) else (if n ≤ 1539 then (if n ≤ 1538 then 3 else 3) else 5))) else (if n ≤ 1546 then (if n ≤ 1543 then (if n ≤ 1542 then (if n ≤ 1541 then 3 else 3) else 5) else (if n ≤ 1545 then (if n ≤ 1544 then 3 else 3) else 5)) else (if n ≤ 1549 then (if n ≤ 1548 then (if n ≤ 1547 then 3 else 3) else 5) else (if n ≤ 1551 then (if n ≤ 1550 then 3 else 3) else 7))))))

def certificate_d_block_15 (n : ℕ) : ℕ :=
  (if n ≤ 1602 then (if n ≤ 1577 then (if n ≤ 1565 then (if n ≤ 1559 then (if n ≤ 1556 then (if n ≤ 1554 then (if n ≤ 1553 then 3 else 3) else (if n ≤ 1555 then 5 else 3)) else (if n ≤ 1558 then (if n ≤ 1557 then 3 else 5) else 3)) else (if n ≤ 1562 then (if n ≤ 1561 then (if n ≤ 1560 then 3 else 5) else 3) else (if n ≤ 1564 then (if n ≤ 1563 then 3 else 5) else 3))) else (if n ≤ 1571 then (if n ≤ 1568 then (if n ≤ 1567 then (if n ≤ 1566 then 3 else 13) else 3) else (if n ≤ 1570 then (if n ≤ 1569 then 3 else 5) else 3)) else (if n ≤ 1574 then (if n ≤ 1573 then (if n ≤ 1572 then 3 else 5) else 3) else (if n ≤ 1576 then (if n ≤ 1575 then 3 else 5) else 3)))) else (if n ≤ 1590 then (if n ≤ 1584 then (if n ≤ 1581 then (if n ≤ 1579 then (if n ≤ 1578 then 3 else 5) else (if n ≤ 1580 then 3 else 3)) else (if n ≤ 1583 then (if n ≤ 1582 then 7 else 3) else 3)) else (if n ≤ 1587 then (if n ≤ 1586 then (if n ≤ 1585 then 5 else 3) else 3) else (if n ≤ 1589 then (if n ≤ 1588 then 5 else 3) else 3))) else (if n ≤ 1596 then (if n ≤ 1593 then (if n ≤ 1592 then (if n ≤ 1591 then 5 else 3) else 3) else (if n ≤ 1595 then (if n ≤ 1594 then 5 else 3) else 3)) else (if n ≤ 1599 then (if n ≤ 1598 then (if n ≤ 1597 then 11 else 3) else 3) else (if n ≤ 1601 then (if n ≤ 1600 then 5 else 3) else 3))))) else (if n ≤ 1627 then (if n ≤ 1615 then (if n ≤ 1609 then (if n ≤ 1606 then (if n ≤ 1604 then (if n ≤ 1603 then 5 else 3) else (if n ≤ 1605 then 3 else 5)) else (if n ≤ 1608 then (if n ≤ 1607 then 3 else 3) else 5)) else (if n ≤ 1612 then (if n ≤ 1611 then (if n ≤ 1610 then 3 else 3) else 11) else (if n ≤ 1614 then (if n ≤ 1613 then 3 else 3) else 5))) else (if n ≤ 1621 then (if n ≤ 1618 then (if n ≤ 1617 then (if n ≤ 1616 then 3 else 3) else 5) else (if n ≤ 1620 then (if n ≤ 1619 then 3 else 3) else 5)) else (if n ≤ 1624 then (if n ≤ 1623 then (if n ≤ 1622 then 3 else 3) else 5) else (if n ≤ 1626 then (if n ≤ 1625 then 3 else 3) else 11)))) else (if n ≤ 1640 then (if n ≤ 1634 then (if n ≤ 1631 then (if n ≤ 1629 then (if n ≤ 1628 then 3 else 3) else (if n ≤ 1630 then 5 else 3)) else (if n ≤ 1633 then (if n ≤ 1632 then 3 else 5) else 3)) else (if n ≤ 1637 then (if n ≤ 1636 then (if n ≤ 1635 then 3 else 5) else 3) else (if n ≤ 1639 then (if n ≤ 1638 then 3 else 5) else 3))) else (if n ≤ 1646 then (if n ≤ 1643 then (if n ≤ 1642 then (if n ≤ 1641 then 3 else 7) else 3) else (if n ≤ 1645 then (if n ≤ 1644 then 3 else 5) else 3)) else (if n ≤ 1649 then (if n ≤ 1648 then (if n ≤ 1647 then 3 else 5) else 3) else (if n ≤ 1651 then (if n ≤ 1650 then 3 else 5) else 3))))))

def certificate_d_block_16 (n : ℕ) : ℕ :=
  (if n ≤ 1702 then (if n ≤ 1677 then (if n ≤ 1665 then (if n ≤ 1659 then (if n ≤ 1656 then (if n ≤ 1654 then (if n ≤ 1653 then 3 else 5) else (if n ≤ 1655 then 3 else 3)) else (if n ≤ 1658 then (if n ≤ 1657 then 7 else 3) else 3)) else (if n ≤ 1662 then (if n ≤ 1661 then (if n ≤ 1660 then 5 else 3) else 3) else (if n ≤ 1664 then (if n ≤ 1663 then 5 else 3) else 3))) else (if n ≤ 1671 then (if n ≤ 1668 then (if n ≤ 1667 then (if n ≤ 1666 then 5 else 3) else 3) else (if n ≤ 1670 then (if n ≤ 1669 then 5 else 3) else 3)) else (if n ≤ 1674 then (if n ≤ 1673 then (if n ≤ 1672 then 11 else 3) else 3) else (if n ≤ 1676 then (if n ≤ 1675 then 5 else 3) else 3)))) else (if n ≤ 1690 then (if n ≤ 1684 then (if n ≤ 1681 then (if n ≤ 1679 then (if n ≤ 1678 then 5 else 3) else (if n ≤ 1680 then 3 else 5)) else (if n ≤ 1683 then (if n ≤ 1682 then 3 else 3) else 5)) else (if n ≤ 1687 then (if n ≤ 1686 then (if n ≤ 1685 then 3 else 3) else 7) else (if n ≤ 1689 then (if n ≤ 1688 then 3 else 3) else 5))) else (if n ≤ 1696 then (if n ≤ 1693 then (if n ≤ 1692 then (if n ≤ 1691 then 3 else 3) else 5) else (if n ≤ 1695 then (if n ≤ 1694 then 3 else 3) else 5)) else (if n ≤ 1699 then (if n ≤ 1698 then (if n ≤ 1697 then 3 else 3) else 5) else (if n ≤ 1701 then (if n ≤ 1700 then 3 else 3) else 11))))) else (if n ≤ 1727 then (if n ≤ 1715 then (if n ≤ 1709 then (if n ≤ 1706 then (if n ≤ 1704 then (if n ≤ 1703 then 3 else 3) else (if n ≤ 1705 then 5 else 3)) else (if n ≤ 1708 then (if n ≤ 1707 then 3 else 5) else 3)) else (if n ≤ 1712 then (if n ≤ 1711 then (if n ≤ 1710 then 3 else 5) else 3) else (if n ≤ 1714 then (if n ≤ 1713 then 3 else 5) else 3))) else (if n ≤ 1721 then (if n ≤ 1718 then (if n ≤ 1717 then (if n ≤ 1716 then 3 else 11) else 3) else (if n ≤ 1720 then (if n ≤ 1719 then 3 else 5) else 3)) else (if n ≤ 1724 then (if n ≤ 1723 then (if n ≤ 1722 then 3 else 5) else 3) else (if n ≤ 1726 then (if n ≤ 1725 then 3 else 5) else 3)))) else (if n ≤ 1740 then (if n ≤ 1734 then (if n ≤ 1731 then (if n ≤ 1729 then (if n ≤ 1728 then 3 else 5) else (if n ≤ 1730 then 3 else 3)) else (if n ≤ 1733 then (if n ≤ 1732 then 13 else 3) else 3)) else (if n ≤ 1737 then (if n ≤ 1736 then (if n ≤ 1735 then 5 else 3) else 3) else (if n ≤ 1739 then (if n ≤ 1738 then 5 else 3) else 3))) else (if n ≤ 1746 then (if n ≤ 1743 then (if n ≤ 1742 then (if n ≤ 1741 then 5 else 3) else 3) else (if n ≤ 1745 then (if n ≤ 1744 then 5 else 3) else 3)) else (if n ≤ 1749 then (if n ≤ 1748 then (if n ≤ 1747 then 7 else 3) else 3) else (if n ≤ 1751 then (if n ≤ 1750 then 5 else 3) else 3))))))

def certificate_d_block_17 (n : ℕ) : ℕ :=
  (if n ≤ 1802 then (if n ≤ 1777 then (if n ≤ 1765 then (if n ≤ 1759 then (if n ≤ 1756 then (if n ≤ 1754 then (if n ≤ 1753 then 5 else 3) else (if n ≤ 1755 then 3 else 5)) else (if n ≤ 1758 then (if n ≤ 1757 then 3 else 3) else 5)) else (if n ≤ 1762 then (if n ≤ 1761 then (if n ≤ 1760 then 3 else 3) else 7) else (if n ≤ 1764 then (if n ≤ 1763 then 3 else 3) else 5))) else (if n ≤ 1771 then (if n ≤ 1768 then (if n ≤ 1767 then (if n ≤ 1766 then 3 else 3) else 5) else (if n ≤ 1770 then (if n ≤ 1769 then 3 else 3) else 5)) else (if n ≤ 1774 then (if n ≤ 1773 then (if n ≤ 1772 then 3 else 3) else 5) else (if n ≤ 1776 then (if n ≤ 1775 then 3 else 3) else 11)))) else (if n ≤ 1790 then (if n ≤ 1784 then (if n ≤ 1781 then (if n ≤ 1779 then (if n ≤ 1778 then 3 else 3) else (if n ≤ 1780 then 5 else 3)) else (if n ≤ 1783 then (if n ≤ 1782 then 3 else 5) else 3)) else (if n ≤ 1787 then (if n ≤ 1786 then (if n ≤ 1785 then 3 else 5) else 3) else (if n ≤ 1789 then (if n ≤ 1788 then 3 else 5) else 3))) else (if n ≤ 1796 then (if n ≤ 1793 then (if n ≤ 1792 then (if n ≤ 1791 then 3 else 7) else 3) else (if n ≤ 1795 then (if n ≤ 1794 then 3 else 5) else 3)) else (if n ≤ 1799 then (if n ≤ 1798 then (if n ≤ 1797 then 3 else 5) else 3) else (if n ≤ 1801 then (if n ≤ 1800 then 3 else 5) else 3))))) else (if n ≤ 1827 then (if n ≤ 1815 then (if n ≤ 1809 then (if n ≤ 1806 then (if n ≤ 1804 then (if n ≤ 1803 then 3 else 5) else (if n ≤ 1805 then 3 else 3)) else (if n ≤ 1808 then (if n ≤ 1807 then 11 else 3) else 3)) else (if n ≤ 1812 then (if n ≤ 1811 then (if n ≤ 1810 then 5 else 3) else 3) else (if n ≤ 1814 then (if n ≤ 1813 then 5 else 3) else 3))) else (if n ≤ 1821 then (if n ≤ 1818 then (if n ≤ 1817 then (if n ≤ 1816 then 5 else 3) else 3) else (if n ≤ 1820 then (if n ≤ 1819 then 5 else 3) else 3)) else (if n ≤ 1824 then (if n ≤ 1823 then (if n ≤ 1822 then 11 else 3) else 3) else (if n ≤ 1826 then (if n ≤ 1825 then 5 else 3) else 3)))) else (if n ≤ 1840 then (if n ≤ 1834 then (if n ≤ 1831 then (if n ≤ 1829 then (if n ≤ 1828 then 5 else 3) else (if n ≤ 1830 then 3 else 5)) else (if n ≤ 1833 then (if n ≤ 1832 then 3 else 3) else 5)) else (if n ≤ 1837 then (if n ≤ 1836 then (if n ≤ 1835 then 3 else 3) else 11) else (if n ≤ 1839 then (if n ≤ 1838 then 3 else 3) else 5))) else (if n ≤ 1846 then (if n ≤ 1843 then (if n ≤ 1842 then (if n ≤ 1841 then 3 else 3) else 5) else (if n ≤ 1845 then (if n ≤ 1844 then 3 else 3) else 5)) else (if n ≤ 1849 then (if n ≤ 1848 then (if n ≤ 1847 then 3 else 3) else 5) else (if n ≤ 1851 then (if n ≤ 1850 then 3 else 3) else 7))))))

def certificate_d_block_18 (n : ℕ) : ℕ :=
  (if n ≤ 1902 then (if n ≤ 1877 then (if n ≤ 1865 then (if n ≤ 1859 then (if n ≤ 1856 then (if n ≤ 1854 then (if n ≤ 1853 then 3 else 3) else (if n ≤ 1855 then 5 else 3)) else (if n ≤ 1858 then (if n ≤ 1857 then 3 else 5) else 3)) else (if n ≤ 1862 then (if n ≤ 1861 then (if n ≤ 1860 then 3 else 5) else 3) else (if n ≤ 1864 then (if n ≤ 1863 then 3 else 5) else 3))) else (if n ≤ 1871 then (if n ≤ 1868 then (if n ≤ 1867 then (if n ≤ 1866 then 3 else 7) else 3) else (if n ≤ 1870 then (if n ≤ 1869 then 3 else 5) else 3)) else (if n ≤ 1874 then (if n ≤ 1873 then (if n ≤ 1872 then 3 else 5) else 3) else (if n ≤ 1876 then (if n ≤ 1875 then 3 else 5) else 3)))) else (if n ≤ 1890 then (if n ≤ 1884 then (if n ≤ 1881 then (if n ≤ 1879 then (if n ≤ 1878 then 3 else 5) else (if n ≤ 1880 then 3 else 3)) else (if n ≤ 1883 then (if n ≤ 1882 then 11 else 3) else 3)) else (if n ≤ 1887 then (if n ≤ 1886 then (if n ≤ 1885 then 5 else 3) else 3) else (if n ≤ 1889 then (if n ≤ 1888 then 5 else 3) else 3))) else (if n ≤ 1896 then (if n ≤ 1893 then (if n ≤ 1892 then (if n ≤ 1891 then 5 else 3) else 3) else (if n ≤ 1895 then (if n ≤ 1894 then 5 else 3) else 3)) else (if n ≤ 1899 then (if n ≤ 1898 then (if n ≤ 1897 then 7 else 3) else 3) else (if n ≤ 1901 then (if n ≤ 1900 then 5 else 3) else 3))))) else (if n ≤ 1927 then (if n ≤ 1915 then (if n ≤ 1909 then (if n ≤ 1906 then (if n ≤ 1904 then (if n ≤ 1903 then 5 else 3) else (if n ≤ 1905 then 3 else 5)) else (if n ≤ 1908 then (if n ≤ 1907 then 3 else 3) else 5)) else (if n ≤ 1912 then (if n ≤ 1911 then (if n ≤ 1910 then 3 else 3) else 11) else (if n ≤ 1914 then (if n ≤ 1913 then 3 else 3) else 5))) else (if n ≤ 1921 then (if n ≤ 1918 then (if n ≤ 1917 then (if n ≤ 1916 then 3 else 3) else 5) else (if n ≤ 1920 then (if n ≤ 1919 then 3 else 3) else 5)) else (if n ≤ 1924 then (if n ≤ 1923 then (if n ≤ 1922 then 3 else 3) else 5) else (if n ≤ 1926 then (if n ≤ 1925 then 3 else 3) else 11)))) else (if n ≤ 1940 then (if n ≤ 1934 then (if n ≤ 1931 then (if n ≤ 1929 then (if n ≤ 1928 then 3 else 3) else (if n ≤ 1930 then 5 else 3)) else (if n ≤ 1933 then (if n ≤ 1932 then 3 else 5) else 3)) else (if n ≤ 1937 then (if n ≤ 1936 then (if n ≤ 1935 then 3 else 5) else 3) else (if n ≤ 1939 then (if n ≤ 1938 then 3 else 5) else 3))) else (if n ≤ 1946 then (if n ≤ 1943 then (if n ≤ 1942 then (if n ≤ 1941 then 3 else 11) else 3) else (if n ≤ 1945 then (if n ≤ 1944 then 3 else 5) else 3)) else (if n ≤ 1949 then (if n ≤ 1948 then (if n ≤ 1947 then 3 else 5) else 3) else (if n ≤ 1951 then (if n ≤ 1950 then 3 else 5) else 3))))))

def certificate_d_block_19 (n : ℕ) : ℕ :=
  (if n ≤ 2002 then (if n ≤ 1977 then (if n ≤ 1965 then (if n ≤ 1959 then (if n ≤ 1956 then (if n ≤ 1954 then (if n ≤ 1953 then 3 else 5) else (if n ≤ 1955 then 3 else 3)) else (if n ≤ 1958 then (if n ≤ 1957 then 7 else 3) else 3)) else (if n ≤ 1962 then (if n ≤ 1961 then (if n ≤ 1960 then 5 else 3) else 3) else (if n ≤ 1964 then (if n ≤ 1963 then 5 else 3) else 3))) else (if n ≤ 1971 then (if n ≤ 1968 then (if n ≤ 1967 then (if n ≤ 1966 then 5 else 3) else 3) else (if n ≤ 1970 then (if n ≤ 1969 then 5 else 3) else 3)) else (if n ≤ 1974 then (if n ≤ 1973 then (if n ≤ 1972 then 7 else 3) else 3) else (if n ≤ 1976 then (if n ≤ 1975 then 5 else 3) else 3)))) else (if n ≤ 1990 then (if n ≤ 1984 then (if n ≤ 1981 then (if n ≤ 1979 then (if n ≤ 1978 then 5 else 3) else (if n ≤ 1980 then 3 else 5)) else (if n ≤ 1983 then (if n ≤ 1982 then 3 else 3) else 5)) else (if n ≤ 1987 then (if n ≤ 1986 then (if n ≤ 1985 then 3 else 3) else 11) else (if n ≤ 1989 then (if n ≤ 1988 then 3 else 3) else 5))) else (if n ≤ 1996 then (if n ≤ 1993 then (if n ≤ 1992 then (if n ≤ 1991 then 3 else 3) else 5) else (if n ≤ 1995 then (if n ≤ 1994 then 3 else 3) else 5)) else (if n ≤ 1999 then (if n ≤ 1998 then (if n ≤ 1997 then 3 else 3) else 5) else (if n ≤ 2001 then (if n ≤ 2000 then 3 else 3) else 7))))) else (if n ≤ 2027 then (if n ≤ 2015 then (if n ≤ 2009 then (if n ≤ 2006 then (if n ≤ 2004 then (if n ≤ 2003 then 3 else 3) else (if n ≤ 2005 then 5 else 3)) else (if n ≤ 2008 then (if n ≤ 2007 then 3 else 5) else 3)) else (if n ≤ 2012 then (if n ≤ 2011 then (if n ≤ 2010 then 3 else 5) else 3) else (if n ≤ 2014 then (if n ≤ 2013 then 3 else 5) else 3))) else (if n ≤ 2021 then (if n ≤ 2018 then (if n ≤ 2017 then (if n ≤ 2016 then 3 else 11) else 3) else (if n ≤ 2020 then (if n ≤ 2019 then 3 else 5) else 3)) else (if n ≤ 2024 then (if n ≤ 2023 then (if n ≤ 2022 then 3 else 5) else 3) else (if n ≤ 2026 then (if n ≤ 2025 then 3 else 5) else 3)))) else (if n ≤ 2040 then (if n ≤ 2034 then (if n ≤ 2031 then (if n ≤ 2029 then (if n ≤ 2028 then 3 else 5) else (if n ≤ 2030 then 3 else 3)) else (if n ≤ 2033 then (if n ≤ 2032 then 11 else 3) else 3)) else (if n ≤ 2037 then (if n ≤ 2036 then (if n ≤ 2035 then 5 else 3) else 3) else (if n ≤ 2039 then (if n ≤ 2038 then 5 else 3) else 3))) else (if n ≤ 2046 then (if n ≤ 2043 then (if n ≤ 2042 then (if n ≤ 2041 then 5 else 3) else 3) else (if n ≤ 2045 then (if n ≤ 2044 then 5 else 3) else 3)) else (if n ≤ 2049 then (if n ≤ 2048 then (if n ≤ 2047 then 11 else 3) else 3) else (if n ≤ 2051 then (if n ≤ 2050 then 5 else 3) else 3))))))

def certificate_d_block_20 (n : ℕ) : ℕ :=
  (if n ≤ 2053 then 5 else 3)

def certificate_k (n : ℕ) : ℕ :=
  (if n ≤ 1152 then (if n ≤ 652 then (if n ≤ 352 then (if n ≤ 252 then (if n ≤ 152 then certificate_k_block_0 n else certificate_k_block_1 n) else certificate_k_block_2 n) else (if n ≤ 552 then (if n ≤ 452 then certificate_k_block_3 n else certificate_k_block_4 n) else certificate_k_block_5 n)) else (if n ≤ 952 then (if n ≤ 852 then (if n ≤ 752 then certificate_k_block_6 n else certificate_k_block_7 n) else certificate_k_block_8 n) else (if n ≤ 1052 then certificate_k_block_9 n else certificate_k_block_10 n))) else (if n ≤ 1652 then (if n ≤ 1452 then (if n ≤ 1352 then (if n ≤ 1252 then certificate_k_block_11 n else certificate_k_block_12 n) else certificate_k_block_13 n) else (if n ≤ 1552 then certificate_k_block_14 n else certificate_k_block_15 n)) else (if n ≤ 1952 then (if n ≤ 1852 then (if n ≤ 1752 then certificate_k_block_16 n else certificate_k_block_17 n) else certificate_k_block_18 n) else (if n ≤ 2052 then certificate_k_block_19 n else certificate_k_block_20 n))))

def certificate_d (n : ℕ) : ℕ :=
  (if n ≤ 1152 then (if n ≤ 652 then (if n ≤ 352 then (if n ≤ 252 then (if n ≤ 152 then certificate_d_block_0 n else certificate_d_block_1 n) else certificate_d_block_2 n) else (if n ≤ 552 then (if n ≤ 452 then certificate_d_block_3 n else certificate_d_block_4 n) else certificate_d_block_5 n)) else (if n ≤ 952 then (if n ≤ 852 then (if n ≤ 752 then certificate_d_block_6 n else certificate_d_block_7 n) else certificate_d_block_8 n) else (if n ≤ 1052 then certificate_d_block_9 n else certificate_d_block_10 n))) else (if n ≤ 1652 then (if n ≤ 1452 then (if n ≤ 1352 then (if n ≤ 1252 then certificate_d_block_11 n else certificate_d_block_12 n) else certificate_d_block_13 n) else (if n ≤ 1552 then certificate_d_block_14 n else certificate_d_block_15 n)) else (if n ≤ 1952 then (if n ≤ 1852 then (if n ≤ 1752 then certificate_d_block_16 n else certificate_d_block_17 n) else certificate_d_block_18 n) else (if n ≤ 2052 then certificate_d_block_19 n else certificate_d_block_20 n))))

lemma cert_valid_0 : ∀ n ∈ Finset.Ico 53 253,
    let k := certificate_k n;
    let d := certificate_d n;
    1 ≤ k ∧ k ≤ log 2 (2 * n + 1) ∧ 1 < d ∧ d < 2 * n + 1 - 2 ^ k ∧ d ∣ 2 * n + 1 - 2 ^ k := by
  decide

lemma cert_valid_1 : ∀ n ∈ Finset.Ico 253 453,
    let k := certificate_k n;
    let d := certificate_d n;
    1 ≤ k ∧ k ≤ log 2 (2 * n + 1) ∧ 1 < d ∧ d < 2 * n + 1 - 2 ^ k ∧ d ∣ 2 * n + 1 - 2 ^ k := by
  decide

lemma cert_valid_2 : ∀ n ∈ Finset.Ico 453 653,
    let k := certificate_k n;
    let d := certificate_d n;
    1 ≤ k ∧ k ≤ log 2 (2 * n + 1) ∧ 1 < d ∧ d < 2 * n + 1 - 2 ^ k ∧ d ∣ 2 * n + 1 - 2 ^ k := by
  decide

lemma cert_valid_3 : ∀ n ∈ Finset.Ico 653 853,
    let k := certificate_k n;
    let d := certificate_d n;
    1 ≤ k ∧ k ≤ log 2 (2 * n + 1) ∧ 1 < d ∧ d < 2 * n + 1 - 2 ^ k ∧ d ∣ 2 * n + 1 - 2 ^ k := by
  decide

lemma cert_valid_4 : ∀ n ∈ Finset.Ico 853 1053,
    let k := certificate_k n;
    let d := certificate_d n;
    1 ≤ k ∧ k ≤ log 2 (2 * n + 1) ∧ 1 < d ∧ d < 2 * n + 1 - 2 ^ k ∧ d ∣ 2 * n + 1 - 2 ^ k := by
  decide

lemma cert_valid_5 : ∀ n ∈ Finset.Ico 1053 1253,
    let k := certificate_k n;
    let d := certificate_d n;
    1 ≤ k ∧ k ≤ log 2 (2 * n + 1) ∧ 1 < d ∧ d < 2 * n + 1 - 2 ^ k ∧ d ∣ 2 * n + 1 - 2 ^ k := by
  decide

lemma cert_valid_6 : ∀ n ∈ Finset.Ico 1253 1453,
    let k := certificate_k n;
    let d := certificate_d n;
    1 ≤ k ∧ k ≤ log 2 (2 * n + 1) ∧ 1 < d ∧ d < 2 * n + 1 - 2 ^ k ∧ d ∣ 2 * n + 1 - 2 ^ k := by
  decide

lemma cert_valid_7 : ∀ n ∈ Finset.Ico 1453 1653,
    let k := certificate_k n;
    let d := certificate_d n;
    1 ≤ k ∧ k ≤ log 2 (2 * n + 1) ∧ 1 < d ∧ d < 2 * n + 1 - 2 ^ k ∧ d ∣ 2 * n + 1 - 2 ^ k := by
  decide

lemma cert_valid_8 : ∀ n ∈ Finset.Ico 1653 1853,
    let k := certificate_k n;
    let d := certificate_d n;
    1 ≤ k ∧ k ≤ log 2 (2 * n + 1) ∧ 1 < d ∧ d < 2 * n + 1 - 2 ^ k ∧ d ∣ 2 * n + 1 - 2 ^ k := by
  decide

lemma cert_valid_9 : ∀ n ∈ Finset.Ico 1853 2053,
    let k := certificate_k n;
    let d := certificate_d n;
    1 ≤ k ∧ k ≤ log 2 (2 * n + 1) ∧ 1 < d ∧ d < 2 * n + 1 - 2 ^ k ∧ d ∣ 2 * n + 1 - 2 ^ k := by
  decide

lemma cert_valid_10 : ∀ n ∈ Finset.Ico 2053 2055,
    let k := certificate_k n;
    let d := certificate_d n;
    1 ≤ k ∧ k ≤ log 2 (2 * n + 1) ∧ 1 < d ∧ d < 2 * n + 1 - 2 ^ k ∧ d ∣ 2 * n + 1 - 2 ^ k := by
  decide

lemma cert_valid : ∀ n ∈ Finset.Ico 53 2055,
    let k := certificate_k n;
    let d := certificate_d n;
    1 ≤ k ∧ k ≤ log 2 (2 * n + 1) ∧ 1 < d ∧ d < 2 * n + 1 - 2 ^ k ∧ d ∣ 2 * n + 1 - 2 ^ k := by
  intro n hn
  rw [Finset.mem_Ico] at hn
  rcases lt_or_ge n 253 with h_lt_0 | h_ge_0
  · exact cert_valid_0 n (by rw [Finset.mem_Ico]; omega)
  rcases lt_or_ge n 453 with h_lt_1 | h_ge_1
  · exact cert_valid_1 n (by rw [Finset.mem_Ico]; omega)
  rcases lt_or_ge n 653 with h_lt_2 | h_ge_2
  · exact cert_valid_2 n (by rw [Finset.mem_Ico]; omega)
  rcases lt_or_ge n 853 with h_lt_3 | h_ge_3
  · exact cert_valid_3 n (by rw [Finset.mem_Ico]; omega)
  rcases lt_or_ge n 1053 with h_lt_4 | h_ge_4
  · exact cert_valid_4 n (by rw [Finset.mem_Ico]; omega)
  rcases lt_or_ge n 1253 with h_lt_5 | h_ge_5
  · exact cert_valid_5 n (by rw [Finset.mem_Ico]; omega)
  rcases lt_or_ge n 1453 with h_lt_6 | h_ge_6
  · exact cert_valid_6 n (by rw [Finset.mem_Ico]; omega)
  rcases lt_or_ge n 1653 with h_lt_7 | h_ge_7
  · exact cert_valid_7 n (by rw [Finset.mem_Ico]; omega)
  rcases lt_or_ge n 1853 with h_lt_8 | h_ge_8
  · exact cert_valid_8 n (by rw [Finset.mem_Ico]; omega)
  rcases lt_or_ge n 2053 with h_lt_9 | h_ge_9
  · exact cert_valid_9 n (by rw [Finset.mem_Ico]; omega)
  · exact cert_valid_10 n (by rw [Finset.mem_Ico]; omega)

lemma leaf_covered_template_3 (n : ℕ) (k : ℕ) (hn : 2 * n + 1 ≥ 4111) (hk1 : 1 ≤ k) (hk2 : 2^k ≤ 2 * n + 1) (h_mod : (2 * n + 1) % 3 = 2^k % 3) (h_gt : 3 < 2 * n + 1 - 2^k) (h1 : 1 < 2 * n + 1 - 2^k) : A282459 n > 0 := by
  have h_dvd : 3 ∣ 2 * n + 1 - 2^k := dvd_of_mod_eq (2 * n + 1) k 3 h_mod hk2
  have h_in : k ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := k_in_Icc n k hk1 hk2
  have h_comp : 1 < 2 * n + 1 - 2^k ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ k) :=
    composite_of_dvd (2 * n + 1) k 3 hp3 h_dvd h_gt h1
  exact A282459_pos_of_exists n k h_in h_comp

lemma leaf_covered_template_5 (n : ℕ) (k : ℕ) (hn : 2 * n + 1 ≥ 4111) (hk1 : 1 ≤ k) (hk2 : 2^k ≤ 2 * n + 1) (h_mod : (2 * n + 1) % 5 = 2^k % 5) (h_gt : 5 < 2 * n + 1 - 2^k) (h1 : 1 < 2 * n + 1 - 2^k) : A282459 n > 0 := by
  have h_dvd : 5 ∣ 2 * n + 1 - 2^k := dvd_of_mod_eq (2 * n + 1) k 5 h_mod hk2
  have h_in : k ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := k_in_Icc n k hk1 hk2
  have h_comp : 1 < 2 * n + 1 - 2^k ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ k) :=
    composite_of_dvd (2 * n + 1) k 5 hp5 h_dvd h_gt h1
  exact A282459_pos_of_exists n k h_in h_comp

lemma leaf_covered_template_11 (n : ℕ) (k : ℕ) (hn : 2 * n + 1 ≥ 4111) (hk1 : 1 ≤ k) (hk2 : 2^k ≤ 2 * n + 1) (h_mod : (2 * n + 1) % 11 = 2^k % 11) (h_gt : 11 < 2 * n + 1 - 2^k) (h1 : 1 < 2 * n + 1 - 2^k) : A282459 n > 0 := by
  have h_dvd : 11 ∣ 2 * n + 1 - 2^k := dvd_of_mod_eq (2 * n + 1) k 11 h_mod hk2
  have h_in : k ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := k_in_Icc n k hk1 hk2
  have h_comp : 1 < 2 * n + 1 - 2^k ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ k) :=
    composite_of_dvd (2 * n + 1) k 11 hp11 h_dvd h_gt h1
  exact A282459_pos_of_exists n k h_in h_comp

lemma leaf_covered_template_13 (n : ℕ) (k : ℕ) (hn : 2 * n + 1 ≥ 4111) (hk1 : 1 ≤ k) (hk2 : 2^k ≤ 2 * n + 1) (h_mod : (2 * n + 1) % 13 = 2^k % 13) (h_gt : 13 < 2 * n + 1 - 2^k) (h1 : 1 < 2 * n + 1 - 2^k) : A282459 n > 0 := by
  have h_dvd : 13 ∣ 2 * n + 1 - 2^k := dvd_of_mod_eq (2 * n + 1) k 13 h_mod hk2
  have h_in : k ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := k_in_Icc n k hk1 hk2
  have h_comp : 1 < 2 * n + 1 - 2^k ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ k) :=
    composite_of_dvd (2 * n + 1) k 13 hp13 h_dvd h_gt h1
  exact A282459_pos_of_exists n k h_in h_comp

lemma leaf_covered_template_17 (n : ℕ) (k : ℕ) (hn : 2 * n + 1 ≥ 4111) (hk1 : 1 ≤ k) (hk2 : 2^k ≤ 2 * n + 1) (h_mod : (2 * n + 1) % 17 = 2^k % 17) (h_gt : 17 < 2 * n + 1 - 2^k) (h1 : 1 < 2 * n + 1 - 2^k) : A282459 n > 0 := by
  have h_dvd : 17 ∣ 2 * n + 1 - 2^k := dvd_of_mod_eq (2 * n + 1) k 17 h_mod hk2
  have h_in : k ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := k_in_Icc n k hk1 hk2
  have h_comp : 1 < 2 * n + 1 - 2^k ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ k) :=
    composite_of_dvd (2 * n + 1) k 17 hp17 h_dvd h_gt h1
  exact A282459_pos_of_exists n k h_in h_comp

lemma leaf_covered_template_19 (n : ℕ) (k : ℕ) (hn : 2 * n + 1 ≥ 4111) (hk1 : 1 ≤ k) (hk2 : 2^k ≤ 2 * n + 1) (h_mod : (2 * n + 1) % 19 = 2^k % 19) (h_gt : 19 < 2 * n + 1 - 2^k) (h1 : 1 < 2 * n + 1 - 2^k) : A282459 n > 0 := by
  have h_dvd : 19 ∣ 2 * n + 1 - 2^k := dvd_of_mod_eq (2 * n + 1) k 19 h_mod hk2
  have h_in : k ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := k_in_Icc n k hk1 hk2
  have h_comp : 1 < 2 * n + 1 - 2^k ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ k) :=
    composite_of_dvd (2 * n + 1) k 19 hp19 h_dvd h_gt h1
  exact A282459_pos_of_exists n k h_in h_comp

lemma leaf_covered_template_23 (n : ℕ) (k : ℕ) (hn : 2 * n + 1 ≥ 4111) (hk1 : 1 ≤ k) (hk2 : 2^k ≤ 2 * n + 1) (h_mod : (2 * n + 1) % 23 = 2^k % 23) (h_gt : 23 < 2 * n + 1 - 2^k) (h1 : 1 < 2 * n + 1 - 2^k) : A282459 n > 0 := by
  have h_dvd : 23 ∣ 2 * n + 1 - 2^k := dvd_of_mod_eq (2 * n + 1) k 23 h_mod hk2
  have h_in : k ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := k_in_Icc n k hk1 hk2
  have h_comp : 1 < 2 * n + 1 - 2^k ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ k) :=
    composite_of_dvd (2 * n + 1) k 23 hp23 h_dvd h_gt h1
  exact A282459_pos_of_exists n k h_in h_comp

lemma leaf_covered_template_29 (n : ℕ) (k : ℕ) (hn : 2 * n + 1 ≥ 4111) (hk1 : 1 ≤ k) (hk2 : 2^k ≤ 2 * n + 1) (h_mod : (2 * n + 1) % 29 = 2^k % 29) (h_gt : 29 < 2 * n + 1 - 2^k) (h1 : 1 < 2 * n + 1 - 2^k) : A282459 n > 0 := by
  have h_dvd : 29 ∣ 2 * n + 1 - 2^k := dvd_of_mod_eq (2 * n + 1) k 29 h_mod hk2
  have h_in : k ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := k_in_Icc n k hk1 hk2
  have h_comp : 1 < 2 * n + 1 - 2^k ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ k) :=
    composite_of_dvd (2 * n + 1) k 29 hp29 h_dvd h_gt h1
  exact A282459_pos_of_exists n k h_in h_comp

lemma leaf_single_0 (n : ℕ) (h_eq : n = 231060472) : A282459 n > 0 := by
  subst h_eq
  have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 231060472 + 1)) := by decide
  have hdvd_231060472 : 31 ∣ 2 * 231060472 + 1 - 2 ^ 3 := by decide
  have h_comp : 1 < 2 * 231060472 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 231060472 + 1 - 2 ^ 3) :=
    composite_of_dvd (2 * 231060472 + 1) 3 31 hp31 hdvd_231060472 (by decide) (by decide)
  exact A282459_pos_of_exists 231060472 3 hk h_comp

lemma leaf_single_1 (n : ℕ) (h_eq : n = 110507182) : A282459 n > 0 := by
  subst h_eq
  have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 110507182 + 1)) := by decide
  have hdvd_110507182 : 37 ∣ 2 * 110507182 + 1 - 2 ^ 3 := by decide
  have h_comp : 1 < 2 * 110507182 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 110507182 + 1 - 2 ^ 3) :=
    composite_of_dvd (2 * 110507182 + 1) 3 37 hp37 hdvd_110507182 (by decide) (by decide)
  exact A282459_pos_of_exists 110507182 3 hk h_comp

lemma leaf_single_2 (n : ℕ) (h_eq : n = 431982622) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 431982622 + 1)) := by decide
  have hdvd_431982622 : 41 ∣ 2 * 431982622 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 431982622 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 431982622 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 431982622 + 1) 1 41 hp41 hdvd_431982622 (by decide) (by decide)
  exact A282459_pos_of_exists 431982622 1 hk h_comp

lemma leaf_single_3 (n : ℕ) (h_eq : n = 452074837) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 452074837 + 1)) := by decide
  have hdvd_452074837 : 7 ∣ 2 * 452074837 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 452074837 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 452074837 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 452074837 + 1) 1 7 hp7 hdvd_452074837 (by decide) (by decide)
  exact A282459_pos_of_exists 452074837 1 hk h_comp

lemma leaf_single_4 (n : ℕ) (h_eq : n = 150691612) : A282459 n > 0 := by
  subst h_eq
  have hk : 4 ∈ Finset.Icc 1 (log 2 (2 * 150691612 + 1)) := by decide
  have hdvd_150691612 : 31 ∣ 2 * 150691612 + 1 - 2 ^ 4 := by decide
  have h_comp : 1 < 2 * 150691612 + 1 - 2 ^ 4 ∧ ¬ Nat.Prime (2 * 150691612 + 1 - 2 ^ 4) :=
    composite_of_dvd (2 * 150691612 + 1) 4 31 hp31 hdvd_150691612 (by decide) (by decide)
  exact A282459_pos_of_exists 150691612 4 hk h_comp

lemma leaf_single_5 (n : ℕ) (h_eq : n = 170783827) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 170783827 + 1)) := by decide
  have hdvd_170783827 : 7 ∣ 2 * 170783827 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 170783827 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 170783827 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 170783827 + 1) 1 7 hp7 hdvd_170783827 (by decide) (by decide)
  exact A282459_pos_of_exists 170783827 1 hk h_comp

lemma leaf_single_6 (n : ℕ) (h_eq : n = 331521547) : A282459 n > 0 := by
  subst h_eq
  have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 331521547 + 1)) := by decide
  have hdvd_331521547 : 7 ∣ 2 * 331521547 + 1 - 2 ^ 3 := by decide
  have h_comp : 1 < 2 * 331521547 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 331521547 + 1 - 2 ^ 3) :=
    composite_of_dvd (2 * 331521547 + 1) 3 7 hp7 hdvd_331521547 (by decide) (by decide)
  exact A282459_pos_of_exists 331521547 3 hk h_comp

lemma leaf_single_7 (n : ℕ) (h_eq : n = 190876042) : A282459 n > 0 := by
  subst h_eq
  have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 190876042 + 1)) := by decide
  have hdvd_190876042 : 7 ∣ 2 * 190876042 + 1 - 2 ^ 3 := by decide
  have h_comp : 1 < 2 * 190876042 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 190876042 + 1 - 2 ^ 3) :=
    composite_of_dvd (2 * 190876042 + 1) 3 7 hp7 hdvd_190876042 (by decide) (by decide)
  exact A282459_pos_of_exists 190876042 3 hk h_comp

lemma leaf_single_8 (n : ℕ) (h_eq : n = 50230537) : A282459 n > 0 := by
  subst h_eq
  have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 50230537 + 1)) := by decide
  have hdvd_50230537 : 7 ∣ 2 * 50230537 + 1 - 2 ^ 3 := by decide
  have h_comp : 1 < 2 * 50230537 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 50230537 + 1 - 2 ^ 3) :=
    composite_of_dvd (2 * 50230537 + 1) 3 7 hp7 hdvd_50230537 (by decide) (by decide)
  exact A282459_pos_of_exists 50230537 3 hk h_comp

lemma leaf_single_9 (n : ℕ) (h_eq : n = 210968257) : A282459 n > 0 := by
  subst h_eq
  have hk : 19 ∈ Finset.Icc 1 (log 2 (2 * 210968257 + 1)) := by decide
  have hdvd_210968257 : 41 ∣ 2 * 210968257 + 1 - 2 ^ 19 := by decide
  have h_comp : 1 < 2 * 210968257 + 1 - 2 ^ 19 ∧ ¬ Nat.Prime (2 * 210968257 + 1 - 2 ^ 19) :=
    composite_of_dvd (2 * 210968257 + 1) 19 41 hp41 hdvd_210968257 (by decide) (by decide)
  exact A282459_pos_of_exists 210968257 19 hk h_comp

lemma leaf_single_10 (n : ℕ) (h_eq : n = 371705977) : A282459 n > 0 := by
  subst h_eq
  have hk : 12 ∈ Finset.Icc 1 (log 2 (2 * 371705977 + 1)) := by decide
  have hdvd_371705977 : 41 ∣ 2 * 371705977 + 1 - 2 ^ 12 := by decide
  have h_comp : 1 < 2 * 371705977 + 1 - 2 ^ 12 ∧ ¬ Nat.Prime (2 * 371705977 + 1 - 2 ^ 12) :=
    composite_of_dvd (2 * 371705977 + 1) 12 41 hp41 hdvd_371705977 (by decide) (by decide)
  exact A282459_pos_of_exists 371705977 12 hk h_comp

lemma leaf_single_11 (n : ℕ) (h_eq : n = 70322752) : A282459 n > 0 := by
  subst h_eq
  have hk : 5 ∈ Finset.Icc 1 (log 2 (2 * 70322752 + 1)) := by decide
  have hdvd_70322752 : 37 ∣ 2 * 70322752 + 1 - 2 ^ 5 := by decide
  have h_comp : 1 < 2 * 70322752 + 1 - 2 ^ 5 ∧ ¬ Nat.Prime (2 * 70322752 + 1 - 2 ^ 5) :=
    composite_of_dvd (2 * 70322752 + 1) 5 37 hp37 hdvd_70322752 (by decide) (by decide)
  exact A282459_pos_of_exists 70322752 5 hk h_comp

lemma leaf_single_12 (n : ℕ) (h_eq : n = 203876887) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 203876887 + 1)) := by decide
  have hdvd_203876887 : 7 ∣ 2 * 203876887 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 203876887 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 203876887 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 203876887 + 1) 1 7 hp7 hdvd_203876887 (by decide) (by decide)
  exact A282459_pos_of_exists 203876887 1 hk h_comp

lemma leaf_single_13 (n : ℕ) (h_eq : n = 83323597) : A282459 n > 0 := by
  subst h_eq
  have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 83323597 + 1)) := by decide
  have hdvd_83323597 : 7 ∣ 2 * 83323597 + 1 - 2 ^ 3 := by decide
  have h_comp : 1 < 2 * 83323597 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 83323597 + 1 - 2 ^ 3) :=
    composite_of_dvd (2 * 83323597 + 1) 3 7 hp7 hdvd_83323597 (by decide) (by decide)
  exact A282459_pos_of_exists 83323597 3 hk h_comp

lemma leaf_single_14 (n : ℕ) (h_eq : n = 404799037) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 404799037 + 1)) := by decide
  have hdvd_404799037 : 37 ∣ 2 * 404799037 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 404799037 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 404799037 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 404799037 + 1) 1 37 hp37 hdvd_404799037 (by decide) (by decide)
  exact A282459_pos_of_exists 404799037 1 hk h_comp

lemma leaf_single_15 (n : ℕ) (h_eq : n = 424891252) : A282459 n > 0 := by
  subst h_eq
  have hk : 6 ∈ Finset.Icc 1 (log 2 (2 * 424891252 + 1)) := by decide
  have hdvd_424891252 : 37 ∣ 2 * 424891252 + 1 - 2 ^ 6 := by decide
  have h_comp : 1 < 2 * 424891252 + 1 - 2 ^ 6 ∧ ¬ Nat.Prime (2 * 424891252 + 1 - 2 ^ 6) :=
    composite_of_dvd (2 * 424891252 + 1) 6 37 hp37 hdvd_424891252 (by decide) (by decide)
  exact A282459_pos_of_exists 424891252 6 hk h_comp

lemma leaf_single_16 (n : ℕ) (h_eq : n = 123508027) : A282459 n > 0 := by
  subst h_eq
  have hk : 12 ∈ Finset.Icc 1 (log 2 (2 * 123508027 + 1)) := by decide
  have hdvd_123508027 : 53 ∣ 2 * 123508027 + 1 - 2 ^ 12 := by decide
  have h_comp : 1 < 2 * 123508027 + 1 - 2 ^ 12 ∧ ¬ Nat.Prime (2 * 123508027 + 1 - 2 ^ 12) :=
    composite_of_dvd (2 * 123508027 + 1) 12 53 hp53 hdvd_123508027 (by decide) (by decide)
  exact A282459_pos_of_exists 123508027 12 hk h_comp

lemma leaf_single_17 (n : ℕ) (h_eq : n = 143600242) : A282459 n > 0 := by
  subst h_eq
  have hk : 24 ∈ Finset.Icc 1 (log 2 (2 * 143600242 + 1)) := by decide
  have hdvd_143600242 : 37 ∣ 2 * 143600242 + 1 - 2 ^ 24 := by decide
  have h_comp : 1 < 2 * 143600242 + 1 - 2 ^ 24 ∧ ¬ Nat.Prime (2 * 143600242 + 1 - 2 ^ 24) :=
    composite_of_dvd (2 * 143600242 + 1) 24 37 hp37 hdvd_143600242 (by decide) (by decide)
  exact A282459_pos_of_exists 143600242 24 hk h_comp

lemma leaf_single_18 (n : ℕ) (h_eq : n = 304337962) : A282459 n > 0 := by
  subst h_eq
  have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 304337962 + 1)) := by decide
  have hdvd_304337962 : 7 ∣ 2 * 304337962 + 1 - 2 ^ 2 := by decide
  have h_comp : 1 < 2 * 304337962 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 304337962 + 1 - 2 ^ 2) :=
    composite_of_dvd (2 * 304337962 + 1) 2 7 hp7 hdvd_304337962 (by decide) (by decide)
  exact A282459_pos_of_exists 304337962 2 hk h_comp

lemma leaf_single_19 (n : ℕ) (h_eq : n = 163692457) : A282459 n > 0 := by
  subst h_eq
  have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 163692457 + 1)) := by decide
  have hdvd_163692457 : 7 ∣ 2 * 163692457 + 1 - 2 ^ 2 := by decide
  have h_comp : 1 < 2 * 163692457 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 163692457 + 1 - 2 ^ 2) :=
    composite_of_dvd (2 * 163692457 + 1) 2 7 hp7 hdvd_163692457 (by decide) (by decide)
  exact A282459_pos_of_exists 163692457 2 hk h_comp

lemma leaf_single_20 (n : ℕ) (h_eq : n = 23046952) : A282459 n > 0 := by
  subst h_eq
  have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 23046952 + 1)) := by decide
  have hdvd_23046952 : 7 ∣ 2 * 23046952 + 1 - 2 ^ 2 := by decide
  have h_comp : 1 < 2 * 23046952 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 23046952 + 1 - 2 ^ 2) :=
    composite_of_dvd (2 * 23046952 + 1) 2 7 hp7 hdvd_23046952 (by decide) (by decide)
  exact A282459_pos_of_exists 23046952 2 hk h_comp

lemma leaf_single_21 (n : ℕ) (h_eq : n = 183784672) : A282459 n > 0 := by
  subst h_eq
  have hk : 15 ∈ Finset.Icc 1 (log 2 (2 * 183784672 + 1)) := by decide
  have hdvd_183784672 : 37 ∣ 2 * 183784672 + 1 - 2 ^ 15 := by decide
  have h_comp : 1 < 2 * 183784672 + 1 - 2 ^ 15 ∧ ¬ Nat.Prime (2 * 183784672 + 1 - 2 ^ 15) :=
    composite_of_dvd (2 * 183784672 + 1) 15 37 hp37 hdvd_183784672 (by decide) (by decide)
  exact A282459_pos_of_exists 183784672 15 hk h_comp

lemma leaf_single_22 (n : ℕ) (h_eq : n = 344522392) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 344522392 + 1)) := by decide
  have hdvd_344522392 : 7 ∣ 2 * 344522392 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 344522392 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 344522392 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 344522392 + 1) 1 7 hp7 hdvd_344522392 (by decide) (by decide)
  exact A282459_pos_of_exists 344522392 1 hk h_comp

lemma leaf_single_23 (n : ℕ) (h_eq : n = 43139167) : A282459 n > 0 := by
  subst h_eq
  have hk : 20 ∈ Finset.Icc 1 (log 2 (2 * 43139167 + 1)) := by decide
  have hdvd_43139167 : 37 ∣ 2 * 43139167 + 1 - 2 ^ 20 := by decide
  have h_comp : 1 < 2 * 43139167 + 1 - 2 ^ 20 ∧ ¬ Nat.Prime (2 * 43139167 + 1 - 2 ^ 20) :=
    composite_of_dvd (2 * 43139167 + 1) 20 37 hp37 hdvd_43139167 (by decide) (by decide)
  exact A282459_pos_of_exists 43139167 20 hk h_comp

lemma leaf_single_24 (n : ℕ) (h_eq : n = 339794812) : A282459 n > 0 := by
  subst h_eq
  have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 339794812 + 1)) := by decide
  have hdvd_339794812 : 7 ∣ 2 * 339794812 + 1 - 2 ^ 3 := by decide
  have h_comp : 1 < 2 * 339794812 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 339794812 + 1 - 2 ^ 3) :=
    composite_of_dvd (2 * 339794812 + 1) 3 7 hp7 hdvd_339794812 (by decide) (by decide)
  exact A282459_pos_of_exists 339794812 3 hk h_comp

lemma leaf_single_25 (n : ℕ) (h_eq : n = 219241522) : A282459 n > 0 := by
  subst h_eq
  have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 219241522 + 1)) := by decide
  have hdvd_219241522 : 37 ∣ 2 * 219241522 + 1 - 2 ^ 2 := by decide
  have h_comp : 1 < 2 * 219241522 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 219241522 + 1 - 2 ^ 2) :=
    composite_of_dvd (2 * 219241522 + 1) 2 37 hp37 hdvd_219241522 (by decide) (by decide)
  exact A282459_pos_of_exists 219241522 2 hk h_comp

lemma leaf_single_26 (n : ℕ) (h_eq : n = 78596017) : A282459 n > 0 := by
  subst h_eq
  have hk : 16 ∈ Finset.Icc 1 (log 2 (2 * 78596017 + 1)) := by decide
  have hdvd_78596017 : 47 ∣ 2 * 78596017 + 1 - 2 ^ 16 := by decide
  have h_comp : 1 < 2 * 78596017 + 1 - 2 ^ 16 ∧ ¬ Nat.Prime (2 * 78596017 + 1 - 2 ^ 16) :=
    composite_of_dvd (2 * 78596017 + 1) 16 47 hp47 hdvd_78596017 (by decide) (by decide)
  exact A282459_pos_of_exists 78596017 16 hk h_comp

lemma leaf_single_27 (n : ℕ) (h_eq : n = 98688232) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 98688232 + 1)) := by decide
  have hdvd_98688232 : 37 ∣ 2 * 98688232 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 98688232 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 98688232 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 98688232 + 1) 1 37 hp37 hdvd_98688232 (by decide) (by decide)
  exact A282459_pos_of_exists 98688232 1 hk h_comp

lemma leaf_single_28 (n : ℕ) (h_eq : n = 259425952) : A282459 n > 0 := by
  subst h_eq
  have hk : 7 ∈ Finset.Icc 1 (log 2 (2 * 259425952 + 1)) := by decide
  have hdvd_259425952 : 37 ∣ 2 * 259425952 + 1 - 2 ^ 7 := by decide
  have h_comp : 1 < 2 * 259425952 + 1 - 2 ^ 7 ∧ ¬ Nat.Prime (2 * 259425952 + 1 - 2 ^ 7) :=
    composite_of_dvd (2 * 259425952 + 1) 7 37 hp37 hdvd_259425952 (by decide) (by decide)
  exact A282459_pos_of_exists 259425952 7 hk h_comp

lemma leaf_single_29 (n : ℕ) (h_eq : n = 279518167) : A282459 n > 0 := by
  subst h_eq
  have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 279518167 + 1)) := by decide
  have hdvd_279518167 : 7 ∣ 2 * 279518167 + 1 - 2 ^ 2 := by decide
  have h_comp : 1 < 2 * 279518167 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 279518167 + 1 - 2 ^ 2) :=
    composite_of_dvd (2 * 279518167 + 1) 2 7 hp7 hdvd_279518167 (by decide) (by decide)
  exact A282459_pos_of_exists 279518167 2 hk h_comp

lemma leaf_single_30 (n : ℕ) (h_eq : n = 440255887) : A282459 n > 0 := by
  subst h_eq
  have hk : 25 ∈ Finset.Icc 1 (log 2 (2 * 440255887 + 1)) := by decide
  have hdvd_440255887 : 37 ∣ 2 * 440255887 + 1 - 2 ^ 25 := by decide
  have h_comp : 1 < 2 * 440255887 + 1 - 2 ^ 25 ∧ ¬ Nat.Prime (2 * 440255887 + 1 - 2 ^ 25) :=
    composite_of_dvd (2 * 440255887 + 1) 25 37 hp37 hdvd_440255887 (by decide) (by decide)
  exact A282459_pos_of_exists 440255887 25 hk h_comp

lemma leaf_single_31 (n : ℕ) (h_eq : n = 299610382) : A282459 n > 0 := by
  subst h_eq
  have hk : 14 ∈ Finset.Icc 1 (log 2 (2 * 299610382 + 1)) := by decide
  have hdvd_299610382 : 37 ∣ 2 * 299610382 + 1 - 2 ^ 14 := by decide
  have h_comp : 1 < 2 * 299610382 + 1 - 2 ^ 14 ∧ ¬ Nat.Prime (2 * 299610382 + 1 - 2 ^ 14) :=
    composite_of_dvd (2 * 299610382 + 1) 14 37 hp37 hdvd_299610382 (by decide) (by decide)
  exact A282459_pos_of_exists 299610382 14 hk h_comp

lemma leaf_single_32 (n : ℕ) (h_eq : n = 158964877) : A282459 n > 0 := by
  subst h_eq
  have hk : 26 ∈ Finset.Icc 1 (log 2 (2 * 158964877 + 1)) := by decide
  have hdvd_158964877 : 37 ∣ 2 * 158964877 + 1 - 2 ^ 26 := by decide
  have h_comp : 1 < 2 * 158964877 + 1 - 2 ^ 26 ∧ ¬ Nat.Prime (2 * 158964877 + 1 - 2 ^ 26) :=
    composite_of_dvd (2 * 158964877 + 1) 26 37 hp37 hdvd_158964877 (by decide) (by decide)
  exact A282459_pos_of_exists 158964877 26 hk h_comp

lemma leaf_single_33 (n : ℕ) (h_eq : n = 319702597) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 319702597 + 1)) := by decide
  have hdvd_319702597 : 7 ∣ 2 * 319702597 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 319702597 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 319702597 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 319702597 + 1) 1 7 hp7 hdvd_319702597 (by decide) (by decide)
  exact A282459_pos_of_exists 319702597 1 hk h_comp

lemma leaf_single_34 (n : ℕ) (h_eq : n = 18319372) : A282459 n > 0 := by
  subst h_eq
  have hk : 11 ∈ Finset.Icc 1 (log 2 (2 * 18319372 + 1)) := by decide
  have hdvd_18319372 : 37 ∣ 2 * 18319372 + 1 - 2 ^ 11 := by decide
  have h_comp : 1 < 2 * 18319372 + 1 - 2 ^ 11 ∧ ¬ Nat.Prime (2 * 18319372 + 1 - 2 ^ 11) :=
    composite_of_dvd (2 * 18319372 + 1) 11 37 hp37 hdvd_18319372 (by decide) (by decide)
  exact A282459_pos_of_exists 18319372 11 hk h_comp

lemma leaf_single_35 (n : ℕ) (h_eq : n = 179057092) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 179057092 + 1)) := by decide
  have hdvd_179057092 : 7 ∣ 2 * 179057092 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 179057092 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 179057092 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 179057092 + 1) 1 7 hp7 hdvd_179057092 (by decide) (by decide)
  exact A282459_pos_of_exists 179057092 1 hk h_comp

lemma leaf_single_36 (n : ℕ) (h_eq : n = 176693302) : A282459 n > 0 := by
  subst h_eq
  have hk : 28 ∈ Finset.Icc 1 (log 2 (2 * 176693302 + 1)) := by decide
  have hdvd_176693302 : 37 ∣ 2 * 176693302 + 1 - 2 ^ 28 := by decide
  have h_comp : 1 < 2 * 176693302 + 1 - 2 ^ 28 ∧ ¬ Nat.Prime (2 * 176693302 + 1 - 2 ^ 28) :=
    composite_of_dvd (2 * 176693302 + 1) 28 37 hp37 hdvd_176693302 (by decide) (by decide)
  exact A282459_pos_of_exists 176693302 28 hk h_comp

lemma leaf_single_37 (n : ℕ) (h_eq : n = 56140012) : A282459 n > 0 := by
  subst h_eq
  have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 56140012 + 1)) := by decide
  have hdvd_56140012 : 7 ∣ 2 * 56140012 + 1 - 2 ^ 2 := by decide
  have h_comp : 1 < 2 * 56140012 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 56140012 + 1 - 2 ^ 2) :=
    composite_of_dvd (2 * 56140012 + 1) 2 7 hp7 hdvd_56140012 (by decide) (by decide)
  exact A282459_pos_of_exists 56140012 2 hk h_comp

lemma leaf_single_38 (n : ℕ) (h_eq : n = 377615452) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 377615452 + 1)) := by decide
  have hdvd_377615452 : 7 ∣ 2 * 377615452 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 377615452 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 377615452 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 377615452 + 1) 1 7 hp7 hdvd_377615452 (by decide) (by decide)
  exact A282459_pos_of_exists 377615452 1 hk h_comp

lemma leaf_single_39 (n : ℕ) (h_eq : n = 397707667) : A282459 n > 0 := by
  subst h_eq
  have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 397707667 + 1)) := by decide
  have hdvd_397707667 : 7 ∣ 2 * 397707667 + 1 - 2 ^ 3 := by decide
  have h_comp : 1 < 2 * 397707667 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 397707667 + 1 - 2 ^ 3) :=
    composite_of_dvd (2 * 397707667 + 1) 3 7 hp7 hdvd_397707667 (by decide) (by decide)
  exact A282459_pos_of_exists 397707667 3 hk h_comp

lemma leaf_single_40 (n : ℕ) (h_eq : n = 96324442) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 96324442 + 1)) := by decide
  have hdvd_96324442 : 7 ∣ 2 * 96324442 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 96324442 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 96324442 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 96324442 + 1) 1 7 hp7 hdvd_96324442 (by decide) (by decide)
  exact A282459_pos_of_exists 96324442 1 hk h_comp

lemma leaf_single_41 (n : ℕ) (h_eq : n = 116416657) : A282459 n > 0 := by
  subst h_eq
  have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 116416657 + 1)) := by decide
  have hdvd_116416657 : 7 ∣ 2 * 116416657 + 1 - 2 ^ 3 := by decide
  have h_comp : 1 < 2 * 116416657 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 116416657 + 1 - 2 ^ 3) :=
    composite_of_dvd (2 * 116416657 + 1) 3 7 hp7 hdvd_116416657 (by decide) (by decide)
  exact A282459_pos_of_exists 116416657 3 hk h_comp

lemma leaf_single_42 (n : ℕ) (h_eq : n = 277154377) : A282459 n > 0 := by
  subst h_eq
  have hk : 12 ∈ Finset.Icc 1 (log 2 (2 * 277154377 + 1)) := by decide
  have hdvd_277154377 : 37 ∣ 2 * 277154377 + 1 - 2 ^ 12 := by decide
  have h_comp : 1 < 2 * 277154377 + 1 - 2 ^ 12 ∧ ¬ Nat.Prime (2 * 277154377 + 1 - 2 ^ 12) :=
    composite_of_dvd (2 * 277154377 + 1) 12 37 hp37 hdvd_277154377 (by decide) (by decide)
  exact A282459_pos_of_exists 277154377 12 hk h_comp

lemma leaf_single_43 (n : ℕ) (h_eq : n = 136508872) : A282459 n > 0 := by
  subst h_eq
  have hk : 5 ∈ Finset.Icc 1 (log 2 (2 * 136508872 + 1)) := by decide
  have hdvd_136508872 : 31 ∣ 2 * 136508872 + 1 - 2 ^ 5 := by decide
  have h_comp : 1 < 2 * 136508872 + 1 - 2 ^ 5 ∧ ¬ Nat.Prime (2 * 136508872 + 1 - 2 ^ 5) :=
    composite_of_dvd (2 * 136508872 + 1) 5 31 hp31 hdvd_136508872 (by decide) (by decide)
  exact A282459_pos_of_exists 136508872 5 hk h_comp

lemma leaf_single_44 (n : ℕ) (h_eq : n = 457984312) : A282459 n > 0 := by
  subst h_eq
  have hk : 21 ∈ Finset.Icc 1 (log 2 (2 * 457984312 + 1)) := by decide
  have hdvd_457984312 : 37 ∣ 2 * 457984312 + 1 - 2 ^ 21 := by decide
  have h_comp : 1 < 2 * 457984312 + 1 - 2 ^ 21 ∧ ¬ Nat.Prime (2 * 457984312 + 1 - 2 ^ 21) :=
    composite_of_dvd (2 * 457984312 + 1) 21 37 hp37 hdvd_457984312 (by decide) (by decide)
  exact A282459_pos_of_exists 457984312 21 hk h_comp

lemma leaf_single_45 (n : ℕ) (h_eq : n = 156601087) : A282459 n > 0 := by
  subst h_eq
  have hk : 16 ∈ Finset.Icc 1 (log 2 (2 * 156601087 + 1)) := by decide
  have hdvd_156601087 : 41 ∣ 2 * 156601087 + 1 - 2 ^ 16 := by decide
  have h_comp : 1 < 2 * 156601087 + 1 - 2 ^ 16 ∧ ¬ Nat.Prime (2 * 156601087 + 1 - 2 ^ 16) :=
    composite_of_dvd (2 * 156601087 + 1) 16 41 hp41 hdvd_156601087 (by decide) (by decide)
  exact A282459_pos_of_exists 156601087 16 hk h_comp

lemma leaf_single_46 (n : ℕ) (h_eq : n = 317338807) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 317338807 + 1)) := by decide
  have hdvd_317338807 : 37 ∣ 2 * 317338807 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 317338807 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 317338807 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 317338807 + 1) 1 37 hp37 hdvd_317338807 (by decide) (by decide)
  exact A282459_pos_of_exists 317338807 1 hk h_comp

lemma leaf_single_47 (n : ℕ) (h_eq : n = 15955582) : A282459 n > 0 := by
  subst h_eq
  have hk : 8 ∈ Finset.Icc 1 (log 2 (2 * 15955582 + 1)) := by decide
  have hdvd_15955582 : 37 ∣ 2 * 15955582 + 1 - 2 ^ 8 := by decide
  have h_comp : 1 < 2 * 15955582 + 1 - 2 ^ 8 ∧ ¬ Nat.Prime (2 * 15955582 + 1 - 2 ^ 8) :=
    composite_of_dvd (2 * 15955582 + 1) 8 37 hp37 hdvd_15955582 (by decide) (by decide)
  exact A282459_pos_of_exists 15955582 8 hk h_comp

lemma leaf_single_48 (n : ℕ) (h_eq : n = 13591792) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 13591792 + 1)) := by decide
  have hdvd_13591792 : 7 ∣ 2 * 13591792 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 13591792 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 13591792 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 13591792 + 1) 1 7 hp7 hdvd_13591792 (by decide) (by decide)
  exact A282459_pos_of_exists 13591792 1 hk h_comp

lemma leaf_single_49 (n : ℕ) (h_eq : n = 355159447) : A282459 n > 0 := by
  subst h_eq
  have hk : 18 ∈ Finset.Icc 1 (log 2 (2 * 355159447 + 1)) := by decide
  have hdvd_355159447 : 37 ∣ 2 * 355159447 + 1 - 2 ^ 18 := by decide
  have h_comp : 1 < 2 * 355159447 + 1 - 2 ^ 18 ∧ ¬ Nat.Prime (2 * 355159447 + 1 - 2 ^ 18) :=
    composite_of_dvd (2 * 355159447 + 1) 18 37 hp37 hdvd_355159447 (by decide) (by decide)
  exact A282459_pos_of_exists 355159447 18 hk h_comp

lemma leaf_single_50 (n : ℕ) (h_eq : n = 214513942) : A282459 n > 0 := by
  subst h_eq
  have hk : 16 ∈ Finset.Icc 1 (log 2 (2 * 214513942 + 1)) := by decide
  have hdvd_214513942 : 37 ∣ 2 * 214513942 + 1 - 2 ^ 16 := by decide
  have h_comp : 1 < 2 * 214513942 + 1 - 2 ^ 16 ∧ ¬ Nat.Prime (2 * 214513942 + 1 - 2 ^ 16) :=
    composite_of_dvd (2 * 214513942 + 1) 16 37 hp37 hdvd_214513942 (by decide) (by decide)
  exact A282459_pos_of_exists 214513942 16 hk h_comp

lemma leaf_single_51 (n : ℕ) (h_eq : n = 234606157) : A282459 n > 0 := by
  subst h_eq
  have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 234606157 + 1)) := by decide
  have hdvd_234606157 : 31 ∣ 2 * 234606157 + 1 - 2 ^ 2 := by decide
  have h_comp : 1 < 2 * 234606157 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 234606157 + 1 - 2 ^ 2) :=
    composite_of_dvd (2 * 234606157 + 1) 2 31 hp31 hdvd_234606157 (by decide) (by decide)
  exact A282459_pos_of_exists 234606157 2 hk h_comp

lemma leaf_single_52 (n : ℕ) (h_eq : n = 395343877) : A282459 n > 0 := by
  subst h_eq
  have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 395343877 + 1)) := by decide
  have hdvd_395343877 : 7 ∣ 2 * 395343877 + 1 - 2 ^ 2 := by decide
  have h_comp : 1 < 2 * 395343877 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 395343877 + 1 - 2 ^ 2) :=
    composite_of_dvd (2 * 395343877 + 1) 2 7 hp7 hdvd_395343877 (by decide) (by decide)
  exact A282459_pos_of_exists 395343877 2 hk h_comp

lemma leaf_single_53 (n : ℕ) (h_eq : n = 415436092) : A282459 n > 0 := by
  subst h_eq
  have hk : 8 ∈ Finset.Icc 1 (log 2 (2 * 415436092 + 1)) := by decide
  have hdvd_415436092 : 41 ∣ 2 * 415436092 + 1 - 2 ^ 8 := by decide
  have h_comp : 1 < 2 * 415436092 + 1 - 2 ^ 8 ∧ ¬ Nat.Prime (2 * 415436092 + 1 - 2 ^ 8) :=
    composite_of_dvd (2 * 415436092 + 1) 8 41 hp41 hdvd_415436092 (by decide) (by decide)
  exact A282459_pos_of_exists 415436092 8 hk h_comp

lemma leaf_single_54 (n : ℕ) (h_eq : n = 114052867) : A282459 n > 0 := by
  subst h_eq
  have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 114052867 + 1)) := by decide
  have hdvd_114052867 : 7 ∣ 2 * 114052867 + 1 - 2 ^ 2 := by decide
  have h_comp : 1 < 2 * 114052867 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 114052867 + 1 - 2 ^ 2) :=
    composite_of_dvd (2 * 114052867 + 1) 2 7 hp7 hdvd_114052867 (by decide) (by decide)
  exact A282459_pos_of_exists 114052867 2 hk h_comp

lemma leaf_single_55 (n : ℕ) (h_eq : n = 435528307) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 435528307 + 1)) := by decide
  have hdvd_435528307 : 7 ∣ 2 * 435528307 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 435528307 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 435528307 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 435528307 + 1) 1 7 hp7 hdvd_435528307 (by decide) (by decide)
  exact A282459_pos_of_exists 435528307 1 hk h_comp

lemma leaf_single_56 (n : ℕ) (h_eq : n = 294882802) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 294882802 + 1)) := by decide
  have hdvd_294882802 : 7 ∣ 2 * 294882802 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 294882802 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 294882802 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 294882802 + 1) 1 7 hp7 hdvd_294882802 (by decide) (by decide)
  exact A282459_pos_of_exists 294882802 1 hk h_comp

lemma leaf_single_57 (n : ℕ) (h_eq : n = 455620522) : A282459 n > 0 := by
  subst h_eq
  have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 455620522 + 1)) := by decide
  have hdvd_455620522 : 7 ∣ 2 * 455620522 + 1 - 2 ^ 3 := by decide
  have h_comp : 1 < 2 * 455620522 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 455620522 + 1 - 2 ^ 3) :=
    composite_of_dvd (2 * 455620522 + 1) 3 7 hp7 hdvd_455620522 (by decide) (by decide)
  exact A282459_pos_of_exists 455620522 3 hk h_comp

lemma leaf_single_58 (n : ℕ) (h_eq : n = 154237297) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 154237297 + 1)) := by decide
  have hdvd_154237297 : 7 ∣ 2 * 154237297 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 154237297 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 154237297 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 154237297 + 1) 1 7 hp7 hdvd_154237297 (by decide) (by decide)
  exact A282459_pos_of_exists 154237297 1 hk h_comp

lemma leaf_single_59 (n : ℕ) (h_eq : n = 314975017) : A282459 n > 0 := by
  subst h_eq
  have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 314975017 + 1)) := by decide
  have hdvd_314975017 : 7 ∣ 2 * 314975017 + 1 - 2 ^ 3 := by decide
  have h_comp : 1 < 2 * 314975017 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 314975017 + 1 - 2 ^ 3) :=
    composite_of_dvd (2 * 314975017 + 1) 3 7 hp7 hdvd_314975017 (by decide) (by decide)
  exact A282459_pos_of_exists 314975017 3 hk h_comp

lemma leaf_single_60 (n : ℕ) (h_eq : n = 448529152) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 448529152 + 1)) := by decide
  have hdvd_448529152 : 37 ∣ 2 * 448529152 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 448529152 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 448529152 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 448529152 + 1) 1 37 hp37 hdvd_448529152 (by decide) (by decide)
  exact A282459_pos_of_exists 448529152 1 hk h_comp

lemma leaf_single_61 (n : ℕ) (h_eq : n = 327975862) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 327975862 + 1)) := by decide
  have hdvd_327975862 : 7 ∣ 2 * 327975862 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 327975862 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 327975862 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 327975862 + 1) 1 7 hp7 hdvd_327975862 (by decide) (by decide)
  exact A282459_pos_of_exists 327975862 1 hk h_comp

lemma leaf_single_62 (n : ℕ) (h_eq : n = 187330357) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 187330357 + 1)) := by decide
  have hdvd_187330357 : 7 ∣ 2 * 187330357 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 187330357 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 187330357 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 187330357 + 1) 1 7 hp7 hdvd_187330357 (by decide) (by decide)
  exact A282459_pos_of_exists 187330357 1 hk h_comp

lemma leaf_single_63 (n : ℕ) (h_eq : n = 207422572) : A282459 n > 0 := by
  subst h_eq
  have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 207422572 + 1)) := by decide
  have hdvd_207422572 : 7 ∣ 2 * 207422572 + 1 - 2 ^ 3 := by decide
  have h_comp : 1 < 2 * 207422572 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 207422572 + 1 - 2 ^ 3) :=
    composite_of_dvd (2 * 207422572 + 1) 3 7 hp7 hdvd_207422572 (by decide) (by decide)
  exact A282459_pos_of_exists 207422572 3 hk h_comp

lemma leaf_single_64 (n : ℕ) (h_eq : n = 368160292) : A282459 n > 0 := by
  subst h_eq
  have hk : 11 ∈ Finset.Icc 1 (log 2 (2 * 368160292 + 1)) := by decide
  have hdvd_368160292 : 37 ∣ 2 * 368160292 + 1 - 2 ^ 11 := by decide
  have h_comp : 1 < 2 * 368160292 + 1 - 2 ^ 11 ∧ ¬ Nat.Prime (2 * 368160292 + 1 - 2 ^ 11) :=
    composite_of_dvd (2 * 368160292 + 1) 11 37 hp37 hdvd_368160292 (by decide) (by decide)
  exact A282459_pos_of_exists 368160292 11 hk h_comp

lemma leaf_single_65 (n : ℕ) (h_eq : n = 388252507) : A282459 n > 0 := by
  subst h_eq
  have hk : 13 ∈ Finset.Icc 1 (log 2 (2 * 388252507 + 1)) := by decide
  have hdvd_388252507 : 47 ∣ 2 * 388252507 + 1 - 2 ^ 13 := by decide
  have h_comp : 1 < 2 * 388252507 + 1 - 2 ^ 13 ∧ ¬ Nat.Prime (2 * 388252507 + 1 - 2 ^ 13) :=
    composite_of_dvd (2 * 388252507 + 1) 13 47 hp47 hdvd_388252507 (by decide) (by decide)
  exact A282459_pos_of_exists 388252507 13 hk h_comp

lemma leaf_single_66 (n : ℕ) (h_eq : n = 86869282) : A282459 n > 0 := by
  subst h_eq
  have hk : 20 ∈ Finset.Icc 1 (log 2 (2 * 86869282 + 1)) := by decide
  have hdvd_86869282 : 37 ∣ 2 * 86869282 + 1 - 2 ^ 20 := by decide
  have h_comp : 1 < 2 * 86869282 + 1 - 2 ^ 20 ∧ ¬ Nat.Prime (2 * 86869282 + 1 - 2 ^ 20) :=
    composite_of_dvd (2 * 86869282 + 1) 20 37 hp37 hdvd_86869282 (by decide) (by decide)
  exact A282459_pos_of_exists 86869282 20 hk h_comp

lemma leaf_single_67 (n : ℕ) (h_eq : n = 408344722) : A282459 n > 0 := by
  subst h_eq
  have hk : 12 ∈ Finset.Icc 1 (log 2 (2 * 408344722 + 1)) := by decide
  have hdvd_408344722 : 37 ∣ 2 * 408344722 + 1 - 2 ^ 12 := by decide
  have h_comp : 1 < 2 * 408344722 + 1 - 2 ^ 12 ∧ ¬ Nat.Prime (2 * 408344722 + 1 - 2 ^ 12) :=
    composite_of_dvd (2 * 408344722 + 1) 12 37 hp37 hdvd_408344722 (by decide) (by decide)
  exact A282459_pos_of_exists 408344722 12 hk h_comp

lemma leaf_single_68 (n : ℕ) (h_eq : n = 267699217) : A282459 n > 0 := by
  subst h_eq
  have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 267699217 + 1)) := by decide
  have hdvd_267699217 : 31 ∣ 2 * 267699217 + 1 - 2 ^ 3 := by decide
  have h_comp : 1 < 2 * 267699217 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 267699217 + 1 - 2 ^ 3) :=
    composite_of_dvd (2 * 267699217 + 1) 3 31 hp31 hdvd_267699217 (by decide) (by decide)
  exact A282459_pos_of_exists 267699217 3 hk h_comp

lemma leaf_single_69 (n : ℕ) (h_eq : n = 428436937) : A282459 n > 0 := by
  subst h_eq
  have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 428436937 + 1)) := by decide
  have hdvd_428436937 : 7 ∣ 2 * 428436937 + 1 - 2 ^ 2 := by decide
  have h_comp : 1 < 2 * 428436937 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 428436937 + 1 - 2 ^ 2) :=
    composite_of_dvd (2 * 428436937 + 1) 2 7 hp7 hdvd_428436937 (by decide) (by decide)
  exact A282459_pos_of_exists 428436937 2 hk h_comp

lemma leaf_single_70 (n : ℕ) (h_eq : n = 127053712) : A282459 n > 0 := by
  subst h_eq
  have hk : 16 ∈ Finset.Icc 1 (log 2 (2 * 127053712 + 1)) := by decide
  have hdvd_127053712 : 37 ∣ 2 * 127053712 + 1 - 2 ^ 16 := by decide
  have h_comp : 1 < 2 * 127053712 + 1 - 2 ^ 16 ∧ ¬ Nat.Prime (2 * 127053712 + 1 - 2 ^ 16) :=
    composite_of_dvd (2 * 127053712 + 1) 16 37 hp37 hdvd_127053712 (by decide) (by decide)
  exact A282459_pos_of_exists 127053712 16 hk h_comp

lemma leaf_single_71 (n : ℕ) (h_eq : n = 287791432) : A282459 n > 0 := by
  subst h_eq
  have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 287791432 + 1)) := by decide
  have hdvd_287791432 : 7 ∣ 2 * 287791432 + 1 - 2 ^ 2 := by decide
  have h_comp : 1 < 2 * 287791432 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 287791432 + 1 - 2 ^ 2) :=
    composite_of_dvd (2 * 287791432 + 1) 2 7 hp7 hdvd_287791432 (by decide) (by decide)
  exact A282459_pos_of_exists 287791432 2 hk h_comp

lemma leaf_single_72 (n : ℕ) (h_eq : n = 285427642) : A282459 n > 0 := by
  subst h_eq
  have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 285427642 + 1)) := by decide
  have hdvd_285427642 : 37 ∣ 2 * 285427642 + 1 - 2 ^ 3 := by decide
  have h_comp : 1 < 2 * 285427642 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 285427642 + 1 - 2 ^ 3) :=
    composite_of_dvd (2 * 285427642 + 1) 3 37 hp37 hdvd_285427642 (by decide) (by decide)
  exact A282459_pos_of_exists 285427642 3 hk h_comp

lemma leaf_single_73 (n : ℕ) (h_eq : n = 164874352) : A282459 n > 0 := by
  subst h_eq
  have hk : 27 ∈ Finset.Icc 1 (log 2 (2 * 164874352 + 1)) := by decide
  have hdvd_164874352 : 37 ∣ 2 * 164874352 + 1 - 2 ^ 27 := by decide
  have h_comp : 1 < 2 * 164874352 + 1 - 2 ^ 27 ∧ ¬ Nat.Prime (2 * 164874352 + 1 - 2 ^ 27) :=
    composite_of_dvd (2 * 164874352 + 1) 27 37 hp37 hdvd_164874352 (by decide) (by decide)
  exact A282459_pos_of_exists 164874352 27 hk h_comp

lemma leaf_single_74 (n : ℕ) (h_eq : n = 24228847) : A282459 n > 0 := by
  subst h_eq
  have hk : 4 ∈ Finset.Icc 1 (log 2 (2 * 24228847 + 1)) := by decide
  have hdvd_24228847 : 37 ∣ 2 * 24228847 + 1 - 2 ^ 4 := by decide
  have h_comp : 1 < 2 * 24228847 + 1 - 2 ^ 4 ∧ ¬ Nat.Prime (2 * 24228847 + 1 - 2 ^ 4) :=
    composite_of_dvd (2 * 24228847 + 1) 4 37 hp37 hdvd_24228847 (by decide) (by decide)
  exact A282459_pos_of_exists 24228847 4 hk h_comp

lemma leaf_single_75 (n : ℕ) (h_eq : n = 44321062) : A282459 n > 0 := by
  subst h_eq
  have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 44321062 + 1)) := by decide
  have hdvd_44321062 : 37 ∣ 2 * 44321062 + 1 - 2 ^ 2 := by decide
  have h_comp : 1 < 2 * 44321062 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 44321062 + 1 - 2 ^ 2) :=
    composite_of_dvd (2 * 44321062 + 1) 2 37 hp37 hdvd_44321062 (by decide) (by decide)
  exact A282459_pos_of_exists 44321062 2 hk h_comp

lemma leaf_single_76 (n : ℕ) (h_eq : n = 205058782) : A282459 n > 0 := by
  subst h_eq
  have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 205058782 + 1)) := by decide
  have hdvd_205058782 : 7 ∣ 2 * 205058782 + 1 - 2 ^ 2 := by decide
  have h_comp : 1 < 2 * 205058782 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 205058782 + 1 - 2 ^ 2) :=
    composite_of_dvd (2 * 205058782 + 1) 2 7 hp7 hdvd_205058782 (by decide) (by decide)
  exact A282459_pos_of_exists 205058782 2 hk h_comp

lemma leaf_single_77 (n : ℕ) (h_eq : n = 225150997) : A282459 n > 0 := by
  subst h_eq
  have hk : 9 ∈ Finset.Icc 1 (log 2 (2 * 225150997 + 1)) := by decide
  have hdvd_225150997 : 41 ∣ 2 * 225150997 + 1 - 2 ^ 9 := by decide
  have h_comp : 1 < 2 * 225150997 + 1 - 2 ^ 9 ∧ ¬ Nat.Prime (2 * 225150997 + 1 - 2 ^ 9) :=
    composite_of_dvd (2 * 225150997 + 1) 9 41 hp41 hdvd_225150997 (by decide) (by decide)
  exact A282459_pos_of_exists 225150997 9 hk h_comp

lemma leaf_single_78 (n : ℕ) (h_eq : n = 385888717) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 385888717 + 1)) := by decide
  have hdvd_385888717 : 7 ∣ 2 * 385888717 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 385888717 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 385888717 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 385888717 + 1) 1 7 hp7 hdvd_385888717 (by decide) (by decide)
  exact A282459_pos_of_exists 385888717 1 hk h_comp

lemma leaf_single_79 (n : ℕ) (h_eq : n = 245243212) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 245243212 + 1)) := by decide
  have hdvd_245243212 : 7 ∣ 2 * 245243212 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 245243212 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 245243212 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 245243212 + 1) 1 7 hp7 hdvd_245243212 (by decide) (by decide)
  exact A282459_pos_of_exists 245243212 1 hk h_comp

lemma leaf_single_80 (n : ℕ) (h_eq : n = 104597707) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 104597707 + 1)) := by decide
  have hdvd_104597707 : 7 ∣ 2 * 104597707 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 104597707 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 104597707 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 104597707 + 1) 1 7 hp7 hdvd_104597707 (by decide) (by decide)
  exact A282459_pos_of_exists 104597707 1 hk h_comp

lemma leaf_single_81 (n : ℕ) (h_eq : n = 265335427) : A282459 n > 0 := by
  subst h_eq
  have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 265335427 + 1)) := by decide
  have hdvd_265335427 : 7 ∣ 2 * 265335427 + 1 - 2 ^ 3 := by decide
  have h_comp : 1 < 2 * 265335427 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 265335427 + 1 - 2 ^ 3) :=
    composite_of_dvd (2 * 265335427 + 1) 3 7 hp7 hdvd_265335427 (by decide) (by decide)
  exact A282459_pos_of_exists 265335427 3 hk h_comp

lemma leaf_single_82 (n : ℕ) (h_eq : n = 426073147) : A282459 n > 0 := by
  subst h_eq
  have hk : 19 ∈ Finset.Icc 1 (log 2 (2 * 426073147 + 1)) := by decide
  have hdvd_426073147 : 37 ∣ 2 * 426073147 + 1 - 2 ^ 19 := by decide
  have h_comp : 1 < 2 * 426073147 + 1 - 2 ^ 19 ∧ ¬ Nat.Prime (2 * 426073147 + 1 - 2 ^ 19) :=
    composite_of_dvd (2 * 426073147 + 1) 19 37 hp37 hdvd_426073147 (by decide) (by decide)
  exact A282459_pos_of_exists 426073147 19 hk h_comp

lemma leaf_single_83 (n : ℕ) (h_eq : n = 124689922) : A282459 n > 0 := by
  subst h_eq
  have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 124689922 + 1)) := by decide
  have hdvd_124689922 : 7 ∣ 2 * 124689922 + 1 - 2 ^ 3 := by decide
  have h_comp : 1 < 2 * 124689922 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 124689922 + 1 - 2 ^ 3) :=
    composite_of_dvd (2 * 124689922 + 1) 3 7 hp7 hdvd_124689922 (by decide) (by decide)
  exact A282459_pos_of_exists 124689922 3 hk h_comp

lemma leaf_single_84 (n : ℕ) (h_eq : n = 122326132) : A282459 n > 0 := by
  subst h_eq
  have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 122326132 + 1)) := by decide
  have hdvd_122326132 : 7 ∣ 2 * 122326132 + 1 - 2 ^ 2 := by decide
  have h_comp : 1 < 2 * 122326132 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 122326132 + 1 - 2 ^ 2) :=
    composite_of_dvd (2 * 122326132 + 1) 2 7 hp7 hdvd_122326132 (by decide) (by decide)
  exact A282459_pos_of_exists 122326132 2 hk h_comp

lemma leaf_single_85 (n : ℕ) (h_eq : n = 1772842) : A282459 n > 0 := by
  subst h_eq
  have hk : 7 ∈ Finset.Icc 1 (log 2 (2 * 1772842 + 1)) := by decide
  have hdvd_1772842 : 41 ∣ 2 * 1772842 + 1 - 2 ^ 7 := by decide
  have h_comp : 1 < 2 * 1772842 + 1 - 2 ^ 7 ∧ ¬ Nat.Prime (2 * 1772842 + 1 - 2 ^ 7) :=
    composite_of_dvd (2 * 1772842 + 1) 7 41 hp41 hdvd_1772842 (by decide) (by decide)
  exact A282459_pos_of_exists 1772842 7 hk h_comp

lemma leaf_single_86 (n : ℕ) (h_eq : n = 323248282) : A282459 n > 0 := by
  subst h_eq
  have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 323248282 + 1)) := by decide
  have hdvd_323248282 : 7 ∣ 2 * 323248282 + 1 - 2 ^ 3 := by decide
  have h_comp : 1 < 2 * 323248282 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 323248282 + 1 - 2 ^ 3) :=
    composite_of_dvd (2 * 323248282 + 1) 3 7 hp7 hdvd_323248282 (by decide) (by decide)
  exact A282459_pos_of_exists 323248282 3 hk h_comp

lemma leaf_single_87 (n : ℕ) (h_eq : n = 343340497) : A282459 n > 0 := by
  subst h_eq
  have hk : 14 ∈ Finset.Icc 1 (log 2 (2 * 343340497 + 1)) := by decide
  have hdvd_343340497 : 37 ∣ 2 * 343340497 + 1 - 2 ^ 14 := by decide
  have h_comp : 1 < 2 * 343340497 + 1 - 2 ^ 14 ∧ ¬ Nat.Prime (2 * 343340497 + 1 - 2 ^ 14) :=
    composite_of_dvd (2 * 343340497 + 1) 14 37 hp37 hdvd_343340497 (by decide) (by decide)
  exact A282459_pos_of_exists 343340497 14 hk h_comp

lemma leaf_single_88 (n : ℕ) (h_eq : n = 41957272) : A282459 n > 0 := by
  subst h_eq
  have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 41957272 + 1)) := by decide
  have hdvd_41957272 : 7 ∣ 2 * 41957272 + 1 - 2 ^ 3 := by decide
  have h_comp : 1 < 2 * 41957272 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 41957272 + 1 - 2 ^ 3) :=
    composite_of_dvd (2 * 41957272 + 1) 3 7 hp7 hdvd_41957272 (by decide) (by decide)
  exact A282459_pos_of_exists 41957272 3 hk h_comp

lemma leaf_single_89 (n : ℕ) (h_eq : n = 62049487) : A282459 n > 0 := by
  subst h_eq
  have hk : 11 ∈ Finset.Icc 1 (log 2 (2 * 62049487 + 1)) := by decide
  have hdvd_62049487 : 37 ∣ 2 * 62049487 + 1 - 2 ^ 11 := by decide
  have h_comp : 1 < 2 * 62049487 + 1 - 2 ^ 11 ∧ ¬ Nat.Prime (2 * 62049487 + 1 - 2 ^ 11) :=
    composite_of_dvd (2 * 62049487 + 1) 11 37 hp37 hdvd_62049487 (by decide) (by decide)
  exact A282459_pos_of_exists 62049487 11 hk h_comp

lemma leaf_single_90 (n : ℕ) (h_eq : n = 222787207) : A282459 n > 0 := by
  subst h_eq
  have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 222787207 + 1)) := by decide
  have hdvd_222787207 : 73 ∣ 2 * 222787207 + 1 - 2 ^ 3 := by decide
  have h_comp : 1 < 2 * 222787207 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 222787207 + 1 - 2 ^ 3) :=
    composite_of_dvd (2 * 222787207 + 1) 3 73 hp73 hdvd_222787207 (by decide) (by decide)
  exact A282459_pos_of_exists 222787207 3 hk h_comp

lemma leaf_single_91 (n : ℕ) (h_eq : n = 82141702) : A282459 n > 0 := by
  subst h_eq
  have hk : 14 ∈ Finset.Icc 1 (log 2 (2 * 82141702 + 1)) := by decide
  have hdvd_82141702 : 47 ∣ 2 * 82141702 + 1 - 2 ^ 14 := by decide
  have h_comp : 1 < 2 * 82141702 + 1 - 2 ^ 14 ∧ ¬ Nat.Prime (2 * 82141702 + 1 - 2 ^ 14) :=
    composite_of_dvd (2 * 82141702 + 1) 14 47 hp47 hdvd_82141702 (by decide) (by decide)
  exact A282459_pos_of_exists 82141702 14 hk h_comp

lemma leaf_single_92 (n : ℕ) (h_eq : n = 403617142) : A282459 n > 0 := by
  subst h_eq
  have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 403617142 + 1)) := by decide
  have hdvd_403617142 : 7 ∣ 2 * 403617142 + 1 - 2 ^ 2 := by decide
  have h_comp : 1 < 2 * 403617142 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 403617142 + 1 - 2 ^ 2) :=
    composite_of_dvd (2 * 403617142 + 1) 2 7 hp7 hdvd_403617142 (by decide) (by decide)
  exact A282459_pos_of_exists 403617142 2 hk h_comp

lemma leaf_single_93 (n : ℕ) (h_eq : n = 102233917) : A282459 n > 0 := by
  subst h_eq
  have hk : 12 ∈ Finset.Icc 1 (log 2 (2 * 102233917 + 1)) := by decide
  have hdvd_102233917 : 37 ∣ 2 * 102233917 + 1 - 2 ^ 12 := by decide
  have h_comp : 1 < 2 * 102233917 + 1 - 2 ^ 12 ∧ ¬ Nat.Prime (2 * 102233917 + 1 - 2 ^ 12) :=
    composite_of_dvd (2 * 102233917 + 1) 12 37 hp37 hdvd_102233917 (by decide) (by decide)
  exact A282459_pos_of_exists 102233917 12 hk h_comp

lemma leaf_single_94 (n : ℕ) (h_eq : n = 262971637) : A282459 n > 0 := by
  subst h_eq
  have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 262971637 + 1)) := by decide
  have hdvd_262971637 : 7 ∣ 2 * 262971637 + 1 - 2 ^ 2 := by decide
  have h_comp : 1 < 2 * 262971637 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 262971637 + 1 - 2 ^ 2) :=
    composite_of_dvd (2 * 262971637 + 1) 2 7 hp7 hdvd_262971637 (by decide) (by decide)
  exact A282459_pos_of_exists 262971637 2 hk h_comp

lemma leaf_single_95 (n : ℕ) (h_eq : n = 423709357) : A282459 n > 0 := by
  subst h_eq
  have hk : 7 ∈ Finset.Icc 1 (log 2 (2 * 423709357 + 1)) := by decide
  have hdvd_423709357 : 43 ∣ 2 * 423709357 + 1 - 2 ^ 7 := by decide
  have h_comp : 1 < 2 * 423709357 + 1 - 2 ^ 7 ∧ ¬ Nat.Prime (2 * 423709357 + 1 - 2 ^ 7) :=
    composite_of_dvd (2 * 423709357 + 1) 7 43 hp43 hdvd_423709357 (by decide) (by decide)
  exact A282459_pos_of_exists 423709357 7 hk h_comp

lemma leaf_single_96 (n : ℕ) (h_eq : n = 258244057) : A282459 n > 0 := by
  subst h_eq
  have hk : 16 ∈ Finset.Icc 1 (log 2 (2 * 258244057 + 1)) := by decide
  have hdvd_258244057 : 37 ∣ 2 * 258244057 + 1 - 2 ^ 16 := by decide
  have h_comp : 1 < 2 * 258244057 + 1 - 2 ^ 16 ∧ ¬ Nat.Prime (2 * 258244057 + 1 - 2 ^ 16) :=
    composite_of_dvd (2 * 258244057 + 1) 16 37 hp37 hdvd_258244057 (by decide) (by decide)
  exact A282459_pos_of_exists 258244057 16 hk h_comp

lemma leaf_single_97 (n : ℕ) (h_eq : n = 137690767) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 137690767 + 1)) := by decide
  have hdvd_137690767 : 7 ∣ 2 * 137690767 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 137690767 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 137690767 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 137690767 + 1) 1 7 hp7 hdvd_137690767 (by decide) (by decide)
  exact A282459_pos_of_exists 137690767 1 hk h_comp

lemma leaf_single_98 (n : ℕ) (h_eq : n = 459166207) : A282459 n > 0 := by
  subst h_eq
  have hk : 25 ∈ Finset.Icc 1 (log 2 (2 * 459166207 + 1)) := by decide
  have hdvd_459166207 : 59 ∣ 2 * 459166207 + 1 - 2 ^ 25 := by decide
  have h_comp : 1 < 2 * 459166207 + 1 - 2 ^ 25 ∧ ¬ Nat.Prime (2 * 459166207 + 1 - 2 ^ 25) :=
    composite_of_dvd (2 * 459166207 + 1) 25 59 hp59 hdvd_459166207 (by decide) (by decide)
  exact A282459_pos_of_exists 459166207 25 hk h_comp

lemma leaf_single_99 (n : ℕ) (h_eq : n = 17137477) : A282459 n > 0 := by
  subst h_eq
  have hk : 3 ∈ Finset.Icc 1 (log 2 (2 * 17137477 + 1)) := by decide
  have hdvd_17137477 : 7 ∣ 2 * 17137477 + 1 - 2 ^ 3 := by decide
  have h_comp : 1 < 2 * 17137477 + 1 - 2 ^ 3 ∧ ¬ Nat.Prime (2 * 17137477 + 1 - 2 ^ 3) :=
    composite_of_dvd (2 * 17137477 + 1) 3 7 hp7 hdvd_17137477 (by decide) (by decide)
  exact A282459_pos_of_exists 17137477 3 hk h_comp

lemma leaf_single_100 (n : ℕ) (h_eq : n = 177875197) : A282459 n > 0 := by
  subst h_eq
  have hk : 25 ∈ Finset.Icc 1 (log 2 (2 * 177875197 + 1)) := by decide
  have hdvd_177875197 : 37 ∣ 2 * 177875197 + 1 - 2 ^ 25 := by decide
  have h_comp : 1 < 2 * 177875197 + 1 - 2 ^ 25 ∧ ¬ Nat.Prime (2 * 177875197 + 1 - 2 ^ 25) :=
    composite_of_dvd (2 * 177875197 + 1) 25 37 hp37 hdvd_177875197 (by decide) (by decide)
  exact A282459_pos_of_exists 177875197 25 hk h_comp

lemma leaf_single_101 (n : ℕ) (h_eq : n = 197967412) : A282459 n > 0 := by
  subst h_eq
  have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 197967412 + 1)) := by decide
  have hdvd_197967412 : 31 ∣ 2 * 197967412 + 1 - 2 ^ 2 := by decide
  have h_comp : 1 < 2 * 197967412 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 197967412 + 1 - 2 ^ 2) :=
    composite_of_dvd (2 * 197967412 + 1) 2 31 hp31 hdvd_197967412 (by decide) (by decide)
  exact A282459_pos_of_exists 197967412 2 hk h_comp

lemma leaf_single_102 (n : ℕ) (h_eq : n = 358705132) : A282459 n > 0 := by
  subst h_eq
  have hk : 15 ∈ Finset.Icc 1 (log 2 (2 * 358705132 + 1)) := by decide
  have hdvd_358705132 : 37 ∣ 2 * 358705132 + 1 - 2 ^ 15 := by decide
  have h_comp : 1 < 2 * 358705132 + 1 - 2 ^ 15 ∧ ¬ Nat.Prime (2 * 358705132 + 1 - 2 ^ 15) :=
    composite_of_dvd (2 * 358705132 + 1) 15 37 hp37 hdvd_358705132 (by decide) (by decide)
  exact A282459_pos_of_exists 358705132 15 hk h_comp

lemma leaf_single_103 (n : ℕ) (h_eq : n = 218059627) : A282459 n > 0 := by
  subst h_eq
  have hk : 1 ∈ Finset.Icc 1 (log 2 (2 * 218059627 + 1)) := by decide
  have hdvd_218059627 : 31 ∣ 2 * 218059627 + 1 - 2 ^ 1 := by decide
  have h_comp : 1 < 2 * 218059627 + 1 - 2 ^ 1 ∧ ¬ Nat.Prime (2 * 218059627 + 1 - 2 ^ 1) :=
    composite_of_dvd (2 * 218059627 + 1) 1 31 hp31 hdvd_218059627 (by decide) (by decide)
  exact A282459_pos_of_exists 218059627 1 hk h_comp

lemma leaf_single_104 (n : ℕ) (h_eq : n = 77414122) : A282459 n > 0 := by
  subst h_eq
  have hk : 4 ∈ Finset.Icc 1 (log 2 (2 * 77414122 + 1)) := by decide
  have hdvd_77414122 : 31 ∣ 2 * 77414122 + 1 - 2 ^ 4 := by decide
  have h_comp : 1 < 2 * 77414122 + 1 - 2 ^ 4 ∧ ¬ Nat.Prime (2 * 77414122 + 1 - 2 ^ 4) :=
    composite_of_dvd (2 * 77414122 + 1) 4 31 hp31 hdvd_77414122 (by decide) (by decide)
  exact A282459_pos_of_exists 77414122 4 hk h_comp

lemma leaf_single_105 (n : ℕ) (h_eq : n = 238151842) : A282459 n > 0 := by
  subst h_eq
  have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 238151842 + 1)) := by decide
  have hdvd_238151842 : 7 ∣ 2 * 238151842 + 1 - 2 ^ 2 := by decide
  have h_comp : 1 < 2 * 238151842 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 238151842 + 1 - 2 ^ 2) :=
    composite_of_dvd (2 * 238151842 + 1) 2 7 hp7 hdvd_238151842 (by decide) (by decide)
  exact A282459_pos_of_exists 238151842 2 hk h_comp

lemma leaf_single_106 (n : ℕ) (h_eq : n = 398889562) : A282459 n > 0 := by
  subst h_eq
  have hk : 18 ∈ Finset.Icc 1 (log 2 (2 * 398889562 + 1)) := by decide
  have hdvd_398889562 : 37 ∣ 2 * 398889562 + 1 - 2 ^ 18 := by decide
  have h_comp : 1 < 2 * 398889562 + 1 - 2 ^ 18 ∧ ¬ Nat.Prime (2 * 398889562 + 1 - 2 ^ 18) :=
    composite_of_dvd (2 * 398889562 + 1) 18 37 hp37 hdvd_398889562 (by decide) (by decide)
  exact A282459_pos_of_exists 398889562 18 hk h_comp

lemma leaf_single_107 (n : ℕ) (h_eq : n = 97506337) : A282459 n > 0 := by
  subst h_eq
  have hk : 2 ∈ Finset.Icc 1 (log 2 (2 * 97506337 + 1)) := by decide
  have hdvd_97506337 : 7 ∣ 2 * 97506337 + 1 - 2 ^ 2 := by decide
  have h_comp : 1 < 2 * 97506337 + 1 - 2 ^ 2 ∧ ¬ Nat.Prime (2 * 97506337 + 1 - 2 ^ 2) :=
    composite_of_dvd (2 * 97506337 + 1) 2 7 hp7 hdvd_97506337 (by decide) (by decide)
  exact A282459_pos_of_exists 97506337 2 hk h_comp

lemma solve_tree_node_0_23 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19 : (2 * n + 1) % 19 = 0) (h_mod_29 : (2 * n + 1) % 29 = 0) (h_mod_17 : (2 * n + 1) % 17 = 0) (h_mod_23_lt : (2 * n + 1) % 23 < 23) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 23
  · -- Case % 23 = 0
    have h_eq : n = 231060472 := by omega
    exact leaf_single_0 n h_eq
  · -- Case % 23 = 1
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^11 % 23 := by omega
    have hk2 : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) (2^11) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 11 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 2
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^1 % 23 := by omega
    have hk2 : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) (2^1) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 1 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 3
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^8 % 23 := by omega
    have hk2 : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) (2^8) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 8 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 4
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^2 % 23 := by omega
    have hk2 : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) (2^2) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 2 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 5
    have h_eq : n = 110507182 := by omega
    exact leaf_single_1 n h_eq
  · -- Case % 23 = 6
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^9 % 23 := by omega
    have hk2 : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) (2^9) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 9 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 7
    have h_eq : n = 431982622 := by omega
    exact leaf_single_2 n h_eq
  · -- Case % 23 = 8
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^3 % 23 := by omega
    have hk2 : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) (2^3) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 3 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 9
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^5 % 23 := by omega
    have hk2 : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) (2^5) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 5 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 10
    have h_eq : n = 452074837 := by omega
    exact leaf_single_3 n h_eq
  · -- Case % 23 = 11
    have h_eq : n = 150691612 := by omega
    exact leaf_single_4 n h_eq
  · -- Case % 23 = 12
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^10 % 23 := by omega
    have hk2 : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) (2^10) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 10 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 13
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^7 % 23 := by omega
    have hk2 : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) (2^7) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 7 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 14
    have h_eq : n = 170783827 := by omega
    exact leaf_single_5 n h_eq
  · -- Case % 23 = 15
    have h_eq : n = 331521547 := by omega
    exact leaf_single_6 n h_eq
  · -- Case % 23 = 16
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^4 % 23 := by omega
    have hk2 : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) (2^4) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 4 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 17
    have h_eq : n = 190876042 := by omega
    exact leaf_single_7 n h_eq
  · -- Case % 23 = 18
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^6 % 23 := by omega
    have hk2 : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) (2^6) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 6 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 19
    have h_eq : n = 50230537 := by omega
    exact leaf_single_8 n h_eq
  · -- Case % 23 = 20
    have h_eq : n = 210968257 := by omega
    exact leaf_single_9 n h_eq
  · -- Case % 23 = 21
    have h_eq : n = 371705977 := by omega
    exact leaf_single_10 n h_eq
  · -- Case % 23 = 22
    have h_eq : n = 70322752 := by omega
    exact leaf_single_11 n h_eq

lemma solve_tree_node_1_23 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19 : (2 * n + 1) % 19 = 0) (h_mod_29 : (2 * n + 1) % 29 = 0) (h_mod_17 : (2 * n + 1) % 17 = 3) (h_mod_23_lt : (2 * n + 1) % 23 < 23) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 23
  · -- Case % 23 = 0
    have h_eq : n = 203876887 := by omega
    exact leaf_single_12 n h_eq
  · -- Case % 23 = 1
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^11 % 23 := by omega
    have hk2 : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) (2^11) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 11 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 2
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^1 % 23 := by omega
    have hk2 : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) (2^1) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 1 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 3
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^8 % 23 := by omega
    have hk2 : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) (2^8) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 8 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 4
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^2 % 23 := by omega
    have hk2 : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) (2^2) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 2 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 5
    have h_eq : n = 83323597 := by omega
    exact leaf_single_13 n h_eq
  · -- Case % 23 = 6
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^9 % 23 := by omega
    have hk2 : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) (2^9) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 9 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 7
    have h_eq : n = 404799037 := by omega
    exact leaf_single_14 n h_eq
  · -- Case % 23 = 8
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^3 % 23 := by omega
    have hk2 : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) (2^3) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 3 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 9
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^5 % 23 := by omega
    have hk2 : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) (2^5) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 5 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 10
    have h_eq : n = 424891252 := by omega
    exact leaf_single_15 n h_eq
  · -- Case % 23 = 11
    have h_eq : n = 123508027 := by omega
    exact leaf_single_16 n h_eq
  · -- Case % 23 = 12
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^10 % 23 := by omega
    have hk2 : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) (2^10) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 10 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 13
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^7 % 23 := by omega
    have hk2 : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) (2^7) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 7 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 14
    have h_eq : n = 143600242 := by omega
    exact leaf_single_17 n h_eq
  · -- Case % 23 = 15
    have h_eq : n = 304337962 := by omega
    exact leaf_single_18 n h_eq
  · -- Case % 23 = 16
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^4 % 23 := by omega
    have hk2 : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) (2^4) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 4 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 17
    have h_eq : n = 163692457 := by omega
    exact leaf_single_19 n h_eq
  · -- Case % 23 = 18
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^6 % 23 := by omega
    have hk2 : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) (2^6) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 6 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 19
    have h_eq : n = 23046952 := by omega
    exact leaf_single_20 n h_eq
  · -- Case % 23 = 20
    have h_eq : n = 183784672 := by omega
    exact leaf_single_21 n h_eq
  · -- Case % 23 = 21
    have h_eq : n = 344522392 := by omega
    exact leaf_single_22 n h_eq
  · -- Case % 23 = 22
    have h_eq : n = 43139167 := by omega
    exact leaf_single_23 n h_eq

lemma solve_tree_node_2_23 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19 : (2 * n + 1) % 19 = 0) (h_mod_29 : (2 * n + 1) % 29 = 0) (h_mod_17 : (2 * n + 1) % 17 = 5) (h_mod_23_lt : (2 * n + 1) % 23 < 23) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 23
  · -- Case % 23 = 0
    have h_eq : n = 339794812 := by omega
    exact leaf_single_24 n h_eq
  · -- Case % 23 = 1
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^11 % 23 := by omega
    have hk2 : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) (2^11) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 11 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 2
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^1 % 23 := by omega
    have hk2 : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) (2^1) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 1 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 3
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^8 % 23 := by omega
    have hk2 : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) (2^8) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 8 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 4
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^2 % 23 := by omega
    have hk2 : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) (2^2) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 2 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 5
    have h_eq : n = 219241522 := by omega
    exact leaf_single_25 n h_eq
  · -- Case % 23 = 6
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^9 % 23 := by omega
    have hk2 : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) (2^9) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 9 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 7
    have h_eq : n = 78596017 := by omega
    exact leaf_single_26 n h_eq
  · -- Case % 23 = 8
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^3 % 23 := by omega
    have hk2 : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) (2^3) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 3 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 9
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^5 % 23 := by omega
    have hk2 : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) (2^5) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 5 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 10
    have h_eq : n = 98688232 := by omega
    exact leaf_single_27 n h_eq
  · -- Case % 23 = 11
    have h_eq : n = 259425952 := by omega
    exact leaf_single_28 n h_eq
  · -- Case % 23 = 12
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^10 % 23 := by omega
    have hk2 : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) (2^10) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 10 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 13
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^7 % 23 := by omega
    have hk2 : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) (2^7) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 7 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 14
    have h_eq : n = 279518167 := by omega
    exact leaf_single_29 n h_eq
  · -- Case % 23 = 15
    have h_eq : n = 440255887 := by omega
    exact leaf_single_30 n h_eq
  · -- Case % 23 = 16
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^4 % 23 := by omega
    have hk2 : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) (2^4) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 4 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 17
    have h_eq : n = 299610382 := by omega
    exact leaf_single_31 n h_eq
  · -- Case % 23 = 18
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^6 % 23 := by omega
    have hk2 : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) (2^6) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 6 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 19
    have h_eq : n = 158964877 := by omega
    exact leaf_single_32 n h_eq
  · -- Case % 23 = 20
    have h_eq : n = 319702597 := by omega
    exact leaf_single_33 n h_eq
  · -- Case % 23 = 21
    have h_eq : n = 18319372 := by omega
    exact leaf_single_34 n h_eq
  · -- Case % 23 = 22
    have h_eq : n = 179057092 := by omega
    exact leaf_single_35 n h_eq

lemma solve_tree_node_3_23 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19 : (2 * n + 1) % 19 = 0) (h_mod_29 : (2 * n + 1) % 29 = 0) (h_mod_17 : (2 * n + 1) % 17 = 6) (h_mod_23_lt : (2 * n + 1) % 23 < 23) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 23
  · -- Case % 23 = 0
    have h_eq : n = 176693302 := by omega
    exact leaf_single_36 n h_eq
  · -- Case % 23 = 1
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^11 % 23 := by omega
    have hk2 : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) (2^11) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 11 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 2
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^1 % 23 := by omega
    have hk2 : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) (2^1) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 1 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 3
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^8 % 23 := by omega
    have hk2 : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) (2^8) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 8 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 4
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^2 % 23 := by omega
    have hk2 : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) (2^2) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 2 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 5
    have h_eq : n = 56140012 := by omega
    exact leaf_single_37 n h_eq
  · -- Case % 23 = 6
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^9 % 23 := by omega
    have hk2 : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) (2^9) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 9 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 7
    have h_eq : n = 377615452 := by omega
    exact leaf_single_38 n h_eq
  · -- Case % 23 = 8
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^3 % 23 := by omega
    have hk2 : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) (2^3) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 3 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 9
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^5 % 23 := by omega
    have hk2 : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) (2^5) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 5 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 10
    have h_eq : n = 397707667 := by omega
    exact leaf_single_39 n h_eq
  · -- Case % 23 = 11
    have h_eq : n = 96324442 := by omega
    exact leaf_single_40 n h_eq
  · -- Case % 23 = 12
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^10 % 23 := by omega
    have hk2 : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) (2^10) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 10 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 13
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^7 % 23 := by omega
    have hk2 : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) (2^7) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 7 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 14
    have h_eq : n = 116416657 := by omega
    exact leaf_single_41 n h_eq
  · -- Case % 23 = 15
    have h_eq : n = 277154377 := by omega
    exact leaf_single_42 n h_eq
  · -- Case % 23 = 16
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^4 % 23 := by omega
    have hk2 : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) (2^4) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 4 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 17
    have h_eq : n = 136508872 := by omega
    exact leaf_single_43 n h_eq
  · -- Case % 23 = 18
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^6 % 23 := by omega
    have hk2 : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) (2^6) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 6 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 19
    have h_eq : n = 457984312 := by omega
    exact leaf_single_44 n h_eq
  · -- Case % 23 = 20
    have h_eq : n = 156601087 := by omega
    exact leaf_single_45 n h_eq
  · -- Case % 23 = 21
    have h_eq : n = 317338807 := by omega
    exact leaf_single_46 n h_eq
  · -- Case % 23 = 22
    have h_eq : n = 15955582 := by omega
    exact leaf_single_47 n h_eq

lemma solve_tree_node_4_23 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19 : (2 * n + 1) % 19 = 0) (h_mod_29 : (2 * n + 1) % 29 = 0) (h_mod_17 : (2 * n + 1) % 17 = 7) (h_mod_23_lt : (2 * n + 1) % 23 < 23) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 23
  · -- Case % 23 = 0
    have h_eq : n = 13591792 := by omega
    exact leaf_single_48 n h_eq
  · -- Case % 23 = 1
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^11 % 23 := by omega
    have hk2 : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) (2^11) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 11 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 2
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^1 % 23 := by omega
    have hk2 : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) (2^1) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 1 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 3
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^8 % 23 := by omega
    have hk2 : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) (2^8) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 8 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 4
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^2 % 23 := by omega
    have hk2 : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) (2^2) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 2 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 5
    have h_eq : n = 355159447 := by omega
    exact leaf_single_49 n h_eq
  · -- Case % 23 = 6
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^9 % 23 := by omega
    have hk2 : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) (2^9) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 9 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 7
    have h_eq : n = 214513942 := by omega
    exact leaf_single_50 n h_eq
  · -- Case % 23 = 8
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^3 % 23 := by omega
    have hk2 : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) (2^3) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 3 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 9
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^5 % 23 := by omega
    have hk2 : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) (2^5) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 5 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 10
    have h_eq : n = 234606157 := by omega
    exact leaf_single_51 n h_eq
  · -- Case % 23 = 11
    have h_eq : n = 395343877 := by omega
    exact leaf_single_52 n h_eq
  · -- Case % 23 = 12
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^10 % 23 := by omega
    have hk2 : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) (2^10) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 10 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 13
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^7 % 23 := by omega
    have hk2 : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) (2^7) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 7 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 14
    have h_eq : n = 415436092 := by omega
    exact leaf_single_53 n h_eq
  · -- Case % 23 = 15
    have h_eq : n = 114052867 := by omega
    exact leaf_single_54 n h_eq
  · -- Case % 23 = 16
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^4 % 23 := by omega
    have hk2 : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) (2^4) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 4 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 17
    have h_eq : n = 435528307 := by omega
    exact leaf_single_55 n h_eq
  · -- Case % 23 = 18
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^6 % 23 := by omega
    have hk2 : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) (2^6) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 6 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 19
    have h_eq : n = 294882802 := by omega
    exact leaf_single_56 n h_eq
  · -- Case % 23 = 20
    have h_eq : n = 455620522 := by omega
    exact leaf_single_57 n h_eq
  · -- Case % 23 = 21
    have h_eq : n = 154237297 := by omega
    exact leaf_single_58 n h_eq
  · -- Case % 23 = 22
    have h_eq : n = 314975017 := by omega
    exact leaf_single_59 n h_eq

lemma solve_tree_node_5_23 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19 : (2 * n + 1) % 19 = 0) (h_mod_29 : (2 * n + 1) % 29 = 0) (h_mod_17 : (2 * n + 1) % 17 = 10) (h_mod_23_lt : (2 * n + 1) % 23 < 23) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 23
  · -- Case % 23 = 0
    have h_eq : n = 448529152 := by omega
    exact leaf_single_60 n h_eq
  · -- Case % 23 = 1
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^11 % 23 := by omega
    have hk2 : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) (2^11) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 11 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 2
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^1 % 23 := by omega
    have hk2 : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) (2^1) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 1 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 3
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^8 % 23 := by omega
    have hk2 : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) (2^8) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 8 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 4
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^2 % 23 := by omega
    have hk2 : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) (2^2) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 2 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 5
    have h_eq : n = 327975862 := by omega
    exact leaf_single_61 n h_eq
  · -- Case % 23 = 6
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^9 % 23 := by omega
    have hk2 : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) (2^9) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 9 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 7
    have h_eq : n = 187330357 := by omega
    exact leaf_single_62 n h_eq
  · -- Case % 23 = 8
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^3 % 23 := by omega
    have hk2 : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) (2^3) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 3 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 9
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^5 % 23 := by omega
    have hk2 : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) (2^5) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 5 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 10
    have h_eq : n = 207422572 := by omega
    exact leaf_single_63 n h_eq
  · -- Case % 23 = 11
    have h_eq : n = 368160292 := by omega
    exact leaf_single_64 n h_eq
  · -- Case % 23 = 12
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^10 % 23 := by omega
    have hk2 : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) (2^10) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 10 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 13
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^7 % 23 := by omega
    have hk2 : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) (2^7) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 7 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 14
    have h_eq : n = 388252507 := by omega
    exact leaf_single_65 n h_eq
  · -- Case % 23 = 15
    have h_eq : n = 86869282 := by omega
    exact leaf_single_66 n h_eq
  · -- Case % 23 = 16
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^4 % 23 := by omega
    have hk2 : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) (2^4) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 4 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 17
    have h_eq : n = 408344722 := by omega
    exact leaf_single_67 n h_eq
  · -- Case % 23 = 18
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^6 % 23 := by omega
    have hk2 : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) (2^6) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 6 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 19
    have h_eq : n = 267699217 := by omega
    exact leaf_single_68 n h_eq
  · -- Case % 23 = 20
    have h_eq : n = 428436937 := by omega
    exact leaf_single_69 n h_eq
  · -- Case % 23 = 21
    have h_eq : n = 127053712 := by omega
    exact leaf_single_70 n h_eq
  · -- Case % 23 = 22
    have h_eq : n = 287791432 := by omega
    exact leaf_single_71 n h_eq

lemma solve_tree_node_6_23 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19 : (2 * n + 1) % 19 = 0) (h_mod_29 : (2 * n + 1) % 29 = 0) (h_mod_17 : (2 * n + 1) % 17 = 11) (h_mod_23_lt : (2 * n + 1) % 23 < 23) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 23
  · -- Case % 23 = 0
    have h_eq : n = 285427642 := by omega
    exact leaf_single_72 n h_eq
  · -- Case % 23 = 1
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^11 % 23 := by omega
    have hk2 : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) (2^11) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 11 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 2
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^1 % 23 := by omega
    have hk2 : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) (2^1) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 1 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 3
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^8 % 23 := by omega
    have hk2 : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) (2^8) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 8 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 4
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^2 % 23 := by omega
    have hk2 : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) (2^2) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 2 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 5
    have h_eq : n = 164874352 := by omega
    exact leaf_single_73 n h_eq
  · -- Case % 23 = 6
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^9 % 23 := by omega
    have hk2 : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) (2^9) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 9 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 7
    have h_eq : n = 24228847 := by omega
    exact leaf_single_74 n h_eq
  · -- Case % 23 = 8
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^3 % 23 := by omega
    have hk2 : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) (2^3) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 3 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 9
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^5 % 23 := by omega
    have hk2 : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) (2^5) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 5 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 10
    have h_eq : n = 44321062 := by omega
    exact leaf_single_75 n h_eq
  · -- Case % 23 = 11
    have h_eq : n = 205058782 := by omega
    exact leaf_single_76 n h_eq
  · -- Case % 23 = 12
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^10 % 23 := by omega
    have hk2 : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) (2^10) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 10 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 13
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^7 % 23 := by omega
    have hk2 : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) (2^7) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 7 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 14
    have h_eq : n = 225150997 := by omega
    exact leaf_single_77 n h_eq
  · -- Case % 23 = 15
    have h_eq : n = 385888717 := by omega
    exact leaf_single_78 n h_eq
  · -- Case % 23 = 16
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^4 % 23 := by omega
    have hk2 : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) (2^4) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 4 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 17
    have h_eq : n = 245243212 := by omega
    exact leaf_single_79 n h_eq
  · -- Case % 23 = 18
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^6 % 23 := by omega
    have hk2 : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) (2^6) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 6 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 19
    have h_eq : n = 104597707 := by omega
    exact leaf_single_80 n h_eq
  · -- Case % 23 = 20
    have h_eq : n = 265335427 := by omega
    exact leaf_single_81 n h_eq
  · -- Case % 23 = 21
    have h_eq : n = 426073147 := by omega
    exact leaf_single_82 n h_eq
  · -- Case % 23 = 22
    have h_eq : n = 124689922 := by omega
    exact leaf_single_83 n h_eq

lemma solve_tree_node_7_23 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19 : (2 * n + 1) % 19 = 0) (h_mod_29 : (2 * n + 1) % 29 = 0) (h_mod_17 : (2 * n + 1) % 17 = 12) (h_mod_23_lt : (2 * n + 1) % 23 < 23) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 23
  · -- Case % 23 = 0
    have h_eq : n = 122326132 := by omega
    exact leaf_single_84 n h_eq
  · -- Case % 23 = 1
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^11 % 23 := by omega
    have hk2 : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) (2^11) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 11 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 2
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^1 % 23 := by omega
    have hk2 : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) (2^1) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 1 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 3
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^8 % 23 := by omega
    have hk2 : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) (2^8) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 8 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 4
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^2 % 23 := by omega
    have hk2 : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) (2^2) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 2 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 5
    have h_eq : n = 1772842 := by omega
    exact leaf_single_85 n h_eq
  · -- Case % 23 = 6
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^9 % 23 := by omega
    have hk2 : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) (2^9) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 9 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 7
    have h_eq : n = 323248282 := by omega
    exact leaf_single_86 n h_eq
  · -- Case % 23 = 8
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^3 % 23 := by omega
    have hk2 : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) (2^3) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 3 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 9
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^5 % 23 := by omega
    have hk2 : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) (2^5) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 5 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 10
    have h_eq : n = 343340497 := by omega
    exact leaf_single_87 n h_eq
  · -- Case % 23 = 11
    have h_eq : n = 41957272 := by omega
    exact leaf_single_88 n h_eq
  · -- Case % 23 = 12
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^10 % 23 := by omega
    have hk2 : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) (2^10) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 10 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 13
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^7 % 23 := by omega
    have hk2 : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) (2^7) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 7 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 14
    have h_eq : n = 62049487 := by omega
    exact leaf_single_89 n h_eq
  · -- Case % 23 = 15
    have h_eq : n = 222787207 := by omega
    exact leaf_single_90 n h_eq
  · -- Case % 23 = 16
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^4 % 23 := by omega
    have hk2 : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) (2^4) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 4 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 17
    have h_eq : n = 82141702 := by omega
    exact leaf_single_91 n h_eq
  · -- Case % 23 = 18
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^6 % 23 := by omega
    have hk2 : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) (2^6) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 6 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 19
    have h_eq : n = 403617142 := by omega
    exact leaf_single_92 n h_eq
  · -- Case % 23 = 20
    have h_eq : n = 102233917 := by omega
    exact leaf_single_93 n h_eq
  · -- Case % 23 = 21
    have h_eq : n = 262971637 := by omega
    exact leaf_single_94 n h_eq
  · -- Case % 23 = 22
    have h_eq : n = 423709357 := by omega
    exact leaf_single_95 n h_eq

lemma solve_tree_node_8_23 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19 : (2 * n + 1) % 19 = 0) (h_mod_29 : (2 * n + 1) % 29 = 0) (h_mod_17 : (2 * n + 1) % 17 = 14) (h_mod_23_lt : (2 * n + 1) % 23 < 23) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 23
  · -- Case % 23 = 0
    have h_eq : n = 258244057 := by omega
    exact leaf_single_96 n h_eq
  · -- Case % 23 = 1
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^11 % 23 := by omega
    have hk2 : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) (2^11) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 11 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 2
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^1 % 23 := by omega
    have hk2 : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) (2^1) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 1 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 3
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^8 % 23 := by omega
    have hk2 : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) (2^8) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 8 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 4
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^2 % 23 := by omega
    have hk2 : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) (2^2) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 2 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 5
    have h_eq : n = 137690767 := by omega
    exact leaf_single_97 n h_eq
  · -- Case % 23 = 6
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^9 % 23 := by omega
    have hk2 : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) (2^9) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 9 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 7
    have h_eq : n = 459166207 := by omega
    exact leaf_single_98 n h_eq
  · -- Case % 23 = 8
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^3 % 23 := by omega
    have hk2 : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) (2^3) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 3 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 9
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^5 % 23 := by omega
    have hk2 : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) (2^5) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 5 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 10
    have h_eq : n = 17137477 := by omega
    exact leaf_single_99 n h_eq
  · -- Case % 23 = 11
    have h_eq : n = 177875197 := by omega
    exact leaf_single_100 n h_eq
  · -- Case % 23 = 12
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^10 % 23 := by omega
    have hk2 : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) (2^10) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 10 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 13
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^7 % 23 := by omega
    have hk2 : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) (2^7) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 7 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 14
    have h_eq : n = 197967412 := by omega
    exact leaf_single_101 n h_eq
  · -- Case % 23 = 15
    have h_eq : n = 358705132 := by omega
    exact leaf_single_102 n h_eq
  · -- Case % 23 = 16
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^4 % 23 := by omega
    have hk2 : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) (2^4) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 4 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 17
    have h_eq : n = 218059627 := by omega
    exact leaf_single_103 n h_eq
  · -- Case % 23 = 18
    have h_mod_23_eq : (2 * n + 1) % 23 = 2^6 % 23 := by omega
    have hk2 : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    have h_gt : 23 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) (2^6) 23 4111 2048 23 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_23 n 6 hn (by decide) hk2 h_mod_23_eq h_gt h1
  · -- Case % 23 = 19
    have h_eq : n = 77414122 := by omega
    exact leaf_single_104 n h_eq
  · -- Case % 23 = 20
    have h_eq : n = 238151842 := by omega
    exact leaf_single_105 n h_eq
  · -- Case % 23 = 21
    have h_eq : n = 398889562 := by omega
    exact leaf_single_106 n h_eq
  · -- Case % 23 = 22
    have h_eq : n = 97506337 := by omega
    exact leaf_single_107 n h_eq

lemma solve_tree_node_9_17 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19 : (2 * n + 1) % 19 = 0) (h_mod_29 : (2 * n + 1) % 29 = 0) (h_mod_17_lt : (2 * n + 1) % 17 < 17) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 17
  · -- Case % 17 = 0
    have h_eq_17 : (2 * n + 1) % 17 = 0 := by omega
    exact solve_tree_node_0_23 n hn h_mod_3 h_mod_5 h_mod_11 h_mod_13 h_mod_19 h_mod_29 h_eq_17 (Nat.mod_lt _ (by decide))
  · -- Case % 17 = 1
    have h_mod_17_eq : (2 * n + 1) % 17 = 2^8 % 17 := by omega
    have hk2 : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    have h_gt : 17 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) (2^8) 17 4111 2048 17 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_17 n 8 hn (by decide) hk2 h_mod_17_eq h_gt h1
  · -- Case % 17 = 2
    have h_mod_17_eq : (2 * n + 1) % 17 = 2^1 % 17 := by omega
    have hk2 : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    have h_gt : 17 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) (2^1) 17 4111 2048 17 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_17 n 1 hn (by decide) hk2 h_mod_17_eq h_gt h1
  · -- Case % 17 = 3
    have h_eq_17 : (2 * n + 1) % 17 = 3 := by omega
    exact solve_tree_node_1_23 n hn h_mod_3 h_mod_5 h_mod_11 h_mod_13 h_mod_19 h_mod_29 h_eq_17 (Nat.mod_lt _ (by decide))
  · -- Case % 17 = 4
    have h_mod_17_eq : (2 * n + 1) % 17 = 2^2 % 17 := by omega
    have hk2 : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    have h_gt : 17 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) (2^2) 17 4111 2048 17 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_17 n 2 hn (by decide) hk2 h_mod_17_eq h_gt h1
  · -- Case % 17 = 5
    have h_eq_17 : (2 * n + 1) % 17 = 5 := by omega
    exact solve_tree_node_2_23 n hn h_mod_3 h_mod_5 h_mod_11 h_mod_13 h_mod_19 h_mod_29 h_eq_17 (Nat.mod_lt _ (by decide))
  · -- Case % 17 = 6
    have h_eq_17 : (2 * n + 1) % 17 = 6 := by omega
    exact solve_tree_node_3_23 n hn h_mod_3 h_mod_5 h_mod_11 h_mod_13 h_mod_19 h_mod_29 h_eq_17 (Nat.mod_lt _ (by decide))
  · -- Case % 17 = 7
    have h_eq_17 : (2 * n + 1) % 17 = 7 := by omega
    exact solve_tree_node_4_23 n hn h_mod_3 h_mod_5 h_mod_11 h_mod_13 h_mod_19 h_mod_29 h_eq_17 (Nat.mod_lt _ (by decide))
  · -- Case % 17 = 8
    have h_mod_17_eq : (2 * n + 1) % 17 = 2^3 % 17 := by omega
    have hk2 : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    have h_gt : 17 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) (2^3) 17 4111 2048 17 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_17 n 3 hn (by decide) hk2 h_mod_17_eq h_gt h1
  · -- Case % 17 = 9
    have h_mod_17_eq : (2 * n + 1) % 17 = 2^7 % 17 := by omega
    have hk2 : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    have h_gt : 17 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) (2^7) 17 4111 2048 17 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_17 n 7 hn (by decide) hk2 h_mod_17_eq h_gt h1
  · -- Case % 17 = 10
    have h_eq_17 : (2 * n + 1) % 17 = 10 := by omega
    exact solve_tree_node_5_23 n hn h_mod_3 h_mod_5 h_mod_11 h_mod_13 h_mod_19 h_mod_29 h_eq_17 (Nat.mod_lt _ (by decide))
  · -- Case % 17 = 11
    have h_eq_17 : (2 * n + 1) % 17 = 11 := by omega
    exact solve_tree_node_6_23 n hn h_mod_3 h_mod_5 h_mod_11 h_mod_13 h_mod_19 h_mod_29 h_eq_17 (Nat.mod_lt _ (by decide))
  · -- Case % 17 = 12
    have h_eq_17 : (2 * n + 1) % 17 = 12 := by omega
    exact solve_tree_node_7_23 n hn h_mod_3 h_mod_5 h_mod_11 h_mod_13 h_mod_19 h_mod_29 h_eq_17 (Nat.mod_lt _ (by decide))
  · -- Case % 17 = 13
    have h_mod_17_eq : (2 * n + 1) % 17 = 2^6 % 17 := by omega
    have hk2 : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    have h_gt : 17 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) (2^6) 17 4111 2048 17 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_17 n 6 hn (by decide) hk2 h_mod_17_eq h_gt h1
  · -- Case % 17 = 14
    have h_eq_17 : (2 * n + 1) % 17 = 14 := by omega
    exact solve_tree_node_8_23 n hn h_mod_3 h_mod_5 h_mod_11 h_mod_13 h_mod_19 h_mod_29 h_eq_17 (Nat.mod_lt _ (by decide))
  · -- Case % 17 = 15
    have h_mod_17_eq : (2 * n + 1) % 17 = 2^5 % 17 := by omega
    have hk2 : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    have h_gt : 17 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) (2^5) 17 4111 2048 17 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_17 n 5 hn (by decide) hk2 h_mod_17_eq h_gt h1
  · -- Case % 17 = 16
    have h_mod_17_eq : (2 * n + 1) % 17 = 2^4 % 17 := by omega
    have hk2 : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    have h_gt : 17 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) (2^4) 17 4111 2048 17 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_17 n 4 hn (by decide) hk2 h_mod_17_eq h_gt h1

lemma solve_tree_node_10_29 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19 : (2 * n + 1) % 19 = 0) (h_mod_29_lt : (2 * n + 1) % 29 < 29) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 29
  · -- Case % 29 = 0
    have h_eq_29 : (2 * n + 1) % 29 = 0 := by omega
    exact solve_tree_node_9_17 n hn h_mod_3 h_mod_5 h_mod_11 h_mod_13 h_mod_19 h_eq_29 (Nat.mod_lt _ (by decide))
  · -- Case % 29 = 1
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^28 % 29 := by omega
    have hn_large : 2 * n + 1 ≥ 268435457 := by omega
    have hk2 : 2^28 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^28) 268435457 268435456 hn_large (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^28 := gt_of_ge (2 * n + 1) (2^28) 29 268435457 268435456 29 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^28 := h1_of_ge (2 * n + 1) (2^28) 268435457 268435456 hn_large (by decide) (by decide)
    exact leaf_covered_template_29 n 28 hn_large (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 2
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^1 % 29 := by omega
    have hk2 : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) (2^1) 29 4111 2048 29 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_29 n 1 hn (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 3
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^5 % 29 := by omega
    have hk2 : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) (2^5) 29 4111 2048 29 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_29 n 5 hn (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 4
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^2 % 29 := by omega
    have hk2 : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) (2^2) 29 4111 2048 29 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_29 n 2 hn (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 5
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^22 % 29 := by omega
    have hn_large : 2 * n + 1 ≥ 4194305 := by omega
    have hk2 : 2^22 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^22) 4194305 4194304 hn_large (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^22 := gt_of_ge (2 * n + 1) (2^22) 29 4194305 4194304 29 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^22 := h1_of_ge (2 * n + 1) (2^22) 4194305 4194304 hn_large (by decide) (by decide)
    exact leaf_covered_template_29 n 22 hn_large (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 6
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^6 % 29 := by omega
    have hk2 : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) (2^6) 29 4111 2048 29 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_29 n 6 hn (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 7
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^12 % 29 := by omega
    have hn_large : 2 * n + 1 ≥ 4097 := by omega
    have hk2 : 2^12 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^12) 4097 4096 hn_large (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^12 := gt_of_ge (2 * n + 1) (2^12) 29 4097 4096 29 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^12 := h1_of_ge (2 * n + 1) (2^12) 4097 4096 hn_large (by decide) (by decide)
    exact leaf_covered_template_29 n 12 hn_large (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 8
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^3 % 29 := by omega
    have hk2 : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) (2^3) 29 4111 2048 29 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_29 n 3 hn (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 9
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^10 % 29 := by omega
    have hk2 : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) (2^10) 29 4111 2048 29 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_29 n 10 hn (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 10
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^23 % 29 := by omega
    have hn_large : 2 * n + 1 ≥ 8388609 := by omega
    have hk2 : 2^23 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^23) 8388609 8388608 hn_large (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^23 := gt_of_ge (2 * n + 1) (2^23) 29 8388609 8388608 29 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^23 := h1_of_ge (2 * n + 1) (2^23) 8388609 8388608 hn_large (by decide) (by decide)
    exact leaf_covered_template_29 n 23 hn_large (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 11
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^25 % 29 := by omega
    have hn_large : 2 * n + 1 ≥ 33554433 := by omega
    have hk2 : 2^25 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^25) 33554433 33554432 hn_large (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^25 := gt_of_ge (2 * n + 1) (2^25) 29 33554433 33554432 29 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^25 := h1_of_ge (2 * n + 1) (2^25) 33554433 33554432 hn_large (by decide) (by decide)
    exact leaf_covered_template_29 n 25 hn_large (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 12
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^7 % 29 := by omega
    have hk2 : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) (2^7) 29 4111 2048 29 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_29 n 7 hn (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 13
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^18 % 29 := by omega
    have hn_large : 2 * n + 1 ≥ 262145 := by omega
    have hk2 : 2^18 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^18) 262145 262144 hn_large (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^18 := gt_of_ge (2 * n + 1) (2^18) 29 262145 262144 29 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^18 := h1_of_ge (2 * n + 1) (2^18) 262145 262144 hn_large (by decide) (by decide)
    exact leaf_covered_template_29 n 18 hn_large (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 14
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^13 % 29 := by omega
    have hn_large : 2 * n + 1 ≥ 8193 := by omega
    have hk2 : 2^13 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^13) 8193 8192 hn_large (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^13 := gt_of_ge (2 * n + 1) (2^13) 29 8193 8192 29 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^13 := h1_of_ge (2 * n + 1) (2^13) 8193 8192 hn_large (by decide) (by decide)
    exact leaf_covered_template_29 n 13 hn_large (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 15
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^27 % 29 := by omega
    have hn_large : 2 * n + 1 ≥ 134217729 := by omega
    have hk2 : 2^27 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^27) 134217729 134217728 hn_large (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^27 := gt_of_ge (2 * n + 1) (2^27) 29 134217729 134217728 29 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^27 := h1_of_ge (2 * n + 1) (2^27) 134217729 134217728 hn_large (by decide) (by decide)
    exact leaf_covered_template_29 n 27 hn_large (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 16
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^4 % 29 := by omega
    have hk2 : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) (2^4) 29 4111 2048 29 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_29 n 4 hn (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 17
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^21 % 29 := by omega
    have hn_large : 2 * n + 1 ≥ 2097153 := by omega
    have hk2 : 2^21 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^21) 2097153 2097152 hn_large (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^21 := gt_of_ge (2 * n + 1) (2^21) 29 2097153 2097152 29 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^21 := h1_of_ge (2 * n + 1) (2^21) 2097153 2097152 hn_large (by decide) (by decide)
    exact leaf_covered_template_29 n 21 hn_large (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 18
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^11 % 29 := by omega
    have hk2 : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) (2^11) 29 4111 2048 29 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_29 n 11 hn (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 19
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^9 % 29 := by omega
    have hk2 : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) (2^9) 29 4111 2048 29 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_29 n 9 hn (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 20
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^24 % 29 := by omega
    have hn_large : 2 * n + 1 ≥ 16777217 := by omega
    have hk2 : 2^24 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^24) 16777217 16777216 hn_large (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^24 := gt_of_ge (2 * n + 1) (2^24) 29 16777217 16777216 29 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^24 := h1_of_ge (2 * n + 1) (2^24) 16777217 16777216 hn_large (by decide) (by decide)
    exact leaf_covered_template_29 n 24 hn_large (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 21
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^17 % 29 := by omega
    have hn_large : 2 * n + 1 ≥ 131073 := by omega
    have hk2 : 2^17 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^17) 131073 131072 hn_large (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^17 := gt_of_ge (2 * n + 1) (2^17) 29 131073 131072 29 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^17 := h1_of_ge (2 * n + 1) (2^17) 131073 131072 hn_large (by decide) (by decide)
    exact leaf_covered_template_29 n 17 hn_large (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 22
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^26 % 29 := by omega
    have hn_large : 2 * n + 1 ≥ 67108865 := by omega
    have hk2 : 2^26 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^26) 67108865 67108864 hn_large (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^26 := gt_of_ge (2 * n + 1) (2^26) 29 67108865 67108864 29 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^26 := h1_of_ge (2 * n + 1) (2^26) 67108865 67108864 hn_large (by decide) (by decide)
    exact leaf_covered_template_29 n 26 hn_large (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 23
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^20 % 29 := by omega
    have hn_large : 2 * n + 1 ≥ 1048577 := by omega
    have hk2 : 2^20 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^20) 1048577 1048576 hn_large (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^20 := gt_of_ge (2 * n + 1) (2^20) 29 1048577 1048576 29 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^20 := h1_of_ge (2 * n + 1) (2^20) 1048577 1048576 hn_large (by decide) (by decide)
    exact leaf_covered_template_29 n 20 hn_large (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 24
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^8 % 29 := by omega
    have hk2 : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) (2^8) 29 4111 2048 29 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_29 n 8 hn (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 25
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^16 % 29 := by omega
    have hn_large : 2 * n + 1 ≥ 65537 := by omega
    have hk2 : 2^16 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^16) 65537 65536 hn_large (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^16 := gt_of_ge (2 * n + 1) (2^16) 29 65537 65536 29 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^16 := h1_of_ge (2 * n + 1) (2^16) 65537 65536 hn_large (by decide) (by decide)
    exact leaf_covered_template_29 n 16 hn_large (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 26
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^19 % 29 := by omega
    have hn_large : 2 * n + 1 ≥ 524289 := by omega
    have hk2 : 2^19 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^19) 524289 524288 hn_large (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^19 := gt_of_ge (2 * n + 1) (2^19) 29 524289 524288 29 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^19 := h1_of_ge (2 * n + 1) (2^19) 524289 524288 hn_large (by decide) (by decide)
    exact leaf_covered_template_29 n 19 hn_large (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 27
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^15 % 29 := by omega
    have hn_large : 2 * n + 1 ≥ 32769 := by omega
    have hk2 : 2^15 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^15) 32769 32768 hn_large (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^15 := gt_of_ge (2 * n + 1) (2^15) 29 32769 32768 29 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^15 := h1_of_ge (2 * n + 1) (2^15) 32769 32768 hn_large (by decide) (by decide)
    exact leaf_covered_template_29 n 15 hn_large (by decide) hk2 h_mod_29_eq h_gt h1
  · -- Case % 29 = 28
    have h_mod_29_eq : (2 * n + 1) % 29 = 2^14 % 29 := by omega
    have hn_large : 2 * n + 1 ≥ 16385 := by omega
    have hk2 : 2^14 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^14) 16385 16384 hn_large (by decide) (by decide)
    have h_gt : 29 < 2 * n + 1 - 2^14 := gt_of_ge (2 * n + 1) (2^14) 29 16385 16384 29 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^14 := h1_of_ge (2 * n + 1) (2^14) 16385 16384 hn_large (by decide) (by decide)
    exact leaf_covered_template_29 n 14 hn_large (by decide) hk2 h_mod_29_eq h_gt h1

lemma solve_tree_node_11_19 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13 : (2 * n + 1) % 13 = 0) (h_mod_19_lt : (2 * n + 1) % 19 < 19) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 19
  · -- Case % 19 = 0
    have h_eq_19 : (2 * n + 1) % 19 = 0 := by omega
    exact solve_tree_node_10_29 n hn h_mod_3 h_mod_5 h_mod_11 h_mod_13 h_eq_19 (Nat.mod_lt _ (by decide))
  · -- Case % 19 = 1
    have h_mod_19_eq : (2 * n + 1) % 19 = 2^18 % 19 := by omega
    have hn_large : 2 * n + 1 ≥ 262145 := by omega
    have hk2 : 2^18 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^18) 262145 262144 hn_large (by decide) (by decide)
    have h_gt : 19 < 2 * n + 1 - 2^18 := gt_of_ge (2 * n + 1) (2^18) 19 262145 262144 19 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^18 := h1_of_ge (2 * n + 1) (2^18) 262145 262144 hn_large (by decide) (by decide)
    exact leaf_covered_template_19 n 18 hn_large (by decide) hk2 h_mod_19_eq h_gt h1
  · -- Case % 19 = 2
    have h_mod_19_eq : (2 * n + 1) % 19 = 2^1 % 19 := by omega
    have hk2 : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    have h_gt : 19 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) (2^1) 19 4111 2048 19 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_19 n 1 hn (by decide) hk2 h_mod_19_eq h_gt h1
  · -- Case % 19 = 3
    have h_mod_19_eq : (2 * n + 1) % 19 = 2^13 % 19 := by omega
    have hn_large : 2 * n + 1 ≥ 8193 := by omega
    have hk2 : 2^13 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^13) 8193 8192 hn_large (by decide) (by decide)
    have h_gt : 19 < 2 * n + 1 - 2^13 := gt_of_ge (2 * n + 1) (2^13) 19 8193 8192 19 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^13 := h1_of_ge (2 * n + 1) (2^13) 8193 8192 hn_large (by decide) (by decide)
    exact leaf_covered_template_19 n 13 hn_large (by decide) hk2 h_mod_19_eq h_gt h1
  · -- Case % 19 = 4
    have h_mod_19_eq : (2 * n + 1) % 19 = 2^2 % 19 := by omega
    have hk2 : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    have h_gt : 19 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) (2^2) 19 4111 2048 19 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_19 n 2 hn (by decide) hk2 h_mod_19_eq h_gt h1
  · -- Case % 19 = 5
    have h_mod_19_eq : (2 * n + 1) % 19 = 2^16 % 19 := by omega
    have hn_large : 2 * n + 1 ≥ 65537 := by omega
    have hk2 : 2^16 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^16) 65537 65536 hn_large (by decide) (by decide)
    have h_gt : 19 < 2 * n + 1 - 2^16 := gt_of_ge (2 * n + 1) (2^16) 19 65537 65536 19 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^16 := h1_of_ge (2 * n + 1) (2^16) 65537 65536 hn_large (by decide) (by decide)
    exact leaf_covered_template_19 n 16 hn_large (by decide) hk2 h_mod_19_eq h_gt h1
  · -- Case % 19 = 6
    have h_mod_19_eq : (2 * n + 1) % 19 = 2^14 % 19 := by omega
    have hn_large : 2 * n + 1 ≥ 16385 := by omega
    have hk2 : 2^14 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^14) 16385 16384 hn_large (by decide) (by decide)
    have h_gt : 19 < 2 * n + 1 - 2^14 := gt_of_ge (2 * n + 1) (2^14) 19 16385 16384 19 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^14 := h1_of_ge (2 * n + 1) (2^14) 16385 16384 hn_large (by decide) (by decide)
    exact leaf_covered_template_19 n 14 hn_large (by decide) hk2 h_mod_19_eq h_gt h1
  · -- Case % 19 = 7
    have h_mod_19_eq : (2 * n + 1) % 19 = 2^6 % 19 := by omega
    have hk2 : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    have h_gt : 19 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) (2^6) 19 4111 2048 19 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_19 n 6 hn (by decide) hk2 h_mod_19_eq h_gt h1
  · -- Case % 19 = 8
    have h_mod_19_eq : (2 * n + 1) % 19 = 2^3 % 19 := by omega
    have hk2 : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    have h_gt : 19 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) (2^3) 19 4111 2048 19 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_19 n 3 hn (by decide) hk2 h_mod_19_eq h_gt h1
  · -- Case % 19 = 9
    have h_mod_19_eq : (2 * n + 1) % 19 = 2^8 % 19 := by omega
    have hk2 : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    have h_gt : 19 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) (2^8) 19 4111 2048 19 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_19 n 8 hn (by decide) hk2 h_mod_19_eq h_gt h1
  · -- Case % 19 = 10
    have h_mod_19_eq : (2 * n + 1) % 19 = 2^17 % 19 := by omega
    have hn_large : 2 * n + 1 ≥ 131073 := by omega
    have hk2 : 2^17 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^17) 131073 131072 hn_large (by decide) (by decide)
    have h_gt : 19 < 2 * n + 1 - 2^17 := gt_of_ge (2 * n + 1) (2^17) 19 131073 131072 19 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^17 := h1_of_ge (2 * n + 1) (2^17) 131073 131072 hn_large (by decide) (by decide)
    exact leaf_covered_template_19 n 17 hn_large (by decide) hk2 h_mod_19_eq h_gt h1
  · -- Case % 19 = 11
    have h_mod_19_eq : (2 * n + 1) % 19 = 2^12 % 19 := by omega
    have hn_large : 2 * n + 1 ≥ 4097 := by omega
    have hk2 : 2^12 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^12) 4097 4096 hn_large (by decide) (by decide)
    have h_gt : 19 < 2 * n + 1 - 2^12 := gt_of_ge (2 * n + 1) (2^12) 19 4097 4096 19 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^12 := h1_of_ge (2 * n + 1) (2^12) 4097 4096 hn_large (by decide) (by decide)
    exact leaf_covered_template_19 n 12 hn_large (by decide) hk2 h_mod_19_eq h_gt h1
  · -- Case % 19 = 12
    have h_mod_19_eq : (2 * n + 1) % 19 = 2^15 % 19 := by omega
    have hn_large : 2 * n + 1 ≥ 32769 := by omega
    have hk2 : 2^15 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^15) 32769 32768 hn_large (by decide) (by decide)
    have h_gt : 19 < 2 * n + 1 - 2^15 := gt_of_ge (2 * n + 1) (2^15) 19 32769 32768 19 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^15 := h1_of_ge (2 * n + 1) (2^15) 32769 32768 hn_large (by decide) (by decide)
    exact leaf_covered_template_19 n 15 hn_large (by decide) hk2 h_mod_19_eq h_gt h1
  · -- Case % 19 = 13
    have h_mod_19_eq : (2 * n + 1) % 19 = 2^5 % 19 := by omega
    have hk2 : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    have h_gt : 19 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) (2^5) 19 4111 2048 19 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_19 n 5 hn (by decide) hk2 h_mod_19_eq h_gt h1
  · -- Case % 19 = 14
    have h_mod_19_eq : (2 * n + 1) % 19 = 2^7 % 19 := by omega
    have hk2 : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    have h_gt : 19 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) (2^7) 19 4111 2048 19 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_19 n 7 hn (by decide) hk2 h_mod_19_eq h_gt h1
  · -- Case % 19 = 15
    have h_mod_19_eq : (2 * n + 1) % 19 = 2^11 % 19 := by omega
    have hk2 : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    have h_gt : 19 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) (2^11) 19 4111 2048 19 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_19 n 11 hn (by decide) hk2 h_mod_19_eq h_gt h1
  · -- Case % 19 = 16
    have h_mod_19_eq : (2 * n + 1) % 19 = 2^4 % 19 := by omega
    have hk2 : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    have h_gt : 19 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) (2^4) 19 4111 2048 19 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_19 n 4 hn (by decide) hk2 h_mod_19_eq h_gt h1
  · -- Case % 19 = 17
    have h_mod_19_eq : (2 * n + 1) % 19 = 2^10 % 19 := by omega
    have hk2 : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    have h_gt : 19 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) (2^10) 19 4111 2048 19 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_19 n 10 hn (by decide) hk2 h_mod_19_eq h_gt h1
  · -- Case % 19 = 18
    have h_mod_19_eq : (2 * n + 1) % 19 = 2^9 % 19 := by omega
    have hk2 : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    have h_gt : 19 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) (2^9) 19 4111 2048 19 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_19 n 9 hn (by decide) hk2 h_mod_19_eq h_gt h1

lemma solve_tree_node_12_13 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11 : (2 * n + 1) % 11 = 0) (h_mod_13_lt : (2 * n + 1) % 13 < 13) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 13
  · -- Case % 13 = 0
    have h_eq_13 : (2 * n + 1) % 13 = 0 := by omega
    exact solve_tree_node_11_19 n hn h_mod_3 h_mod_5 h_mod_11 h_eq_13 (Nat.mod_lt _ (by decide))
  · -- Case % 13 = 1
    have h_mod_13_eq : (2 * n + 1) % 13 = 2^12 % 13 := by omega
    have hn_large : 2 * n + 1 ≥ 4097 := by omega
    have hk2 : 2^12 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^12) 4097 4096 hn_large (by decide) (by decide)
    have h_gt : 13 < 2 * n + 1 - 2^12 := gt_of_ge (2 * n + 1) (2^12) 13 4097 4096 13 hn_large (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^12 := h1_of_ge (2 * n + 1) (2^12) 4097 4096 hn_large (by decide) (by decide)
    exact leaf_covered_template_13 n 12 hn_large (by decide) hk2 h_mod_13_eq h_gt h1
  · -- Case % 13 = 2
    have h_mod_13_eq : (2 * n + 1) % 13 = 2^1 % 13 := by omega
    have hk2 : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    have h_gt : 13 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) (2^1) 13 4111 2048 13 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_13 n 1 hn (by decide) hk2 h_mod_13_eq h_gt h1
  · -- Case % 13 = 3
    have h_mod_13_eq : (2 * n + 1) % 13 = 2^4 % 13 := by omega
    have hk2 : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    have h_gt : 13 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) (2^4) 13 4111 2048 13 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_13 n 4 hn (by decide) hk2 h_mod_13_eq h_gt h1
  · -- Case % 13 = 4
    have h_mod_13_eq : (2 * n + 1) % 13 = 2^2 % 13 := by omega
    have hk2 : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    have h_gt : 13 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) (2^2) 13 4111 2048 13 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_13 n 2 hn (by decide) hk2 h_mod_13_eq h_gt h1
  · -- Case % 13 = 5
    have h_mod_13_eq : (2 * n + 1) % 13 = 2^9 % 13 := by omega
    have hk2 : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    have h_gt : 13 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) (2^9) 13 4111 2048 13 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_13 n 9 hn (by decide) hk2 h_mod_13_eq h_gt h1
  · -- Case % 13 = 6
    have h_mod_13_eq : (2 * n + 1) % 13 = 2^5 % 13 := by omega
    have hk2 : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    have h_gt : 13 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) (2^5) 13 4111 2048 13 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_13 n 5 hn (by decide) hk2 h_mod_13_eq h_gt h1
  · -- Case % 13 = 7
    have h_mod_13_eq : (2 * n + 1) % 13 = 2^11 % 13 := by omega
    have hk2 : 2^11 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    have h_gt : 13 < 2 * n + 1 - 2^11 := gt_of_ge (2 * n + 1) (2^11) 13 4111 2048 13 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^11 := h1_of_ge (2 * n + 1) (2^11) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_13 n 11 hn (by decide) hk2 h_mod_13_eq h_gt h1
  · -- Case % 13 = 8
    have h_mod_13_eq : (2 * n + 1) % 13 = 2^3 % 13 := by omega
    have hk2 : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    have h_gt : 13 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) (2^3) 13 4111 2048 13 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_13 n 3 hn (by decide) hk2 h_mod_13_eq h_gt h1
  · -- Case % 13 = 9
    have h_mod_13_eq : (2 * n + 1) % 13 = 2^8 % 13 := by omega
    have hk2 : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    have h_gt : 13 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) (2^8) 13 4111 2048 13 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_13 n 8 hn (by decide) hk2 h_mod_13_eq h_gt h1
  · -- Case % 13 = 10
    have h_mod_13_eq : (2 * n + 1) % 13 = 2^10 % 13 := by omega
    have hk2 : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    have h_gt : 13 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) (2^10) 13 4111 2048 13 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_13 n 10 hn (by decide) hk2 h_mod_13_eq h_gt h1
  · -- Case % 13 = 11
    have h_mod_13_eq : (2 * n + 1) % 13 = 2^7 % 13 := by omega
    have hk2 : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    have h_gt : 13 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) (2^7) 13 4111 2048 13 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_13 n 7 hn (by decide) hk2 h_mod_13_eq h_gt h1
  · -- Case % 13 = 12
    have h_mod_13_eq : (2 * n + 1) % 13 = 2^6 % 13 := by omega
    have hk2 : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    have h_gt : 13 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) (2^6) 13 4111 2048 13 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_13 n 6 hn (by decide) hk2 h_mod_13_eq h_gt h1

lemma solve_tree_node_13_11 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5 : (2 * n + 1) % 5 = 0) (h_mod_11_lt : (2 * n + 1) % 11 < 11) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 11
  · -- Case % 11 = 0
    have h_eq_11 : (2 * n + 1) % 11 = 0 := by omega
    exact solve_tree_node_12_13 n hn h_mod_3 h_mod_5 h_eq_11 (Nat.mod_lt _ (by decide))
  · -- Case % 11 = 1
    have h_mod_11_eq : (2 * n + 1) % 11 = 2^10 % 11 := by omega
    have hk2 : 2^10 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    have h_gt : 11 < 2 * n + 1 - 2^10 := gt_of_ge (2 * n + 1) (2^10) 11 4111 2048 11 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^10 := h1_of_ge (2 * n + 1) (2^10) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_11 n 10 hn (by decide) hk2 h_mod_11_eq h_gt h1
  · -- Case % 11 = 2
    have h_mod_11_eq : (2 * n + 1) % 11 = 2^1 % 11 := by omega
    have hk2 : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    have h_gt : 11 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) (2^1) 11 4111 2048 11 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_11 n 1 hn (by decide) hk2 h_mod_11_eq h_gt h1
  · -- Case % 11 = 3
    have h_mod_11_eq : (2 * n + 1) % 11 = 2^8 % 11 := by omega
    have hk2 : 2^8 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    have h_gt : 11 < 2 * n + 1 - 2^8 := gt_of_ge (2 * n + 1) (2^8) 11 4111 2048 11 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^8 := h1_of_ge (2 * n + 1) (2^8) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_11 n 8 hn (by decide) hk2 h_mod_11_eq h_gt h1
  · -- Case % 11 = 4
    have h_mod_11_eq : (2 * n + 1) % 11 = 2^2 % 11 := by omega
    have hk2 : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    have h_gt : 11 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) (2^2) 11 4111 2048 11 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_11 n 2 hn (by decide) hk2 h_mod_11_eq h_gt h1
  · -- Case % 11 = 5
    have h_mod_11_eq : (2 * n + 1) % 11 = 2^4 % 11 := by omega
    have hk2 : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    have h_gt : 11 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) (2^4) 11 4111 2048 11 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_11 n 4 hn (by decide) hk2 h_mod_11_eq h_gt h1
  · -- Case % 11 = 6
    have h_mod_11_eq : (2 * n + 1) % 11 = 2^9 % 11 := by omega
    have hk2 : 2^9 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    have h_gt : 11 < 2 * n + 1 - 2^9 := gt_of_ge (2 * n + 1) (2^9) 11 4111 2048 11 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^9 := h1_of_ge (2 * n + 1) (2^9) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_11 n 9 hn (by decide) hk2 h_mod_11_eq h_gt h1
  · -- Case % 11 = 7
    have h_mod_11_eq : (2 * n + 1) % 11 = 2^7 % 11 := by omega
    have hk2 : 2^7 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    have h_gt : 11 < 2 * n + 1 - 2^7 := gt_of_ge (2 * n + 1) (2^7) 11 4111 2048 11 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^7 := h1_of_ge (2 * n + 1) (2^7) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_11 n 7 hn (by decide) hk2 h_mod_11_eq h_gt h1
  · -- Case % 11 = 8
    have h_mod_11_eq : (2 * n + 1) % 11 = 2^3 % 11 := by omega
    have hk2 : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    have h_gt : 11 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) (2^3) 11 4111 2048 11 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_11 n 3 hn (by decide) hk2 h_mod_11_eq h_gt h1
  · -- Case % 11 = 9
    have h_mod_11_eq : (2 * n + 1) % 11 = 2^6 % 11 := by omega
    have hk2 : 2^6 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    have h_gt : 11 < 2 * n + 1 - 2^6 := gt_of_ge (2 * n + 1) (2^6) 11 4111 2048 11 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^6 := h1_of_ge (2 * n + 1) (2^6) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_11 n 6 hn (by decide) hk2 h_mod_11_eq h_gt h1
  · -- Case % 11 = 10
    have h_mod_11_eq : (2 * n + 1) % 11 = 2^5 % 11 := by omega
    have hk2 : 2^5 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    have h_gt : 11 < 2 * n + 1 - 2^5 := gt_of_ge (2 * n + 1) (2^5) 11 4111 2048 11 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^5 := h1_of_ge (2 * n + 1) (2^5) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_11 n 5 hn (by decide) hk2 h_mod_11_eq h_gt h1

lemma solve_tree_node_14_5 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3 : (2 * n + 1) % 3 = 0) (h_mod_5_lt : (2 * n + 1) % 5 < 5) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 5
  · -- Case % 5 = 0
    have h_eq_5 : (2 * n + 1) % 5 = 0 := by omega
    exact solve_tree_node_13_11 n hn h_mod_3 h_eq_5 (Nat.mod_lt _ (by decide))
  · -- Case % 5 = 1
    have h_mod_5_eq : (2 * n + 1) % 5 = 2^4 % 5 := by omega
    have hk2 : 2^4 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    have h_gt : 5 < 2 * n + 1 - 2^4 := gt_of_ge (2 * n + 1) (2^4) 5 4111 2048 5 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^4 := h1_of_ge (2 * n + 1) (2^4) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_5 n 4 hn (by decide) hk2 h_mod_5_eq h_gt h1
  · -- Case % 5 = 2
    have h_mod_5_eq : (2 * n + 1) % 5 = 2^1 % 5 := by omega
    have hk2 : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    have h_gt : 5 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) (2^1) 5 4111 2048 5 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_5 n 1 hn (by decide) hk2 h_mod_5_eq h_gt h1
  · -- Case % 5 = 3
    have h_mod_5_eq : (2 * n + 1) % 5 = 2^3 % 5 := by omega
    have hk2 : 2^3 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    have h_gt : 5 < 2 * n + 1 - 2^3 := gt_of_ge (2 * n + 1) (2^3) 5 4111 2048 5 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^3 := h1_of_ge (2 * n + 1) (2^3) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_5 n 3 hn (by decide) hk2 h_mod_5_eq h_gt h1
  · -- Case % 5 = 4
    have h_mod_5_eq : (2 * n + 1) % 5 = 2^2 % 5 := by omega
    have hk2 : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    have h_gt : 5 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) (2^2) 5 4111 2048 5 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_5 n 2 hn (by decide) hk2 h_mod_5_eq h_gt h1

lemma solve_tree_node_15_3 (n : ℕ) (hn : 2 * n + 1 ≥ 4111) (h_mod_3_lt : (2 * n + 1) % 3 < 3) : A282459 n > 0 := by
  interval_cases (2 * n + 1) % 3
  · -- Case % 3 = 0
    have h_eq_3 : (2 * n + 1) % 3 = 0 := by omega
    exact solve_tree_node_14_5 n hn h_eq_3 (Nat.mod_lt _ (by decide))
  · -- Case % 3 = 1
    have h_mod_3_eq : (2 * n + 1) % 3 = 2^2 % 3 := by omega
    have hk2 : 2^2 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    have h_gt : 3 < 2 * n + 1 - 2^2 := gt_of_ge (2 * n + 1) (2^2) 3 4111 2048 3 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^2 := h1_of_ge (2 * n + 1) (2^2) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_3 n 2 hn (by decide) hk2 h_mod_3_eq h_gt h1
  · -- Case % 3 = 2
    have h_mod_3_eq : (2 * n + 1) % 3 = 2^1 % 3 := by omega
    have hk2 : 2^1 ≤ 2 * n + 1 := hk_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    have h_gt : 3 < 2 * n + 1 - 2^1 := gt_of_ge (2 * n + 1) (2^1) 3 4111 2048 3 hn (by decide) (by decide) (by decide)
    have h1 : 1 < 2 * n + 1 - 2^1 := h1_of_ge (2 * n + 1) (2^1) 4111 2048 hn (by decide) (by decide)
    exact leaf_covered_template_3 n 1 hn (by decide) hk2 h_mod_3_eq h_gt h1

/--
It is conjectured that `A282459 n > 0` for all `n > 52`.
-/
theorem oeis_282459_conjecture_0 : ∀ n : ℕ, n > 52 → A282459 n > 0 := by
  intro n hn
  rcases lt_or_ge n 2055 with h_small | h_large
  · have h_in : n ∈ Finset.Ico 53 2055 := by
      rw [Finset.mem_Ico]
      omega
    have h_cert := cert_valid n h_in
    dsimp at h_cert
    have hk_in : certificate_k n ∈ Finset.Icc 1 (log 2 (2 * n + 1)) := by
      rw [Finset.mem_Icc]
      exact ⟨h_cert.1, h_cert.2.1⟩
    have h_comp : 1 < 2 * n + 1 - 2 ^ (certificate_k n) ∧ ¬ Nat.Prime (2 * n + 1 - 2 ^ (certificate_k n)) := by
      exact composite_of_proper_divisor (2 * n + 1) (certificate_k n) (certificate_d n) h_cert.2.2.1 h_cert.2.2.2.1 h_cert.2.2.2.2
    exact A282459_pos_of_exists n (certificate_k n) hk_in h_comp
  · have hN : 2 * n + 1 ≥ 4111 := by omega
    have h_mod_3 : (2 * n + 1) % 3 < 3 := Nat.mod_lt _ (by decide)
    exact solve_tree_node_15_3 n hN h_mod_3
