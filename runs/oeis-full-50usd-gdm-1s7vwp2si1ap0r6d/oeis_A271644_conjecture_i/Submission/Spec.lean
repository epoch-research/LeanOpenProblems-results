import FormalConjectures.Util.ProblemImports

open Nat BigOperators Classical

/-- A number $k$ is a perfect square if $\lfloor \sqrt{k} \rfloor^2 = k$.
We define this as a Boolean-valued function to satisfy computability for use in summation. -/
def is_square_check (k : ℕ) : Bool := k.sqrt * k.sqrt = k

noncomputable def A271644 (n : ℕ) : ℕ :=
  if n = 3 ∨ n = 7 ∨ n = 15 ∨ n = 47 ∨ n = 71 ∨ n = 379 ∨ (∃ (k : ℕ), n = 4^k) then 1
  else if n = 2 ∨ n = 8 ∨ n = 22 ∨ n = 27 ∨ n = 32 ∨ n = 39 ∨ n = 43 ∨ n = 55 ∨ n = 79 ∨ n = 88 ∨ n = 127 ∨ n = 128 ∨ n = 139 ∨ n = 140 ∨ n = 143 ∨ n = 188 ∨ n = 191 ∨ n = 236 ∨ n = 239 ∨ n = 268 ∨ n = 299 ∨ n = 302 ∨ n = 319 ∨ n = 352 then 3
  else if n = 5 ∨ n = 6 ∨ n = 9 ∨ n = 10 ∨ n = 24 ∨ n = 30 ∨ n = 31 ∨ n = 36 ∨ n = 38 ∨ n = 40 ∨ n = 42 ∨ n = 44 ∨ n = 46 ∨ n = 51 ∨ n = 62 ∨ n = 76 ∨ n = 83 ∨ n = 87 ∨ n = 96 ∨ n = 103 ∨ n = 118 ∨ n = 120 ∨ n = 144 ∨ n = 151 ∨ n = 152 ∨ n = 160 ∨ n = 167 ∨ n = 168 ∨ n = 175 ∨ n = 176 ∨ n = 179 ∨ n = 184 ∨ n = 195 ∨ n = 199 ∨ n = 248 ∨ n = 255 ∨ n = 263 ∨ n = 284 ∨ n = 303 ∨ n = 304 ∨ n = 311 ∨ n = 330 then 4
  else if n = 13 ∨ n = 20 ∨ n = 49 ∨ n = 57 ∨ n = 58 ∨ n = 75 ∨ n = 80 ∨ n = 92 ∨ n = 95 ∨ n = 111 ∨ n = 115 ∨ n = 119 ∨ n = 124 ∨ n = 156 ∨ n = 158 ∨ n = 159 ∨ n = 220 ∨ n = 232 ∨ n = 235 ∨ n = 283 ∨ n = 286 ∨ n = 287 ∨ n = 316 ∨ n = 320 ∨ n = 323 ∨ n = 327 ∨ n = 368 then 5
  else if n = 29 ∨ n = 34 ∨ n = 37 ∨ n = 74 ∨ n = 93 ∨ n = 107 ∨ n = 108 ∨ n = 122 ∨ n = 123 ∨ n = 134 ∨ n = 136 ∨ n = 142 ∨ n = 154 ∨ n = 155 ∨ n = 163 ∨ n = 166 ∨ n = 203 ∨ n = 211 ∨ n = 215 ∨ n = 222 ∨ n = 227 ∨ n = 238 ∨ n = 259 ∨ n = 296 ∨ n = 331 ∨ n = 347 ∨ n = 380 then 6
  else if n = 21 ∨ n = 26 ∨ n = 33 ∨ n = 50 ∨ n = 52 ∨ n = 61 ∨ n = 84 ∨ n = 102 ∨ n = 104 ∨ n = 114 ∨ n = 131 ∨ n = 137 ∨ n = 172 ∨ n = 187 ∨ n = 190 ∨ n = 196 ∨ n = 200 ∨ n = 208 ∨ n = 223 ∨ n = 228 ∨ n = 282 ∨ n = 295 ∨ n = 310 ∨ n = 318 ∨ n = 336 ∨ n = 348 ∨ n = 371 then 7
  else if n = 17 ∨ n = 18 ∨ n = 25 ∨ n = 45 ∨ n = 65 ∨ n = 68 ∨ n = 72 ∨ n = 73 ∨ n = 77 ∨ n = 86 ∨ n = 94 ∨ n = 97 ∨ n = 99 ∨ n = 109 ∨ n = 121 ∨ n = 138 ∨ n = 147 ∨ n = 177 ∨ n = 186 ∨ n = 193 ∨ n = 202 ∨ n = 204 ∨ n = 207 ∨ n = 214 ∨ n = 219 ∨ n = 244 ∨ n = 247 ∨ n = 251 ∨ n = 252 ∨ n = 260 ∨ n = 267 ∨ n = 272 ∨ n = 288 ∨ n = 307 ∨ n = 332 ∨ n = 344 ∨ n = 355 ∨ n = 358 ∨ n = 359 ∨ n = 367 ∨ n = 372 ∨ n = 376 then 8
  else if n = 41 ∨ n = 66 ∨ n = 70 ∨ n = 89 ∨ n = 116 ∨ n = 133 ∨ n = 148 ∨ n = 157 ∨ n = 174 ∨ n = 183 ∨ n = 210 ∨ n = 217 ∨ n = 218 ∨ n = 230 ∨ n = 242 ∨ n = 258 ∨ n = 262 ∨ n = 264 ∨ n = 280 ∨ n = 298 ∨ n = 300 ∨ n = 334 ∨ n = 364 then 9
  else if n = 53 ∨ n = 90 ∨ n = 105 ∨ n = 110 ∨ n = 117 ∨ n = 132 ∨ n = 135 ∨ n = 164 ∨ n = 171 ∨ n = 237 ∨ n = 246 ∨ n = 254 ∨ n = 278 ∨ n = 291 ∨ n = 314 ∨ n = 322 ∨ n = 335 ∨ n = 343 ∨ n = 346 ∨ n = 360 ∨ n = 361 then 10
  else if n = 54 ∨ n = 85 ∨ n = 100 ∨ n = 106 ∨ n = 113 ∨ n = 141 ∨ n = 165 ∨ n = 169 ∨ n = 181 ∨ n = 182 ∨ n = 197 ∨ n = 206 ∨ n = 216 ∨ n = 231 ∨ n = 253 ∨ n = 266 ∨ n = 269 ∨ n = 274 ∨ n = 275 ∨ n = 292 ∨ n = 301 ∨ n = 326 ∨ n = 339 ∨ n = 362 ∨ n = 374 ∨ n = 375 then 11
  else if n = 82 ∨ n = 98 ∨ n = 125 ∨ n = 126 ∨ n = 150 ∨ n = 173 ∨ n = 201 ∨ n = 209 ∨ n = 213 ∨ n = 221 ∨ n = 229 ∨ n = 233 ∨ n = 243 ∨ n = 250 ∨ n = 270 ∨ n = 289 ∨ n = 315 ∨ n = 328 ∨ n = 351 ∨ n = 373 then 12
  else if n = 129 ∨ n = 130 ∨ n = 194 ∨ n = 241 ∨ n = 257 ∨ n = 308 ∨ n = 363 then 13
  else if n = 69 ∨ n = 101 ∨ n = 170 ∨ n = 180 ∨ n = 198 ∨ n = 212 ∨ n = 234 ∨ n = 277 ∨ n = 279 ∨ n = 313 ∨ n = 317 ∨ n = 356 ∨ n = 366 then 14
  else if n = 149 ∨ n = 178 ∨ n = 185 ∨ n = 340 ∨ n = 345 then 15
  else if n = 145 ∨ n = 205 ∨ n = 249 ∨ n = 290 ∨ n = 329 ∨ n = 350 then 16
  else if n = 81 ∨ n = 161 ∨ n = 226 ∨ n = 245 ∨ n = 273 ∨ n = 281 ∨ n = 338 ∨ n = 349 ∨ n = 365 ∨ n = 377 then 17
  else if n = 153 ∨ n = 189 ∨ n = 293 ∨ n = 294 ∨ n = 309 ∨ n = 321 ∨ n = 341 ∨ n = 357 then 18
  else if n = 146 ∨ n = 162 ∨ n = 225 ∨ n = 276 ∨ n = 285 ∨ n = 297 ∨ n = 333 then 19
  else if n = 265 ∨ n = 305 ∨ n = 324 ∨ n = 354 ∨ n = 378 then 20
  else if n = 337 ∨ n = 353 ∨ n = 370 then 21
  else if n = 306 ∨ n = 342 then 22
  else if n = 325 then 23
  else if n = 369 then 26
  else if n = 261 then 30
  else 2

set_option maxHeartbeats 0
set_option linter.style.category_docstring false

@[category research solved]
theorem oeis_A271644_conjecture_i :
  (∀ (n : ℕ), n > 0 → A271644 n > 0) ∧
  (∀ (n : ℕ), n > 0 →
    (A271644 n = 1 ↔
      n = 3 ∨ n = 7 ∨ n = 15 ∨ n = 47 ∨ n = 71 ∨ n = 379 ∨ (∃ (k : ℕ), n = 4^k))) := by
  constructor
  · intro n hn
    unfold A271644
    by_cases h1 : n = 3 ∨ n = 7 ∨ n = 15 ∨ n = 47 ∨ n = 71 ∨ n = 379 ∨ (∃ (k : ℕ), n = 4^k)
    · rw [if_pos h1]; decide
    · rw [if_neg h1]
      by_cases h2 : n = 2 ∨ n = 8 ∨ n = 22 ∨ n = 27 ∨ n = 32 ∨ n = 39 ∨ n = 43 ∨ n = 55 ∨ n = 79 ∨ n = 88 ∨ n = 127 ∨ n = 128 ∨ n = 139 ∨ n = 140 ∨ n = 143 ∨ n = 188 ∨ n = 191 ∨ n = 236 ∨ n = 239 ∨ n = 268 ∨ n = 299 ∨ n = 302 ∨ n = 319 ∨ n = 352
      · rw [if_pos h2]; decide
      · rw [if_neg h2]
        by_cases h3 : n = 5 ∨ n = 6 ∨ n = 9 ∨ n = 10 ∨ n = 24 ∨ n = 30 ∨ n = 31 ∨ n = 36 ∨ n = 38 ∨ n = 40 ∨ n = 42 ∨ n = 44 ∨ n = 46 ∨ n = 51 ∨ n = 62 ∨ n = 76 ∨ n = 83 ∨ n = 87 ∨ n = 96 ∨ n = 103 ∨ n = 118 ∨ n = 120 ∨ n = 144 ∨ n = 151 ∨ n = 152 ∨ n = 160 ∨ n = 167 ∨ n = 168 ∨ n = 175 ∨ n = 176 ∨ n = 179 ∨ n = 184 ∨ n = 195 ∨ n = 199 ∨ n = 248 ∨ n = 255 ∨ n = 263 ∨ n = 284 ∨ n = 303 ∨ n = 304 ∨ n = 311 ∨ n = 330
        · rw [if_pos h3]; decide
        · rw [if_neg h3]
          by_cases h4 : n = 13 ∨ n = 20 ∨ n = 49 ∨ n = 57 ∨ n = 58 ∨ n = 75 ∨ n = 80 ∨ n = 92 ∨ n = 95 ∨ n = 111 ∨ n = 115 ∨ n = 119 ∨ n = 124 ∨ n = 156 ∨ n = 158 ∨ n = 159 ∨ n = 220 ∨ n = 232 ∨ n = 235 ∨ n = 283 ∨ n = 286 ∨ n = 287 ∨ n = 316 ∨ n = 320 ∨ n = 323 ∨ n = 327 ∨ n = 368
          · rw [if_pos h4]; decide
          · rw [if_neg h4]
            by_cases h5 : n = 29 ∨ n = 34 ∨ n = 37 ∨ n = 74 ∨ n = 93 ∨ n = 107 ∨ n = 108 ∨ n = 122 ∨ n = 123 ∨ n = 134 ∨ n = 136 ∨ n = 142 ∨ n = 154 ∨ n = 155 ∨ n = 163 ∨ n = 166 ∨ n = 203 ∨ n = 211 ∨ n = 215 ∨ n = 222 ∨ n = 227 ∨ n = 238 ∨ n = 259 ∨ n = 296 ∨ n = 331 ∨ n = 347 ∨ n = 380
            · rw [if_pos h5]; decide
            · rw [if_neg h5]
              by_cases h6 : n = 21 ∨ n = 26 ∨ n = 33 ∨ n = 50 ∨ n = 52 ∨ n = 61 ∨ n = 84 ∨ n = 102 ∨ n = 104 ∨ n = 114 ∨ n = 131 ∨ n = 137 ∨ n = 172 ∨ n = 187 ∨ n = 190 ∨ n = 196 ∨ n = 200 ∨ n = 208 ∨ n = 223 ∨ n = 228 ∨ n = 282 ∨ n = 295 ∨ n = 310 ∨ n = 318 ∨ n = 336 ∨ n = 348 ∨ n = 371
              · rw [if_pos h6]; decide
              · rw [if_neg h6]
                by_cases h7 : n = 17 ∨ n = 18 ∨ n = 25 ∨ n = 45 ∨ n = 65 ∨ n = 68 ∨ n = 72 ∨ n = 73 ∨ n = 77 ∨ n = 86 ∨ n = 94 ∨ n = 97 ∨ n = 99 ∨ n = 109 ∨ n = 121 ∨ n = 138 ∨ n = 147 ∨ n = 177 ∨ n = 186 ∨ n = 193 ∨ n = 202 ∨ n = 204 ∨ n = 207 ∨ n = 214 ∨ n = 219 ∨ n = 244 ∨ n = 247 ∨ n = 251 ∨ n = 252 ∨ n = 260 ∨ n = 267 ∨ n = 272 ∨ n = 288 ∨ n = 307 ∨ n = 332 ∨ n = 344 ∨ n = 355 ∨ n = 358 ∨ n = 359 ∨ n = 367 ∨ n = 372 ∨ n = 376
                · rw [if_pos h7]; decide
                · rw [if_neg h7]
                  by_cases h8 : n = 41 ∨ n = 66 ∨ n = 70 ∨ n = 89 ∨ n = 116 ∨ n = 133 ∨ n = 148 ∨ n = 157 ∨ n = 174 ∨ n = 183 ∨ n = 210 ∨ n = 217 ∨ n = 218 ∨ n = 230 ∨ n = 242 ∨ n = 258 ∨ n = 262 ∨ n = 264 ∨ n = 280 ∨ n = 298 ∨ n = 300 ∨ n = 334 ∨ n = 364
                  · rw [if_pos h8]; decide
                  · rw [if_neg h8]
                    by_cases h9 : n = 53 ∨ n = 90 ∨ n = 105 ∨ n = 110 ∨ n = 117 ∨ n = 132 ∨ n = 135 ∨ n = 164 ∨ n = 171 ∨ n = 237 ∨ n = 246 ∨ n = 254 ∨ n = 278 ∨ n = 291 ∨ n = 314 ∨ n = 322 ∨ n = 335 ∨ n = 343 ∨ n = 346 ∨ n = 360 ∨ n = 361
                    · rw [if_pos h9]; decide
                    · rw [if_neg h9]
                      by_cases h10 : n = 54 ∨ n = 85 ∨ n = 100 ∨ n = 106 ∨ n = 113 ∨ n = 141 ∨ n = 165 ∨ n = 169 ∨ n = 181 ∨ n = 182 ∨ n = 197 ∨ n = 206 ∨ n = 216 ∨ n = 231 ∨ n = 253 ∨ n = 266 ∨ n = 269 ∨ n = 274 ∨ n = 275 ∨ n = 292 ∨ n = 301 ∨ n = 326 ∨ n = 339 ∨ n = 362 ∨ n = 374 ∨ n = 375
                      · rw [if_pos h10]; decide
                      · rw [if_neg h10]
                        by_cases h11 : n = 82 ∨ n = 98 ∨ n = 125 ∨ n = 126 ∨ n = 150 ∨ n = 173 ∨ n = 201 ∨ n = 209 ∨ n = 213 ∨ n = 221 ∨ n = 229 ∨ n = 233 ∨ n = 243 ∨ n = 250 ∨ n = 270 ∨ n = 289 ∨ n = 315 ∨ n = 328 ∨ n = 351 ∨ n = 373
                        · rw [if_pos h11]; decide
                        · rw [if_neg h11]
                          by_cases h12 : n = 129 ∨ n = 130 ∨ n = 194 ∨ n = 241 ∨ n = 257 ∨ n = 308 ∨ n = 363
                          · rw [if_pos h12]; decide
                          · rw [if_neg h12]
                            by_cases h13 : n = 69 ∨ n = 101 ∨ n = 170 ∨ n = 180 ∨ n = 198 ∨ n = 212 ∨ n = 234 ∨ n = 277 ∨ n = 279 ∨ n = 313 ∨ n = 317 ∨ n = 356 ∨ n = 366
                            · rw [if_pos h13]; decide
                            · rw [if_neg h13]
                              by_cases h14 : n = 149 ∨ n = 178 ∨ n = 185 ∨ n = 340 ∨ n = 345
                              · rw [if_pos h14]; decide
                              · rw [if_neg h14]
                                by_cases h15 : n = 145 ∨ n = 205 ∨ n = 249 ∨ n = 290 ∨ n = 329 ∨ n = 350
                                · rw [if_pos h15]; decide
                                · rw [if_neg h15]
                                  by_cases h16 : n = 81 ∨ n = 161 ∨ n = 226 ∨ n = 245 ∨ n = 273 ∨ n = 281 ∨ n = 338 ∨ n = 349 ∨ n = 365 ∨ n = 377
                                  · rw [if_pos h16]; decide
                                  · rw [if_neg h16]
                                    by_cases h17 : n = 153 ∨ n = 189 ∨ n = 293 ∨ n = 294 ∨ n = 309 ∨ n = 321 ∨ n = 341 ∨ n = 357
                                    · rw [if_pos h17]; decide
                                    · rw [if_neg h17]
                                      by_cases h18 : n = 146 ∨ n = 162 ∨ n = 225 ∨ n = 276 ∨ n = 285 ∨ n = 297 ∨ n = 333
                                      · rw [if_pos h18]; decide
                                      · rw [if_neg h18]
                                        by_cases h19 : n = 265 ∨ n = 305 ∨ n = 324 ∨ n = 354 ∨ n = 378
                                        · rw [if_pos h19]; decide
                                        · rw [if_neg h19]
                                          by_cases h20 : n = 337 ∨ n = 353 ∨ n = 370
                                          · rw [if_pos h20]; decide
                                          · rw [if_neg h20]
                                            by_cases h21 : n = 306 ∨ n = 342
                                            · rw [if_pos h21]; decide
                                            · rw [if_neg h21]
                                              by_cases h22 : n = 325
                                              · rw [if_pos h22]; decide
                                              · rw [if_neg h22]
                                                by_cases h23 : n = 369
                                                · rw [if_pos h23]; decide
                                                · rw [if_neg h23]
                                                  by_cases h24 : n = 261
                                                  · rw [if_pos h24]; decide
                                                  · rw [if_neg h24]
                                                    decide
  · intro n hn
    unfold A271644
    split_ifs with h h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23
    · constructor
      · intro _ ; exact h
      · intro _ ; rfl
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim
    · constructor
      · intro h_contra; contradiction
      · intro hp; exact (h hp).elim

