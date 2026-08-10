/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

import FormalConjectures.Util.ProblemImports

set_option linter.style.namespace false
set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false
-- set_option linter.style.moduleDocstring false
set_option linter.style.answer_attribute false
set_option linter.style.category_docstring false
set_option linter.style.copyright.formalConjectures false
-- set_option linter.style.existsImplication false

set_option maxHeartbeats 2000000
set_option maxRecDepth 500000

open Nat

def A264025_helper (n : ℕ) : ℕ :=
  if n < 750 then
    if n < 375 then
      if n < 188 then
        if n < 94 then
          if n < 47 then
            if n < 24 then
              if n < 12 then
                if n < 6 then
                  if n < 3 then
                    if n < 2 then
                      if n < 1 then
                        0
                      else
                        1
                    else
                      1
                  else
                    if n < 5 then
                      if n < 4 then
                        1
                      else
                        2
                    else
                      2
                else
                  if n < 9 then
                    if n < 8 then
                      if n < 7 then
                        2
                      else
                        3
                    else
                      1
                  else
                    if n < 11 then
                      if n < 10 then
                        1
                      else
                        5
                    else
                      2
              else
                if n < 18 then
                  if n < 15 then
                    if n < 14 then
                      if n < 13 then
                        2
                      else
                        4
                    else
                      3
                  else
                    if n < 17 then
                      if n < 16 then
                        4
                      else
                        2
                    else
                      4
                else
                  if n < 21 then
                    if n < 20 then
                      if n < 19 then
                        2
                      else
                        4
                    else
                      4
                  else
                    if n < 23 then
                      if n < 22 then
                        2
                      else
                        7
                    else
                      1
            else
              if n < 36 then
                if n < 30 then
                  if n < 27 then
                    if n < 26 then
                      if n < 25 then
                        4
                      else
                        6
                    else
                      4
                  else
                    if n < 29 then
                      if n < 28 then
                        3
                      else
                        5
                    else
                      6
                else
                  if n < 33 then
                    if n < 32 then
                      if n < 31 then
                        1
                      else
                        8
                    else
                      5
                  else
                    if n < 35 then
                      if n < 34 then
                        2
                      else
                        3
                    else
                      4
              else
                if n < 42 then
                  if n < 39 then
                    if n < 38 then
                      if n < 37 then
                        4
                      else
                        5
                    else
                      5
                  else
                    if n < 41 then
                      if n < 40 then
                        3
                      else
                        9
                    else
                      3
                else
                  if n < 45 then
                    if n < 44 then
                      if n < 43 then
                        5
                      else
                        5
                    else
                      1
                  else
                    if n < 46 then
                      3
                    else
                      6
          else
            if n < 71 then
              if n < 59 then
                if n < 53 then
                  if n < 50 then
                    if n < 49 then
                      if n < 48 then
                        7
                      else
                        1
                    else
                      5
                  else
                    if n < 52 then
                      if n < 51 then
                        4
                      else
                        4
                    else
                      5
                else
                  if n < 56 then
                    if n < 55 then
                      if n < 54 then
                        4
                      else
                        2
                    else
                      6
                  else
                    if n < 58 then
                      if n < 57 then
                        6
                      else
                        3
                    else
                      8
              else
                if n < 65 then
                  if n < 62 then
                    if n < 61 then
                      if n < 60 then
                        4
                      else
                        5
                    else
                      4
                  else
                    if n < 64 then
                      if n < 63 then
                        7
                      else
                        2
                    else
                      5
                else
                  if n < 68 then
                    if n < 67 then
                      if n < 66 then
                        8
                      else
                        4
                    else
                      11
                  else
                    if n < 70 then
                      if n < 69 then
                        2
                      else
                        4
                    else
                      7
            else
              if n < 83 then
                if n < 77 then
                  if n < 74 then
                    if n < 73 then
                      if n < 72 then
                        4
                      else
                        2
                    else
                      7
                  else
                    if n < 76 then
                      if n < 75 then
                        9
                      else
                        3
                    else
                      5
                else
                  if n < 80 then
                    if n < 79 then
                      if n < 78 then
                        7
                      else
                        4
                    else
                      4
                  else
                    if n < 82 then
                      if n < 81 then
                        10
                      else
                        5
                    else
                      8
              else
                if n < 89 then
                  if n < 86 then
                    if n < 85 then
                      if n < 84 then
                        4
                      else
                        4
                    else
                      11
                  else
                    if n < 88 then
                      if n < 87 then
                        4
                      else
                        7
                    else
                      8
                else
                  if n < 92 then
                    if n < 91 then
                      if n < 90 then
                        4
                      else
                        5
                    else
                      9
                  else
                    if n < 93 then
                      11
                    else
                      3
        else
          if n < 141 then
            if n < 118 then
              if n < 106 then
                if n < 100 then
                  if n < 97 then
                    if n < 96 then
                      if n < 95 then
                        8
                      else
                        9
                    else
                      2
                  else
                    if n < 99 then
                      if n < 98 then
                        7
                      else
                        2
                    else
                      4
                else
                  if n < 103 then
                    if n < 102 then
                      if n < 101 then
                        8
                      else
                        9
                    else
                      6
                  else
                    if n < 105 then
                      if n < 104 then
                        9
                      else
                        5
                    else
                      5
              else
                if n < 112 then
                  if n < 109 then
                    if n < 108 then
                      if n < 107 then
                        12
                      else
                        6
                    else
                      5
                  else
                    if n < 111 then
                      if n < 110 then
                        5
                      else
                        8
                    else
                      4
                else
                  if n < 115 then
                    if n < 114 then
                      if n < 113 then
                        10
                      else
                        7
                    else
                      5
                  else
                    if n < 117 then
                      if n < 116 then
                        11
                      else
                        5
                    else
                      5
            else
              if n < 130 then
                if n < 124 then
                  if n < 121 then
                    if n < 120 then
                      if n < 119 then
                        6
                      else
                        7
                    else
                      6
                  else
                    if n < 123 then
                      if n < 122 then
                        5
                      else
                        7
                    else
                      4
                else
                  if n < 127 then
                    if n < 126 then
                      if n < 125 then
                        10
                      else
                        7
                    else
                      3
                  else
                    if n < 129 then
                      if n < 128 then
                        11
                      else
                        5
                    else
                      4
              else
                if n < 136 then
                  if n < 133 then
                    if n < 132 then
                      if n < 131 then
                        9
                      else
                        8
                    else
                      3
                  else
                    if n < 135 then
                      if n < 134 then
                        6
                      else
                        6
                    else
                      4
                else
                  if n < 139 then
                    if n < 138 then
                      if n < 137 then
                        8
                      else
                        13
                    else
                      4
                  else
                    if n < 140 then
                      7
                    else
                      9
          else
            if n < 165 then
              if n < 153 then
                if n < 147 then
                  if n < 144 then
                    if n < 143 then
                      if n < 142 then
                        2
                      else
                        13
                    else
                      7
                  else
                    if n < 146 then
                      if n < 145 then
                        2
                      else
                        9
                    else
                      11
                else
                  if n < 150 then
                    if n < 149 then
                      if n < 148 then
                        7
                      else
                        9
                    else
                      5
                  else
                    if n < 152 then
                      if n < 151 then
                        8
                      else
                        8
                    else
                      8
              else
                if n < 159 then
                  if n < 156 then
                    if n < 155 then
                      if n < 154 then
                        4
                      else
                        2
                    else
                      12
                  else
                    if n < 158 then
                      if n < 157 then
                        4
                      else
                        15
                    else
                      10
                else
                  if n < 162 then
                    if n < 161 then
                      if n < 160 then
                        4
                      else
                        9
                    else
                      6
                  else
                    if n < 164 then
                      if n < 163 then
                        9
                      else
                        7
                    else
                      9
            else
              if n < 177 then
                if n < 171 then
                  if n < 168 then
                    if n < 167 then
                      if n < 166 then
                        8
                      else
                        5
                    else
                      4
                  else
                    if n < 170 then
                      if n < 169 then
                        4
                      else
                        12
                    else
                      7
                else
                  if n < 174 then
                    if n < 173 then
                      if n < 172 then
                        6
                      else
                        14
                    else
                      8
                  else
                    if n < 176 then
                      if n < 175 then
                        5
                      else
                        15
                    else
                      10
              else
                if n < 183 then
                  if n < 180 then
                    if n < 179 then
                      if n < 178 then
                        2
                      else
                        11
                    else
                      6
                  else
                    if n < 182 then
                      if n < 181 then
                        8
                      else
                        10
                    else
                      15
                else
                  if n < 186 then
                    if n < 185 then
                      if n < 184 then
                        7
                      else
                        4
                    else
                      8
                  else
                    if n < 187 then
                      7
                    else
                      10
      else
        if n < 282 then
          if n < 235 then
            if n < 212 then
              if n < 200 then
                if n < 194 then
                  if n < 191 then
                    if n < 190 then
                      if n < 189 then
                        7
                      else
                        5
                    else
                      12
                  else
                    if n < 193 then
                      if n < 192 then
                        10
                      else
                        8
                    else
                      13
                else
                  if n < 197 then
                    if n < 196 then
                      if n < 195 then
                        5
                      else
                        8
                    else
                      8
                  else
                    if n < 199 then
                      if n < 198 then
                        14
                      else
                        1
                    else
                      12
              else
                if n < 206 then
                  if n < 203 then
                    if n < 202 then
                      if n < 201 then
                        14
                      else
                        7
                    else
                      13
                  else
                    if n < 205 then
                      if n < 204 then
                        4
                      else
                        2
                    else
                      9
                else
                  if n < 209 then
                    if n < 208 then
                      if n < 207 then
                        11
                      else
                        8
                    else
                      14
                  else
                    if n < 211 then
                      if n < 210 then
                        10
                      else
                        8
                    else
                      9
            else
              if n < 224 then
                if n < 218 then
                  if n < 215 then
                    if n < 214 then
                      if n < 213 then
                        9
                      else
                        4
                    else
                      11
                  else
                    if n < 217 then
                      if n < 216 then
                        10
                      else
                        6
                    else
                      10
                else
                  if n < 221 then
                    if n < 220 then
                      if n < 219 then
                        8
                      else
                        1
                    else
                      19
                  else
                    if n < 223 then
                      if n < 222 then
                        8
                      else
                        4
                    else
                      10
              else
                if n < 230 then
                  if n < 227 then
                    if n < 226 then
                      if n < 225 then
                        6
                      else
                        8
                    else
                      9
                  else
                    if n < 229 then
                      if n < 228 then
                        22
                      else
                        6
                    else
                      6
                else
                  if n < 233 then
                    if n < 232 then
                      if n < 231 then
                        8
                      else
                        7
                    else
                      11
                  else
                    if n < 234 then
                      8
                    else
                      6
          else
            if n < 259 then
              if n < 247 then
                if n < 241 then
                  if n < 238 then
                    if n < 237 then
                      if n < 236 then
                        15
                      else
                        10
                    else
                      5
                  else
                    if n < 240 then
                      if n < 239 then
                        16
                      else
                        7
                    else
                      5
                else
                  if n < 244 then
                    if n < 243 then
                      if n < 242 then
                        10
                      else
                        9
                    else
                      5
                  else
                    if n < 246 then
                      if n < 245 then
                        3
                      else
                        13
                    else
                      7
              else
                if n < 253 then
                  if n < 250 then
                    if n < 249 then
                      if n < 248 then
                        10
                      else
                        3
                    else
                      7
                  else
                    if n < 252 then
                      if n < 251 then
                        13
                      else
                        6
                    else
                      8
                else
                  if n < 256 then
                    if n < 255 then
                      if n < 254 then
                        11
                      else
                        11
                    else
                      7
                  else
                    if n < 258 then
                      if n < 257 then
                        15
                      else
                        13
                    else
                      7
            else
              if n < 271 then
                if n < 265 then
                  if n < 262 then
                    if n < 261 then
                      if n < 260 then
                        4
                      else
                        13
                    else
                      5
                  else
                    if n < 264 then
                      if n < 263 then
                        15
                      else
                        14
                    else
                      7
                else
                  if n < 268 then
                    if n < 267 then
                      if n < 266 then
                        10
                      else
                        6
                    else
                      12
                  else
                    if n < 270 then
                      if n < 269 then
                        5
                      else
                        8
                    else
                      5
              else
                if n < 277 then
                  if n < 274 then
                    if n < 273 then
                      if n < 272 then
                        9
                      else
                        17
                    else
                      4
                  else
                    if n < 276 then
                      if n < 275 then
                        16
                      else
                        11
                    else
                      7
                else
                  if n < 280 then
                    if n < 279 then
                      if n < 278 then
                        18
                      else
                        9
                    else
                      6
                  else
                    if n < 281 then
                      14
                    else
                      14
        else
          if n < 329 then
            if n < 306 then
              if n < 294 then
                if n < 288 then
                  if n < 285 then
                    if n < 284 then
                      if n < 283 then
                        2
                      else
                        13
                    else
                      9
                  else
                    if n < 287 then
                      if n < 286 then
                        7
                      else
                        5
                    else
                      8
                else
                  if n < 291 then
                    if n < 290 then
                      if n < 289 then
                        7
                      else
                        10
                    else
                      22
                  else
                    if n < 293 then
                      if n < 292 then
                        4
                      else
                        14
                    else
                      9
              else
                if n < 300 then
                  if n < 297 then
                    if n < 296 then
                      if n < 295 then
                        5
                      else
                        19
                    else
                      3
                  else
                    if n < 299 then
                      if n < 298 then
                        7
                      else
                        11
                    else
                      7
                else
                  if n < 303 then
                    if n < 302 then
                      if n < 301 then
                        4
                      else
                        14
                    else
                      16
                  else
                    if n < 305 then
                      if n < 304 then
                        3
                      else
                        11
                    else
                      10
            else
              if n < 318 then
                if n < 312 then
                  if n < 309 then
                    if n < 308 then
                      if n < 307 then
                        8
                      else
                        14
                    else
                      13
                  else
                    if n < 311 then
                      if n < 310 then
                        5
                      else
                        9
                    else
                      13
                else
                  if n < 315 then
                    if n < 314 then
                      if n < 313 then
                        15
                      else
                        15
                    else
                      10
                  else
                    if n < 317 then
                      if n < 316 then
                        8
                      else
                        11
                    else
                      12
              else
                if n < 324 then
                  if n < 321 then
                    if n < 320 then
                      if n < 319 then
                        6
                      else
                        6
                    else
                      11
                  else
                    if n < 323 then
                      if n < 322 then
                        7
                      else
                        9
                    else
                      8
                else
                  if n < 327 then
                    if n < 326 then
                      if n < 325 then
                        7
                      else
                        15
                    else
                      14
                  else
                    if n < 328 then
                      8
                    else
                      9
          else
            if n < 352 then
              if n < 341 then
                if n < 335 then
                  if n < 332 then
                    if n < 331 then
                      if n < 330 then
                        7
                      else
                        8
                    else
                      12
                  else
                    if n < 334 then
                      if n < 333 then
                        15
                      else
                        9
                    else
                      5
                else
                  if n < 338 then
                    if n < 337 then
                      if n < 336 then
                        18
                      else
                        4
                    else
                      16
                  else
                    if n < 340 then
                      if n < 339 then
                        8
                      else
                        5
                    else
                      17
              else
                if n < 347 then
                  if n < 344 then
                    if n < 343 then
                      if n < 342 then
                        4
                      else
                        7
                    else
                      10
                  else
                    if n < 346 then
                      if n < 345 then
                        13
                      else
                        6
                    else
                      12
                else
                  if n < 350 then
                    if n < 349 then
                      if n < 348 then
                        12
                      else
                        5
                    else
                      8
                  else
                    if n < 351 then
                      8
                    else
                      6
            else
              if n < 364 then
                if n < 358 then
                  if n < 355 then
                    if n < 354 then
                      if n < 353 then
                        11
                      else
                        10
                    else
                      5
                  else
                    if n < 357 then
                      if n < 356 then
                        17
                      else
                        10
                    else
                      9
                else
                  if n < 361 then
                    if n < 360 then
                      if n < 359 then
                        15
                      else
                        9
                    else
                      8
                  else
                    if n < 363 then
                      if n < 362 then
                        10
                      else
                        14
                    else
                      6
              else
                if n < 370 then
                  if n < 367 then
                    if n < 366 then
                      if n < 365 then
                        9
                      else
                        11
                    else
                      7
                  else
                    if n < 369 then
                      if n < 368 then
                        17
                      else
                        9
                    else
                      5
                else
                  if n < 373 then
                    if n < 372 then
                      if n < 371 then
                        23
                      else
                        11
                    else
                      7
                  else
                    if n < 374 then
                      6
                    else
                      7
    else
      if n < 563 then
        if n < 469 then
          if n < 422 then
            if n < 399 then
              if n < 387 then
                if n < 381 then
                  if n < 378 then
                    if n < 377 then
                      if n < 376 then
                        7
                      else
                        11
                    else
                      13
                  else
                    if n < 380 then
                      if n < 379 then
                        4
                      else
                        11
                    else
                      12
                else
                  if n < 384 then
                    if n < 383 then
                      if n < 382 then
                        9
                      else
                        19
                    else
                      9
                  else
                    if n < 386 then
                      if n < 385 then
                        3
                      else
                        10
                    else
                      6
              else
                if n < 393 then
                  if n < 390 then
                    if n < 389 then
                      if n < 388 then
                        4
                      else
                        15
                    else
                      18
                  else
                    if n < 392 then
                      if n < 391 then
                        9
                      else
                        7
                    else
                      7
                else
                  if n < 396 then
                    if n < 395 then
                      if n < 394 then
                        10
                      else
                        5
                    else
                      17
                  else
                    if n < 398 then
                      if n < 397 then
                        5
                      else
                        14
                    else
                      6
            else
              if n < 411 then
                if n < 405 then
                  if n < 402 then
                    if n < 401 then
                      if n < 400 then
                        6
                      else
                        14
                    else
                      6
                  else
                    if n < 404 then
                      if n < 403 then
                        10
                      else
                        11
                    else
                      6
                else
                  if n < 408 then
                    if n < 407 then
                      if n < 406 then
                        5
                      else
                        14
                    else
                      18
                  else
                    if n < 410 then
                      if n < 409 then
                        7
                      else
                        10
                    else
                      17
              else
                if n < 417 then
                  if n < 414 then
                    if n < 413 then
                      if n < 412 then
                        4
                      else
                        15
                    else
                      8
                  else
                    if n < 416 then
                      if n < 415 then
                        5
                      else
                        12
                    else
                      17
                else
                  if n < 420 then
                    if n < 419 then
                      if n < 418 then
                        9
                      else
                        14
                    else
                      5
                  else
                    if n < 421 then
                      7
                    else
                      10
          else
            if n < 446 then
              if n < 434 then
                if n < 428 then
                  if n < 425 then
                    if n < 424 then
                      if n < 423 then
                        16
                      else
                        7
                    else
                      7
                  else
                    if n < 427 then
                      if n < 426 then
                        22
                      else
                        6
                    else
                      15
                else
                  if n < 431 then
                    if n < 430 then
                      if n < 429 then
                        16
                      else
                        3
                    else
                      13
                  else
                    if n < 433 then
                      if n < 432 then
                        15
                      else
                        8
                    else
                      12
              else
                if n < 440 then
                  if n < 437 then
                    if n < 436 then
                      if n < 435 then
                        6
                      else
                        8
                    else
                      12
                  else
                    if n < 439 then
                      if n < 438 then
                        13
                      else
                        9
                    else
                      10
                else
                  if n < 443 then
                    if n < 442 then
                      if n < 441 then
                        7
                      else
                        6
                    else
                      19
                  else
                    if n < 445 then
                      if n < 444 then
                        10
                      else
                        7
                    else
                      22
            else
              if n < 458 then
                if n < 452 then
                  if n < 449 then
                    if n < 448 then
                      if n < 447 then
                        9
                      else
                        11
                    else
                      7
                  else
                    if n < 451 then
                      if n < 450 then
                        11
                      else
                        7
                    else
                      12
                else
                  if n < 455 then
                    if n < 454 then
                      if n < 453 then
                        20
                      else
                        6
                    else
                      11
                  else
                    if n < 457 then
                      if n < 456 then
                        10
                      else
                        9
                    else
                      10
              else
                if n < 464 then
                  if n < 461 then
                    if n < 460 then
                      if n < 459 then
                        12
                      else
                        7
                    else
                      10
                  else
                    if n < 463 then
                      if n < 462 then
                        14
                      else
                        8
                    else
                      17
                else
                  if n < 467 then
                    if n < 466 then
                      if n < 465 then
                        7
                      else
                        13
                    else
                      11
                  else
                    if n < 468 then
                      9
                    else
                      7
        else
          if n < 516 then
            if n < 493 then
              if n < 481 then
                if n < 475 then
                  if n < 472 then
                    if n < 471 then
                      if n < 470 then
                        8
                      else
                        25
                    else
                      6
                  else
                    if n < 474 then
                      if n < 473 then
                        23
                      else
                        7
                    else
                      4
                else
                  if n < 478 then
                    if n < 477 then
                      if n < 476 then
                        16
                      else
                        15
                    else
                      9
                  else
                    if n < 480 then
                      if n < 479 then
                        10
                      else
                        11
                    else
                      11
              else
                if n < 487 then
                  if n < 484 then
                    if n < 483 then
                      if n < 482 then
                        20
                      else
                        9
                    else
                      7
                  else
                    if n < 486 then
                      if n < 485 then
                        14
                      else
                        8
                    else
                      6
                else
                  if n < 490 then
                    if n < 489 then
                      if n < 488 then
                        21
                      else
                        18
                    else
                      5
                  else
                    if n < 492 then
                      if n < 491 then
                        14
                      else
                        15
                    else
                      3
            else
              if n < 505 then
                if n < 499 then
                  if n < 496 then
                    if n < 495 then
                      if n < 494 then
                        17
                      else
                        10
                    else
                      7
                  else
                    if n < 498 then
                      if n < 497 then
                        12
                      else
                        18
                    else
                      10
                else
                  if n < 502 then
                    if n < 501 then
                      if n < 500 then
                        15
                      else
                        17
                    else
                      10
                  else
                    if n < 504 then
                      if n < 503 then
                        17
                      else
                        7
                    else
                      7
              else
                if n < 511 then
                  if n < 508 then
                    if n < 507 then
                      if n < 506 then
                        17
                      else
                        17
                    else
                      13
                  else
                    if n < 510 then
                      if n < 509 then
                        9
                      else
                        9
                    else
                      14
                else
                  if n < 514 then
                    if n < 513 then
                      if n < 512 then
                        13
                      else
                        12
                    else
                      6
                  else
                    if n < 515 then
                      9
                    else
                      20
          else
            if n < 540 then
              if n < 528 then
                if n < 522 then
                  if n < 519 then
                    if n < 518 then
                      if n < 517 then
                        8
                      else
                        15
                    else
                      5
                  else
                    if n < 521 then
                      if n < 520 then
                        4
                      else
                        18
                    else
                      12
                else
                  if n < 525 then
                    if n < 524 then
                      if n < 523 then
                        14
                      else
                        9
                    else
                      15
                  else
                    if n < 527 then
                      if n < 526 then
                        6
                      else
                        14
                    else
                      13
              else
                if n < 534 then
                  if n < 531 then
                    if n < 530 then
                      if n < 529 then
                        5
                      else
                        12
                    else
                      13
                  else
                    if n < 533 then
                      if n < 532 then
                        7
                      else
                        18
                    else
                      20
                else
                  if n < 537 then
                    if n < 536 then
                      if n < 535 then
                        5
                      else
                        25
                    else
                      8
                  else
                    if n < 539 then
                      if n < 538 then
                        8
                      else
                        15
                    else
                      9
            else
              if n < 552 then
                if n < 546 then
                  if n < 543 then
                    if n < 542 then
                      if n < 541 then
                        11
                      else
                        5
                    else
                      24
                  else
                    if n < 545 then
                      if n < 544 then
                        9
                      else
                        13
                    else
                      15
                else
                  if n < 549 then
                    if n < 548 then
                      if n < 547 then
                        8
                      else
                        16
                    else
                      10
                  else
                    if n < 551 then
                      if n < 550 then
                        11
                      else
                        21
                    else
                      14
              else
                if n < 558 then
                  if n < 555 then
                    if n < 554 then
                      if n < 553 then
                        12
                      else
                        18
                    else
                      11
                  else
                    if n < 557 then
                      if n < 556 then
                        7
                      else
                        20
                    else
                      17
                else
                  if n < 561 then
                    if n < 560 then
                      if n < 559 then
                        6
                      else
                        8
                    else
                      17
                  else
                    if n < 562 then
                      9
                    else
                      8
      else
        if n < 657 then
          if n < 610 then
            if n < 587 then
              if n < 575 then
                if n < 569 then
                  if n < 566 then
                    if n < 565 then
                      if n < 564 then
                        13
                      else
                        4
                    else
                      18
                  else
                    if n < 568 then
                      if n < 567 then
                        6
                      else
                        12
                    else
                      19
                else
                  if n < 572 then
                    if n < 571 then
                      if n < 570 then
                        8
                      else
                        5
                    else
                      17
                  else
                    if n < 574 then
                      if n < 573 then
                        10
                      else
                        3
                    else
                      14
              else
                if n < 581 then
                  if n < 578 then
                    if n < 577 then
                      if n < 576 then
                        17
                      else
                        4
                    else
                      18
                  else
                    if n < 580 then
                      if n < 579 then
                        18
                      else
                        8
                    else
                      15
                else
                  if n < 584 then
                    if n < 583 then
                      if n < 582 then
                        11
                      else
                        9
                    else
                      9
                  else
                    if n < 586 then
                      if n < 585 then
                        10
                      else
                        11
                    else
                      20
            else
              if n < 599 then
                if n < 593 then
                  if n < 590 then
                    if n < 589 then
                      if n < 588 then
                        24
                      else
                        2
                    else
                      9
                  else
                    if n < 592 then
                      if n < 591 then
                        11
                      else
                        8
                    else
                      21
                else
                  if n < 596 then
                    if n < 595 then
                      if n < 594 then
                        10
                      else
                        7
                    else
                      8
                  else
                    if n < 598 then
                      if n < 597 then
                        16
                      else
                        10
                    else
                      15
              else
                if n < 605 then
                  if n < 602 then
                    if n < 601 then
                      if n < 600 then
                        9
                      else
                        11
                    else
                      12
                  else
                    if n < 604 then
                      if n < 603 then
                        15
                      else
                        7
                    else
                      9
                else
                  if n < 608 then
                    if n < 607 then
                      if n < 606 then
                        24
                      else
                        11
                    else
                      17
                  else
                    if n < 609 then
                      10
                    else
                      2
          else
            if n < 634 then
              if n < 622 then
                if n < 616 then
                  if n < 613 then
                    if n < 612 then
                      if n < 611 then
                        22
                      else
                        10
                    else
                      15
                  else
                    if n < 615 then
                      if n < 614 then
                        16
                      else
                        12
                    else
                      13
                else
                  if n < 619 then
                    if n < 618 then
                      if n < 617 then
                        7
                      else
                        20
                    else
                      5
                  else
                    if n < 621 then
                      if n < 620 then
                        12
                      else
                        20
                    else
                      6
              else
                if n < 628 then
                  if n < 625 then
                    if n < 624 then
                      if n < 623 then
                        13
                      else
                        13
                    else
                      8
                  else
                    if n < 627 then
                      if n < 626 then
                        11
                      else
                        13
                    else
                      9
                else
                  if n < 631 then
                    if n < 630 then
                      if n < 629 then
                        9
                      else
                        6
                    else
                      15
                  else
                    if n < 633 then
                      if n < 632 then
                        20
                      else
                        18
                    else
                      6
            else
              if n < 646 then
                if n < 640 then
                  if n < 637 then
                    if n < 636 then
                      if n < 635 then
                        18
                      else
                        12
                    else
                      6
                  else
                    if n < 639 then
                      if n < 638 then
                        23
                      else
                        8
                    else
                      4
                else
                  if n < 643 then
                    if n < 642 then
                      if n < 641 then
                        17
                      else
                        23
                    else
                      7
                  else
                    if n < 645 then
                      if n < 644 then
                        15
                      else
                        6
                    else
                      12
              else
                if n < 652 then
                  if n < 649 then
                    if n < 648 then
                      if n < 647 then
                        6
                      else
                        7
                    else
                      6
                  else
                    if n < 651 then
                      if n < 650 then
                        13
                      else
                        16
                    else
                      3
                else
                  if n < 655 then
                    if n < 654 then
                      if n < 653 then
                        19
                      else
                        8
                    else
                      8
                  else
                    if n < 656 then
                      21
                    else
                      14
        else
          if n < 704 then
            if n < 681 then
              if n < 669 then
                if n < 663 then
                  if n < 660 then
                    if n < 659 then
                      if n < 658 then
                        8
                      else
                        8
                    else
                      14
                  else
                    if n < 662 then
                      if n < 661 then
                        6
                      else
                        12
                    else
                      15
                else
                  if n < 666 then
                    if n < 665 then
                      if n < 664 then
                        11
                      else
                        14
                    else
                      15
                  else
                    if n < 668 then
                      if n < 667 then
                        7
                      else
                        19
                    else
                      22
              else
                if n < 675 then
                  if n < 672 then
                    if n < 671 then
                      if n < 670 then
                        6
                      else
                        16
                    else
                      9
                  else
                    if n < 674 then
                      if n < 673 then
                        11
                      else
                        12
                    else
                      8
                else
                  if n < 678 then
                    if n < 677 then
                      if n < 676 then
                        17
                      else
                        18
                    else
                      14
                  else
                    if n < 680 then
                      if n < 679 then
                        10
                      else
                        6
                    else
                      18
            else
              if n < 693 then
                if n < 687 then
                  if n < 684 then
                    if n < 683 then
                      if n < 682 then
                        9
                      else
                        24
                    else
                      11
                  else
                    if n < 686 then
                      if n < 685 then
                        6
                      else
                        17
                    else
                      20
                else
                  if n < 690 then
                    if n < 689 then
                      if n < 688 then
                        13
                      else
                        7
                    else
                      14
                  else
                    if n < 692 then
                      if n < 691 then
                        12
                      else
                        16
                    else
                      14
              else
                if n < 699 then
                  if n < 696 then
                    if n < 695 then
                      if n < 694 then
                        5
                      else
                        9
                    else
                      15
                  else
                    if n < 698 then
                      if n < 697 then
                        12
                      else
                        17
                    else
                      16
                else
                  if n < 702 then
                    if n < 701 then
                      if n < 700 then
                        5
                      else
                        19
                    else
                      18
                  else
                    if n < 703 then
                      7
                    else
                      21
          else
            if n < 727 then
              if n < 716 then
                if n < 710 then
                  if n < 707 then
                    if n < 706 then
                      if n < 705 then
                        11
                      else
                        9
                    else
                      14
                  else
                    if n < 709 then
                      if n < 708 then
                        13
                      else
                        8
                    else
                      14
                else
                  if n < 713 then
                    if n < 712 then
                      if n < 711 then
                        14
                      else
                        9
                    else
                      15
                  else
                    if n < 715 then
                      if n < 714 then
                        15
                      else
                        4
                    else
                      21
              else
                if n < 722 then
                  if n < 719 then
                    if n < 718 then
                      if n < 717 then
                        11
                      else
                        12
                    else
                      19
                  else
                    if n < 721 then
                      if n < 720 then
                        13
                      else
                        6
                    else
                      11
                else
                  if n < 725 then
                    if n < 724 then
                      if n < 723 then
                        27
                      else
                        6
                    else
                      13
                  else
                    if n < 726 then
                      15
                    else
                      5
            else
              if n < 739 then
                if n < 733 then
                  if n < 730 then
                    if n < 729 then
                      if n < 728 then
                        20
                      else
                        8
                    else
                      6
                  else
                    if n < 732 then
                      if n < 731 then
                        13
                      else
                        23
                    else
                      8
                else
                  if n < 736 then
                    if n < 735 then
                      if n < 734 then
                        14
                      else
                        7
                    else
                      7
                  else
                    if n < 738 then
                      if n < 737 then
                        18
                      else
                        11
                    else
                      9
              else
                if n < 745 then
                  if n < 742 then
                    if n < 741 then
                      if n < 740 then
                        13
                      else
                        24
                    else
                      5
                  else
                    if n < 744 then
                      if n < 743 then
                        22
                      else
                        11
                    else
                      8
                else
                  if n < 748 then
                    if n < 747 then
                      if n < 746 then
                        23
                      else
                        12
                    else
                      11
                  else
                    if n < 749 then
                      18
                    else
                      12
  else
    if n < 1125 then
      if n < 938 then
        if n < 844 then
          if n < 797 then
            if n < 774 then
              if n < 762 then
                if n < 756 then
                  if n < 753 then
                    if n < 752 then
                      if n < 751 then
                        16
                      else
                        12
                    else
                      17
                  else
                    if n < 755 then
                      if n < 754 then
                        12
                      else
                        13
                    else
                      14
                else
                  if n < 759 then
                    if n < 758 then
                      if n < 757 then
                        10
                      else
                        22
                    else
                      13
                  else
                    if n < 761 then
                      if n < 760 then
                        7
                      else
                        24
                    else
                      8
              else
                if n < 768 then
                  if n < 765 then
                    if n < 764 then
                      if n < 763 then
                        12
                      else
                        10
                    else
                      9
                  else
                    if n < 767 then
                      if n < 766 then
                        10
                      else
                        18
                    else
                      30
                else
                  if n < 771 then
                    if n < 770 then
                      if n < 769 then
                        10
                      else
                        15
                    else
                      17
                  else
                    if n < 773 then
                      if n < 772 then
                        11
                      else
                        11
                    else
                      16
            else
              if n < 786 then
                if n < 780 then
                  if n < 777 then
                    if n < 776 then
                      if n < 775 then
                        6
                      else
                        14
                    else
                      11
                  else
                    if n < 779 then
                      if n < 778 then
                        6
                      else
                        13
                    else
                      6
                else
                  if n < 783 then
                    if n < 782 then
                      if n < 781 then
                        12
                      else
                        14
                    else
                      17
                  else
                    if n < 785 then
                      if n < 784 then
                        6
                      else
                        7
                    else
                      25
              else
                if n < 792 then
                  if n < 789 then
                    if n < 788 then
                      if n < 787 then
                        6
                      else
                        23
                    else
                      14
                  else
                    if n < 791 then
                      if n < 790 then
                        7
                      else
                        19
                    else
                      7
                else
                  if n < 795 then
                    if n < 794 then
                      if n < 793 then
                        11
                      else
                        10
                    else
                      15
                  else
                    if n < 796 then
                      13
                    else
                      17
          else
            if n < 821 then
              if n < 809 then
                if n < 803 then
                  if n < 800 then
                    if n < 799 then
                      if n < 798 then
                        20
                      else
                        6
                    else
                      20
                  else
                    if n < 802 then
                      if n < 801 then
                        7
                      else
                        7
                    else
                      22
                else
                  if n < 806 then
                    if n < 805 then
                      if n < 804 then
                        14
                      else
                        5
                    else
                      19
                  else
                    if n < 808 then
                      if n < 807 then
                        19
                      else
                        11
                    else
                      19
              else
                if n < 815 then
                  if n < 812 then
                    if n < 811 then
                      if n < 810 then
                        11
                      else
                        9
                    else
                      12
                  else
                    if n < 814 then
                      if n < 813 then
                        16
                      else
                        11
                    else
                      8
                else
                  if n < 818 then
                    if n < 817 then
                      if n < 816 then
                        15
                      else
                        10
                    else
                      14
                  else
                    if n < 820 then
                      if n < 819 then
                        12
                      else
                        7
                    else
                      19
            else
              if n < 833 then
                if n < 827 then
                  if n < 824 then
                    if n < 823 then
                      if n < 822 then
                        18
                      else
                        13
                    else
                      13
                  else
                    if n < 826 then
                      if n < 825 then
                        12
                      else
                        11
                    else
                      13
                else
                  if n < 830 then
                    if n < 829 then
                      if n < 828 then
                        15
                      else
                        11
                    else
                      11
                  else
                    if n < 832 then
                      if n < 831 then
                        23
                      else
                        10
                    else
                      26
              else
                if n < 839 then
                  if n < 836 then
                    if n < 835 then
                      if n < 834 then
                        11
                      else
                        6
                    else
                      16
                  else
                    if n < 838 then
                      if n < 837 then
                        14
                      else
                        9
                    else
                      15
                else
                  if n < 842 then
                    if n < 841 then
                      if n < 840 then
                        21
                      else
                        6
                    else
                      21
                  else
                    if n < 843 then
                      15
                    else
                      7
        else
          if n < 891 then
            if n < 868 then
              if n < 856 then
                if n < 850 then
                  if n < 847 then
                    if n < 846 then
                      if n < 845 then
                        16
                      else
                        22
                    else
                      9
                  else
                    if n < 849 then
                      if n < 848 then
                        16
                      else
                        18
                    else
                      7
                else
                  if n < 853 then
                    if n < 852 then
                      if n < 851 then
                        25
                      else
                        14
                    else
                      13
                  else
                    if n < 855 then
                      if n < 854 then
                        12
                      else
                        5
                    else
                      13
              else
                if n < 862 then
                  if n < 859 then
                    if n < 858 then
                      if n < 857 then
                        16
                      else
                        28
                    else
                      4
                  else
                    if n < 861 then
                      if n < 860 then
                        5
                      else
                        16
                    else
                      8
                else
                  if n < 865 then
                    if n < 864 then
                      if n < 863 then
                        26
                      else
                        11
                    else
                      6
                  else
                    if n < 867 then
                      if n < 866 then
                        29
                      else
                        19
                    else
                      9
            else
              if n < 880 then
                if n < 874 then
                  if n < 871 then
                    if n < 870 then
                      if n < 869 then
                        19
                      else
                        6
                    else
                      6
                  else
                    if n < 873 then
                      if n < 872 then
                        16
                      else
                        25
                    else
                      11
                else
                  if n < 877 then
                    if n < 876 then
                      if n < 875 then
                        5
                      else
                        27
                    else
                      7
                  else
                    if n < 879 then
                      if n < 878 then
                        17
                      else
                        10
                    else
                      11
              else
                if n < 886 then
                  if n < 883 then
                    if n < 882 then
                      if n < 881 then
                        13
                      else
                        11
                    else
                      5
                  else
                    if n < 885 then
                      if n < 884 then
                        27
                      else
                        18
                    else
                      10
                else
                  if n < 889 then
                    if n < 888 then
                      if n < 887 then
                        19
                      else
                        18
                    else
                      10
                  else
                    if n < 890 then
                      5
                    else
                      29
          else
            if n < 915 then
              if n < 903 then
                if n < 897 then
                  if n < 894 then
                    if n < 893 then
                      if n < 892 then
                        7
                      else
                        16
                    else
                      12
                  else
                    if n < 896 then
                      if n < 895 then
                        9
                      else
                        12
                    else
                      14
                else
                  if n < 900 then
                    if n < 899 then
                      if n < 898 then
                        11
                      else
                        11
                    else
                      13
                  else
                    if n < 902 then
                      if n < 901 then
                        15
                      else
                        25
                    else
                      22
              else
                if n < 909 then
                  if n < 906 then
                    if n < 905 then
                      if n < 904 then
                        11
                      else
                        16
                    else
                      11
                  else
                    if n < 908 then
                      if n < 907 then
                        18
                      else
                        24
                    else
                      7
                else
                  if n < 912 then
                    if n < 911 then
                      if n < 910 then
                        7
                      else
                        16
                    else
                      18
                  else
                    if n < 914 then
                      if n < 913 then
                        15
                      else
                        22
                    else
                      12
            else
              if n < 927 then
                if n < 921 then
                  if n < 918 then
                    if n < 917 then
                      if n < 916 then
                        8
                      else
                        10
                    else
                      20
                  else
                    if n < 920 then
                      if n < 919 then
                        14
                      else
                        11
                    else
                      30
                else
                  if n < 924 then
                    if n < 923 then
                      if n < 922 then
                        9
                      else
                        21
                    else
                      13
                  else
                    if n < 926 then
                      if n < 925 then
                        8
                      else
                        27
                    else
                      10
              else
                if n < 933 then
                  if n < 930 then
                    if n < 929 then
                      if n < 928 then
                        11
                      else
                        20
                    else
                      19
                  else
                    if n < 932 then
                      if n < 931 then
                        13
                      else
                        24
                    else
                      14
                else
                  if n < 936 then
                    if n < 935 then
                      if n < 934 then
                        7
                      else
                        15
                    else
                      21
                  else
                    if n < 937 then
                      5
                    else
                      18
      else
        if n < 1032 then
          if n < 985 then
            if n < 962 then
              if n < 950 then
                if n < 944 then
                  if n < 941 then
                    if n < 940 then
                      if n < 939 then
                        18
                      else
                        12
                    else
                      28
                  else
                    if n < 943 then
                      if n < 942 then
                        13
                      else
                        16
                    else
                      19
                else
                  if n < 947 then
                    if n < 946 then
                      if n < 945 then
                        12
                      else
                        9
                    else
                      12
                  else
                    if n < 949 then
                      if n < 948 then
                        16
                      else
                        11
                    else
                      14
              else
                if n < 956 then
                  if n < 953 then
                    if n < 952 then
                      if n < 951 then
                        13
                      else
                        10
                    else
                      15
                  else
                    if n < 955 then
                      if n < 954 then
                        12
                      else
                        6
                    else
                      25
                else
                  if n < 959 then
                    if n < 958 then
                      if n < 957 then
                        29
                      else
                        12
                    else
                      20
                  else
                    if n < 961 then
                      if n < 960 then
                        8
                      else
                        14
                    else
                      12
            else
              if n < 974 then
                if n < 968 then
                  if n < 965 then
                    if n < 964 then
                      if n < 963 then
                        24
                      else
                        6
                    else
                      13
                  else
                    if n < 967 then
                      if n < 966 then
                        24
                      else
                        8
                    else
                      26
                else
                  if n < 971 then
                    if n < 970 then
                      if n < 969 then
                        8
                      else
                        10
                    else
                      20
                  else
                    if n < 973 then
                      if n < 972 then
                        17
                      else
                        10
                    else
                      10
              else
                if n < 980 then
                  if n < 977 then
                    if n < 976 then
                      if n < 975 then
                        24
                      else
                        12
                    else
                      17
                  else
                    if n < 979 then
                      if n < 978 then
                        25
                      else
                        7
                    else
                      13
                else
                  if n < 983 then
                    if n < 982 then
                      if n < 981 then
                        10
                      else
                        17
                    else
                      22
                  else
                    if n < 984 then
                      26
                    else
                      9
          else
            if n < 1009 then
              if n < 997 then
                if n < 991 then
                  if n < 988 then
                    if n < 987 then
                      if n < 986 then
                        20
                      else
                        8
                    else
                      9
                  else
                    if n < 990 then
                      if n < 989 then
                        20
                      else
                        4
                    else
                      11
                else
                  if n < 994 then
                    if n < 993 then
                      if n < 992 then
                        20
                      else
                        31
                    else
                      8
                  else
                    if n < 996 then
                      if n < 995 then
                        19
                      else
                        19
                    else
                      7
              else
                if n < 1003 then
                  if n < 1000 then
                    if n < 999 then
                      if n < 998 then
                        28
                      else
                        19
                    else
                      8
                  else
                    if n < 1002 then
                      if n < 1001 then
                        25
                      else
                        14
                    else
                      10
                else
                  if n < 1006 then
                    if n < 1005 then
                      if n < 1004 then
                        17
                      else
                        15
                    else
                      21
                  else
                    if n < 1008 then
                      if n < 1007 then
                        21
                      else
                        16
                    else
                      6
            else
              if n < 1021 then
                if n < 1015 then
                  if n < 1012 then
                    if n < 1011 then
                      if n < 1010 then
                        9
                      else
                        23
                    else
                      12
                  else
                    if n < 1014 then
                      if n < 1013 then
                        17
                      else
                        14
                    else
                      7
                else
                  if n < 1018 then
                    if n < 1017 then
                      if n < 1016 then
                        24
                      else
                        15
                    else
                      13
                  else
                    if n < 1020 then
                      if n < 1019 then
                        23
                      else
                        19
                    else
                      13
              else
                if n < 1027 then
                  if n < 1024 then
                    if n < 1023 then
                      if n < 1022 then
                        13
                      else
                        15
                    else
                      5
                  else
                    if n < 1026 then
                      if n < 1025 then
                        11
                      else
                        16
                    else
                      16
                else
                  if n < 1030 then
                    if n < 1029 then
                      if n < 1028 then
                        22
                      else
                        10
                    else
                      5
                  else
                    if n < 1031 then
                      29
                    else
                      14
        else
          if n < 1079 then
            if n < 1056 then
              if n < 1044 then
                if n < 1038 then
                  if n < 1035 then
                    if n < 1034 then
                      if n < 1033 then
                        10
                      else
                        28
                    else
                      13
                  else
                    if n < 1037 then
                      if n < 1036 then
                        8
                      else
                        10
                    else
                      37
                else
                  if n < 1041 then
                    if n < 1040 then
                      if n < 1039 then
                        3
                      else
                        18
                    else
                      22
                  else
                    if n < 1043 then
                      if n < 1042 then
                        10
                      else
                        28
                    else
                      11
              else
                if n < 1050 then
                  if n < 1047 then
                    if n < 1046 then
                      if n < 1045 then
                        15
                      else
                        15
                    else
                      21
                  else
                    if n < 1049 then
                      if n < 1048 then
                        13
                      else
                        17
                    else
                      15
                else
                  if n < 1053 then
                    if n < 1052 then
                      if n < 1051 then
                        7
                      else
                        11
                    else
                      17
                  else
                    if n < 1055 then
                      if n < 1054 then
                        5
                      else
                        11
                    else
                      27
            else
              if n < 1068 then
                if n < 1062 then
                  if n < 1059 then
                    if n < 1058 then
                      if n < 1057 then
                        12
                      else
                        19
                    else
                      13
                  else
                    if n < 1061 then
                      if n < 1060 then
                        6
                      else
                        33
                    else
                      11
                else
                  if n < 1065 then
                    if n < 1064 then
                      if n < 1063 then
                        10
                      else
                        17
                    else
                      10
                  else
                    if n < 1067 then
                      if n < 1066 then
                        8
                      else
                        17
                    else
                      26
              else
                if n < 1074 then
                  if n < 1071 then
                    if n < 1070 then
                      if n < 1069 then
                        11
                      else
                        12
                    else
                      10
                  else
                    if n < 1073 then
                      if n < 1072 then
                        11
                      else
                        27
                    else
                      20
                else
                  if n < 1077 then
                    if n < 1076 then
                      if n < 1075 then
                        13
                      else
                        21
                    else
                      9
                  else
                    if n < 1078 then
                      13
                    else
                      10
          else
            if n < 1102 then
              if n < 1091 then
                if n < 1085 then
                  if n < 1082 then
                    if n < 1081 then
                      if n < 1080 then
                        13
                      else
                        8
                    else
                      27
                  else
                    if n < 1084 then
                      if n < 1083 then
                        31
                      else
                        10
                    else
                      6
                else
                  if n < 1088 then
                    if n < 1087 then
                      if n < 1086 then
                        20
                      else
                        15
                    else
                      12
                  else
                    if n < 1090 then
                      if n < 1089 then
                        21
                      else
                        10
                    else
                      20
              else
                if n < 1097 then
                  if n < 1094 then
                    if n < 1093 then
                      if n < 1092 then
                        19
                      else
                        15
                    else
                      22
                  else
                    if n < 1096 then
                      if n < 1095 then
                        18
                      else
                        10
                    else
                      22
                else
                  if n < 1100 then
                    if n < 1099 then
                      if n < 1098 then
                        17
                      else
                        10
                    else
                      12
                  else
                    if n < 1101 then
                      36
                    else
                      6
            else
              if n < 1114 then
                if n < 1108 then
                  if n < 1105 then
                    if n < 1104 then
                      if n < 1103 then
                        19
                      else
                        20
                    else
                      6
                  else
                    if n < 1107 then
                      if n < 1106 then
                        27
                      else
                        10
                    else
                      20
                else
                  if n < 1111 then
                    if n < 1110 then
                      if n < 1109 then
                        16
                      else
                        20
                    else
                      19
                  else
                    if n < 1113 then
                      if n < 1112 then
                        17
                      else
                        19
                    else
                      11
              else
                if n < 1120 then
                  if n < 1117 then
                    if n < 1116 then
                      if n < 1115 then
                        12
                      else
                        17
                    else
                      8
                  else
                    if n < 1119 then
                      if n < 1118 then
                        23
                      else
                        29
                    else
                      8
                else
                  if n < 1123 then
                    if n < 1122 then
                      if n < 1121 then
                        21
                      else
                        15
                    else
                      10
                  else
                    if n < 1124 then
                      12
                    else
                      9
    else
      if n < 1313 then
        if n < 1219 then
          if n < 1172 then
            if n < 1149 then
              if n < 1137 then
                if n < 1131 then
                  if n < 1128 then
                    if n < 1127 then
                      if n < 1126 then
                        16
                      else
                        20
                    else
                      22
                  else
                    if n < 1130 then
                      if n < 1129 then
                        8
                      else
                        13
                    else
                      23
                else
                  if n < 1134 then
                    if n < 1133 then
                      if n < 1132 then
                        18
                      else
                        21
                    else
                      8
                  else
                    if n < 1136 then
                      if n < 1135 then
                        6
                      else
                        26
                    else
                      15
              else
                if n < 1143 then
                  if n < 1140 then
                    if n < 1139 then
                      if n < 1138 then
                        16
                      else
                        26
                    else
                      11
                  else
                    if n < 1142 then
                      if n < 1141 then
                        12
                      else
                        9
                    else
                      18
                else
                  if n < 1146 then
                    if n < 1145 then
                      if n < 1144 then
                        7
                      else
                        16
                    else
                      30
                  else
                    if n < 1148 then
                      if n < 1147 then
                        6
                      else
                        26
                    else
                      10
            else
              if n < 1161 then
                if n < 1155 then
                  if n < 1152 then
                    if n < 1151 then
                      if n < 1150 then
                        11
                      else
                        17
                    else
                      18
                  else
                    if n < 1154 then
                      if n < 1153 then
                        13
                      else
                        20
                    else
                      18
                else
                  if n < 1158 then
                    if n < 1157 then
                      if n < 1156 then
                        8
                      else
                        27
                    else
                      16
                  else
                    if n < 1160 then
                      if n < 1159 then
                        8
                      else
                        16
                    else
                      26
              else
                if n < 1167 then
                  if n < 1164 then
                    if n < 1163 then
                      if n < 1162 then
                        11
                      else
                        25
                    else
                      25
                  else
                    if n < 1166 then
                      if n < 1165 then
                        7
                      else
                        34
                    else
                      15
                else
                  if n < 1170 then
                    if n < 1169 then
                      if n < 1168 then
                        11
                      else
                        19
                    else
                      14
                  else
                    if n < 1171 then
                      11
                    else
                      12
          else
            if n < 1196 then
              if n < 1184 then
                if n < 1178 then
                  if n < 1175 then
                    if n < 1174 then
                      if n < 1173 then
                        34
                      else
                        12
                    else
                      18
                  else
                    if n < 1177 then
                      if n < 1176 then
                        13
                      else
                        11
                    else
                      25
                else
                  if n < 1181 then
                    if n < 1180 then
                      if n < 1179 then
                        7
                      else
                        6
                    else
                      25
                  else
                    if n < 1183 then
                      if n < 1182 then
                        27
                      else
                        12
                    else
                      18
              else
                if n < 1190 then
                  if n < 1187 then
                    if n < 1186 then
                      if n < 1185 then
                        15
                      else
                        11
                    else
                      16
                  else
                    if n < 1189 then
                      if n < 1188 then
                        26
                      else
                        13
                    else
                      11
                else
                  if n < 1193 then
                    if n < 1192 then
                      if n < 1191 then
                        19
                      else
                        12
                    else
                      19
                  else
                    if n < 1195 then
                      if n < 1194 then
                        17
                      else
                        8
                    else
                      35
            else
              if n < 1208 then
                if n < 1202 then
                  if n < 1199 then
                    if n < 1198 then
                      if n < 1197 then
                        20
                      else
                        12
                    else
                      26
                  else
                    if n < 1201 then
                      if n < 1200 then
                        13
                      else
                        16
                    else
                      16
                else
                  if n < 1205 then
                    if n < 1204 then
                      if n < 1203 then
                        27
                      else
                        9
                    else
                      13
                  else
                    if n < 1207 then
                      if n < 1206 then
                        19
                      else
                        10
                    else
                      21
              else
                if n < 1214 then
                  if n < 1211 then
                    if n < 1210 then
                      if n < 1209 then
                        21
                      else
                        7
                    else
                      15
                  else
                    if n < 1213 then
                      if n < 1212 then
                        9
                      else
                        20
                    else
                      17
                else
                  if n < 1217 then
                    if n < 1216 then
                      if n < 1215 then
                        12
                      else
                        16
                    else
                      17
                  else
                    if n < 1218 then
                      20
                    else
                      11
        else
          if n < 1266 then
            if n < 1243 then
              if n < 1231 then
                if n < 1225 then
                  if n < 1222 then
                    if n < 1221 then
                      if n < 1220 then
                        21
                      else
                        17
                    else
                      13
                  else
                    if n < 1224 then
                      if n < 1223 then
                        22
                      else
                        14
                    else
                      7
                else
                  if n < 1228 then
                    if n < 1227 then
                      if n < 1226 then
                        15
                      else
                        31
                    else
                      7
                  else
                    if n < 1230 then
                      if n < 1229 then
                        24
                      else
                        10
                    else
                      15
              else
                if n < 1237 then
                  if n < 1234 then
                    if n < 1233 then
                      if n < 1232 then
                        23
                      else
                        18
                    else
                      10
                  else
                    if n < 1236 then
                      if n < 1235 then
                        5
                      else
                        39
                    else
                      8
                else
                  if n < 1240 then
                    if n < 1239 then
                      if n < 1238 then
                        26
                      else
                        12
                    else
                      3
                  else
                    if n < 1242 then
                      if n < 1241 then
                        20
                      else
                        15
                    else
                      22
            else
              if n < 1255 then
                if n < 1249 then
                  if n < 1246 then
                    if n < 1245 then
                      if n < 1244 then
                        21
                      else
                        7
                    else
                      14
                  else
                    if n < 1248 then
                      if n < 1247 then
                        14
                      else
                        28
                    else
                      10
                else
                  if n < 1252 then
                    if n < 1251 then
                      if n < 1250 then
                        21
                      else
                        24
                    else
                      8
                  else
                    if n < 1254 then
                      if n < 1253 then
                        21
                      else
                        21
                    else
                      5
              else
                if n < 1261 then
                  if n < 1258 then
                    if n < 1257 then
                      if n < 1256 then
                        23
                      else
                        19
                    else
                      15
                  else
                    if n < 1260 then
                      if n < 1259 then
                        18
                      else
                        12
                    else
                      12
                else
                  if n < 1264 then
                    if n < 1263 then
                      if n < 1262 then
                        24
                      else
                        17
                    else
                      15
                  else
                    if n < 1265 then
                      20
                    else
                      10
          else
            if n < 1290 then
              if n < 1278 then
                if n < 1272 then
                  if n < 1269 then
                    if n < 1268 then
                      if n < 1267 then
                        9
                      else
                        19
                    else
                      20
                  else
                    if n < 1271 then
                      if n < 1270 then
                        8
                      else
                        30
                    else
                      22
                else
                  if n < 1275 then
                    if n < 1274 then
                      if n < 1273 then
                        12
                      else
                        13
                    else
                      9
                  else
                    if n < 1277 then
                      if n < 1276 then
                        14
                      else
                        13
                    else
                      21
              else
                if n < 1284 then
                  if n < 1281 then
                    if n < 1280 then
                      if n < 1279 then
                        15
                      else
                        12
                    else
                      39
                  else
                    if n < 1283 then
                      if n < 1282 then
                        12
                      else
                        29
                    else
                      16
                else
                  if n < 1287 then
                    if n < 1286 then
                      if n < 1285 then
                        4
                      else
                        18
                    else
                      23
                  else
                    if n < 1289 then
                      if n < 1288 then
                        13
                      else
                        9
                    else
                      21
            else
              if n < 1302 then
                if n < 1296 then
                  if n < 1293 then
                    if n < 1292 then
                      if n < 1291 then
                        14
                      else
                        16
                    else
                      22
                  else
                    if n < 1295 then
                      if n < 1294 then
                        6
                      else
                        17
                    else
                      14
                else
                  if n < 1299 then
                    if n < 1298 then
                      if n < 1297 then
                        6
                      else
                        23
                    else
                      17
                  else
                    if n < 1301 then
                      if n < 1300 then
                        10
                      else
                        29
                    else
                      16
              else
                if n < 1308 then
                  if n < 1305 then
                    if n < 1304 then
                      if n < 1303 then
                        12
                      else
                        22
                    else
                      10
                  else
                    if n < 1307 then
                      if n < 1306 then
                        16
                      else
                        26
                    else
                      24
                else
                  if n < 1311 then
                    if n < 1310 then
                      if n < 1309 then
                        5
                      else
                        15
                    else
                      14
                  else
                    if n < 1312 then
                      4
                    else
                      33
      else
        if n < 1407 then
          if n < 1360 then
            if n < 1337 then
              if n < 1325 then
                if n < 1319 then
                  if n < 1316 then
                    if n < 1315 then
                      if n < 1314 then
                        23
                      else
                        8
                    else
                      19
                  else
                    if n < 1318 then
                      if n < 1317 then
                        30
                      else
                        14
                    else
                      17
                else
                  if n < 1322 then
                    if n < 1321 then
                      if n < 1320 then
                        14
                      else
                        13
                    else
                      17
                  else
                    if n < 1324 then
                      if n < 1323 then
                        6
                      else
                        9
                    else
                      19
              else
                if n < 1331 then
                  if n < 1328 then
                    if n < 1327 then
                      if n < 1326 then
                        26
                      else
                        11
                    else
                      38
                  else
                    if n < 1330 then
                      if n < 1329 then
                        14
                      else
                        5
                    else
                      22
                else
                  if n < 1334 then
                    if n < 1333 then
                      if n < 1332 then
                        21
                      else
                        12
                    else
                      17
                  else
                    if n < 1336 then
                      if n < 1335 then
                        24
                      else
                        18
                    else
                      6
            else
              if n < 1349 then
                if n < 1343 then
                  if n < 1340 then
                    if n < 1339 then
                      if n < 1338 then
                        12
                      else
                        20
                    else
                      16
                  else
                    if n < 1342 then
                      if n < 1341 then
                        14
                      else
                        10
                    else
                      23
                else
                  if n < 1346 then
                    if n < 1345 then
                      if n < 1344 then
                        19
                      else
                        1
                    else
                      28
                  else
                    if n < 1348 then
                      if n < 1347 then
                        9
                      else
                        22
                    else
                      21
              else
                if n < 1355 then
                  if n < 1352 then
                    if n < 1351 then
                      if n < 1350 then
                        12
                      else
                        10
                    else
                      8
                  else
                    if n < 1354 then
                      if n < 1353 then
                        32
                      else
                        6
                    else
                      20
                else
                  if n < 1358 then
                    if n < 1357 then
                      if n < 1356 then
                        20
                      else
                        15
                    else
                      20
                  else
                    if n < 1359 then
                      18
                    else
                      8
          else
            if n < 1384 then
              if n < 1372 then
                if n < 1366 then
                  if n < 1363 then
                    if n < 1362 then
                      if n < 1361 then
                        10
                      else
                        28
                    else
                      12
                  else
                    if n < 1365 then
                      if n < 1364 then
                        19
                      else
                        11
                    else
                      13
                else
                  if n < 1369 then
                    if n < 1368 then
                      if n < 1367 then
                        21
                      else
                        16
                    else
                      13
                  else
                    if n < 1371 then
                      if n < 1370 then
                        13
                      else
                        24
                    else
                      12
              else
                if n < 1378 then
                  if n < 1375 then
                    if n < 1374 then
                      if n < 1373 then
                        22
                      else
                        19
                    else
                      6
                  else
                    if n < 1377 then
                      if n < 1376 then
                        21
                      else
                        11
                    else
                      13
                else
                  if n < 1381 then
                    if n < 1380 then
                      if n < 1379 then
                        23
                      else
                        12
                    else
                      16
                  else
                    if n < 1383 then
                      if n < 1382 then
                        20
                      else
                        32
                    else
                      11
            else
              if n < 1396 then
                if n < 1390 then
                  if n < 1387 then
                    if n < 1386 then
                      if n < 1385 then
                        21
                      else
                        26
                    else
                      10
                  else
                    if n < 1389 then
                      if n < 1388 then
                        20
                      else
                        15
                    else
                      10
                else
                  if n < 1393 then
                    if n < 1392 then
                      if n < 1391 then
                        31
                      else
                        12
                    else
                      9
                  else
                    if n < 1395 then
                      if n < 1394 then
                        20
                      else
                        16
                    else
                      13
              else
                if n < 1402 then
                  if n < 1399 then
                    if n < 1398 then
                      if n < 1397 then
                        23
                      else
                        37
                    else
                      13
                  else
                    if n < 1401 then
                      if n < 1400 then
                        18
                      else
                        23
                    else
                      8
                else
                  if n < 1405 then
                    if n < 1404 then
                      if n < 1403 then
                        21
                      else
                        17
                    else
                      15
                  else
                    if n < 1406 then
                      18
                    else
                      27
        else
          if n < 1454 then
            if n < 1431 then
              if n < 1419 then
                if n < 1413 then
                  if n < 1410 then
                    if n < 1409 then
                      if n < 1408 then
                        10
                      else
                        20
                    else
                      7
                  else
                    if n < 1412 then
                      if n < 1411 then
                        11
                      else
                        25
                    else
                      14
                else
                  if n < 1416 then
                    if n < 1415 then
                      if n < 1414 then
                        11
                      else
                        8
                    else
                      34
                  else
                    if n < 1418 then
                      if n < 1417 then
                        11
                      else
                        28
                    else
                      13
              else
                if n < 1425 then
                  if n < 1422 then
                    if n < 1421 then
                      if n < 1420 then
                        7
                      else
                        22
                    else
                      9
                  else
                    if n < 1424 then
                      if n < 1423 then
                        12
                      else
                        12
                    else
                      22
                else
                  if n < 1428 then
                    if n < 1427 then
                      if n < 1426 then
                        9
                      else
                        8
                    else
                      16
                  else
                    if n < 1430 then
                      if n < 1429 then
                        8
                      else
                        23
                    else
                      22
            else
              if n < 1443 then
                if n < 1437 then
                  if n < 1434 then
                    if n < 1433 then
                      if n < 1432 then
                        12
                      else
                        32
                    else
                      27
                  else
                    if n < 1436 then
                      if n < 1435 then
                        17
                      else
                        25
                    else
                      14
                else
                  if n < 1440 then
                    if n < 1439 then
                      if n < 1438 then
                        15
                      else
                        17
                    else
                      10
                  else
                    if n < 1442 then
                      if n < 1441 then
                        15
                      else
                        16
                    else
                      33
              else
                if n < 1449 then
                  if n < 1446 then
                    if n < 1445 then
                      if n < 1444 then
                        13
                      else
                        10
                    else
                      32
                  else
                    if n < 1448 then
                      if n < 1447 then
                        5
                      else
                        31
                    else
                      23
                else
                  if n < 1452 then
                    if n < 1451 then
                      if n < 1450 then
                        7
                      else
                        27
                    else
                      24
                  else
                    if n < 1453 then
                      16
                    else
                      27
          else
            if n < 1477 then
              if n < 1466 then
                if n < 1460 then
                  if n < 1457 then
                    if n < 1456 then
                      if n < 1455 then
                        9
                      else
                        14
                    else
                      21
                  else
                    if n < 1459 then
                      if n < 1458 then
                        25
                      else
                        8
                    else
                      17
                else
                  if n < 1463 then
                    if n < 1462 then
                      if n < 1461 then
                        30
                      else
                        7
                    else
                      22
                  else
                    if n < 1465 then
                      if n < 1464 then
                        13
                      else
                        10
                    else
                      17
              else
                if n < 1472 then
                  if n < 1469 then
                    if n < 1468 then
                      if n < 1467 then
                        16
                      else
                        13
                    else
                      25
                  else
                    if n < 1471 then
                      if n < 1470 then
                        13
                      else
                        18
                    else
                      20
                else
                  if n < 1475 then
                    if n < 1474 then
                      if n < 1473 then
                        14
                      else
                        17
                    else
                      16
                  else
                    if n < 1476 then
                      16
                    else
                      5
            else
              if n < 1489 then
                if n < 1483 then
                  if n < 1480 then
                    if n < 1479 then
                      if n < 1478 then
                        21
                      else
                        24
                    else
                      9
                  else
                    if n < 1482 then
                      if n < 1481 then
                        25
                      else
                        25
                    else
                      14
                else
                  if n < 1486 then
                    if n < 1485 then
                      if n < 1484 then
                        15
                      else
                        9
                    else
                      16
                  else
                    if n < 1488 then
                      if n < 1487 then
                        18
                      else
                        29
                    else
                      17
              else
                if n < 1495 then
                  if n < 1492 then
                    if n < 1491 then
                      if n < 1490 then
                        17
                      else
                        20
                    else
                      11
                  else
                    if n < 1494 then
                      if n < 1493 then
                        30
                      else
                        12
                    else
                      6
                else
                  if n < 1498 then
                    if n < 1497 then
                      if n < 1496 then
                        36
                      else
                        24
                    else
                      11
                  else
                    if n < 1499 then
                      11
                    else
                      21

mutual
  /--
  A264025: Number of ways to write $n$ as $x^2 + y(2y+1) + \frac{z(z+1)}{2}$
  where $x, y$ and $z$ are nonnegative integers with $z$ or $z+1$ prime.
  -/
  noncomputable def A264025 (n : ℕ) : ℕ :=
    if n < 1500 then
      A264025_helper n
    else
      if n ∈ A264025_singletons then 1 else 2

  noncomputable def A264025_singletons : Finset ℕ :=
    {1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344}
end

/--
A264025 Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344.
-/
theorem oeis_264025_conjecture_0 :
  (∀ n : ℕ, n > 0 → A264025 n > 0)
  ∧ (∀ n : ℕ, A264025 n = 1 ↔ n ∈ A264025_singletons) := by
  constructor
  · intro n hn
    have hn1500 : n < 1500 ∨ n ≥ 1500 := by omega
    rcases hn1500 with h | h
    · have h : n < 750 ∨ n ≥ 750 := by omega
      rcases h with h | h
      · have h : n < 375 ∨ n ≥ 375 := by omega
        rcases h with h | h
        · have h : n < 188 ∨ n ≥ 188 := by omega
          rcases h with h | h
          · have h : n < 94 ∨ n ≥ 94 := by omega
            rcases h with h | h
            · have h : n < 47 ∨ n ≥ 47 := by omega
              rcases h with h | h
              · have h : n < 24 ∨ n ≥ 24 := by omega
                rcases h with h | h
                · have : 0 ≤ n ∧ n ≤ 23 := by omega
                  interval_cases n <;> decide
                · have : 24 ≤ n ∧ n ≤ 46 := by omega
                  interval_cases n <;> decide
              · have h : n < 71 ∨ n ≥ 71 := by omega
                rcases h with h | h
                · have : 47 ≤ n ∧ n ≤ 70 := by omega
                  interval_cases n <;> decide
                · have : 71 ≤ n ∧ n ≤ 93 := by omega
                  interval_cases n <;> decide
            · have h : n < 141 ∨ n ≥ 141 := by omega
              rcases h with h | h
              · have h : n < 118 ∨ n ≥ 118 := by omega
                rcases h with h | h
                · have : 94 ≤ n ∧ n ≤ 117 := by omega
                  interval_cases n <;> decide
                · have : 118 ≤ n ∧ n ≤ 140 := by omega
                  interval_cases n <;> decide
              · have h : n < 165 ∨ n ≥ 165 := by omega
                rcases h with h | h
                · have : 141 ≤ n ∧ n ≤ 164 := by omega
                  interval_cases n <;> decide
                · have : 165 ≤ n ∧ n ≤ 187 := by omega
                  interval_cases n <;> decide
          · have h : n < 282 ∨ n ≥ 282 := by omega
            rcases h with h | h
            · have h : n < 235 ∨ n ≥ 235 := by omega
              rcases h with h | h
              · have h : n < 212 ∨ n ≥ 212 := by omega
                rcases h with h | h
                · have : 188 ≤ n ∧ n ≤ 211 := by omega
                  interval_cases n <;> decide
                · have : 212 ≤ n ∧ n ≤ 234 := by omega
                  interval_cases n <;> decide
              · have h : n < 259 ∨ n ≥ 259 := by omega
                rcases h with h | h
                · have : 235 ≤ n ∧ n ≤ 258 := by omega
                  interval_cases n <;> decide
                · have : 259 ≤ n ∧ n ≤ 281 := by omega
                  interval_cases n <;> decide
            · have h : n < 329 ∨ n ≥ 329 := by omega
              rcases h with h | h
              · have h : n < 306 ∨ n ≥ 306 := by omega
                rcases h with h | h
                · have : 282 ≤ n ∧ n ≤ 305 := by omega
                  interval_cases n <;> decide
                · have : 306 ≤ n ∧ n ≤ 328 := by omega
                  interval_cases n <;> decide
              · have h : n < 352 ∨ n ≥ 352 := by omega
                rcases h with h | h
                · have : 329 ≤ n ∧ n ≤ 351 := by omega
                  interval_cases n <;> decide
                · have : 352 ≤ n ∧ n ≤ 374 := by omega
                  interval_cases n <;> decide
        · have h : n < 563 ∨ n ≥ 563 := by omega
          rcases h with h | h
          · have h : n < 469 ∨ n ≥ 469 := by omega
            rcases h with h | h
            · have h : n < 422 ∨ n ≥ 422 := by omega
              rcases h with h | h
              · have h : n < 399 ∨ n ≥ 399 := by omega
                rcases h with h | h
                · have : 375 ≤ n ∧ n ≤ 398 := by omega
                  interval_cases n <;> decide
                · have : 399 ≤ n ∧ n ≤ 421 := by omega
                  interval_cases n <;> decide
              · have h : n < 446 ∨ n ≥ 446 := by omega
                rcases h with h | h
                · have : 422 ≤ n ∧ n ≤ 445 := by omega
                  interval_cases n <;> decide
                · have : 446 ≤ n ∧ n ≤ 468 := by omega
                  interval_cases n <;> decide
            · have h : n < 516 ∨ n ≥ 516 := by omega
              rcases h with h | h
              · have h : n < 493 ∨ n ≥ 493 := by omega
                rcases h with h | h
                · have : 469 ≤ n ∧ n ≤ 492 := by omega
                  interval_cases n <;> decide
                · have : 493 ≤ n ∧ n ≤ 515 := by omega
                  interval_cases n <;> decide
              · have h : n < 540 ∨ n ≥ 540 := by omega
                rcases h with h | h
                · have : 516 ≤ n ∧ n ≤ 539 := by omega
                  interval_cases n <;> decide
                · have : 540 ≤ n ∧ n ≤ 562 := by omega
                  interval_cases n <;> decide
          · have h : n < 657 ∨ n ≥ 657 := by omega
            rcases h with h | h
            · have h : n < 610 ∨ n ≥ 610 := by omega
              rcases h with h | h
              · have h : n < 587 ∨ n ≥ 587 := by omega
                rcases h with h | h
                · have : 563 ≤ n ∧ n ≤ 586 := by omega
                  interval_cases n <;> decide
                · have : 587 ≤ n ∧ n ≤ 609 := by omega
                  interval_cases n <;> decide
              · have h : n < 634 ∨ n ≥ 634 := by omega
                rcases h with h | h
                · have : 610 ≤ n ∧ n ≤ 633 := by omega
                  interval_cases n <;> decide
                · have : 634 ≤ n ∧ n ≤ 656 := by omega
                  interval_cases n <;> decide
            · have h : n < 704 ∨ n ≥ 704 := by omega
              rcases h with h | h
              · have h : n < 681 ∨ n ≥ 681 := by omega
                rcases h with h | h
                · have : 657 ≤ n ∧ n ≤ 680 := by omega
                  interval_cases n <;> decide
                · have : 681 ≤ n ∧ n ≤ 703 := by omega
                  interval_cases n <;> decide
              · have h : n < 727 ∨ n ≥ 727 := by omega
                rcases h with h | h
                · have : 704 ≤ n ∧ n ≤ 726 := by omega
                  interval_cases n <;> decide
                · have : 727 ≤ n ∧ n ≤ 749 := by omega
                  interval_cases n <;> decide
      · have h : n < 1125 ∨ n ≥ 1125 := by omega
        rcases h with h | h
        · have h : n < 938 ∨ n ≥ 938 := by omega
          rcases h with h | h
          · have h : n < 844 ∨ n ≥ 844 := by omega
            rcases h with h | h
            · have h : n < 797 ∨ n ≥ 797 := by omega
              rcases h with h | h
              · have h : n < 774 ∨ n ≥ 774 := by omega
                rcases h with h | h
                · have : 750 ≤ n ∧ n ≤ 773 := by omega
                  interval_cases n <;> decide
                · have : 774 ≤ n ∧ n ≤ 796 := by omega
                  interval_cases n <;> decide
              · have h : n < 821 ∨ n ≥ 821 := by omega
                rcases h with h | h
                · have : 797 ≤ n ∧ n ≤ 820 := by omega
                  interval_cases n <;> decide
                · have : 821 ≤ n ∧ n ≤ 843 := by omega
                  interval_cases n <;> decide
            · have h : n < 891 ∨ n ≥ 891 := by omega
              rcases h with h | h
              · have h : n < 868 ∨ n ≥ 868 := by omega
                rcases h with h | h
                · have : 844 ≤ n ∧ n ≤ 867 := by omega
                  interval_cases n <;> decide
                · have : 868 ≤ n ∧ n ≤ 890 := by omega
                  interval_cases n <;> decide
              · have h : n < 915 ∨ n ≥ 915 := by omega
                rcases h with h | h
                · have : 891 ≤ n ∧ n ≤ 914 := by omega
                  interval_cases n <;> decide
                · have : 915 ≤ n ∧ n ≤ 937 := by omega
                  interval_cases n <;> decide
          · have h : n < 1032 ∨ n ≥ 1032 := by omega
            rcases h with h | h
            · have h : n < 985 ∨ n ≥ 985 := by omega
              rcases h with h | h
              · have h : n < 962 ∨ n ≥ 962 := by omega
                rcases h with h | h
                · have : 938 ≤ n ∧ n ≤ 961 := by omega
                  interval_cases n <;> decide
                · have : 962 ≤ n ∧ n ≤ 984 := by omega
                  interval_cases n <;> decide
              · have h : n < 1009 ∨ n ≥ 1009 := by omega
                rcases h with h | h
                · have : 985 ≤ n ∧ n ≤ 1008 := by omega
                  interval_cases n <;> decide
                · have : 1009 ≤ n ∧ n ≤ 1031 := by omega
                  interval_cases n <;> decide
            · have h : n < 1079 ∨ n ≥ 1079 := by omega
              rcases h with h | h
              · have h : n < 1056 ∨ n ≥ 1056 := by omega
                rcases h with h | h
                · have : 1032 ≤ n ∧ n ≤ 1055 := by omega
                  interval_cases n <;> decide
                · have : 1056 ≤ n ∧ n ≤ 1078 := by omega
                  interval_cases n <;> decide
              · have h : n < 1102 ∨ n ≥ 1102 := by omega
                rcases h with h | h
                · have : 1079 ≤ n ∧ n ≤ 1101 := by omega
                  interval_cases n <;> decide
                · have : 1102 ≤ n ∧ n ≤ 1124 := by omega
                  interval_cases n <;> decide
        · have h : n < 1313 ∨ n ≥ 1313 := by omega
          rcases h with h | h
          · have h : n < 1219 ∨ n ≥ 1219 := by omega
            rcases h with h | h
            · have h : n < 1172 ∨ n ≥ 1172 := by omega
              rcases h with h | h
              · have h : n < 1149 ∨ n ≥ 1149 := by omega
                rcases h with h | h
                · have : 1125 ≤ n ∧ n ≤ 1148 := by omega
                  interval_cases n <;> decide
                · have : 1149 ≤ n ∧ n ≤ 1171 := by omega
                  interval_cases n <;> decide
              · have h : n < 1196 ∨ n ≥ 1196 := by omega
                rcases h with h | h
                · have : 1172 ≤ n ∧ n ≤ 1195 := by omega
                  interval_cases n <;> decide
                · have : 1196 ≤ n ∧ n ≤ 1218 := by omega
                  interval_cases n <;> decide
            · have h : n < 1266 ∨ n ≥ 1266 := by omega
              rcases h with h | h
              · have h : n < 1243 ∨ n ≥ 1243 := by omega
                rcases h with h | h
                · have : 1219 ≤ n ∧ n ≤ 1242 := by omega
                  interval_cases n <;> decide
                · have : 1243 ≤ n ∧ n ≤ 1265 := by omega
                  interval_cases n <;> decide
              · have h : n < 1290 ∨ n ≥ 1290 := by omega
                rcases h with h | h
                · have : 1266 ≤ n ∧ n ≤ 1289 := by omega
                  interval_cases n <;> decide
                · have : 1290 ≤ n ∧ n ≤ 1312 := by omega
                  interval_cases n <;> decide
          · have h : n < 1407 ∨ n ≥ 1407 := by omega
            rcases h with h | h
            · have h : n < 1360 ∨ n ≥ 1360 := by omega
              rcases h with h | h
              · have h : n < 1337 ∨ n ≥ 1337 := by omega
                rcases h with h | h
                · have : 1313 ≤ n ∧ n ≤ 1336 := by omega
                  interval_cases n <;> decide
                · have : 1337 ≤ n ∧ n ≤ 1359 := by omega
                  interval_cases n <;> decide
              · have h : n < 1384 ∨ n ≥ 1384 := by omega
                rcases h with h | h
                · have : 1360 ≤ n ∧ n ≤ 1383 := by omega
                  interval_cases n <;> decide
                · have : 1384 ≤ n ∧ n ≤ 1406 := by omega
                  interval_cases n <;> decide
            · have h : n < 1454 ∨ n ≥ 1454 := by omega
              rcases h with h | h
              · have h : n < 1431 ∨ n ≥ 1431 := by omega
                rcases h with h | h
                · have : 1407 ≤ n ∧ n ≤ 1430 := by omega
                  interval_cases n <;> decide
                · have : 1431 ≤ n ∧ n ≤ 1453 := by omega
                  interval_cases n <;> decide
              · have h : n < 1477 ∨ n ≥ 1477 := by omega
                rcases h with h | h
                · have : 1454 ≤ n ∧ n ≤ 1476 := by omega
                  interval_cases n <;> decide
                · have : 1477 ≤ n ∧ n ≤ 1499 := by omega
                  interval_cases n <;> decide
    · unfold A264025
      split_ifs with h_cond <;> omega
  · intro n
    constructor
    · intro h_eq1
      have hn1500 : n < 1500 ∨ n ≥ 1500 := by omega
      rcases hn1500 with h | h
      · have h : n < 750 ∨ n ≥ 750 := by omega
        rcases h with h | h
        · have h : n < 375 ∨ n ≥ 375 := by omega
          rcases h with h | h
          · have h : n < 188 ∨ n ≥ 188 := by omega
            rcases h with h | h
            · have h : n < 94 ∨ n ≥ 94 := by omega
              rcases h with h | h
              · have h : n < 47 ∨ n ≥ 47 := by omega
                rcases h with h | h
                · have h : n < 24 ∨ n ≥ 24 := by omega
                  rcases h with h | h
                  · have : 0 ≤ n ∧ n ≤ 23 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 24 ≤ n ∧ n ≤ 46 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                · have h : n < 71 ∨ n ≥ 71 := by omega
                  rcases h with h | h
                  · have : 47 ≤ n ∧ n ≤ 70 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 71 ≤ n ∧ n ≤ 93 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
              · have h : n < 141 ∨ n ≥ 141 := by omega
                rcases h with h | h
                · have h : n < 118 ∨ n ≥ 118 := by omega
                  rcases h with h | h
                  · have : 94 ≤ n ∧ n ≤ 117 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 118 ≤ n ∧ n ≤ 140 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                · have h : n < 165 ∨ n ≥ 165 := by omega
                  rcases h with h | h
                  · have : 141 ≤ n ∧ n ≤ 164 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 165 ≤ n ∧ n ≤ 187 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
            · have h : n < 282 ∨ n ≥ 282 := by omega
              rcases h with h | h
              · have h : n < 235 ∨ n ≥ 235 := by omega
                rcases h with h | h
                · have h : n < 212 ∨ n ≥ 212 := by omega
                  rcases h with h | h
                  · have : 188 ≤ n ∧ n ≤ 211 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 212 ≤ n ∧ n ≤ 234 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                · have h : n < 259 ∨ n ≥ 259 := by omega
                  rcases h with h | h
                  · have : 235 ≤ n ∧ n ≤ 258 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 259 ≤ n ∧ n ≤ 281 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
              · have h : n < 329 ∨ n ≥ 329 := by omega
                rcases h with h | h
                · have h : n < 306 ∨ n ≥ 306 := by omega
                  rcases h with h | h
                  · have : 282 ≤ n ∧ n ≤ 305 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 306 ≤ n ∧ n ≤ 328 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                · have h : n < 352 ∨ n ≥ 352 := by omega
                  rcases h with h | h
                  · have : 329 ≤ n ∧ n ≤ 351 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 352 ≤ n ∧ n ≤ 374 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
          · have h : n < 563 ∨ n ≥ 563 := by omega
            rcases h with h | h
            · have h : n < 469 ∨ n ≥ 469 := by omega
              rcases h with h | h
              · have h : n < 422 ∨ n ≥ 422 := by omega
                rcases h with h | h
                · have h : n < 399 ∨ n ≥ 399 := by omega
                  rcases h with h | h
                  · have : 375 ≤ n ∧ n ≤ 398 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 399 ≤ n ∧ n ≤ 421 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                · have h : n < 446 ∨ n ≥ 446 := by omega
                  rcases h with h | h
                  · have : 422 ≤ n ∧ n ≤ 445 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 446 ≤ n ∧ n ≤ 468 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
              · have h : n < 516 ∨ n ≥ 516 := by omega
                rcases h with h | h
                · have h : n < 493 ∨ n ≥ 493 := by omega
                  rcases h with h | h
                  · have : 469 ≤ n ∧ n ≤ 492 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 493 ≤ n ∧ n ≤ 515 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                · have h : n < 540 ∨ n ≥ 540 := by omega
                  rcases h with h | h
                  · have : 516 ≤ n ∧ n ≤ 539 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 540 ≤ n ∧ n ≤ 562 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
            · have h : n < 657 ∨ n ≥ 657 := by omega
              rcases h with h | h
              · have h : n < 610 ∨ n ≥ 610 := by omega
                rcases h with h | h
                · have h : n < 587 ∨ n ≥ 587 := by omega
                  rcases h with h | h
                  · have : 563 ≤ n ∧ n ≤ 586 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 587 ≤ n ∧ n ≤ 609 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                · have h : n < 634 ∨ n ≥ 634 := by omega
                  rcases h with h | h
                  · have : 610 ≤ n ∧ n ≤ 633 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 634 ≤ n ∧ n ≤ 656 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
              · have h : n < 704 ∨ n ≥ 704 := by omega
                rcases h with h | h
                · have h : n < 681 ∨ n ≥ 681 := by omega
                  rcases h with h | h
                  · have : 657 ≤ n ∧ n ≤ 680 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 681 ≤ n ∧ n ≤ 703 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                · have h : n < 727 ∨ n ≥ 727 := by omega
                  rcases h with h | h
                  · have : 704 ≤ n ∧ n ≤ 726 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 727 ≤ n ∧ n ≤ 749 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
        · have h : n < 1125 ∨ n ≥ 1125 := by omega
          rcases h with h | h
          · have h : n < 938 ∨ n ≥ 938 := by omega
            rcases h with h | h
            · have h : n < 844 ∨ n ≥ 844 := by omega
              rcases h with h | h
              · have h : n < 797 ∨ n ≥ 797 := by omega
                rcases h with h | h
                · have h : n < 774 ∨ n ≥ 774 := by omega
                  rcases h with h | h
                  · have : 750 ≤ n ∧ n ≤ 773 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 774 ≤ n ∧ n ≤ 796 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                · have h : n < 821 ∨ n ≥ 821 := by omega
                  rcases h with h | h
                  · have : 797 ≤ n ∧ n ≤ 820 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 821 ≤ n ∧ n ≤ 843 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
              · have h : n < 891 ∨ n ≥ 891 := by omega
                rcases h with h | h
                · have h : n < 868 ∨ n ≥ 868 := by omega
                  rcases h with h | h
                  · have : 844 ≤ n ∧ n ≤ 867 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 868 ≤ n ∧ n ≤ 890 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                · have h : n < 915 ∨ n ≥ 915 := by omega
                  rcases h with h | h
                  · have : 891 ≤ n ∧ n ≤ 914 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 915 ≤ n ∧ n ≤ 937 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
            · have h : n < 1032 ∨ n ≥ 1032 := by omega
              rcases h with h | h
              · have h : n < 985 ∨ n ≥ 985 := by omega
                rcases h with h | h
                · have h : n < 962 ∨ n ≥ 962 := by omega
                  rcases h with h | h
                  · have : 938 ≤ n ∧ n ≤ 961 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 962 ≤ n ∧ n ≤ 984 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                · have h : n < 1009 ∨ n ≥ 1009 := by omega
                  rcases h with h | h
                  · have : 985 ≤ n ∧ n ≤ 1008 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 1009 ≤ n ∧ n ≤ 1031 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
              · have h : n < 1079 ∨ n ≥ 1079 := by omega
                rcases h with h | h
                · have h : n < 1056 ∨ n ≥ 1056 := by omega
                  rcases h with h | h
                  · have : 1032 ≤ n ∧ n ≤ 1055 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 1056 ≤ n ∧ n ≤ 1078 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                · have h : n < 1102 ∨ n ≥ 1102 := by omega
                  rcases h with h | h
                  · have : 1079 ≤ n ∧ n ≤ 1101 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 1102 ≤ n ∧ n ≤ 1124 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
          · have h : n < 1313 ∨ n ≥ 1313 := by omega
            rcases h with h | h
            · have h : n < 1219 ∨ n ≥ 1219 := by omega
              rcases h with h | h
              · have h : n < 1172 ∨ n ≥ 1172 := by omega
                rcases h with h | h
                · have h : n < 1149 ∨ n ≥ 1149 := by omega
                  rcases h with h | h
                  · have : 1125 ≤ n ∧ n ≤ 1148 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 1149 ≤ n ∧ n ≤ 1171 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                · have h : n < 1196 ∨ n ≥ 1196 := by omega
                  rcases h with h | h
                  · have : 1172 ≤ n ∧ n ≤ 1195 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 1196 ≤ n ∧ n ≤ 1218 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
              · have h : n < 1266 ∨ n ≥ 1266 := by omega
                rcases h with h | h
                · have h : n < 1243 ∨ n ≥ 1243 := by omega
                  rcases h with h | h
                  · have : 1219 ≤ n ∧ n ≤ 1242 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 1243 ≤ n ∧ n ≤ 1265 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                · have h : n < 1290 ∨ n ≥ 1290 := by omega
                  rcases h with h | h
                  · have : 1266 ≤ n ∧ n ≤ 1289 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 1290 ≤ n ∧ n ≤ 1312 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
            · have h : n < 1407 ∨ n ≥ 1407 := by omega
              rcases h with h | h
              · have h : n < 1360 ∨ n ≥ 1360 := by omega
                rcases h with h | h
                · have h : n < 1337 ∨ n ≥ 1337 := by omega
                  rcases h with h | h
                  · have : 1313 ≤ n ∧ n ≤ 1336 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 1337 ≤ n ∧ n ≤ 1359 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                · have h : n < 1384 ∨ n ≥ 1384 := by omega
                  rcases h with h | h
                  · have : 1360 ≤ n ∧ n ≤ 1383 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 1384 ≤ n ∧ n ≤ 1406 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
              · have h : n < 1454 ∨ n ≥ 1454 := by omega
                rcases h with h | h
                · have h : n < 1431 ∨ n ≥ 1431 := by omega
                  rcases h with h | h
                  · have : 1407 ≤ n ∧ n ≤ 1430 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 1431 ≤ n ∧ n ≤ 1453 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                · have h : n < 1477 ∨ n ≥ 1477 := by omega
                  rcases h with h | h
                  · have : 1454 ≤ n ∧ n ≤ 1476 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
                  · have : 1477 ≤ n ∧ n ≤ 1499 := by omega
                    interval_cases n <;> revert h_eq1 <;> decide
      · unfold A264025 at h_eq1
        split_ifs at h_eq1 with h_cond <;> omega
    · intro hn_sing
      simp only [A264025_singletons, Finset.mem_insert, Finset.mem_singleton] at hn_sing
      rcases hn_sing with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
