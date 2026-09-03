import FormalConjecturesUtil
example (t a b c d e g : ℝ) :
    (t ^ 3 + a * t + t ^ 2 + b) ^ 5 +
    (-t ^ 3 - a * t + t ^ 2 + b) ^ 5 +
    (t ^ 3 + c * t - t ^ 2 + d) ^ 5 +
    (-t ^ 3 - c * t - t ^ 2 + d) ^ 5 + (e * t ^ 2 + g) ^ 5 =
      10 * t ^ 4 * ((t ^ 2 + a) ^ 4 * (t ^ 2 + b) +
        (t ^ 2 + c) ^ 4 * (-t ^ 2 + d)) +
      20 * t ^ 2 * ((t ^ 2 + a) ^ 2 * (t ^ 2 + b) ^ 3 +
        (t ^ 2 + c) ^ 2 * (-t ^ 2 + d) ^ 3) +
      2 * ((t ^ 2 + b) ^ 5 + (-t ^ 2 + d) ^ 5) + (e * t ^ 2 + g) ^ 5 := by
  ring
