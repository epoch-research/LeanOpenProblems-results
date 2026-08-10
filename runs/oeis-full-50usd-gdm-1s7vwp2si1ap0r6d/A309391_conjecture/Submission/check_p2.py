import time

p = 16843
p2 = p * p

print("Computing sum...")
t0 = time.time()

# We want to compute sum_{k=1}^{p^2-2} 1/k mod p^2.
# Note that we can only do this for k coprime to p.
# Wait! In the rational sum, the terms that are multiples of p are of the form 1/(j*p) for j = 1, ..., p-1.
# Their sum is 1/p * H_{p-1}.
# Since H_{p-1} is divisible by p^3, 1/p * H_{p-1} is divisible by p^2, so it is 0 mod p^2.
# Therefore, we only need to compute the sum of 1/k mod p^2 for all k <= p^2 - 2 that are coprime to p!
# Let's verify this mathematically and computationally.

# Let's compute sum_{k=1, gcd(k,p)=1}^{p^2-2} 1/k mod p^2.
# The number of such terms is p^2 - 2 - (p - 1) = p^2 - p - 1 = 283669805 terms.
# To compute this fast, we can use a C-like loop or sage, or just python.
# In Python, we can do it in batches or using a simple loop.
# Let's do a fast python loop.
ans = 0
# We can do modular inverse in Python using pow(k, -1, p2) or pow(k, p2 - p - 1, p2) (since phi(p2) = p(p-1) = p2 - p)
# But computing pow(k, -1, p2) for 280M numbers is slow.
# Instead of doing pow(k, -1, p2) for each k, we can do a product or we can just trust the math.
# Wait, the math says:
# sum_{k=1, p \nmid k}^{p^2-1} 1/k = \sum_{k=1}^{(p^2-1)/2} (1/k + 1/(p^2-k)) = \sum (p^2) / (k(p^2-k)) = p^2 \sum 1/(k(p^2-k)) = 0 mod p^2.
# Therefore, sum_{k=1, p \nmid k}^{p^2-2} 1/k = sum_{k=1, p \nmid k}^{p^2-1} 1/k - 1/(p^2-1) \equiv 0 - 1/(-1) = 1 mod p^2.
# Let's verify this math. Is there any flaw?
# No! Since p \nmid k, both k and p^2-k are coprime to p, so their inverses mod p^2 exist.
# The sum 1/k + 1/(p^2-k) mod p^2 is indeed 0 because:
# 1/k + 1/(p^2-k) = (p^2-k + k) / (k(p^2-k)) = p^2 / (k(p^2-k)) \equiv 0 (mod p^2).
# This is perfectly rigorous and works for ANY prime p >= 3.
# Let's check for a small prime, say p=3, p2=9.
# H_7 = 1 + 1/2 + 1/3 + 1/4 + 1/5 + 1/6 + 1/7 = 363/140.
# Is H_7 \equiv 1 (mod 9)?
# H_7 = 363/140. 363 = 3 * 121, 140 is coprime to 9.
# Modulo 9, 140 \equiv 5.
# 363 \equiv 3.
# So H_7 mod 9 is 3 * (5^-1 mod 9) = 3 * 2 = 6 != 1 (mod 9).
# Why? Because p=3 is not a Wolstenholme prime!
# H_{p-1} = H_2 = 1 + 1/2 = 3/2.
# 1/p * H_{p-1} = 1/3 * 3/2 = 1/2.
# Modulo p^2 (which is 9), 1/2 \equiv 5 (mod 9).
# Indeed, H_7 = S_{ndiv} + 1/3 * H_2 = (1 + 1/2 + 1/4 + 1/5 + 1/7) + 1/2.
# S_{ndiv} mod 9:
# 1 + 1/2 + 1/4 + 1/5 + 1/7 \equiv 1 + 5 + 7 + 2 + 4 = 19 \equiv 1 (mod 9).
# (Note that 1/7 mod 9 = 4, since 7*4=28 \equiv 1 mod 9).
# (1/8 is missing because n-2 = 7, so the last term coprime to 3 is 7, and 8 is indeed missing).
# So S_{ndiv} \equiv 1 - 1/8 = 1 - 8 \equiv 2 \equiv 1 - (-1) \equiv 1 - 1/(-1) = 2 (mod 9).
# Thus, S_{ndiv} \equiv 2 (mod 9).
# And 1/3 * H_2 = 1/2 \equiv 5 (mod 9).
# So H_7 = S_{ndiv} + 1/3 * H_2 \equiv 2 + 5 = 7 \equiv -2 (mod 9).
# Wait, earlier we got H_7 \equiv 6 (mod 9). Why the difference?
# Let's check: 363/140 mod 9. 363 = 40 * 9 + 3. 140 = 15 * 9 + 5.
# 3/5 mod 9. 5 * x \equiv 3 (mod 9). Since gcd(5, 9)=1, 5*6 = 30 \equiv 3 (mod 9). So yes, 6 mod 9.
# Wait, let's sum:
# 1/1 + 1/2 + 1/4 + 1/5 + 1/7 + 1/2.
# 1/2 is counted twice: once in 1/2, once in 1/3 * H_2 (which is 1/2).
# Sum: 1 + 1/2 + 1/4 + 1/5 + 1/7 + 1/2 = 1 + 1 + 1/4 + 1/5 + 1/7 = 2 + 7 + 2 + 4 = 15 \equiv 6 (mod 9).
# It matches perfectly!
# So H_{p^2-2} = S_{ndiv} + 1/p * H_{p-1} \equiv 1 + 1/p * H_{p-1} (mod p^2).
# And for a Wolstenholme prime p, H_{p-1} \equiv 0 (mod p^3), so 1/p * H_{p-1} \equiv 0 (mod p^2).
# Thus H_{p^2-2} \equiv 1 + 0 = 1 (mod p^2).
# This is incredibly clean!
# Let's verify for p = 5, which is also not Wolstenholme.
# For p = 5, p^2 = 25. H_4 = 25/12. H_{p-1} = 25/12 = 25 * 12^-1 = 0 mod 25, but not 0 mod 125.
# Let's print the theory. It's beautiful.
