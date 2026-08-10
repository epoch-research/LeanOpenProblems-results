#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <math.h>

#define MAX_N 42100000

bool is_square(long long n) {
    if (n < 0) return false;
    long long r = (long long)sqrt(n);
    return r * r == n || (r + 1) * (r + 1) == n || (r - 1) * (r - 1) == n;
}

bool check_n(long long n) {
    // Search for a valid quadruple (x, y, z, w)
    // We want x^2 + y^2 + z^2 + w^2 = n
    // with IsSquare y or IsSquare z or IsSquare w.
    // To make it fast, we can loop over the square coordinate first!
    
    // Case 1: y is a square. Let y = j*j.
    for (long long j = 0; j * j * j * j <= n; j++) {
        long long y = j * j;
        long long y2 = y * y;
        for (long long z = 0; y2 + z * z <= n; z++) {
            long long z2 = z * z;
            // We want x + 3*y + 5*z to be a square s*s.
            // So x = s*s - 3*y - 5*z >= 0.
            long long start_s = (long long)ceil(sqrt(3 * y + 5 * z));
            for (long long s = start_s; ; s++) {
                long long x = s * s - 3 * y - 5 * z;
                long long x2 = x * x;
                if (y2 + z2 + x2 > n) break;
                long long w2 = n - y2 - z2 - x2;
                if (is_square(w2)) {
                    return true;
                }
            }
        }
    }
    
    // Case 2: z is a square. Let z = k*k.
    for (long long k = 0; k * k * k * k <= n; k++) {
        long long z = k * k;
        long long z2 = z * z;
        for (long long y = 0; y * y + z2 <= n; y++) {
            long long y2 = y * y;
            long long start_s = (long long)ceil(sqrt(3 * y + 5 * z));
            for (long long s = start_s; ; s++) {
                long long x = s * s - 3 * y - 5 * z;
                long long x2 = x * x;
                if (y2 + z2 + x2 > n) break;
                long long w2 = n - y2 - z2 - x2;
                if (is_square(w2)) {
                    return true;
                }
            }
        }
    }

    // Case 3: w is a square. Let w = l*l.
    for (long long l = 0; l * l * l * l <= n; l++) {
        long long w = l * l;
        long long w2 = w * w;
        for (long long y = 0; y * y + w2 <= n; y++) {
            long long y2 = y * y;
            for (long long z = 0; y2 + z * z + w2 <= n; z++) {
                long long z2 = z * z;
                long long start_s = (long long)ceil(sqrt(3 * y + 5 * z));
                for (long long s = start_s; ; s++) {
                    long long x = s * s - 3 * y - 5 * z;
                    long long x2 = x * x;
                    if (y2 + z2 + x2 + w2 > n) break;
                    if (y2 + z2 + x2 + w2 == n) {
                        return true;
                    }
                }
            }
        }
    }

    return false;
}

int main() {
    setvbuf(stdout, NULL, _IONBF, 0);
    printf("Checking up to %d...\n", MAX_N);
    for (int n = 42000000; n < MAX_N; n++) {
        if (!check_n(n)) {
            printf("Counterexample found: %d\n", n);
            return 0;
        }
        if (n > 0 && n % 100000 == 0) {
            printf("Checked %d hundred thousands...\n", n / 100000);
        }
    }
    printf("All checked up to %d! Conjecture holds.\n", MAX_N);
    return 0;
}
