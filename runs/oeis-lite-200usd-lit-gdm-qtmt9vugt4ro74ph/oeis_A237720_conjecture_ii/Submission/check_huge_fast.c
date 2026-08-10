#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <math.h>

#define MAX_VAL 20000000000LL

bool *is_prime;
int *prime_count;

void sieve() {
    is_prime = malloc(MAX_VAL * sizeof(bool));
    prime_count = malloc(MAX_VAL * sizeof(int));
    for (int i = 0; i < MAX_VAL; i++) is_prime[i] = true;
    is_prime[0] = is_prime[1] = false;
    for (int i = 2; i * (long long)i < MAX_VAL; i++) {
        if (is_prime[i]) {
            for (int j = i * i; j < MAX_VAL; j += i) {
                is_prime[j] = false;
            }
        }
    }
    int count = 0;
    for (int i = 0; i < MAX_VAL; i++) {
        if (is_prime[i]) count++;
        prime_count[i] = count;
    }
}

bool has_prime_in_range(int low, int high) {
    if (low > high) return false;
    if (low < 0) low = 0;
    int count_high = prime_count[high];
    int count_low_minus_1 = (low == 0) ? 0 : prime_count[low - 1];
    return count_high > count_low_minus_1;
}

int main() {
    printf("Starting sieve up to 2 billion...\n");
    sieve();
    printf("Sieve completed.\n");
    
    int limit = 1000000000;
    for (int n = 3; n <= limit; n++) {
        bool found = false;
        int r_start = (int)sqrt(n + 2);
        int r_end = (int)sqrt(2 * n - 1);
        for (int r = r_start; r <= r_end; r++) {
            if (is_prime[r]) {
                int low = r * r - n;
                int high = (r + 1) * (r + 1) - 1 - n;
                if (high >= n) high = n - 1;
                if (has_prime_in_range(low, high)) {
                    found = true;
                    break;
                }
            }
        }
        if (!found) {
            printf("Counterexample found: n = %d\n", n);
            return 0;
        }
        if (n % 100000000 == 0) {
            printf("Checked up to %d\n", n);
        }
    }
    printf("No counterexamples found up to %d.\n", limit);
    return 0;
}
