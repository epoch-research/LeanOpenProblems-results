#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>

#define MAX_N 3000000
uint32_t arr[150000];
int len = 1;

void mult3() {
    uint64_t carry = 0;
    for (int i = 0; i < len; i++) {
        uint64_t val = (uint64_t)arr[i] * 3 + carry;
        arr[i] = (uint32_t)(val & 0xFFFFFFFF);
        carry = val >> 32;
    }
    if (carry) {
        arr[len++] = (uint32_t)carry;
    }
}

int get_bit(int n) {
    int idx = n / 32;
    int bit = n % 32;
    if (idx >= len) return 0;
    return (arr[idx] >> bit) & 1;
}

int main() {
    arr[0] = 1;
    int64_t a = 0;
    int64_t max_a = 0;
    int max_n = 0;
    
    for (int n = 1; n <= MAX_N; n++) {
        mult3();
        int bit = get_bit(n);
        int term = (bit == 0) ? 1 : -1;
        a -= term;
        if (a > max_a) {
            max_a = a;
            max_n = n;
        }
    }
    printf("Max a(n): %lld at n=%d\n", (long long)max_a, max_n);
    return 0;
}
