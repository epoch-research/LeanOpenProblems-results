#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>

#define MAX_N 4000000
uint32_t arr[500000];
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
    int last_success = 0;
    int first_fail_after_799344 = 0;
    
    for (int n = 1; n <= MAX_N; n++) {
        mult3();
        int bit = get_bit(n);
        int term = (bit == 0) ? 1 : -1;
        a -= term;
        
        double limit = sqrt(n);
        if (a <= limit) {
            last_success = n;
        } else {
            if (n > 799344 && first_fail_after_799344 == 0) {
                first_fail_after_799344 = n;
            }
        }
    }
    printf("Last success up to %d: %d\n", MAX_N, last_success);
    printf("First failure after 799344: %d\n", first_fail_after_799344);
    return 0;
}
