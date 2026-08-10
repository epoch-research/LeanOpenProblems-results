#include <stdio.h>
#include <stdlib.h>

int main() {
    long long limit = 1000000000000LL; // 1 trillion
    long long last_both_pos = -1;
    long long both_pos_count = 0;
    
    long long w[4] = {0, 1, 0, 0};
    
    // b=2
    w[2] = (w[1] ^ 2) - w[0];
    // b=3
    w[3] = (w[2] ^ 3) - w[1];
    
    if (w[0] > 0 && w[3] > 0) {
        last_both_pos = 0;
        both_pos_count++;
    }
    
    for (long long b = 4; b < limit; b++) {
        long long val = (w[3] ^ b) - w[2];
        
        w[0] = w[1];
        w[1] = w[2];
        w[2] = w[3];
        w[3] = val;
        
        long long n = b - 3;
        if (n % 6 < 3) {
            if (w[0] > 0 && w[3] > 0) {
                last_both_pos = n;
                both_pos_count++;
            }
        }
        
        if (b % 100000000000LL == 0) {
            printf("b=%lld, count so far: %lld, last so far: %lld\n", b, both_pos_count, last_both_pos);
        }
    }
    
    printf("Final both_pos count: %lld, last both_pos: %lld\n", both_pos_count, last_both_pos);
    return 0;
}
