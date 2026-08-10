#include <stdio.h>
#include <stdlib.h>

int main() {
    long long limit = 10000000000LL; // 10 billion
    long long both_pos = 0;
    long long both_neg = 0;
    
    // We want to pair n and n+3.
    // If n % 6 < 3, then fn = n+3.
    // So we want to compare a(n) and a(n+3).
    // To do this, we can maintain a sliding window of the last 4 values:
    // w[0] = a(i-3), w[1] = a(i-2), w[2] = a(i-1), w[3] = a(i)
    long long w[4] = {0, 1, 0, 0};
    
    // b=2
    w[2] = (w[1] ^ 2) - w[0];
    // b=3
    w[3] = (w[2] ^ 3) - w[1];
    
    // For n=0, fn=3. Both are in the window.
    if (w[0] > 0 && w[3] > 0) both_pos++;
    if (w[0] < 0 && w[3] < 0) both_neg++;
    
    for (long long b = 4; b < limit; b++) {
        long long val = (w[3] ^ b) - w[2];
        
        // shift window
        w[0] = w[1];
        w[1] = w[2];
        w[2] = w[3];
        w[3] = val;
        
        // n = b - 3. We want to check if n % 6 < 3.
        long long n = b - 3;
        if (n % 6 < 3) {
            if (w[0] > 0 && w[3] > 0) both_pos++;
            if (w[0] < 0 && w[3] < 0) both_neg++;
        }
        
        if (b % 1000000000LL == 0) {
            printf("b=%lld, both_pos: %lld, both_neg: %lld\n", b, both_pos, both_neg);
        }
    }
    
    printf("Final both_pos: %lld, both_neg: %lld\n", both_pos, both_neg);
    return 0;
}
