#include <stdio.h>
#include <stdlib.h>

int main() {
    long long limit = 200000000000LL; // 200 billion
    long long pos = 0;
    long long neg = 0;
    long long max_diff = -1;
    long long min_diff = 10000000000LL;
    long long max_b = -1;
    long long min_b = -1;
    
    long long a_prev2 = 0;
    long long a_prev1 = 1;
    
    if (a_prev2 > 0) pos++;
    else if (a_prev2 < 0) neg++;
    
    long long diff = pos - neg;
    if (diff > max_diff) { max_diff = diff; max_b = 0; }
    if (diff < min_diff) { min_diff = diff; min_b = 0; }
    
    if (a_prev1 > 0) pos++;
    else if (a_prev1 < 0) neg++;
    
    diff = pos - neg;
    if (diff > max_diff) { max_diff = diff; max_b = 1; }
    if (diff < min_diff) { min_diff = diff; min_b = 1; }
    
    for (long long n = 0; n < limit - 2; n++) {
        long long b = n + 2;
        long long val = (a_prev1 ^ b) - a_prev2;
        a_prev2 = a_prev1;
        a_prev1 = val;
        
        if (val > 0) pos++;
        else if (val < 0) neg++;
        
        diff = pos - neg;
        if (diff > max_diff) { max_diff = diff; max_b = b; }
        if (diff < min_diff) { min_diff = diff; min_b = b; }
        
        if (b % 10000000000LL == 0) {
            printf("Reached b=%lld, max_diff so far: %lld, min_diff so far: %lld, current diff: %lld\n", b, max_diff, min_diff, pos - neg);
        }
    }
    
    printf("Max diff: %lld at b=%lld\n", max_diff, max_b);
    printf("Min diff: %lld at b=%lld\n", min_diff, min_b);
    printf("Final diff: %lld at b=%lld\n", pos - neg, limit);
    return 0;
}
