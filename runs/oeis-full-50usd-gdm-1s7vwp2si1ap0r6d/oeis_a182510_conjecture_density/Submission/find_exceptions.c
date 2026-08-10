#include <stdio.h>
#include <stdlib.h>
#include <math.h>

int main() {
    long long limit = 10000000000LL; // 10 billion
    long long a_prev2 = 0;
    long long a_prev1 = 1;
    long long last_exception = -1;
    long long num_exceptions = 0;
    
    if (abs(0) <= 5) { num_exceptions++; last_exception = 0; }
    if (abs(1) <= 7) { num_exceptions++; last_exception = 1; }
    
    for (long long n = 0; n < limit - 2; n++) {
        long long b = n + 2;
        long long val = (a_prev1 ^ b) - a_prev2;
        a_prev2 = a_prev1;
        a_prev1 = val;
        
        long long abs_val = val < 0 ? -val : val;
        if (abs_val <= 2 * b + 5) {
            num_exceptions++;
            last_exception = b;
        }
        
        if (b % 1000000000LL == 0) {
            printf("Reached b=%lld, num_exceptions: %lld, last_exception: %lld\n", b, num_exceptions, last_exception);
        }
    }
    
    printf("Total exceptions: %lld\n", num_exceptions);
    printf("Last exception: %lld\n", last_exception);
    return 0;
}
