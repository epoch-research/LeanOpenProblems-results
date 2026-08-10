#include <stdio.h>
#include <stdlib.h>

int main() {
    long long limit = 10000000000LL; // 10 billion
    long long a_prev2 = 0;
    long long a_prev1 = 1;
    long long both_pos = 0;
    long long both_neg = 0;
    
    // We need to keep a buffer of size 4 to compare a(n) and a(n+3).
    // Specifically, when we compute a(n), we can compare it with a(n-3).
    // Let's store the last 4 values: a(n), a(n-1), a(n-2), a(n-3).
    long long buf[4] = {0};
    buf[0] = 0; // a(0)
    buf[1] = 1; // a(1)
    
    // a(2)
    buf[2] = (buf[1] ^ 2) - buf[0];
    
    // a(3)
    buf[3] = (buf[2] ^ 3) - buf[1];
    if (buf[0] > 0 && buf[3] > 0) both_pos++;
    if (buf[0] < 0 && buf[3] < 0) both_neg++;
    
    long long a_p2 = buf[2];
    long long a_p1 = buf[3];
    
    for (long long n = 2; n < limit - 2; n++) {
        long long b = n + 2;
        long long val = (a_p1 ^ b) - a_p2;
        a_p2 = a_p1;
        a_p1 = val;
        
        // We want to compare val = a(b) with a(b-3).
        // Since we are moving forward, we can just maintain a shifting buffer of size 4.
        // Or simpler: let's store a larger buffer if we want, but since we only need n-3,
        // we can do it by saving values.
        // Let's write a simpler way: since limit is 10 billion, we can't store 10 billion elements.
        // But we can store the last 4 elements of the sequence!
        // Let's do that.
    }
    return 0;
}
