#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <math.h>

typedef struct {
    double m;
    long long e;
} Val;

Val add(Val v1, Val v2, Val v3) {
    long long max_e = v1.e;
    if (v2.e > max_e) max_e = v2.e;
    if (v3.e > max_e) max_e = v3.e;
    
    double m1 = v1.m * pow(2.0, v1.e - max_e);
    double m2 = v2.m * pow(2.0, v2.e - max_e);
    double m3 = v3.m * pow(2.0, v3.e - max_e);
    
    double sum_m = m1 + m2 + m3;
    long long sum_e = max_e;
    while (sum_m >= 2.0) {
        sum_m /= 2.0;
        sum_e++;
    }
    while (sum_m < 1.0 && sum_m > 0) {
        sum_m *= 2.0;
        sum_e--;
    }
    Val res = {sum_m, sum_e};
    return res;
}

int get_a_val(Val v) {
    if (v.m >= 1.5) return 1;
    return 0;
}

int main() {
    long long limit = 100000000;
    
    int current_val = 0;
    long long run_len = 1;
    long long run_start = 2;
    
    Val prev3 = {1.0, 0}; // T_3 = 1
    Val prev2 = {1.0, 1}; // T_4 = 2
    Val prev1 = {1.0, 2}; // T_5 = 4
    
    for (long long n = 6; n < limit; n++) {
        Val curr = add(prev1, prev2, prev3);
        int val = get_a_val(curr);
        
        if (val == current_val) {
            run_len++;
        } else {
            bool is_maximal = true;
            if (run_start == 2 && current_val == 0) {
                is_maximal = false;
            }
            if (is_maximal) {
                if (current_val == 0) {
                    if (run_len != 4 && run_len != 5) {
                        printf("COUNTEREXAMPLE: 0-run of length %lld starting at n=%lld\n", run_len, run_start);
                        return 0;
                    }
                } else {
                    if (run_len != 3 && run_len != 4) {
                        printf("COUNTEREXAMPLE: 1-run of length %lld starting at n=%lld\n", run_len, run_start);
                        return 0;
                    }
                }
            }
            current_val = val;
            run_len = 1;
            run_start = n;
        }
        
        prev3 = prev2;
        prev2 = prev1;
        prev1 = curr;
    }
    
    printf("Checked up to %lld with no counterexamples!\n", limit);
    return 0;
}

