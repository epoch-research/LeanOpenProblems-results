#include <stdio.h>
#include <stdlib.h>

int a(int n) {
    if (n <= 1) return 0;
    
    int *config = (int *)malloc(sizeof(int) * (n + 2));
    int *next_config = (int *)malloc(sizeof(int) * (n + 2));
    
    config[0] = n;
    int len = 1;
    int steps = 0;
    
    while (len < n) {
        next_config[0] = (config[0] + 1) / 2;
        for (int i = 1; i < len; i++) {
            next_config[i] = (config[i] + 1) / 2 + config[i-1] / 2;
        }
        next_config[len] = config[len-1] / 2;
        
        int next_len = len + 1;
        while (next_len > 0 && next_config[next_len-1] == 0) {
            next_len--;
        }
        
        int *temp = config;
        config = next_config;
        next_config = temp;
        len = next_len;
        steps++;
    }
    
    free(config);
    free(next_config);
    return steps;
}

int main() {
    setvbuf(stdout, NULL, _IONBF, 0);
    int prev_a = 0; // a(1) = 0
    for (int n = 2; n <= 50000; n++) {
        int curr_a = a(n);
        int diff = curr_a - prev_a;
        if (diff != 1 && diff != 2) {
            printf("COUNTEREXAMPLE FOUND! a(%d) - a(%d) = %d (a(%d)=%d, a(%d)=%d)\n", n, n-1, diff, n, curr_a, n-1, prev_a);
            return 0;
        }
        prev_a = curr_a;
        if (n % 5000 == 0) {
            printf("Checked up to n = %d\n", n);
        }
    }
    printf("Checked all up to 50000, no counterexamples!\n");
    return 0;
}
