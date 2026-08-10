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
    int n_start = 99990;
    int n_end = 100010;
    
    int prev_a = a(n_start - 1);
    for (int n = n_start; n <= n_end; n++) {
        int curr_a = a(n);
        int diff = curr_a - prev_a;
        printf("a(%d) = %d, diff = %d\n", n, curr_a, diff);
        prev_a = curr_a;
    }
    return 0;
}
