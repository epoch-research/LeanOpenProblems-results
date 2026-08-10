#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main() {
    int Bad[10] = {65, 67, 69, 71, 73, 75, 77, 79, 81, 83};
    int max_M = 10000;
    
    // Allocate buffer for BFS
    char *visited = malloc(max_M);
    int *queue = malloc(max_M * sizeof(int));
    
    for (int M = 4; M <= max_M; M += 4) {
        memset(visited, 0, M);
        int head = 0, tail = 0;
        
        int start = 64 % M;
        visited[start] = 1;
        queue[tail++] = start;
        
        int found_bad = 0;
        // Pre-check if start is bad
        for (int i = 0; i < 10; i++) {
            if (start == Bad[i] % M) {
                found_bad = 1;
                break;
            }
        }
        
        if (found_bad) continue;
        
        while (head < tail) {
            int curr = queue[head++];
            
            // Generate transitions
            int nxt[4];
            int num_nxt = 0;
            if (curr % 2 == 0) {
                // f(x) = 3x/2
                // x = q*M + curr
                // f(x) = q*(3M/2) + 3*curr/2
                nxt[0] = ((3 * curr) / 2) % M;
                nxt[1] = ((3 * M) / 2 + (3 * curr) / 2) % M;
                num_nxt = 2;
            } else if (curr % 4 == 1) {
                // f(x) = (3x+1)/4 = q*(3M/4) + (3*curr+1)/4
                int base = (3 * curr + 1) / 4;
                nxt[0] = base % M;
                nxt[1] = ((3 * M) / 4 + base) % M;
                nxt[2] = ((6 * M) / 4 + base) % M;
                nxt[3] = ((9 * M) / 4 + base) % M;
                num_nxt = 4;
            } else {
                // curr % 4 == 3
                int base = (3 * curr - 1) / 4;
                nxt[0] = base % M;
                nxt[1] = ((3 * M) / 4 + base) % M;
                nxt[2] = ((6 * M) / 4 + base) % M;
                nxt[3] = ((9 * M) / 4 + base) % M;
                num_nxt = 4;
            }
            
            for (int i = 0; i < num_nxt; i++) {
                int val = nxt[i];
                if (!visited[val]) {
                    // Check if val is bad
                    int is_bad = 0;
                    for (int j = 0; j < 10; j++) {
                        if (val == Bad[j] % M) {
                            is_bad = 1;
                            break;
                        }
                    }
                    if (is_bad) {
                        found_bad = 1;
                        goto next_M;
                    }
                    visited[val] = 1;
                    queue[tail++] = val;
                }
            }
        }
        
        next_M:
        if (!found_bad) {
            printf("FOUND INVARIANT MODULO M = %d!\n", M);
            free(visited);
            free(queue);
            return 0;
        }
    }
    
    printf("No modular invariant found under %d.\n", max_M);
    free(visited);
    free(queue);
    return 0;
}
