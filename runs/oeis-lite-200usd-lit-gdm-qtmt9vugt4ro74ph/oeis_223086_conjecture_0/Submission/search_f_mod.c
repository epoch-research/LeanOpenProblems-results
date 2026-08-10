#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main() {
    int Z[14] = {58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84};
    int max_M = 100000;
    
    char *visited = malloc(max_M);
    int *queue = malloc(max_M * sizeof(int));
    
    for (int M = 4; M <= max_M; M += 4) {
        memset(visited, 0, M);
        int head = 0, tail = 0;
        
        // Push all z % M to queue
        int found_bad = 0;
        for (int i = 0; i < 14; i++) {
            int r = Z[i] % M;
            if (r == 85 % M) {
                found_bad = 1;
                break;
            }
            if (!visited[r]) {
                visited[r] = 1;
                queue[tail++] = r;
            }
        }
        if (found_bad) continue;
        
        while (head < tail) {
            int curr = queue[head++];
            
            // Generate transitions under f
            int nxt[4];
            int num_nxt = 0;
            if (curr % 2 == 0) {
                nxt[0] = ((3 * curr) / 2) % M;
                nxt[1] = ((3 * M) / 2 + (3 * curr) / 2) % M;
                num_nxt = 2;
            } else if (curr % 4 == 1) {
                int base = (3 * curr + 1) / 4;
                nxt[0] = base % M;
                nxt[1] = ((3 * M) / 4 + base) % M;
                nxt[2] = ((6 * M) / 4 + base) % M;
                nxt[3] = ((9 * M) / 4 + base) % M;
                num_nxt = 4;
            } else {
                int base = (3 * curr - 1) / 4;
                nxt[0] = base % M;
                nxt[1] = ((3 * M) / 4 + base) % M;
                nxt[2] = ((6 * M) / 4 + base) % M;
                nxt[3] = ((9 * M) / 4 + base) % M;
                num_nxt = 4;
            }
            
            for (int i = 0; i < num_nxt; i++) {
                int val = nxt[i];
                if (val == 85 % M) {
                    found_bad = 1;
                    goto next_M;
                }
                if (!visited[val]) {
                    visited[val] = 1;
                    queue[tail++] = val;
                }
            }
        }
        
        next_M:
        if (!found_bad) {
            printf("FOUND INVARIANT MODULO M = %d!\n", M);
            printf("Number of states: %d\n", tail);
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
