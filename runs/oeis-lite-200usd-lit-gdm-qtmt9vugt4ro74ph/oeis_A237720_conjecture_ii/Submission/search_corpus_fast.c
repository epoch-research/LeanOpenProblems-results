#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <dirent.h>
#include <sys/stat.h>

#define SEARCH_STR "A237720"

void search_file(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) return;
    char buf[4096];
    while (fgets(buf, sizeof(buf), f)) {
        if (strstr(buf, SEARCH_STR)) {
            printf("Found match in file: %s\n", path);
            printf("Content: %s\n", buf);
        }
    }
    fclose(f);
}

void walk_dir(const char *dir_path) {
    DIR *dir = opendir(dir_path);
    if (!dir) return;
    struct dirent *entry;
    while ((entry = readdir(dir)) != NULL) {
        if (strcmp(entry->d_name, ".") == 0 || strcmp(entry->d_name, "..") == 0) {
            continue;
        }
        char path[1024];
        snprintf(path, sizeof(path), "%s/%s", dir_path, entry->d_name);
        struct stat st;
        if (stat(path, &st) == 0) {
            if (S_ISDIR(st.st_mode)) {
                walk_dir(path);
            } else if (S_ISREG(st.st_mode) && (strstr(path, ".tex") || strstr(path, ".txt"))) {
                search_file(path);
            }
        }
    }
    closedir(dir);
}

int main() {
    printf("Starting fast search for '%s' in /corpus/src...\n", SEARCH_STR);
    walk_dir("/corpus/src");
    printf("Search finished.\n");
    return 0;
}
