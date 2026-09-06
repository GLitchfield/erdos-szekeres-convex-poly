/* Enumerate the decomposable colorings on n <= MAXN ordered vertices that avoid an
 * a-cap, a u-cup and a strong k-set (Workstream B), by the split recursion of
 * experiment 0114 restricted to the avoiding subclass (hereditary), with the union
 * lemma of experiments 0116/0117 as the rejection test and records bucketed by their
 * longest cup / cap so that only pairs compatible with the strong coupling
 * (cupmax(L) + capmax(U) <= k-1) are examined.
 *
 *   enum_avoid a u k maxn outdir
 *
 * Per n it writes outdir/class_<n>.bin: fixed records
 *   uint64 mask[MASKW]; int8 cupT[n*n]; int8 capT[n*n]; int8 strong; int8 cupmax; int8 capmax; int8 pad
 * (triples of n in lexicographic order, bit set = left turn; cupT[f*n+l] = longest cup with
 * first vertex f and last vertex l, 0 if none; single vertices 1, pairs 2) and prints the
 * counts as JSON on stdout.  Validated against the Python enumerator on small cases.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 16
#define MAXT (MAXN * (MAXN - 1) * (MAXN - 2) / 6)
#define MASKW ((MAXT + 63) / 64)

typedef struct {
    uint64_t mask[MASKW];
    int8_t cupT[MAXN * MAXN];
    int8_t capT[MAXN * MAXN];
    int8_t strong, cupmax, capmax;
} Rec;

typedef struct {
    Rec *recs;
    size_t count, cap;
    size_t *table;      /* hash table of indices+1, 0 = empty */
    size_t tcap;
} Class;

static int A, U, K;
static int tri_index[MAXN][MAXN][MAXN];
static int ntri[MAXN + 1];

static uint64_t hash_mask(const uint64_t *m) {
    uint64_t h = 1469598103934665603ULL;
    for (int w = 0; w < MASKW; w++) { h ^= m[w]; h *= 1099511628211ULL; h ^= h >> 29; }
    return h;
}

static void class_init(Class *c) { memset(c, 0, sizeof *c); c->tcap = 1 << 16; c->table = calloc(c->tcap, sizeof(size_t)); }

static void class_rehash(Class *c) {
    size_t ncap = c->tcap * 2;
    size_t *nt = calloc(ncap, sizeof(size_t));
    for (size_t i = 0; i < c->count; i++) {
        size_t h = hash_mask(c->recs[i].mask) & (ncap - 1);
        while (nt[h]) h = (h + 1) & (ncap - 1);
        nt[h] = i + 1;
    }
    free(c->table); c->table = nt; c->tcap = ncap;
}

/* returns 1 if inserted (new), 0 if present; on insert the record slot is *out */
static int class_insert(Class *c, const uint64_t *mask, Rec **out) {
    if (c->count * 2 >= c->tcap) class_rehash(c);
    size_t h = hash_mask(mask) & (c->tcap - 1);
    while (c->table[h]) {
        if (!memcmp(c->recs[c->table[h] - 1].mask, mask, sizeof(uint64_t) * MASKW)) return 0;
        h = (h + 1) & (c->tcap - 1);
    }
    if (c->count == c->cap) { c->cap = c->cap ? c->cap * 2 : 1024; c->recs = realloc(c->recs, c->cap * sizeof(Rec)); }
    Rec *r = &c->recs[c->count];
    memset(r, 0, sizeof *r);
    memcpy(r->mask, mask, sizeof(uint64_t) * MASKW);
    c->table[h] = ++c->count;
    *out = r;
    return 1;
}

static inline int color(const uint64_t *mask, int i, int j, int k) {
    int t = tri_index[i][j][k];
    return (mask[t >> 6] >> (t & 63)) & 1;
}

/* chain tables and strong max for a coloring on n vertices */
static void compute_tables(Rec *r, int n) {
    static int8_t endt[MAXN][MAXN][MAXN]; /* endt[i][j][f]: longest chain ending with edge (i,j), first f */
    for (int left = 0; left < 2; left++) {
        int8_t *T = left ? r->cupT : r->capT;
        memset(T, 0, n * n);
        for (int v = 0; v < n; v++) T[v * n + v] = 1;
        for (int j = 0; j < n; j++)
            for (int i = 0; i < j; i++) {
                for (int f = 0; f < n; f++) endt[i][j][f] = 0;
                endt[i][j][i] = 2;
                for (int h = 0; h < i; h++)
                    if (color(r->mask, h, i, j) == left)
                        for (int f = 0; f <= h; f++)
                            if (endt[h][i][f] && endt[h][i][f] + 1 > endt[i][j][f]) endt[i][j][f] = endt[h][i][f] + 1;
                for (int f = 0; f <= i; f++)
                    if (endt[i][j][f] > T[f * n + j]) T[f * n + j] = endt[i][j][f];
            }
    }
    int8_t cm = 0, pm = 0;
    for (int x = 0; x < n * n; x++) { if (r->cupT[x] > cm) cm = r->cupT[x]; if (r->capT[x] > pm) pm = r->capT[x]; }
    r->cupmax = cm; r->capmax = pm;
    /* strong max: the largest s < K with a strong s-set (subsets of size 4..K-1); we only need whether
       a strong K-set exists for rejection, which the union lemma decides, so record min(largest, K) */
    int largest = n >= 3 ? 3 : n;
    int vs[MAXN];
    for (int s = 4; s <= n && s <= K; s++) {
        int found = 0;
        /* iterate s-subsets */
        for (int i = 0; i < s; i++) vs[i] = i;
        while (1) {
            int ok = 1;
            for (int p = 0; p < s && ok; p++) for (int q = p + 1; q < s && ok; q++) for (int w = q + 1; w < s && ok; w++) for (int z = w + 1; z < s && ok; z++) {
                int i = vs[p], j = vs[q], m = vs[w], l = vs[z];
                if (color(r->mask, i, j, m) != color(r->mask, i, j, l) || color(r->mask, i, m, l) != color(r->mask, j, m, l)) ok = 0;
            }
            if (ok) { found = 1; break; }
            int t = s - 1;
            while (t >= 0 && vs[t] == n - s + t) t--;
            if (t < 0) break;
            vs[t]++;
            for (int q = t + 1; q < s; q++) vs[q] = vs[q - 1] + 1;
        }
        if (found) largest = s; else break;
    }
    r->strong = (int8_t)largest;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: enum_avoid a u k maxn outdir\n"); return 2; }
    A = atoi(argv[1]); U = atoi(argv[2]); K = atoi(argv[3]);
    int maxn = atoi(argv[4]); const char *outdir = argv[5];
    if (maxn > MAXN) { fprintf(stderr, "maxn <= %d\n", MAXN); return 2; }
    for (int n = 0; n <= MAXN; n++) {
        int t = 0;
        for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) for (int k = j + 1; k < n; k++) tri_index[i][j][k] = t++;
        ntri[n] = t;
    }
    /* note: tri_index is overwritten per n above; recompute per n when needed */
    Class *cls = calloc(maxn + 1, sizeof(Class));
    for (int n = 1; n <= maxn; n++) class_init(&cls[n]);
    /* n = 1, 2: the single empty coloring */
    for (int n = 1; n <= 2 && n <= maxn; n++) {
        uint64_t zero[MASKW] = {0}; Rec *r;
        class_insert(&cls[n], zero, &r);
        for (int v = 0; v < n; v++) { r->cupT[v * n + v] = 1; r->capT[v * n + v] = 1; }
        if (n == 2) { r->cupT[1] = 2; r->capT[1] = 2; }
        r->strong = n; r->cupmax = n; r->capmax = n;
    }
    printf("{\"case\": [%d, %d, %d], \"counts\": {", A, U, K);
    for (int n = 3; n <= maxn; n++) {
        /* triple index for this n */
        int t = 0;
        for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) for (int k = j + 1; k < n; k++) tri_index[i][j][k] = t++;
        long long candidates = 0;
        for (int lower_bits = 1; lower_bits < (1 << n) - 1; lower_bits++) {
            int lower[MAXN], upper[MAXN], nl = 0, nu = 0;
            for (int v = 0; v < n; v++) { if (lower_bits >> v & 1) lower[nl++] = v; else upper[nu++] = v; }
            Class *CL = &cls[nl], *CU = &cls[nu];
            if (!CL->count || !CU->count) continue;
            /* positional flags */
            int u_left[MAXN], u_right[MAXN], l_left[MAXN], l_right[MAXN];
            for (int f = 0; f < nl; f++) { u_left[f] = upper[0] < lower[f]; u_right[f] = upper[nu - 1] > lower[f]; }
            for (int f = 0; f < nu; f++) { l_left[f] = lower[0] < upper[f]; l_right[f] = lower[nl - 1] > upper[f]; }
            /* crossing triples: left iff middle vertex in lower */
            uint64_t cross[MASKW] = {0};
            for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) for (int k = j + 1; k < n; k++) {
                int inl = (lower_bits >> i & 1) + (lower_bits >> j & 1) + (lower_bits >> k & 1);
                if ((inl == 1 || inl == 2) && (lower_bits >> j & 1)) { int ti = tri_index[i][j][k]; cross[ti >> 6] |= 1ULL << (ti & 63); }
            }
            /* transport tables: part-triple index -> global triple index */
            static int tl[MAXT], tu[MAXT];
            int cl = 0, cu = 0;
            for (int x = 0; x < nl; x++) for (int y = x + 1; y < nl; y++) for (int z = y + 1; z < nl; z++) tl[cl++] = tri_index[lower[x]][lower[y]][lower[z]];
            for (int x = 0; x < nu; x++) for (int y = x + 1; y < nu; y++) for (int z = y + 1; z < nu; z++) tu[cu++] = tri_index[upper[x]][upper[y]][upper[z]];
            /* upper records passing their positional cap test, by capmax */
            static int *ubyc[MAXN + 1]; static int ubyc_n[MAXN + 1];
            for (int c = 0; c <= MAXN; c++) ubyc_n[c] = 0;
            for (int c = 0; c <= MAXN; c++) { ubyc[c] = realloc(ubyc[c], (CU->count + 1) * sizeof(int)); }
            for (size_t iu = 0; iu < CU->count; iu++) {
                Rec *ru = &CU->recs[iu];
                if (ru->strong >= K || ru->cupmax >= U) continue;
                int ext = 0;
                for (int f = 0; f < nu; f++) for (int l = f; l < nu; l++) {
                    int v = ru->capT[f * nu + l]; if (!v) continue;
                    v += l_left[f] + l_right[l];
                    if (v > ext) ext = v;
                }
                if (ext >= A) continue;
                ubyc[ru->capmax][ubyc_n[ru->capmax]++] = (int)iu;
            }
            for (size_t il = 0; il < CL->count; il++) {
                Rec *rl = &CL->recs[il];
                if (rl->strong >= K || rl->capmax >= A) continue;
                int ext = 0;
                for (int f = 0; f < nl; f++) for (int l = f; l < nl; l++) {
                    int v = rl->cupT[f * nl + l]; if (!v) continue;
                    v += u_left[f] + u_right[l];
                    if (v > ext) ext = v;
                }
                if (ext >= U) continue;
                /* lifted lower mask */
                uint64_t ml[MASKW] = {0};
                for (int p = 0; p < cl; p++) if (rl->mask[p >> 6] >> (p & 63) & 1) ml[tl[p] >> 6] |= 1ULL << (tl[p] & 63);
                int dmax = K - 1 - rl->cupmax;
                for (int c = 1; c <= dmax && c <= MAXN; c++) {
                    for (int q = 0; q < ubyc_n[c]; q++) {
                        Rec *ru = &CU->recs[ubyc[c][q]];
                        candidates++;
                        uint64_t m[MASKW];
                        for (int w = 0; w < MASKW; w++) m[w] = cross[w] | ml[w];
                        for (int p = 0; p < cu; p++) if (ru->mask[p >> 6] >> (p & 63) & 1) m[tu[p] >> 6] |= 1ULL << (tu[p] & 63);
                        Rec *nr;
                        if (class_insert(&cls[n], m, &nr)) compute_tables(nr, n);
                    }
                }
            }
        }
        fprintf(stderr, "(%d,%d,%d)-avoiding n=%d: %zu colorings from %lld candidates\n", A, U, K, n, cls[n].count, candidates);
        printf("%s\"%d\": %zu", n > 3 ? ", " : "", n, cls[n].count);
        fflush(stdout);
        /* write records */
        char path[512]; snprintf(path, sizeof path, "%s/class_%d.bin", outdir, n);
        FILE *fp = fopen(path, "wb");
        if (fp) {
            for (size_t i = 0; i < cls[n].count; i++) {
                Rec *r = &cls[n].recs[i];
                fwrite(r->mask, sizeof(uint64_t), MASKW, fp);
                fwrite(r->cupT, 1, n * n, fp); fwrite(r->capT, 1, n * n, fp);
                int8_t tail[4] = {r->strong, r->cupmax, r->capmax, 0}; fwrite(tail, 1, 4, fp);
            }
            fclose(fp);
        }
        if (!cls[n].count) break;
    }
    printf("}}\n");
    return 0;
}
