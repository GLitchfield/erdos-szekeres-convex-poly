/* Memoized interval-cut evaluator for context-bound-zero-children-v1.
 *
 * Tokens are 0 for S, +level for a lower external marker, and -level for an
 * upper marker.  This is an exploratory implementation, not a Lean checker.
 */
#include <limits.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
    uint64_t hash;
    size_t depth;
    int *key;
    int64_t value;
    int used;
} CacheEntry;

typedef struct {
    int a, u, k;
    size_t word_len;
    size_t cache_limit, cache_count, cache_capacity;
    CacheEntry *cache;
    int error;
} EvalState;

/* Public ctypes entry point. */
int es_context_bound(int a, int u, int k, const int *word, size_t word_len,
                     const int *maxima, size_t depth, size_t cache_size,
                     int64_t *out);

static uint64_t hash_context(const int *word, size_t n, const int *maxima, size_t depth) {
    uint64_t h = 1469598103934665603ULL;
    h ^= (uint64_t)depth; h *= 1099511628211ULL;
    for (size_t i = 0; i < n; ++i) {
        h ^= (uint32_t)word[i]; h *= 1099511628211ULL;
    }
    for (size_t i = 0; i < depth; ++i) {
        h ^= (uint32_t)maxima[i]; h *= 1099511628211ULL;
    }
    return h;
}

static int key_equal(const CacheEntry *entry, const int *word, size_t n,
                     const int *maxima, size_t depth) {
    return entry->depth == depth &&
           memcmp(entry->key, word, n * sizeof(int)) == 0 &&
           (depth == 0 || memcmp(entry->key + n, maxima, depth * sizeof(int)) == 0);
}

static int cache_lookup(EvalState *state, const int *word, const int *maxima,
                        size_t depth, int64_t *value) {
    uint64_t hash = hash_context(word, state->word_len, maxima, depth);
    size_t slot = (size_t)hash & (state->cache_capacity - 1);
    for (size_t probes = 0; probes < state->cache_capacity; ++probes) {
        CacheEntry *entry = &state->cache[slot];
        if (!entry->used) return 0;
        if (entry->hash == hash && key_equal(entry, word, state->word_len, maxima, depth)) {
            *value = entry->value;
            return 1;
        }
        slot = (slot + 1) & (state->cache_capacity - 1);
    }
    return 0;
}

static void cache_insert(EvalState *state, const int *word, const int *maxima,
                         size_t depth, int64_t value) {
    if (state->cache_count >= state->cache_limit || state->error) return;
    uint64_t hash = hash_context(word, state->word_len, maxima, depth);
    size_t slot = (size_t)hash & (state->cache_capacity - 1);
    while (state->cache[slot].used) slot = (slot + 1) & (state->cache_capacity - 1);
    size_t count = state->word_len + depth;
    int *key = malloc((count ? count : 1) * sizeof(int));
    if (!key) { state->error = 2; return; }
    memcpy(key, word, state->word_len * sizeof(int));
    if (depth) memcpy(key + state->word_len, maxima, depth * sizeof(int));
    state->cache[slot] = (CacheEntry){hash, depth, key, value, 1};
    state->cache_count++;
}

static int64_t gcd_int64(int64_t a, int64_t b) {
    while (b) {
        int64_t remainder = a % b;
        a = b;
        b = remainder;
    }
    return a;
}

static int choose_int(int n, int r, int64_t *out) {
    if (r < 0 || r > n) { *out = 0; return 1; }
    if (r > n - r) r = n - r;
    int64_t result = 1;
    for (int i = 1; i <= r; ++i) {
        int64_t numerator = n - r + i;
        int64_t denominator = i;
        int64_t common = gcd_int64(result, denominator);
        result /= common;
        denominator /= common;
        common = gcd_int64(numerator, denominator);
        numerator /= common;
        denominator /= common;
        if (denominator != 1 || result > INT64_MAX / numerator) return 0;
        result *= numerator;
    }
    *out = result;
    return 1;
}

static int threshold(int a, int u, int k, int64_t *out) {
    if (a <= 1 || u <= 1) { *out = 0; return 1; }
    int64_t combined = (int64_t)a + u;
    if (combined <= (int64_t)k + 3) {
        if (combined - 4 > INT_MAX) return 0;
        return choose_int((int)(combined - 4), a - 2, out);
    }
    int64_t total = 0;
    for (int j = k - a; j <= u - 2; ++j) {
        int64_t term;
        if (!choose_int(k - 2, j, &term) || INT64_MAX - total < term) return 0;
        total += term;
    }
    *out = total;
    return 1;
}

static int max_state(const int *states, size_t count) {
    int best = 0;
    for (size_t i = 0; i < count; ++i) if (states[i] > best) best = states[i];
    return best;
}

static int extension(const int *levels, const int *sides, size_t ext_count,
                     const int *side_at, const int *maxima, size_t depth,
                     int gap, int grow_side, int *strong_out) {
    size_t states_n = ext_count + 1;
    int *left = malloc(states_n * sizeof(int));
    int *right = malloc(states_n * sizeof(int));
    int *next_left = malloc(states_n * sizeof(int));
    int *next_right = malloc(states_n * sizeof(int));
    if (!left || !right || !next_left || !next_right) {
        free(left); free(right); free(next_left); free(next_right);
        return -1;
    }
    for (size_t i = 0; i < states_n; ++i) left[i] = right[i] = -1;
    left[ext_count] = right[ext_count] = 0;
    int best_strong = 0;
    for (size_t li = 1; li <= depth; ++li) {
        if (side_at[li - 1] != grow_side) continue;
        int64_t below = (int64_t)max_state(left, states_n) + max_state(right, states_n);
        int64_t candidate = below + maxima[li - 1];
        if (candidate > best_strong)
            best_strong = candidate > INT_MAX ? INT_MAX : (int)candidate;
        memcpy(next_left, left, states_n * sizeof(int));
        memcpy(next_right, right, states_n * sizeof(int));
        for (size_t state = 0; state < states_n; ++state) {
            if (left[state] >= 0) {
                int bound = state == ext_count ? gap : (int)state;
                for (size_t x = 0; x < ext_count; ++x)
                    if (levels[x] == (int)li && sides[x] == grow_side && (int)x < bound &&
                        left[state] + 1 > next_left[x])
                        next_left[x] = left[state] + 1;
            }
            if (right[state] >= 0) {
                int bound = state == ext_count ? gap : (int)state + 1;
                for (size_t x = 0; x < ext_count; ++x)
                    if (levels[x] == (int)li && sides[x] == grow_side && (int)x >= bound &&
                        right[state] + 1 > next_right[x])
                        next_right[x] = right[state] + 1;
            }
        }
        int *swap = left; left = next_left; next_left = swap;
        swap = right; right = next_right; next_right = swap;
    }
    int count = max_state(left, states_n) + max_state(right, states_n);
    *strong_out = best_strong > count ? best_strong : count;
    free(left); free(right); free(next_left); free(next_right);
    return count;
}

static int64_t base_value(EvalState *state, const int *word, const int *maxima, size_t depth) {
    size_t ext_count = 0;
    int gap = -1;
    for (size_t i = 0; i < state->word_len; ++i) {
        if (word[i] == 0) { if (gap < 0) gap = (int)ext_count; }
        else ext_count++;
    }
    if (gap < 0) { state->error = 3; return 0; }
    int *levels = malloc((ext_count ? ext_count : 1) * sizeof(int));
    int *sides = malloc((ext_count ? ext_count : 1) * sizeof(int));
    int *side_at = malloc((depth ? depth : 1) * sizeof(int));
    int *seen = calloc(depth ? depth : 1, sizeof(int));
    if (!levels || !sides || !side_at || !seen) {
        free(levels); free(sides); free(side_at); free(seen);
        state->error = 2; return 0;
    }
    for (size_t li = 0; li < depth; ++li) side_at[li] = 1; /* unused levels are lower */
    size_t e = 0;
    for (size_t i = 0; i < state->word_len; ++i) if (word[i] != 0) {
        int level = word[i] > 0 ? word[i] : -word[i];
        int side = word[i] > 0 ? 1 : -1;
        if (level < 1 || (size_t)level > depth || (seen[level - 1] && side_at[level - 1] != side)) {
            state->error = 3; break;
        }
        seen[level - 1] = 1; side_at[level - 1] = side;
        levels[e] = level; sides[e] = side; e++;
    }
    int cup_strong = 0, cap_strong = 0;
    int cup_ext = state->error ? -1 : extension(levels, sides, ext_count, side_at, maxima, depth,
                                                 gap, 1, &cup_strong);
    int cap_ext = state->error ? -1 : extension(levels, sides, ext_count, side_at, maxima, depth,
                                                 gap, -1, &cap_strong);
    free(levels); free(sides); free(side_at); free(seen);
    if (cup_ext < 0 || cap_ext < 0) { if (!state->error) state->error = 2; return 0; }
    int cup_limit = state->u - 1 - cup_ext;
    int cup_join = state->k - 1 - cup_strong;
    if (cup_join < cup_limit) cup_limit = cup_join;
    if (cup_limit < 0) cup_limit = 0;
    int cap_limit = state->a - 1 - cap_ext;
    int cap_join = state->k - 1 - cap_strong;
    if (cap_join < cap_limit) cap_limit = cap_join;
    if (cap_limit < 0) cap_limit = 0;
    int minimum = cup_limit < cap_limit ? cup_limit : cap_limit;
    if (minimum < 1) return 0;
    if (minimum < 2) return 1;
    int64_t result;
    if (!threshold(cap_limit + 1, cup_limit + 1, state->k, &result)) {
        state->error = 4;
        return 0;
    }
    return result;
}

static int64_t bound(EvalState *state, const int *word, const int *maxima, size_t depth) {
    if (state->error) return 0;
    int64_t cached;
    if (cache_lookup(state, word, maxima, depth, &cached)) return cached;
    size_t run_count = 0, s_count = 0;
    int previous_s = 0;
    for (size_t pos = 0; pos < state->word_len; ++pos) {
        int is_s = word[pos] == 0;
        if (is_s) { s_count++; if (!previous_s) run_count++; }
        previous_s = is_s;
    }
    if (!s_count) { state->error = 3; return 0; }
    int64_t best = 0;
    if (run_count == 1) {
        best = base_value(state, word, maxima, depth);
        cache_insert(state, word, maxima, depth, best);
        return best;
    }
    int *block_word = malloc(state->word_len * sizeof(int));
    int *rest_word = malloc(state->word_len * sizeof(int));
    int *block_max = malloc((depth + 1) * sizeof(int));
    int *rest_max = malloc((depth + 1) * sizeof(int));
    if (!block_word || !rest_word || !block_max || !rest_max) {
        free(block_word); free(rest_word); free(block_max); free(rest_max);
        state->error = 2; return 0;
    }
    if (depth) {
        memcpy(block_max + 1, maxima, depth * sizeof(int));
        memcpy(rest_max + 1, maxima, depth * sizeof(int));
    }
    for (size_t first = 0; first < s_count && !state->error; ++first) {
        for (size_t last = first; last < s_count && !state->error; ++last) {
            if (first == 0 && last + 1 == s_count) continue;
            for (int orientation = 0; orientation < 2 && !state->error; ++orientation) {
                int block_side = orientation == 0 ? 1 : -1;
                int rest_side = -block_side;
                size_t ordinal = 0;
                for (size_t pos = 0; pos < state->word_len; ++pos) {
                    if (word[pos] == 0) {
                        int in_block = ordinal >= first && ordinal <= last;
                        block_word[pos] = in_block ? 0 : block_side;
                        rest_word[pos] = in_block ? rest_side : 0;
                        ordinal++;
                    } else {
                        block_word[pos] = rest_word[pos] = word[pos] > 0 ? word[pos] + 1 : word[pos] - 1;
                    }
                }
                for (int dp = 1; dp < state->k - 1 && !state->error; ++dp) {
                    int c = state->k - 1 - dp;
                    block_max[0] = block_side == 1 ? dp : c;
                    rest_max[0] = rest_side == -1 ? c : dp;
                    int64_t left = bound(state, block_word, block_max, depth + 1);
                    int64_t right = state->error ? 0 : bound(state, rest_word, rest_max, depth + 1);
                    if (left > INT64_MAX - right) { state->error = 4; break; }
                    int64_t sum = left + right;
                    if (sum > best) best = sum;
                }
            }
        }
    }
    free(block_word); free(rest_word); free(block_max); free(rest_max);
    cache_insert(state, word, maxima, depth, best);
    return best;
}

/* 0 success; 1 bad scalar input; 2 allocation failure; 3 malformed context; 4 overflow. */
int es_context_bound(int a, int u, int k, const int *word, size_t word_len,
                     const int *maxima, size_t depth, size_t cache_size,
                     int64_t *out) {
    if (!word || !out || word_len == 0 || a < 1 || u < 1 || k < 3 || cache_size == 0) return 1;
    if (depth && !maxima) return 1;
    if (word_len > INT_MAX) return 1;
    size_t s_count = 0;
    for (size_t i = 0; i < word_len; ++i) if (word[i] == 0) s_count++;
    if (!s_count) return 3;
    int shift_limit = (int)s_count - 1;
    for (size_t i = 0; i < word_len; ++i) {
        if (word[i] == INT_MIN) return 3;
        int level = word[i] < 0 ? -word[i] : word[i];
        if (level > INT_MAX - shift_limit) return 3;
    }
    for (size_t i = 0; i < depth; ++i) if (maxima[i] < 0) return 3;
    size_t capacity = 1;
    if (cache_size > SIZE_MAX / 2) return 1;
    while (capacity < cache_size * 2) {
        if (capacity > SIZE_MAX / 2) return 1;
        capacity *= 2;
    }
    EvalState state = {a, u, k, word_len, cache_size, 0, capacity, NULL, 0};
    state.cache = calloc(capacity, sizeof(CacheEntry));
    if (!state.cache) return 2;
    int64_t result = bound(&state, word, maxima, depth);
    for (size_t i = 0; i < capacity; ++i) free(state.cache[i].key);
    free(state.cache);
    if (state.error) return state.error;
    *out = result;
    return 0;
}
