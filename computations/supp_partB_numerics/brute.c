/* Exhaustive check over ALL planted branches with at most N vertices (independent of the witness argument).
 * A planted branch = root + multiset of planted branches (children); root degree d = #children + 1.
 * Cavity recursion: R = sum y_c, y = 1/(d + lam R), log T = sum log T_c + log(1 + lam R / d).
 * Reports, for the given lambda and F = f*(lambda):
 *   max_b (log T_b - |b| F)   (ceiling; must be <= 0, = 0 only at a best arm),
 *   min (g(b) - h(y_b)) over non-leaf b other than the cherry and the best arm, h = potential of W_1 (W*)
 *   (the slack identity says g(b) >= h(y_b) for every non-leaf b if W_1 is a witness).
 * usage: brute N lam F eps ydag kap jstar
 */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

static int N;
static double lam, F, eps, ydag, kap, yC, s1;
static double *Y, *L;
static int *S;
static long cnt, cap, lim;
static int curn;

static int npc = 0; static double pa[8], pb[8];   /* optional explicit pieces: h = max(0, pa[i] y + pb[i]) */
static double hpot(double y) {
    double m = 0.0;
    if (npc > 0) { for (int i = 0; i < npc; i++) { double v = pa[i] * y + pb[i]; if (v > m) m = v; } return m; }
    double a = s1 * (y - ydag), b = eps + kap * (y - yC);
    if (a > m) m = a;
    if (b > m) m = b;
    return m;
}

static void rec(long imin, int rem, int m, double R, double Ls) {
    if (rem == 0) {
        int d = m + 1;
        if (cnt >= cap) { fprintf(stderr, "capacity\n"); exit(1); }
        Y[cnt] = 1.0 / (d + lam * R);
        L[cnt] = Ls + log1p(lam * R / d);
        S[cnt] = curn;
        cnt++;
        return;
    }
    for (long i = imin; i < lim; i++) {
        if (S[i] > rem) break;
        rec(i, rem - S[i], m + 1, R + Y[i], Ls + L[i]);
    }
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: brute N lam F eps ydag kap jstar\n"); return 1; }
    N = atoi(argv[1]); lam = atof(argv[2]); F = atof(argv[3]); eps = atof(argv[4]);
    ydag = atof(argv[5]); kap = atof(argv[6]); int jstar = atoi(argv[7]);
    yC = 1.0 / (2.0 + lam); s1 = eps / (yC - ydag);
    for (int i = 8; i + 1 < argc && npc < 8; i += 2) { pa[npc] = atof(argv[i]); pb[npc] = atof(argv[i + 1]); npc++; }
    cap = 40000000L;
    Y = malloc(sizeof(double) * cap); L = malloc(sizeof(double) * cap); S = malloc(sizeof(int) * cap);
    Y[0] = 1.0; L[0] = 0.0; S[0] = 1; cnt = 1;
    for (curn = 2; curn <= N; curn++) {
        lim = cnt;
        rec(0, curn - 1, 0, 0.0, 0.0);
    }
    double maxc = -1e300, mind = 1e300; long ic = -1, id = -1; int armfound = 0;
    double yarm = 1.0 / (jstar + 1 + jstar * lam / (2 + lam));
    for (long i = 0; i < cnt; i++) {
        double c = L[i] - S[i] * F;
        if (c > maxc) { maxc = c; ic = i; }
        if (S[i] <= 2) continue;   /* leaf exempt; cherry is the designed equality g = h(yC) = eps */
        if (S[i] == 2 * jstar + 1 && fabs(Y[i] - yarm) < 1e-12) { armfound = 1; continue; }
        double dd = (S[i] * F - L[i]) - hpot(Y[i]);
        if (dd < mind) { mind = dd; id = i; }
    }
    printf("N=%d lam=%.6f branches=%ld max(logT-|b|F)=%+.3e [size %d, y=%.5f]  min(g-h)=%+.3e [size %d, y=%.5f] bestarm_in_range=%d\n",
           N, lam, cnt, maxc, S[ic], Y[ic], mind, id >= 0 ? S[id] : -1, id >= 0 ? Y[id] : 0.0, armfound);
    return 0;
}
