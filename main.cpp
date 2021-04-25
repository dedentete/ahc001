#pragma GCC optimize("Ofast")
#include <bits/stdc++.h>
using namespace std;
#define rep(i, n) for (int i = 0; i < (int)(n); i++)
#define ALL(v) (v).begin(), (v).end()
using ll = long long;

constexpr int MAX_N = 200;
constexpr int M = 10000;

int n;
int x[MAX_N], y[MAX_N], r[MAX_N];

pair<int, int> ax[MAX_N], ay[MAX_N];
int axidx[MAX_N], ayidx[MAX_N];

int sumxl[M + 1], sumyl[M + 1], sumxr[M + 1], sumyr[M + 1];
int mema[MAX_N], memb[MAX_N], memc[MAX_N], memd[MAX_N];

struct XORShift {
    unsigned int x, y, z, w, t;

    XORShift(int seed) {
        mt19937 rnd(seed);
        x = rnd();
        y = rnd();
        z = rnd();
        w = rnd();
        t = 1;
    }

    int rand() {
        t = x ^ (x << 11);
        x = y;
        y = z;
        z = w;
        w = (w ^ (w >> 19)) ^ (t ^ (t >> 8));
        return w & 0x7fffffff;
    }
} rnd(rand());

struct Timer {
    chrono::system_clock::time_point start, now;

    Timer() {
        start = chrono::system_clock::now();
    }

    double getTime() {
        now = chrono::system_clock::now();
        return chrono::duration<double>(now - start).count();
    }
};

struct STATE {
    int a[MAX_N], b[MAX_N], c[MAX_N], d[MAX_N];
    int s[MAX_N];
    double score;
};

STATE state;

bool canExtendA(int &idx, int &na, int &nb, int &nd) {  // change a
    if (mema[idx] != -1 and state.c[mema[idx]] > na and
        state.d[mema[idx]] > nb and
        nd > state.b[mema[idx]])  // overlap with previous one
        return false;
    for (int i = min(axidx[idx], sumxl[state.a[idx]]) - 1; i >= 0;
         i--) {  // extend a
        if (state.c[ax[i].second] > na and state.d[ax[i].second] > nb and
            nd > state.b[ax[i].second]) {  // overlap
            mema[idx] = ax[i].second;
            return false;
        }
    }
    return true;
}

bool canExtendB(int &idx, int &na, int &nb, int &nc) {  // change b
    if (memb[idx] != -1 and state.c[memb[idx]] > na and
        state.d[memb[idx]] > nb and
        nc > state.a[memb[idx]])  // overlap with previous one
        return false;
    for (int i = min(ayidx[idx], sumyl[state.b[idx]]) - 1; i >= 0;
         i--) {  // extend b
        if (state.c[ay[i].second] > na and state.d[ay[i].second] > nb and
            nc > state.a[ay[i].second]) {  // overlap
            memb[idx] = ay[i].second;
            return false;
        }
    }
    return true;
}

bool canExtendC(int &idx, int &nb, int &nc,
                int &nd) {  // change c
    if (memc[idx] != -1 and state.d[memc[idx]] > nb and
        nc > state.a[memc[idx]] and
        nd > state.b[memc[idx]])  // overlap with previous one
        return false;
    for (int i = max(axidx[idx] + 1, sumxr[state.c[idx]]); i < n;
         i++) {  // extend c
        if (state.d[ax[i].second] > nb and nc > state.a[ax[i].second] and
            nd > state.b[ax[i].second]) {  // overlap
            memc[idx] = ax[i].second;
            return false;
        }
    }
    return true;
}

bool canExtendD(int &idx, int &na, int &nc,
                int &nd) {  // change d
    if (memd[idx] != -1 and state.c[memd[idx]] > na and
        nc > state.a[memd[idx]] and
        nd > state.b[memd[idx]])  // overlap with previous one
        return false;
    for (int i = max(ayidx[idx] + 1, sumyr[state.d[idx]]); i < n;
         i++) {  // extend d
        if (state.c[ay[i].second] > na and nc > state.a[ay[i].second] and
            nd > state.b[ay[i].second]) {  // overlap
            memd[idx] = ay[i].second;
            return false;
        }
    }
    return true;
}

void init() {
    state.score = n;
    rep(i, n) {
        state.a[i] = x[i];
        state.b[i] = y[i];
        state.c[i] = x[i] + 1;
        state.d[i] = y[i] + 1;
        state.s[i] = 1;
        state.score -= (1 - 1.0 / r[i]) * (1 - 1.0 / r[i]);
        ax[i] = {x[i], i};
        ay[i] = {y[i], i};
        sumxl[x[i]]++;
        sumyl[y[i]]++;
        sumxr[x[i]]--;
        sumyr[y[i]]--;
        mema[i] = -1;
        memb[i] = -1;
        memc[i] = -1;
        memd[i] = -1;
    }
    sort(ax, ax + n);
    sort(ay, ay + n);
    rep(i, n) {
        axidx[ax[i].second] = i;
        ayidx[ay[i].second] = i;
    }
    rep(i, M) {
        sumxl[i + 1] += sumxl[i];
        sumyl[i + 1] += sumyl[i];
    }
    sumxr[M] = n;
    sumyr[M] = n;
    for (int i = M; i > 0; i--) {
        sumxr[i - 1] += sumxr[i];
        sumyr[i - 1] += sumyr[i];
    }
}

constexpr double TIMELIMIT = 4.9;

void SA() {
    init();
    double starttemp = 0.001 * n, endtemp = 0;
    int D = 0;
    Timer tmr;
    double startclock = tmr.getTime(), nowclock = 0;
    double temp = -1, prob;
    int steps = 0;
    double newstate_score;
    int idx, nx, ny = -1, width;
    int rand[3], new_s[2];
    rand[0] = -1;
    new_s[1] = -1;
    bool shrink;
    while (true) {
        if (steps % 10000 == 0) {
            nowclock = tmr.getTime();
            if (nowclock - startclock > TIMELIMIT) break;
            D = (TIMELIMIT - nowclock + startclock) * 250 + 50;
            temp = starttemp +
                   (endtemp - starttemp) * (nowclock - startclock) / TIMELIMIT;
        }
        newstate_score = state.score;
        if (nowclock - startclock > 3.0) rand[0] = rnd.rand() % 100;
        if (rand[0]) {
            bool flag = true;
            while (flag) {
                idx = rnd.rand() % n;
                rand[1] = rnd.rand() % 4;
                width = rnd.rand() % D + 1;
                switch (rand[1]) {
                    case 0: {  // change a
                        rand[2] = rnd.rand() % 2;
                        if (rand[2]) {
                            nx = state.a[idx] + width;
                            if (nx > x[idx])  // not included
                                break;
                            if (state.c[idx] <= nx) break;  // not rectangle
                            shrink = true;
                        } else {
                            nx = state.a[idx] - width;
                            if (nx < 0) break;  // not in square
                            shrink = false;
                        }
                        if (shrink or
                            canExtendA(idx, nx, state.b[idx], state.d[idx])) {
                            flag = false;
                            double mn = min(r[idx], state.s[idx]),
                                   mx = max(r[idx], state.s[idx]);
                            newstate_score += (1 - mn / mx) * (1 - mn / mx);
                            new_s[0] = (state.c[idx] - nx) *
                                       (state.d[idx] - state.b[idx]);
                            mn = min(r[idx], new_s[0]),
                            mx = max(r[idx], new_s[0]);
                            newstate_score -= (1 - mn / mx) * (1 - mn / mx);
                        }
                        break;
                    }
                    case 1: {  // change b
                        rand[2] = rnd.rand() % 2;
                        if (rand[2]) {
                            nx = state.b[idx] + width;
                            if (state.d[idx] <= nx) break;  // not rectangle
                            if (nx > y[idx])                // not included
                                break;
                            shrink = true;
                        } else {
                            nx = state.b[idx] - width;
                            if (nx < 0) break;  // not in square
                            shrink = false;
                        }
                        if (shrink or
                            canExtendB(idx, state.a[idx], nx, state.c[idx])) {
                            flag = false;
                            double mn = min(r[idx], state.s[idx]),
                                   mx = max(r[idx], state.s[idx]);
                            newstate_score += (1 - mn / mx) * (1 - mn / mx);
                            new_s[0] = (state.c[idx] - state.a[idx]) *
                                       (state.d[idx] - nx);
                            mn = min(r[idx], new_s[0]),
                            mx = max(r[idx], new_s[0]);
                            newstate_score -= (1 - mn / mx) * (1 - mn / mx);
                        }
                        break;
                    }
                    case 2: {  // change c
                        rand[2] = rnd.rand() % 2;
                        if (rand[2]) {
                            nx = state.c[idx] + width;
                            if (M < nx) break;  // not in square
                            shrink = false;
                        } else {
                            nx = state.c[idx] - width;
                            if (nx <= state.a[idx]) break;  // not rectangle
                            if (nx <= x[idx]) break;        // not included
                            shrink = true;
                        }
                        if (shrink or
                            canExtendC(idx, state.b[idx], nx, state.d[idx])) {
                            flag = false;
                            double mn = min(r[idx], state.s[idx]),
                                   mx = max(r[idx], state.s[idx]);
                            newstate_score += (1 - mn / mx) * (1 - mn / mx);
                            new_s[0] = (nx - state.a[idx]) *
                                       (state.d[idx] - state.b[idx]);
                            mn = min(r[idx], new_s[0]),
                            mx = max(r[idx], new_s[0]);
                            newstate_score -= (1 - mn / mx) * (1 - mn / mx);
                        }
                        break;
                    }
                    case 3: {  // change d
                        rand[2] = rnd.rand() % 2;
                        if (rand[2]) {
                            nx = state.d[idx] + width;
                            if (M < nx) break;  // not in square
                            shrink = false;
                        } else {
                            nx = state.d[idx] - width;
                            if (nx <= state.b[idx]) break;  // not rectangle
                            if (nx <= y[idx])               // not included
                                break;
                            shrink = true;
                        }
                        if (shrink or
                            canExtendD(idx, state.a[idx], state.c[idx], nx)) {
                            flag = false;
                            double mn = min(r[idx], state.s[idx]),
                                   mx = max(r[idx], state.s[idx]);
                            newstate_score += (1 - mn / mx) * (1 - mn / mx);
                            new_s[0] = (state.c[idx] - state.a[idx]) *
                                       (nx - state.b[idx]);
                            mn = min(r[idx], new_s[0]),
                            mx = max(r[idx], new_s[0]);
                            newstate_score -= (1 - mn / mx) * (1 - mn / mx);
                        }
                        break;
                    }
                }
            }
        } else {
            bool flag = true;
            while (flag) {
                idx = rnd.rand() % n;
                rand[1] = rnd.rand() % 4;
                width = rnd.rand() % (D / 10) + 1;
                switch (rand[1]) {
                    case 0: {
                        if (mema[idx] == -1) break;
                        rand[2] = rnd.rand() % 2;
                        if (rand[2]) {
                            nx = state.a[idx] + width;
                            ny = state.c[mema[idx]] + width;
                            if (nx > x[idx])  // not included
                                break;
                            if (state.c[idx] <= nx) break;  // not rectangle
                            if (M < ny) break;              // not in square
                            shrink = true;
                        } else {
                            nx = state.a[idx] - width;
                            ny = state.c[mema[idx]] - width;
                            if (nx < 0) break;  // not in square
                            if (ny <= state.a[mema[idx]])
                                break;                      // not rectangle
                            if (ny <= x[mema[idx]]) break;  // not included
                            shrink = false;
                        }
                        if ((shrink or canExtendA(idx, nx, state.b[idx],
                                                  state.d[idx])) and
                            (not shrink or
                             canExtendC(mema[idx], state.b[mema[idx]], ny,
                                        state.d[mema[idx]]))) {
                            flag = false;
                            double mn = min(r[idx], state.s[idx]),
                                   mx = max(r[idx], state.s[idx]);
                            newstate_score += (1 - mn / mx) * (1 - mn / mx);
                            mn = min(r[mema[idx]], state.s[mema[idx]]),
                            mx = max(r[mema[idx]], state.s[mema[idx]]);
                            newstate_score += (1 - mn / mx) * (1 - mn / mx);
                            new_s[0] = (state.c[idx] - nx) *
                                       (state.d[idx] - state.b[idx]);
                            mn = min(r[idx], new_s[0]),
                            mx = max(r[idx], new_s[0]);
                            newstate_score -= (1 - mn / mx) * (1 - mn / mx);
                            new_s[1] =
                                (ny - state.a[mema[idx]]) *
                                (state.d[mema[idx]] - state.b[mema[idx]]);
                            mn = min(r[mema[idx]], new_s[1]),
                            mx = max(r[mema[idx]], new_s[1]);
                            newstate_score -= (1 - mn / mx) * (1 - mn / mx);
                        }
                        break;
                    }
                    case 1: {
                        if (memb[idx] == -1) break;
                        rand[2] = rnd.rand() % 2;
                        if (rand[2]) {
                            nx = state.b[idx] + width;
                            ny = state.d[memb[idx]] + width;
                            if (state.d[idx] <= nx) break;  // not rectangle
                            if (nx > y[idx])                // not included
                                break;
                            if (M < ny) break;  // not in square
                            shrink = true;
                        } else {
                            nx = state.b[idx] - width;
                            ny = state.d[memb[idx]] - width;
                            if (nx < 0) break;  // not in square
                            if (ny <= state.b[memb[idx]])
                                break;               // not rectangle
                            if (ny <= y[memb[idx]])  // not included
                                break;
                            shrink = false;
                        }
                        if ((shrink or canExtendB(idx, state.a[idx], nx,
                                                  state.c[idx])) and
                            (not shrink or
                             canExtendD(memb[idx], state.a[memb[idx]],
                                        state.c[memb[idx]], ny))) {
                            flag = false;
                            double mn = min(r[idx], state.s[idx]),
                                   mx = max(r[idx], state.s[idx]);
                            newstate_score += (1 - mn / mx) * (1 - mn / mx);
                            mn = min(r[memb[idx]], state.s[memb[idx]]),
                            mx = max(r[memb[idx]], state.s[memb[idx]]);
                            newstate_score += (1 - mn / mx) * (1 - mn / mx);
                            new_s[0] = (state.c[idx] - state.a[idx]) *
                                       (state.d[idx] - nx);
                            mn = min(r[idx], new_s[0]),
                            mx = max(r[idx], new_s[0]);
                            newstate_score -= (1 - mn / mx) * (1 - mn / mx);
                            new_s[1] =
                                (state.c[memb[idx]] - state.a[memb[idx]]) *
                                (ny - state.b[memb[idx]]);
                            mn = min(r[memb[idx]], new_s[1]),
                            mx = max(r[memb[idx]], new_s[1]);
                            newstate_score -= (1 - mn / mx) * (1 - mn / mx);
                        }
                        break;
                    }
                    case 2: {
                        if (memc[idx] == -1) break;
                        rand[2] = rnd.rand() % 2;
                        if (rand[2]) {
                            nx = state.c[idx] + width;
                            ny = state.a[memc[idx]] + width;
                            if (M < nx) break;      // not in square
                            if (ny > x[memc[idx]])  // not included
                                break;
                            if (state.c[memc[idx]] <= ny)
                                break;  // not rectangle
                            shrink = false;
                        } else {
                            nx = state.c[idx] - width;
                            ny = state.a[memc[idx]] - width;
                            if (nx <= state.a[idx]) break;  // not rectangle
                            if (nx <= x[idx]) break;        // not included
                            if (ny < 0) break;              // not in square
                            shrink = true;
                        }
                        if ((shrink or canExtendC(idx, state.b[idx], nx,
                                                  state.d[idx])) and
                            (not shrink or
                             canExtendA(memc[idx], ny, state.b[memc[idx]],

                                        state.d[memc[idx]]))) {
                            flag = false;
                            double mn = min(r[idx], state.s[idx]),
                                   mx = max(r[idx], state.s[idx]);
                            newstate_score += (1 - mn / mx) * (1 - mn / mx);
                            mn = min(r[memc[idx]], state.s[memc[idx]]),
                            mx = max(r[memc[idx]], state.s[memc[idx]]);
                            newstate_score += (1 - mn / mx) * (1 - mn / mx);
                            new_s[0] = (nx - state.a[idx]) *
                                       (state.d[idx] - state.b[idx]);
                            mn = min(r[idx], new_s[0]),
                            mx = max(r[idx], new_s[0]);
                            newstate_score -= (1 - mn / mx) * (1 - mn / mx);
                            new_s[1] =
                                (state.c[memc[idx]] - ny) *
                                (state.d[memc[idx]] - state.b[memc[idx]]);
                            mn = min(r[memc[idx]], new_s[1]),
                            mx = max(r[memc[idx]], new_s[1]);
                            newstate_score -= (1 - mn / mx) * (1 - mn / mx);
                        }
                        break;
                    }
                    case 3: {
                        if (memd[idx] == -1) break;
                        rand[2] = rnd.rand() % 2;
                        if (rand[2]) {
                            nx = state.d[idx] + width;
                            ny = state.b[memd[idx]] + width;
                            if (M < nx) break;  // not in square
                            if (state.d[memd[idx]] <= ny)
                                break;  // not rectangle
                            if (ny > y[memd[idx]]) break;
                            shrink = false;
                        } else {
                            nx = state.d[idx] - width;
                            ny = state.b[memd[idx]] - width;
                            if (nx <= state.b[idx]) break;  // not rectangle
                            if (nx <= y[idx])               // not included
                                break;
                            if (ny < 0) break;  // not in square
                            shrink = true;
                        }
                        if ((shrink or canExtendD(idx, state.a[idx],
                                                  state.c[idx], nx)) and
                            (not shrink or
                             canExtendB(memd[idx], state.a[memd[idx]], ny,
                                        state.c[memd[idx]]))) {
                            flag = false;
                            double mn = min(r[idx], state.s[idx]),
                                   mx = max(r[idx], state.s[idx]);
                            newstate_score += (1 - mn / mx) * (1 - mn / mx);
                            mn = min(r[memd[idx]], state.s[memd[idx]]),
                            mx = max(r[memd[idx]], state.s[memd[idx]]);
                            newstate_score += (1 - mn / mx) * (1 - mn / mx);
                            new_s[0] = (state.c[idx] - state.a[idx]) *
                                       (nx - state.b[idx]);
                            mn = min(r[idx], new_s[0]),
                            mx = max(r[idx], new_s[0]);
                            newstate_score -= (1 - mn / mx) * (1 - mn / mx);
                            new_s[1] =
                                (state.c[memd[idx]] - state.a[memd[idx]]) *
                                (state.d[memd[idx]] - ny);
                            mn = min(r[memd[idx]], new_s[1]),
                            mx = max(r[memd[idx]], new_s[1]);
                            newstate_score -= (1 - mn / mx) * (1 - mn / mx);
                        }
                        break;
                    }
                }
            }
        }
        prob = exp((newstate_score - state.score) / temp);
        if (prob > (rnd.rand() % (int)1e9) / 1e9) {
            if (rand[0]) {
                state.score = newstate_score;
                state.s[idx] = new_s[0];
                switch (rand[1]) {
                    case 0:  // change a
                        state.a[idx] = nx;
                        break;
                    case 1:  // change b
                        state.b[idx] = nx;
                        break;
                    case 2:  // change c
                        state.c[idx] = nx;
                        break;
                    case 3:  // change d
                        state.d[idx] = nx;
                        break;
                }
            } else {
                state.score = newstate_score;
                state.s[idx] = new_s[0];
                switch (rand[1]) {
                    case 0:  // change a
                        state.a[idx] = nx;
                        state.c[mema[idx]] = ny;
                        state.s[mema[idx]] = new_s[1];
                        break;
                    case 1:  // change b
                        state.b[idx] = nx;
                        state.d[memb[idx]] = ny;
                        state.s[memb[idx]] = new_s[1];
                        break;
                    case 2:  // change c
                        state.c[idx] = nx;
                        state.a[memc[idx]] = ny;
                        state.s[memc[idx]] = new_s[1];
                        break;
                    case 3:  // change d
                        state.d[idx] = nx;
                        state.b[memd[idx]] = ny;
                        state.s[memd[idx]] = new_s[1];
                        break;
                }
            }
        }
        steps++;
    }
    cerr << "n     : " << n << endl;
    cerr << "steps : " << steps << endl;
    cerr << "score : " << state.score / n * 1e9 << endl;
}

void input() {
    cin >> n;
    rep(i, n) {
        cin >> x[i] >> y[i] >> r[i];
    }
}

void output() {
    rep(i, n) {
        cout << state.a[i] << " " << state.b[i] << " " << state.c[i] << " "
             << state.d[i] << endl;
    }
}

signed main() {
    input();
    SA();
    output();
    return 0;
}