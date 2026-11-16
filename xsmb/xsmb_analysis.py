#!/usr/bin/env python3
"""Tính tỷ lệ trúng các cách soi cầu XSMB và xuất số liệu cho trang xsmb/index.html.

Cách dùng:
    python3 xsmb_analysis.py <ket_qua_xsmb.csv> <thu_muc_data>

- ket_qua_xsmb.csv: bảng kết quả (cột Ngay yyyy-mm-dd, Thu, Dai, ĐB, G1, G2.1 … G7.4, ...).
- thu_muc_data: thư mục xsmb/data. Hai file nhật ký (nhat_ky.csv, nhat_ky_cach.csv) trong đó
  được giữ lại: dòng cũ không bị viết lại, dòng "Chờ kết quả" được chấm khi đã có kết quả,
  và đề xuất cho kỳ kế tiếp được thêm vào đầu file (chỉ thêm, không sửa đề xuất đã ghi).
"""
import csv
import json
import math
import os
import random
import sys
from collections import defaultdict
from datetime import date, timedelta

COLS = (['ĐB', 'G1', 'G2.1', 'G2.2'] + [f'G3.{i}' for i in range(1, 7)] + [f'G4.{i}' for i in range(1, 5)]
        + [f'G5.{i}' for i in range(1, 7)] + [f'G6.{i}' for i in range(1, 4)] + [f'G7.{i}' for i in range(1, 5)])
PN = 1 - 0.98 ** 27   # một cặp AB/BA (A≠B) về ít nhất 1 nháy
PK = 1 - 0.99 ** 27   # một số kép AA về ít nhất 1 nháy
WINDOWS = [15, 30, 60]
TREND_LAG = 5
MIN_N = 3             # số lần báo tối thiểu trong cửa sổ để vẽ điểm
GAN_MAX = 10          # lô đã quá số kỳ này chưa về thì bỏ khỏi đề xuất (quy tắc thêm ngày 16/11/2026)
METHODS = [  # (mã, tên hiển thị)
    ('C1', 'Cách 1 · 0AB…'), ('C2', 'Cách 2 · X0AB…'), ('C3', 'Cách 3 · ABBXX'), ('C4', 'Cách 4 · ABBB…'),
    ('C5', 'Cách 5 · AB/BA lặp ≥2'), ('C6', 'Cách 6 · G7 0AB'), ('C7', 'Cách 7 · ĐB XABAX + G1 XXAXX'), ('C8', 'Cách 8 · Pascal ĐB+G1'), ('>=2', 'Trùng ≥2 cách'), ('>=3', 'Trùng ≥3 cách'),
    ('1+5', 'Cách 1+5'), ('3+5', 'Cách 3+5'), ('3+4', 'Cách 3+4'), ('RND', 'Đối chứng · 6 cặp ngẫu nhiên/ngày'),
]
BEST = [('C1', 'Cách 1 · 0AB…'), ('C2', 'Cách 2 · X0AB…'), ('C3', 'Cách 3 · ABBXX'), ('C4', 'Cách 4 · ABBB…'),
        ('C5', 'Cách 5 · AB/BA lặp ≥2'), ('C6', 'Cách 6 · G7 0AB'), ('C7', 'Cách 7 · ĐB XABAX + G1 XXAXX'), ('C8', 'Cách 8 · Pascal ĐB+G1'), ('>=2', 'Trùng ≥2 cách'), ('1+5', 'Cách 1+5'),
        ('3+5', 'Cách 3+5'), ('3+4', 'Cách 3+4'), ('3|4', 'Cách 3 hoặc 4')]
NAME = dict(METHODS + BEST)
SINGLE = ['C1', 'C2', 'C3', 'C4', 'C5', 'C6', 'C7']


def key(a, b):
    return tuple(sorted((a, b)))


def fmt_pair(k):
    a, b = k
    return a + b if a == b else f'{a}{b} – {b}{a}'


def pexp(k):
    return PK if k[0] == k[1] else PN


def r1(x):
    return '' if x is None else round(x + 1e-9, 1)


def signals(r):
    """Trả về {mã cách: {cặp: [(số gốc, vị trí), ...]}} cho một kỳ."""
    S = {m: defaultdict(list) for m in SINGLE}
    nums = [(c, r[c]) for c in COLS]
    for c, n in nums:
        L = len(n)
        if L in (4, 5) and n[0] == '0':
            S['C1'][key(n[1], n[2])].append((n, c))
        if L == 5 and n[1] == '0':
            S['C2'][key(n[2], n[3])].append((n, c))
        if L == 5 and n[1] == n[2] and n[0] != n[1]:
            S['C3'][key(n[0], n[1])].append((n, c))
        if L in (4, 5) and n[1] == n[2] == n[3] and n[0] != n[1]:
            S['C4'][key(n[0], n[1])].append((n, c))
    head = defaultdict(list)
    for c, n in nums:
        if len(n) in (4, 5):
            head[key(n[0], n[1])].append((n, c))
    for k, v in head.items():
        if len(v) >= 2:
            S['C5'][k] = v
    g7 = ''.join(r[c] for c in COLS[-4:])
    for i in range(len(g7) - 2):
        if g7[i] == '0':
            S['C6'][key(g7[i + 1], g7[i + 2])].append((' '.join(r[c] for c in COLS[-4:]), 'G7'))
    # Cách 7: giải đặc biệt XABAX (chữ số 2 = chữ số 4 = A, chữ số 3 = B) và giải nhất XXAXX (chữ số giữa = A) → AB/BA
    db, g1 = r['ĐB'], r['G1']
    if len(db) == 5 and len(g1) == 5 and db[1] == db[3] and g1[2] == db[1]:
        S['C7'][key(db[1], db[2])].append((db + ' + ' + g1, 'ĐB'))
    # Cách 8 (Pascal, không tính vào các tổ hợp trùng): ghép 5 số ĐB + 5 số G1, cộng từng cặp chữ số liền nhau
    # lấy hàng đơn vị, lặp lại đến khi còn 2 chữ số AB → AB/BA
    d = [int(x) for x in r['ĐB'] + r['G1']]
    while len(d) > 2:
        d = [(a + b) % 10 for a, b in zip(d, d[1:])]
    S['C8'] = defaultdict(list)
    S['C8'][key(str(d[0]), str(d[1]))].append((r['ĐB'] + ' + ' + r['G1'], 'ĐB'))
    return S


def method_sets(S, rnd=None):
    sets = {m: set(S[m]) for m in SINGLE}
    cnt = defaultdict(int)
    for m in SINGLE:
        for k in sets[m]:
            cnt[k] += 1
    sets['>=2'] = {k for k, v in cnt.items() if v >= 2}
    sets['>=3'] = {k for k, v in cnt.items() if v >= 3}
    sets['1+5'] = sets['C1'] & sets['C5']
    sets['3+5'] = sets['C3'] & sets['C5']
    sets['3+4'] = sets['C3'] & sets['C4']
    sets['3|4'] = sets['C3'] | sets['C4']
    sets['C8'] = set(S['C8'])
    if rnd is not None:
        sets['RND'] = rnd
    return sets


def sources(S, m, k):
    if m in SINGLE or m == 'C8':
        return S[m][k]
    out = []
    for s in SINGLE:
        for x in S[s].get(k, []):
            if x not in out:
                out.append(x)
    return out


def lo(r):
    return [r[c][-2:] for c in COLS]


def hit(k, L):
    a, b = k
    return (a + b) in L or (b + a) in L


def main(src, outdir):
    rows = sorted(csv.DictReader(open(src, encoding='utf-8')), key=lambda r: r['Ngay'])
    rows = [r for r in rows if all(r.get(c) for c in COLS)]
    rng = random.Random(20260426)
    allpairs = [key(str(a), str(b)) for a in range(10) for b in range(a + 1, 10)]   # 45 cặp AB/BA, không gồm kép
    # D[i]: thống kê tín hiệu báo từ kỳ i, chấm bằng kỳ i+1
    D, SIG = [], []
    for i, r in enumerate(rows):
        S = signals(r)
        rnd = set()
        while len(rnd) < 6:
            rnd.add(rng.choice(allpairs))
        sets = method_sets(S, rnd)
        SIG.append((S, sets))
        if i + 1 < len(rows):
            L = lo(rows[i + 1])
            D.append({m: (len(st), sum(hit(k, L) for k in st), sum(pexp(k) for k in st)) for m, st in sets.items()})
    nD = len(D)
    dates = [rows[i + 1]['Ngay'] for i in range(nD)]   # ngày có kết quả để chấm

    def window(m, j, w):
        n = h = e = 0
        for t in range(max(0, j - w + 1), j + 1):
            a, b, c = D[t][m]
            n += a; h += b; e += c
        return n, h, e

    series, summary = [], []
    for m, name in METHODS:
        tot_n = sum(d[m][0] for d in D); tot_h = sum(d[m][1] for d in D); tot_e = sum(d[m][2] for d in D)
        rate = 100 * tot_h / tot_n if tot_n else None
        expd = 100 * tot_e / tot_n if tot_n else None
        z = (tot_h - tot_e) / math.sqrt(tot_n * (expd / 100) * (1 - expd / 100)) if tot_n else None
        for w in WINDOWS:
            P, cn, ch = [], 0, 0
            for j in range(nD):
                cn += D[j][m][0]; ch += D[j][m][1]
                if j < w - 1:
                    continue
                n, h, e = window(m, j, w)
                if n < MIN_N:
                    continue
                p = e / n; sd = 1.96 * math.sqrt(p * (1 - p) / n)
                P.append(dict(j=j, n=n, rate=100 * h / n, exp=100 * p, lo=max(0, 100 * (p - sd)),
                              hi=min(100, 100 * (p + sd)), cum=100 * ch / cn if cn else 0))
            pk, tr = [], []
            for idx, p in enumerate(P):
                nb = P[max(0, idx - 7): idx + 8]
                if p['rate'] == max(q['rate'] for q in nb) and p['rate'] > p['exp'] and not (pk and p['j'] - pk[-1]['j'] <= 7):
                    pk.append(p); p['marker'] = 'Đỉnh'
                if p['rate'] == min(q['rate'] for q in nb) and p['rate'] < p['exp'] and not (tr and p['j'] - tr[-1]['j'] <= 7):
                    tr.append(p); p['marker'] = 'Đáy'

            def after(ms):
                n = h = 0
                for p in ms:   # ngày thứ 8 đến 37 sau mỗi đỉnh/đáy (đỉnh/đáy xác nhận sau 7 ngày)
                    for t in range(p['j'] + 8, min(nD, p['j'] + 38)):
                        n += D[t][m][0]; h += D[t][m][1]
                return (100 * h / n if n else None), n
            gaps = [b['j'] - a['j'] for a, b in zip(pk, pk[1:])]
            ap, apn = after(pk); at, atn = after(tr)
            summary.append(dict(method=name, window=w, avg_peak_gap=r1(sum(gaps) / len(gaps)) if gaps else '',
                                min_peak_gap=min(gaps) if gaps else '', max_peak_gap=max(gaps) if gaps else '',
                                signals=tot_n, hits=tot_h, rate=r1(rate), expected=r1(expd), z=r1(z),
                                roll_max=r1(max(p['rate'] for p in P)) if P else '', roll_min=r1(min(p['rate'] for p in P)) if P else '',
                                peaks=len(pk), troughs=len(tr), days_outside_band=sum(1 for p in P if p['rate'] < p['lo'] or p['rate'] > p['hi']),
                                days_charted=len(P), rate_after_peak=r1(ap), signals_after_peak=apn,
                                rate_after_trough=r1(at), signals_after_trough=atn))
            for p in P:
                series.append(dict(date=dates[p['j']], method=name, window=w, rate=r1(p['rate']), expected=r1(p['exp']),
                                   band_low=r1(p['lo']), band_high=r1(p['hi']), cumulative=r1(p['cum']),
                                   signals_30d=p['n'], marker=p.get('marker', '')))

    # Tỷ lệ về lại theo vị trí số gốc (gộp 6 cách, toàn bộ dữ liệu)
    pos = defaultdict(lambda: [0, 0])
    for i in range(nD):
        S, _ = SIG[i]; L = lo(rows[i + 1])
        for m in SINGLE:
            for k, src_ in S[m].items():
                for _, c in src_:
                    pos[c][0] += 1; pos[c][1] += hit(k, L)
    prate = {c: 100 * v[1] / v[0] for c, v in pos.items() if v[0]}

    # Trạng thái cầu: chuỗi ngày có báo của mỗi cách, ngày "trúng" khi ít nhất 1 cặp của cách đó về
    def outcomes(m):
        return [1 if D[j][m][1] > 0 else 0 for j in range(nD) if D[j][m][0] > 0]

    def state_of(seq):
        if len(seq) < 3:
            return 'Chưa đủ dữ liệu'
        if seq[-2:] == [1, 1]:
            return 'Đang chạy'
        if seq[-2:] == [0, 1]:
            return 'Vừa chạy lại'
        if seq[-3:] == [1, 1, 0]:
            return 'Vừa gãy'
        if seq[-3:] == [0, 0, 0]:
            return 'Trượt 3 kỳ liền'
        return 'Vừa trượt'

    STATES = ['Đang chạy', 'Vừa chạy lại', 'Vừa gãy', 'Vừa trượt', 'Trượt 3 kỳ liền']
    # Chạy thử: tỷ lệ trúng của kỳ báo kế tiếp theo trạng thái cầu, so với tỷ lệ thường của chính cách đó
    st_rows = []
    agg = {s_: [0, 0, 0.0] for s_ in STATES}
    for m in ['C1', 'C2', 'C3', 'C5', 'C6', '>=2']:
        seq = outcomes(m)
        if not seq:
            continue
        base_rate = sum(seq) / len(seq)
        for t in range(6, len(seq)):
            st = state_of(seq[:t])
            if st in agg:
                agg[st][0] += 1; agg[st][1] += seq[t]; agg[st][2] += base_rate
    for s_ in STATES:
        n, h, e = agg[s_]
        st_rows.append(dict(state=s_, days=n, hits=h, rate=r1(100 * h / n) if n else '',
                            base_rate=r1(100 * e / n) if n else '', diff=r1(100 * (h - e) / n) if n else ''))

    # Cặp tốt nhất theo từng cách cho kỳ kế tiếp
    last = rows[-1]
    for_date = (date.fromisoformat(last['Ngay']) + timedelta(days=1)).isoformat()
    lastlbl = date.fromisoformat(last['Ngay']).strftime('%d/%m')
    S, sets = SIG[-1]
    best = []
    for m, name in BEST:
        n15, h15, _ = window(m, nD - 1, 15)
        nb, hb, _ = window(m, nD - 1 - TREND_LAG, 15)   # so với cửa sổ 15 ngày kết thúc 5 kỳ trước
        r15 = 100 * h15 / n15 if n15 else None
        rb = 100 * hb / nb if nb else None
        trend = 'đi ngang' if r15 is None or rb is None or abs(r15 - rb) < 1e-9 else ('lên' if r15 > rb else 'xuống')
        tn = sum(d[m][0] for d in D); th = sum(d[m][1] for d in D); te = sum(d[m][2] for d in D)
        seq = outcomes(m)
        base = dict(for_date=for_date, method=name, state=state_of(seq), last5=''.join('✓' if x else '✗' for x in seq[-5:]), rate_15d=r1(r15), rate_15d_before=r1(rb), trend=trend, signals_15d=n15,
                    rate_200=r1(100 * th / tn) if tn else '', signals_200=tn, expected=r1(100 * te / tn) if tn else '')
        cands = []
        for k in sets[m]:
            src_ = sources(S, m, k)
            pr = sum(prate.get(c, 0) for _, c in src_) / len(src_)   # trung bình theo các số gốc
            cands.append((pr, k, src_))
        cands.sort(key=lambda x: (-x[0], x[1]))
        if not cands:
            best.append(dict(base, pair='Không có', source=f'Kỳ {lastlbl} không có số khớp', position_rate='', other_pairs='', _pairs=[]))
            continue
        pr, k, src_ = cands[0]
        best.append(dict(base, pair=fmt_pair(k), source='; '.join(f'{n} ({c})' for n, c in src_), position_rate=r1(pr),
                         other_pairs=', '.join(''.join(x[1]) for x in cands[1:]), _pairs=cands))

    # Đề xuất 2 cặp, theo thứ tự ưu tiên:
    #  1) cặp được nhiều cách cùng báo (3 cách, rồi 2 cách); cùng số cách thì cặp có nhiều cách "Đang chạy" hơn,
    #     rồi đến tỷ lệ về lại của vị trí số gốc;
    #  2) cặp của cách đơn đang ở trạng thái "Đang chạy" (cách có tỷ lệ 15 ngày cao hơn trước);
    #  3) còn thiếu thì lấy theo cách đang đi lên, trên mức ngẫu nhiên, ≥10 lần báo/15 ngày.
    #  Ở mọi bước đều lọc lô khan (> GAN_MAX kỳ chưa về), xem hàm add() bên dưới.
    state = {b['method']: b['state'] for b in best}
    running = {m for m in SINGLE if state.get(NAME[m]) == 'Đang chạy'}
    agree = defaultdict(list)
    for m in SINGLE:
        for k in S[m]:
            agree[k].append(m)
    g = next(x for x in best if x['method'] == 'Trùng ≥2 cách')
    multi = []
    for k, ms in agree.items():
        if len(ms) >= 2:
            src_ = sources(S, '>=2', k)
            pr = sum(prate.get(c, 0) for _, c in src_) / len(src_)
            multi.append((-len(ms), -len(set(ms) & running), -pr, k, ms, src_))
    multi.sort()

    # Quy tắc lô khan: con lô đã quá GAN_MAX kỳ chưa về thì bỏ khỏi đề xuất. Cặp có 1 con khan thì chỉ
    # đề xuất con còn lại; cả 2 con (hoặc con kép) khan thì bỏ cả cặp và lấy cặp xếp ngay dưới.
    gan = {}
    for x in range(100):
        s = f'{x:02d}'
        n_gan = 0
        for r in reversed(rows):
            if s in lo(r):
                break
            n_gan += 1
        gan[s] = n_gan
    de_xuat = []
    used = set()

    def add(k, rec):
        if len(de_xuat) >= 2 or k in used:
            return
        nums = sorted({k[0] + k[1], k[1] + k[0]})
        keep = [n for n in nums if gan[n] <= GAN_MAX]
        drop = [n for n in nums if gan[n] > GAN_MAX]
        if not keep:
            return
        used.add(k)
        rec['pair'] = fmt_pair(k) if len(keep) == len(nums) else keep[0]
        if drop:
            rec['method'] += '; bỏ ' + ', '.join(f'{n} (khan {gan[n]} kỳ)' for n in drop)
        de_xuat.append(rec)

    for _, nrun, _, k, ms, src_ in multi:
        add(k, dict(for_date=for_date, pair=fmt_pair(k),
                            method=f'Trùng {len(ms)} cách ({"+".join(x[1:] for x in ms)})' + (f', {-nrun} cách đang chạy' if nrun else ''),
                            source_numbers='; '.join(f'{n} ({c})' for n, c in src_[:3]),
                            trend_from=g['rate_15d_before'], trend_to=g['rate_15d'], rate_15d=g['rate_15d'],
                            signals_15d=g['signals_15d'], rate_200=g['rate_200'], signals_200=g['signals_200'],
                            expected=g['expected']))
    run_best = sorted([b for b in best if b['_pairs'] and b['method'] in {NAME[m] for m in running}],
                      key=lambda b: -(b['rate_15d'] if b['rate_15d'] != '' else -1))
    for b in run_best:
        for pr, k, src_ in b['_pairs']:
            add(k, dict(for_date=for_date, pair=fmt_pair(k), method=b['method'] + ' (đang chạy)',
                                source_numbers='; '.join(f'{n} ({c})' for n, c in src_[:1]),
                                trend_from=b['rate_15d_before'], trend_to=b['rate_15d'], rate_15d=b['rate_15d'],
                                signals_15d=b['signals_15d'], rate_200=b['rate_200'], signals_200=b['signals_200'],
                                expected=b['expected']))
    ok = [b for b in best if b['_pairs'] and b['trend'] == 'lên' and b['signals_15d'] >= 10
          and b['rate_15d'] != '' and b['expected'] != '' and b['rate_15d'] > b['expected']]
    ok.sort(key=lambda b: -b['rate_15d'])
    if ok and len(de_xuat) < 2:
        b = ok[0]
        for pr, k, src_ in b['_pairs']:
            form = ''
            if b['method'] == 'Cách 3 hoặc 4':
                form = ' dạng ' + ('ABBXX' if k in S['C3'] else 'ABBB')
            add(k, dict(for_date=for_date, pair=fmt_pair(k), method=b['method'],
                                source_numbers='; '.join(f'{n} ({c})' for n, c in src_[:1]) + form,
                                trend_from=b['rate_15d_before'], trend_to=b['rate_15d'], rate_15d=b['rate_15d'],
                                signals_15d=b['signals_15d'], rate_200=b['rate_200'], signals_200=b['signals_200'],
                                expected=b['expected']))

    os.makedirs(outdir, exist_ok=True)

    def write(name, recs, cols):
        with open(os.path.join(outdir, name), 'w', newline='', encoding='utf-8') as f:
            w = csv.DictWriter(f, fieldnames=cols, extrasaction='ignore')
            w.writeheader(); w.writerows(recs)

    write('series.csv', series, ['date', 'method', 'window', 'rate', 'expected', 'band_low', 'band_high', 'cumulative', 'signals_30d', 'marker'])
    write('summary.csv', summary, list(summary[0].keys()))
    write('states.csv', st_rows, ['state', 'days', 'hits', 'rate', 'base_rate', 'diff'])
    write('best.csv', best, ['for_date', 'method', 'pair', 'source', 'position_rate', 'other_pairs', 'state', 'last5', 'rate_15d', 'rate_15d_before',
                             'trend', 'signals_15d', 'rate_200', 'signals_200', 'expected'])
    write('de_xuat.csv', de_xuat, ['for_date', 'pair', 'method', 'source_numbers', 'trend_from', 'trend_to', 'rate_15d',
                                   'signals_15d', 'rate_200', 'signals_200', 'expected'])

    # Nhật ký: chấm dòng đang chờ, thêm đề xuất kỳ kế tiếp (không sửa dòng cũ)
    res = {r['Ngay']: lo(r) for r in rows}

    def grade(rec):
        if rec.get('result') != 'Chờ kết quả' or rec['for_date'] not in res:
            return rec
        L = res[rec['for_date']]
        p = rec['pair'].replace(' ', '').split('–')
        nums = sorted(set(p))
        came = [f'{x} ({L.count(x)} nháy)' for x in nums if x in L]
        rec['result'] = 'Trúng' if came else 'Trượt'
        rec['came'] = ', '.join(came)
        return rec

    def merge(name, cols, new, keyf):
        path = os.path.join(outdir, name)
        old = list(csv.DictReader(open(path, encoding='utf-8'))) if os.path.exists(path) else []
        old = [grade(r) for r in old]
        have = {keyf(r) for r in old}
        add = [r for r in new if keyf(r) not in have]
        if any(r['for_date'] == for_date for r in old):
            add = []   # đề xuất của kỳ này đã ghi trước đó: giữ nguyên
            fill = {keyf(r): r for r in new}
            for r in old:   # chỉ bổ sung cột trạng thái còn trống, không đổi cặp đã ghi
                if r['for_date'] == for_date and not r.get('state') and keyf(r) in fill:
                    r['state'] = fill[keyf(r)].get('state', '')
        write(name, add + old, cols)

    merge('nhat_ky.csv', ['for_date', 'pair', 'method', 'source_numbers', 'rate_15d', 'expected', 'result', 'came'],
          [dict(d, result='Chờ kết quả', came='') for d in de_xuat], lambda r: (r['for_date'], r['pair']))
    merge('nhat_ky_cach.csv', ['for_date', 'method', 'pair', 'source', 'state', 'result', 'came'],
          [dict(for_date=for_date, method=b['method'], pair=b['pair'], source='' if b['pair'] == 'Không có' else b['source'], state=b['state'],
                result='Không báo' if b['pair'] == 'Không có' else 'Chờ kết quả', came='') for b in best],
          lambda r: (r['for_date'], r['method']))

    first, lastd = rows[0]['Ngay'], rows[-1]['Ngay']
    fd = lambda s: date.fromisoformat(s).strftime('%d/%m/%Y')
    json.dump(dict(draws=len(rows), first=fd(first), last=fd(lastd), next=fd(for_date)),
              open(os.path.join(outdir, 'meta.json'), 'w', encoding='utf-8'), ensure_ascii=False)
    print(f'{len(rows)} kỳ {fd(first)}–{fd(lastd)}; đề xuất cho {fd(for_date)}: '
          + (', '.join(d['pair'] + ' (' + d['method'] + ')' for d in de_xuat) or 'không có'))


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
