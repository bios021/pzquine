import struct
from bitarray import bitarray
from bitarray.util import int2ba
import sys, os
import datetime
import zlib
from crcfix import find_crc_positions, solve_crc
import zipfile, io
import argparse

LENGTH_TABLE = {
    257:(3,0),258:(4,0),259:(5,0),260:(6,0),261:(7,0),262:(8,0),
    263:(9,0),264:(10,0),265:(11,1),266:(13,1),267:(15,1),268:(17,1),
    269:(19,2),270:(23,2),271:(27,2),272:(31,2),273:(35,3),274:(43,3),
    275:(51,3),276:(59,3),277:(67,4),278:(83,4),279:(99,4),280:(115,4),
    281:(131,5),282:(163,5),283:(195,5),284:(227,5),285:(258,0),
}
# distance code 表:code -> (base, extra_bits)
DIST_TABLE = {
    0:(1,0),1:(2,0),2:(3,0),3:(4,0),4:(5,1),5:(7,1),6:(9,2),7:(13,2),
    8:(17,3),9:(25,3),10:(33,4),11:(49,4),12:(65,5),13:(97,5),
    14:(129,6),15:(193,6),16:(257,7),17:(385,7),18:(513,8),19:(769,8),
    20:(1025,9),21:(1537,9),22:(2049,10),23:(3073,10),
    24:(4097,11),25:(6145,11),26:(8193,12),27:(12289,12),
    28:(16385,13),29:(24577,13),
}

LFH_SIG=0x04034b50
CDH_SIG=0x02014b50
EOCD_SIG=0x06054b50

def length_to_symbol(length):
    if length == 258:
        return 285, 0, 0
    best = None
    for sym, (base, extra_bits) in LENGTH_TABLE.items():
        if base <= length:
            best = (sym, extra_bits, length - base)
    return best


def distance_to_symbol(length):
    best = None
    for sym, (base, extra_bits) in DIST_TABLE.items():
        if base <= length:
            best = (sym, extra_bits, length - base)
    return best

def l_token(length, final=False):
    header=bytes([1 if final else 0])
    return header+length.to_bytes(2, "little")+(length^0xffff).to_bytes(2, "little")


def fixed_litlen_code(sym):
    if sym <= 143: return 0x30 + sym, 8
    if sym <= 255: return 0x190 + (sym - 144), 9
    if sym <= 279: return sym - 256, 7
    return 0xC0 + (sym - 280), 8

def write_pair(a, length, distance):
    sym, ex_bit, ex= length_to_symbol(length)
    code, code_len=fixed_litlen_code(sym)
    a.extend(int2ba(code, code_len, endian="big"))
    if ex_bit:
        a.extend(int2ba(ex, ex_bit, endian='little'))
    sym, ex_bit, ex=distance_to_symbol(distance)
    a.extend(int2ba(sym, 5, endian="big"))
    if ex_bit:
        a.extend(int2ba(ex, ex_bit, endian='little'))

def splits(total, k):
    if k == 1:
        if 3<=total<=258:
            yield (total,)
        return 
    for first in range(3, min(258, total-3)+1):
        for rest in splits(total-first, k-1):
            yield (first,)+rest

def candidate_parts(n):
    top=n//258
    for i in range(max(0, top-2), top+1):
        rem=n-(258*i)
        if rem == 0:
            yield (258,)*i
            continue
        for k in (1,2,3):
            for parts in splits(rem, k):
                yield (258,)*i+parts




def encode_r(n, parts, empty=0, final=False):
    a=bitarray(endian="little")
    a.append(1 if (final and empty==0) else 0)
    a.extend(int2ba(1, 2, endian="little"))
    for part in parts:
        write_pair(a, part, n)
    a.extend(int2ba(0, 7, endian="little"))
    for i in range(empty):
        a.append(1 if (final and i==empty-1) else 0)
        a.extend(int2ba(1, 2, endian="little"))
        a.extend(int2ba(0, 7, endian="little"))
    return a

def r_token(n, size=None, final=False):
    """
    Rn：複製最後 n bytes。
    自動挑選拆法，讓總位元數 % 8 ∈ {0, 6, 7}（補齊位元 ≤ 2），後面接 L 才不會錯位。
    size=None → 盡量小；size=5 → 剛好 5 bytes。
    """
    best = None
    for parts in candidate_parts(n):
        bits0 = len(encode_r(n, parts))
        for empty in range(40):
            bits = bits0 + 10 * empty
            if size is not None and bits > 8 * size:
                break
            if bits % 8 not in (0, 6, 7):
                continue
            if size is not None and (bits + 7) // 8 != size:
                continue
            if best is None or bits < best[0]:
                best = (bits, parts, empty)
            break
    if best is None:
        raise ValueError(f"R{n} 無法編成 {size} bytes")
    _, parts, empty = best
    return bytearray(encode_r(n, parts, empty, final).tobytes())


def check_header_footer(P, S, y=0):
    """P、S 是 bytes；y 是放大後 R token 的大小（用 Cox 原版時 y=0）"""
    p, s = len(P), len(S)
    check_literal(p + 5);  check_repeat(p + 5)              # Lp+1、Rp+1
    if y == 0:
        check_literal(s + 5);  check_repeat(s + 5)          # Cox：Ls+1、Rs+1
    else:
        check_literal(s + y + 10);  check_repeat(s + y + 10)  # Table 6
    print(f"OK：p = {p}, s = {s}")

def find_y(s, max_y=64):
    for y in range(1, max_y + 1):
        try:
            return y, r_token(s + y + 10, size=y)
        except ValueError:
            pass
    raise RuntimeError(f"找不到符合的 y（s = {s}）")

def build_lfh(name, data, time, date):
    name_bytes = name.encode('utf-8')
    flag = 0x800 if not name.isascii() else 0
    comp = zlib.compressobj(9, zlib.DEFLATED, -15)  
    comp_data = comp.compress(data) + comp.flush()
    crc32 = zlib.crc32(data) & 0xFFFFFFFF           
    comp_size, uncomp_size, name_len = len(comp_data), len(data), len(name_bytes)
    header=struct.pack('<IHHHHHIIIHH', LFH_SIG, 20, flag, 8, time, date, crc32, comp_size, uncomp_size, name_len, 0)
    info={
        'name_bytes': name_bytes, 'flag': flag, 'crc32': crc32,
        'comp_size': comp_size, 'uncomp_size': uncomp_size,
        'mod_time': time, 'mod_date': date,
    }
    return header+name_bytes, comp_data, info


def build_cdfh(info, local_offset):
    header=struct.pack('<IHHHHHHIIIHHHHHII', CDH_SIG, 20, 20, info['flag'], 8, info['mod_time'], info['mod_date'], info['crc32'], info['comp_size'], info['uncomp_size'], len(info['name_bytes']), 0, 0, 0, 0, 0, local_offset)
    assert len(header) == 46
    return header+info['name_bytes']

def build_lfh_raw(name_bytes, crc32, comp_size, uncomp_size, mod_time, mod_date, flag=0):
    header = struct.pack('<IHHHHHIIIHH', LFH_SIG, 20, flag, 8, mod_time, mod_date,
                         crc32, comp_size, uncomp_size, len(name_bytes), 0)
    return header + name_bytes

def build_ecdfh(count, size, offset):
    return struct.pack('<IHHHHIIH', EOCD_SIG, 0, 0, count, count, size, offset, 0)

def next_r(n):
    for size in [5] + list(range(18, 52)):
        try:
            return r_token(n, size=size)
        except ValueError:
            pass
    raise RuntimeError(f'R{n} 找不到可用的大小')

def build_quine(header, footer):
    if len(header) > 32763 or len(footer) > 32763:
        raise ValueError("header or footer too big")
    l_0=l_token(0)
    l_0f=l_token(0, True)
    l_5=l_token(5)
    l_20=l_token(20)
    r_20=r_token(20, size=5)
    quine=l_token(len(header)+5)+header+l_token(len(header)+5)
    quine+=r_token(len(header)+5)
    x=r_token(len(header)+5)
    #print(len(header))
    while(len(x)!=5):
        quine+=l_token(len(x))+x
        quine+=l_5+l_token(len(x))
        quine+=l_token(len(x)+15)+x+l_5+l_token(len(x))+l_token(len(x)+15)
        x_next = next_r(len(x) + 15)
        #print(len(x_next))
        quine += x_next
        x = x_next
        #print(x)
    quine+=l_5+x
    quine+=l_5+l_5
    quine+=l_20+x+l_5+l_5+l_20
    quine+=r_20
    quine+=l_20+r_20+l_20+r_20+l_20
    quine+=r_20
    quine+=l_20+r_20+l_0+l_0
    y, r_s_y_10=find_y(len(footer))
    quine+=l_token(len(footer)+y+10)
    quine+=r_20
    quine+=l_0
    quine+=l_0
    quine+=l_token(len(footer)+y+10)+r_token(len(footer)+y+10)+l_0+l_0f+footer
    quine+=r_token(len(footer)+y+10)
    quine+=l_0
    quine+=l_0f
    return quine

def make_PS(comp_size, crc):
    q_off = len(out)                                    # quine LFH 的起點
    total = q_off + 30 + len(out_name) + comp_size + len(cdh_out) + 46 + len(out_name) + 22
    info = {'name_bytes': out_name, 'flag': 0, 'mod_time': mod_time, 'mod_date': mod_date,
            'crc32': crc, 'comp_size': comp_size, 'uncomp_size': total}
    P = out + build_lfh_raw(out_name, crc, comp_size, total, mod_time, mod_date)
    cd = cdh_out + build_cdfh(info, q_off)
    S = cd + build_ecdfh(len(infos) + 1, len(cd), len(P) + comp_size)
    return P, S

def make_zip(crc):
    P, S = make_PS(len(quine), crc)           # 用真正的大小
    return P + build_quine(P, S) + S


def dos_datetime(dt):
    t = (dt.hour << 11) | (dt.minute << 5) | (dt.second // 2)
    d = ((dt.year - 1980) << 9) | (dt.month << 5) | dt.day
    return t, d

parser = argparse.ArgumentParser(description="產生 zip quine，可一併打包指定檔案。")
parser.add_argument('-f', '--file', nargs='+', default=[], metavar='FILE',
                    help='要打包進 quine 的檔案，可一次給多個 (-f a.txt b.txt c.txt)')
parser.add_argument('-o', '--output', default='quine.zip', metavar='OUT',
                    help='輸出的 zip 檔名 (預設 quine.zip)')
args = parser.parse_args()

out=bytearray()
out_name=os.path.basename(args.output).encode('utf-8')
P=bytearray()
S=bytearray()
offsets, infos =[0], []
cdh_out=bytearray()

mod_time, mod_date = dos_datetime(datetime.datetime.now())

for path in args.file:
    if os.path.isfile(path):
        with open(path, 'rb')as f:
            data=f.read()
            lfh, comp_data, info = build_lfh(os.path.basename(path), data, mod_time, mod_date)
            infos.append(info)
            out+=lfh+comp_data
            cdh=build_cdfh(infos[-1], offsets[-1])
            offsets.append(len(out))
            cdh_out+=cdh
    else:
        print(f"警告：找不到檔案，略過：{path}", file=sys.stderr)

P, S=make_PS(0, 0)
quine=build_quine(P, S)

z0 = make_zip(0)
z1 = make_zip(0xFFFFFFFF)
positions = find_crc_positions(z0, z1)        # 比對兩版，找出 CRC 的 4 個位置
crc = solve_crc(z0, positions)                # 解出 CRC
zip_data = make_zip(crc)                      # 最終的 quine
print(len(zip_data))
zf = zipfile.ZipFile(io.BytesIO(zip_data))
print(zf.namelist())          # 應該列出所有檔案，包括 quine
print(zf.testzip())
with open(args.output, 'wb') as f:
    f.write(zip_data)
