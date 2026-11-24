import zlib, struct

def find_crc_positions(zip0, zip1):
    """比對 CRC=0 和 CRC=0xFFFFFFFF 兩個版本，找出 CRC 出現的所有位置（每處 4 bytes）"""
    diff = [i for i, (a, b) in enumerate(zip(zip0, zip1)) if a != b]
    assert len(diff) % 4 == 0, diff
    starts = diff[::4]
    for s in starts:
        assert diff.count(s) and all(s + k in diff for k in range(4))
    return starts

def solve_crc(zip0, positions):
    """找 c，使得把 c 填進所有位置後，整個檔案的 CRC-32 剛好等於 c"""
    def f(c):
        data = bytearray(zip0)
        for p in positions:
            data[p:p+4] = struct.pack('<I', c)
        return zlib.crc32(data) & 0xFFFFFFFF
    f0 = f(0)
    cols = [f(1 << i) ^ f0 for i in range(32)]        # CRC 對 c 是仿射的：f(c) = f0 ⊕ Σ c_i·cols[i]
    # 要解 f(c) = c  →  Σ c_i·(cols[i] ⊕ e_i) = f0，GF(2) 上的 32×32 方程組
    rows = []                                          # 每列：(係數 bitmask, 右邊)
    for bit in range(32):
        mask = 0
        for i in range(32):
            if ((cols[i] >> bit) & 1) ^ (1 if i == bit else 0):
                mask |= 1 << i
        rows.append([mask, (f0 >> bit) & 1])
    # 高斯消去
    pivots = []
    r = 0
    for col in range(32):
        piv = next((k for k in range(r, 32) if (rows[k][0] >> col) & 1), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for k in range(32):
            if k != r and (rows[k][0] >> col) & 1:
                rows[k][0] ^= rows[r][0]; rows[k][1] ^= rows[r][1]
        pivots.append(col); r += 1
    if any(m == 0 and v for m, v in rows[r:]):
        return None                                    # 無解，換個修改時間等再試
    c = 0
    for k, col in enumerate(pivots):
        if rows[k][1]:
            c |= 1 << col
    assert f(c) == c
    return c
