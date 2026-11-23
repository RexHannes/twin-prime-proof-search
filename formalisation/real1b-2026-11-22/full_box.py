"""Gold 4.65 (B4) and (B7). Exact, outward-rounded integer cubature."""
from itertools import combinations, product
from math import prod

MESH = 800
SCALE = 10**20
EPS_DEN = 10**9


def admissible(cell):
    i, j, k, l = cell
    s = sum(cell)
    return (i + 1 <= 19 and all(v + 1 <= 19 or v >= 21 for v in cell)
            and l + 1 + s <= 96 and s + 21 <= 96 and 100 <= 49 + s
            and 51 <= i + k + l and k + l + 2 <= 49)


def face(in_mesh_units, shift):
    # Compare s/800 to 1/2 + shift*epsilon and 1/2 - epsilon.
    offset = (in_mesh_units - MESH // 2) * EPS_DEN
    return int(offset >= MESH * shift) + int(offset > -MESH)


def enclosure():
    lower = upper = boxes = cells = 0
    for cell in filter(admissible, combinations(range(3, 49), 4)):
        boxes += 1
        bands = [range(8 * i, 8 * (i + 1)) for i in cell]
        shift3, shift4 = [2 if i >= 21 else 1 for i in cell[2:]]
        for lo in product(*bands):
            a, b, c, d = lo
            fifth = MESH - sum(lo)
            # All upper faces stay below the smallest possible fifth coordinate.
            if d + 1 > fifth - 4:
                raise ValueError("Product-density monotonicity fails on this cell")
            s3, s4 = a + b + d, a + b + c
            hlo = 2 + face(s3, shift3) + face(s4, shift4)
            hhi = 2 + face(s3 + 3, shift3) + face(s4 + 3, shift4)
            den_lo = prod(lo) * fifth
            den_hi = (a+1) * (b+1) * (c+1) * (d+1) * (fifth-4)
            lower += hlo * MESH * SCALE // den_hi
            upper += (hhi * MESH * SCALE + den_lo - 1) // den_lo
            cells += 1
    return boxes, cells, lower, upper


if __name__ == "__main__":
    result = enclosure()
    expected = (1566, 6414336, 26697968067675082204, 28449989344325252602)
    if result != expected:
        raise ValueError(f"Gold 4.65 enclosure mismatch: {result}")
    print(f"{result[0]} boxes, {result[1]} cells, J in [{result[2]}, {result[3]}] / {SCALE}")
