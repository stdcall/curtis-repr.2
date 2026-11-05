"""Exact Bernoulli data and the finite prime count accompanying (50.53).

The prime range is the first 550 primes, from 2 through 3989. For this
count only, 2 is included among the regular primes. An odd prime p is
counted as irregular exactly when it divides a numerator of B_(2i),
1 <= i <= (p - 3)/2. This verifies the finite numerical claim; it does
not establish the class-number criterion or a general K-theory theorem.
"""
from sage.all import QQ, bernoulli, pari


primes = list(map(int, pari.primes(550)))
assert primes[0] == 2 and primes[-1] == 3989
top = (primes[-1] - 3) // 2
pari.bernfrac(2 * top)
numerators = [0] + [
    int(pari.bernfrac(2 * i).numerator()) for i in range(1, top + 1)
]
flint_numerators = [0] + [
    int(bernoulli(2 * i, algorithm='flint').numerator())
    for i in range(1, top + 1)
]
assert numerators == flint_numerators

expected = [QQ(1) / 6, -QQ(1) / 30, QQ(1) / 42,
            -QQ(1) / 30, QQ(5) / 66, -QQ(691) / 2730]
assert [QQ(pari.bernfrac(2 * i)) for i in range(1, 7)] == expected
pairs = {
    p: [2 * i for i in range(1, (p - 3) // 2 + 1)
        if numerators[i] % p == 0]
    for p in primes if p != 2
}
irregular = [p for p in pairs if pairs[p]]
assert irregular[:3] == [37, 59, 67]
assert len(irregular) == 218
assert len(primes) - len(irregular) == 332
assert pairs[37] == [32]

print('ok bernoulli: exact PARI/FLINT agreement through B3986; '
      '218 irregular and 332 regular among primes 2 through 3989')
