"""Four exact algebra checks for Section 40.

The Laurent identity checks the four factors in (40.25). The remaining
examples check the pair swap, the significance of matrix coefficient order
over a noncommutative ring, and Exercise 40.4 on radical reduction.
Finite examples do not establish the general K-theoretic statements.
"""
from sage.all import (GF, QQ, ZZ, LaurentPolynomialRing, PolynomialRing,
                      block_matrix, diagonal_matrix, identity_matrix, matrix)


ring = LaurentPolynomialRing(ZZ, 'u')
u = ring.gen()


def upper(value):
    return matrix(ring, [[1, value], [0, 1]])


def lower(value):
    return matrix(ring, [[1, 0], [value, 1]])


expected = diagonal_matrix(ring, [u, u**(-1)])
assert upper(u**(-1)) * lower(1) * upper(u**(-1) - 1) * lower(-u) != expected
assert upper(u - 1) * lower(1) * upper(u**(-1) - 1) * lower(-u) == expected

first = diagonal_matrix(QQ, [2, 1, 1, 1])
second = diagonal_matrix(QQ, [1, 1, 2, 1])
diagonal = diagonal_matrix(QQ, [QQ(1) / 2, 1, 2, 1])
swap = matrix(QQ, [[0, 0, 1, 0], [0, 1, 0, 0],
                   [1, 0, 0, 0], [0, 0, 0, 1]])
assert second * diagonal != diagonal * first
assert second * swap == swap * first
assert swap * swap == identity_matrix(QQ, 4)

# Entries here are themselves 2-by-2 matrices. Transposing only the
# block indices need not preserve invertibility over this coefficient ring.
e11 = matrix(QQ, [[1, 0], [0, 0]])
e12 = matrix(QQ, [[0, 1], [0, 0]])
e21 = matrix(QQ, [[0, 0], [1, 0]])
e22 = matrix(QQ, [[0, 0], [0, 1]])
original = block_matrix([[e11, e21], [e12, e22]])
block_transpose = block_matrix([[e11, e12], [e21, e22]])
assert original * original == identity_matrix(QQ, 4)
assert block_transpose.rank() == 1

polynomials = PolynomialRing(GF(2), 'x')
x = polynomials.gen()
dual_numbers = polynomials.quotient(x**2, 'eps')
assert sum(1 for a in dual_numbers if a.is_unit()) == 2
assert sum(1 for a in GF(2) if a.is_unit()) == 1

print('ok whitehead: 4 exact cases (block identity; pair swap; '
      'noncommutative coefficients; radical reduction)')
