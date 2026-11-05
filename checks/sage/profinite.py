"""Finite residue-group checks for Section 45.

The determinant kernel in GL_2(F_2) is larger than its commutator
subgroup. Elementary generators still give the whole determinant kernel.
These finite cases do not establish continuity of K_1 over complete rings.
"""
from sage.all import GF, GL, SL, MatrixGroup, matrix


for size in (2, 3, 4):
    field = GF(size, 'a')
    general = GL(2, field)
    generators = []
    for value in field:
        if value:
            generators.extend((matrix(field, [[1, value], [0, 1]]),
                               matrix(field, [[1, 0], [value, 1]])))
    elementary = MatrixGroup(generators)
    determinant_kernel_order = general.order() // (size - 1)
    assert all(generator.det() == 1 for generator in generators)
    assert elementary.order() == SL(2, field).order()
    assert elementary.order() == determinant_kernel_order
    if size == 2:
        assert general.order() == 6
        assert general.gap().DerivedSubgroup().Size() == 3
        assert elementary.order() == general.order()

# Enlarging the matrix size also removes this particular residue exception.
general = GL(3, GF(2))
assert general.order() == 168
assert general.gap().DerivedSubgroup().Size() == general.order()

print('ok profinite: 4 finite residue cases '
      '(elementary determinant kernels; GL_2(F_2) commutator exception; '
      'GL_3(F_2) perfectness)')
