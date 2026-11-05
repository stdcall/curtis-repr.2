"""Two exact counterexamples in Section 38D.

rem:maximal-order-k0-whitehead: the abelianization of GL(2,F_2) has order2.
eq:lattice-relative-class-additivity: the printed quotient sequence fails
for two standard split integer-lattice rows and a rational shear.
These finite computations do not prove the general localization theorem,
the global norm results, or Morita invariance of K_1.
"""
from sage.all import GF, GL, QQ, ZZ, identity_matrix, matrix, vector


group = GL(2, GF(2))
derived = group.subgroup([a * b * a.inverse() * b.inverse()
                         for a in group for b in group])
assert group.order() == 6
assert derived.order() == 3
assert group.order() // derived.order() == 2
assert group.order() // derived.order() != 3  # Printed quotient order.

# The rows are 0 -> Z -> Z^2 -> Z -> 0, with inclusion into the first
# coordinate and projection onto the second. The outer vertical maps are1.
shear = matrix(QQ, [[1, QQ(1) / 2], [0, 1]])
inclusion = vector(QQ, [1, 0])
projection = vector(QQ, [0, 1])
assert shear.is_invertible()
assert shear * inclusion == inclusion
assert projection * shear == projection

# Compute Z^2 intersect shear(Z^2) from the saturated integer kernel of
# 2x = (2 shear)y. Its x-coordinates give a basis of the intersection.
relations = (2 * identity_matrix(ZZ, 2)).augment(-(2 * shear).change_ring(ZZ))
kernel = relations.right_kernel_matrix()
assert relations * kernel.transpose() == 0
intersection = kernel.matrix_from_columns([0, 1]).hermite_form()
assert intersection == matrix(ZZ, [[1, 0], [0, 2]])
assert abs(intersection.det()) == 2
# The end quotients are both zero, while the middle quotient has order2.
assert abs(intersection.det()) > 1

print('ok localization: 2 exact cases (GL2 abelianization; lattice defect)')
