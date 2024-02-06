# ECIP

Implementation of [Liam Eagen](https://eprint.iacr.org/2022/596)'s elliptic curve inner product argument.

# Description

* function_field.rs

    For given $N$ elliptic curve points whose sum is zero, we can find a function field element that interpolates the points. The function field element can be represented by $f(x, y) = a(x) - y b(x)$ for $\deg a, \deg b \leq N/2$. We used two different methods described [here](https://ssjeon.blogspot.com/2023/12/finding-function-field-interpolation.html).

* weil_reciprocity.rs

    Using the Weil reciprocity, we can prove two different type of elliptic curve addition, $\sum_{i=0}^{N-1} P_i = O$ and $\sum_{i=0}^{N-1} e_i P_i = Q$. The challenge from the verifier is a line in projective space. The line can intersects with the elliptic curve with three distinct points(simple challenge) or two points(higher challenge). The details are described [here](https://ssjeon.blogspot.com/2023/12/liam-eagens-elliptic-curve-inner.html). This module contains such four possible tests.

* circuit.rs

    This is a circuit proves $\sum_{i=0}^{N-1} P_i = O$ with higher challenge. Four columns and $2 N$ rows are needed.

* circuit_ecip.rs

    This is a circuit proves $\sum_{i=0}^{N-1} e_i P_i = Q$ with higher challenge. Four columns and $2N + Nl$ rows are needed. Here the scalars $e_i$ are represented by signed integers with size less than $3^l$. If $\mathbb{F}_q \cong E(\mathbb{F}_p)$, then we may choose $l$ such that $q < 3^l$.