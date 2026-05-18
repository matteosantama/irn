"""QP example: project (1, 2) onto {x >= 0, x_1 + x_2 <= 1}.

   min  1/2 ||x - (1, 2)||^2
   s.t. x_1 + x_2 <= 1, x_1 >= 0, x_2 >= 0.

Expanding the objective gives
   min  1/2 x^T x + (-1, -2) x + const,
i.e. P = I, c = (-1, -2).

Known optimum: x = (0, 1), obj + const = 1.
"""

import numpy as np

from irn import solve


def main() -> None:
    P = np.eye(2)
    c = np.array([-1.0, -2.0])
    A = np.array(
        [
            [1.0, 1.0],   # x_1 + x_2 <= 1
            [-1.0, 0.0],  # x_1 >= 0
            [0.0, -1.0],  # x_2 >= 0
        ]
    )
    b = np.array([1.0, 0.0, 0.0])

    result = solve(P, A, b, c, verbose=True)

    # The reported objective excludes the constant 1/2*(1^2 + 2^2) = 2.5.
    full_obj = result.objective + 2.5

    print()
    print(f"status     : {result.status}")
    print(f"iterations : {result.iterations}")
    print(f"x          : {result.x}")
    print(f"y          : {result.y}")
    print(f"s          : {result.s}")
    print(f"objective  : {full_obj:.6f}  (full)")
    print(f"final mu   : {result.mu:.2e}")
    print(f"residual   : {result.residual:.2e}")
    print()
    print("expected   : x ~ (0, 1), obj ~ 1.0")

    np.testing.assert_allclose(result.x, [0.0, 1.0], atol=1e-4)
    np.testing.assert_allclose(full_obj, 1.0, atol=1e-4)
    assert result.status == "optimal", result.status
    print("\nOK")


if __name__ == "__main__":
    main()
