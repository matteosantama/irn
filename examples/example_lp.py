"""LP example: min -x1 - 2 x2 subject to x1 + x2 <= 1, x2 <= 0.7, x >= 0.

Known optimum: x = (0.3, 0.7), obj = -1.7.
Dual: y_1 = 1 (the x1+x2<=1 constraint is active),
      y_2 = 1 (the x2<=0.7 constraint is active),
      y_3 = 0 (x1 >= 0 inactive),
      y_4 = 0 (x2 >= 0 inactive).
"""

import numpy as np

from irn import solve


def main() -> None:
    P = np.zeros((2, 2))
    c = np.array([-1.0, -2.0])

    # A x <= b form, with x >= 0 expressed as -x <= 0
    A = np.array(
        [
            [1.0, 1.0],   # x_1 + x_2 <= 1
            [0.0, 1.0],   # x_2 <= 0.7
            [-1.0, 0.0],  # -x_1 <= 0  i.e. x_1 >= 0
            [0.0, -1.0],  # -x_2 <= 0  i.e. x_2 >= 0
        ]
    )
    b = np.array([1.0, 0.7, 0.0, 0.0])

    result = solve(P, A, b, c, verbose=True)

    print()
    print(f"status     : {result.status}")
    print(f"iterations : {result.iterations}")
    print(f"x          : {result.x}")
    print(f"y          : {result.y}")
    print(f"s          : {result.s}")
    print(f"objective  : {result.objective:.6f}")
    print(f"final mu   : {result.mu:.2e}")
    print(f"residual   : {result.residual:.2e}")
    print()
    print("expected   : x ~ (0.3, 0.7), y ~ (1, 1, 0, 0), obj ~ -1.7")

    # Lightweight assertions
    np.testing.assert_allclose(result.x, [0.3, 0.7], atol=1e-4)
    np.testing.assert_allclose(result.objective, -1.7, atol=1e-4)
    assert result.status == "optimal", result.status
    print("\nOK")


if __name__ == "__main__":
    main()
