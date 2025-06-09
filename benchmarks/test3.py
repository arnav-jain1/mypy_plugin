import numpy as np
from typing_extensions import reveal_type
from typing import Any


def func(x: np.ndarray):
    a = np.zeros((2,3))
    b = np.zeros((4,4))
    c = x @ b
    # reveal_type(x)
    reveal_type(b)
    reveal_type(c)
    return c

x = np.zeros((3,2))
y = np.zeros((4,4))
# a = func(x)
# z = x @ y
