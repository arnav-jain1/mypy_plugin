import numpy as np
from typing_extensions import reveal_type
from typing import *


def func(x: np.ndarray):
    a = np.zeros((2,3))
    b = np.zeros((4,4))
    c = x @ b
    # reveal_type(x)
    reveal_type(b)
    reveal_type(c)
    return c

t = np.zeros((5,4))
t2 = func(t)
print(t2.shape)
reveal_type(t2)
t3 = np.zeros((4,3))
t4 = t2 @ t3
reveal_type(t4)

# a = func(x)
# z = x @ y
