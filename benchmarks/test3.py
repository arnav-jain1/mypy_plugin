import numpy as np
from typing_extensions import reveal_type
from typing import *


def func(x: np.ndarray):
    b = np.zeros((4,4))
    c = x @ b
    reveal_type(c)
    return c

valid_arg = np.zeros((3,4))
invalid_arg = np.zeros((3,9))

valid = func(valid_arg)
invalid = func(invalid_arg)

new_valid = np.zeros((4,3))
new_invalid = np.zeros((10,3))

reveal_type(valid)
x = valid @ new_valid
reveal_type(x)

reveal_type(valid)
y = valid @ new_invalid
reveal_type(y)


# a = func(x)
# z = x @ y
