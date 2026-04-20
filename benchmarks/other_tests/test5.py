
import numpy as np
from typing_extensions import reveal_type
from typing import *



def func(x: np.ndarray[Tuple[int, int]]):
    y = np.zeros((3,4))
    reveal_type(x)
    reveal_type(y)
    z = x * y
    reveal_type(z)
    err = z @ x
    return z

def func2(x: np.ndarray[Tuple[int, Literal[4]]]):
    return


valid_arg = np.zeros((3,4))
invalid_arg = np.zeros((3,9))

a = func2(valid_arg)
b = func2(invalid_arg)

