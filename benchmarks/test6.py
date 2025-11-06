
import numpy as np
from typing_extensions import reveal_type
from typing import *




def func2(x: np.ndarray[Tuple[int, Literal[4]]], a : int):
    y = x[0:a, :]
    reveal_type(y)
    z = x[0:4, 1:3]
    reveal_type(z)
    integer = x[0, 0]
    reveal_type(integer)
    return

