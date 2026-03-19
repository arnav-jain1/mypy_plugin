import numpy as np
from typing_extensions import reveal_type
from typing import *

def func(x: np.ndarray[Tuple[int, int]]):
    y = np.zeros((3,4))
    z = x * y
    
    # ERROR: Reshape not possible​
    a = x.reshape((10))
    # ERROR: Slice not possible​
    b = x[5, :]
    return z



x = np.array([[1,2,3], [4,5,6]])