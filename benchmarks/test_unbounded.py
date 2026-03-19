import numpy as np
from typing import *
from typing_extensions import reveal_type

def test2(x: np.ndarray[Tuple[int]]):
    reveal_type(x)
    
    return x

def test3(x: np.ndarray[Tuple[Any, int]]):
    reveal_type(x)

    y = np.transpose(x)
    reveal_type(y)
    
    return x

def test(x: np.ndarray):
    reveal_type(x)
    
    return x

def func(x: np.ndarray[Tuple[Any, int]]):
    b = np.zeros((4,4))
    c = x @ b
    reveal_type(c)
    return c