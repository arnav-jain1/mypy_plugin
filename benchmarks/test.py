import numpy as np 
import pytest
from typing import reveal_type

# b = np.random.randint(10, size=(3, 4))
a = np.array([[1,2,3], [4,5,6]])
b = np.array([[1,2,3]])
reveal_type(a)
reveal_type(b)
print(b.shape)

c = a * b
print(c)
