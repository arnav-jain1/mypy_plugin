import numpy as np
from typing_extensions import reveal_type
import typing

x = np.array([1, 2, 3, 4, 5, 6])

c = 2
y = x.reshape((3,-1))
reveal_type(y)
print(y.shape)
reveal_type(y)