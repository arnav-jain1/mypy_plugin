import numpy as np
from typing_extensions import reveal_type
import typing

x = np.array([1, 2, 3, 4, 5, 6])

y = x.reshape((2,3))
z = x.reshape((3,2))

a = y * z
reveal_type(a)
print(a)
reveal_type(y)