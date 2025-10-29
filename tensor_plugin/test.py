import numpy as np
from typing_extensions import reveal_type
import typing

x = np.array([1, 2, 3, 4, 5, 6])
c = 1
d = 3
y = x[..., c:d]
reveal_type(y)
