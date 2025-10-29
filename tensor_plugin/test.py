import numpy as np
from typing_extensions import reveal_type

x = np.array([1, 2, 3, 4, 5, 6])
print(x[..., :])
