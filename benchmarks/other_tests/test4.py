import numpy as np
from typing_extensions import reveal_type



x = np.array([[1,2,3], [4,5,6]])
y = np.zeros((3,4))
reveal_type(x)
reveal_type(y)
z = x @ y
reveal_type(z)
err = y @ x
reveal_type(err)


