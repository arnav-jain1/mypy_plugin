import numpy as np 
from typing import reveal_type

# var1 = np.array([[[[1,2,3], [4,5,6]]]])
# print(var1.shape)
# var2 = np.array([[[[1,2,3], [4,5,6]]]])


# v = var1 + var1 + var1
# reveal_type(var1)
# reveal_type(v)

a = np.array([1, 2, 3])
b = np.array([4, 6]) 
result = a + b

print(a.shape)
print(b.shape)
print(result.shape)