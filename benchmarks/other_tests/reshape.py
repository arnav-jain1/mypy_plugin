import numpy as np

a = np.ones((8, 8))

b = a.reshape(-1)

c = a.reshape(64)

d = a.reshape(2, 32)

e = a.reshape(-1, 32)
f = a.reshape((2, 32))
g = a.reshape((-1, 32))
h = a.reshape(2, 32, order='C', copy=None)
i = a.reshape((2, 32), order='C', copy=None)

bad1 = a.reshape(1) # Error
bad2 = a.reshape(10, 2) # Error