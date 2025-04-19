import numpy as np 
from typing import reveal_type, Tuple
from numpy.typing import NDArray

# var1 = np.array([[[[1,2,3], [4,5,6]]]])
# print(var1.shape)
# var2 = np.array([[[[1,2,3], [4,5,6]]]])


# v = var1 + var1 + var1
# reveal_type(var1)
# reveal_type(v)

# x = np.ones((2,3))
# y = np.ones(2)

a = np.random.rand(3, 4)

b = np.random.randn(3, 4)

c = np.random.randint(10, 50, size=(3, 4))

d = np.array([[2, 3, 4, 5]]) 

e = np.array([[2, 2]]) 

f = np.random.randint(10, 50)
x = a + b
y = c + d
z = x + f
m = e + a
# print(np.random.uniform(5, 15, size=(3, 4)))

# print(np.random.normal(loc=10, scale=2, size=(3, 4)))

# print(np.random.binomial(n=20, p=0.4, size=(3, 4)))

# print(np.random.poisson(lam=5, size=(3, 4)))

# print(np.random.exponential(scale=3.0, size=(3, 4)))

# print(np.random.beta(a=2.0, b=5.0, size=(3, 4)))

# print(np.random.gamma(shape=2.0, scale=2.0, size=(3, 4)))

# print(np.random.chisquare(df=4, size=(3, 4)))

# print(np.random.choice([10, 20, 30, 40, 50, 60], size=(3, 4)))

# a = np.array([[1, 2, 3]])
# b = np.array([[4, 2]]) 
# c = a + b
# print(a.shape)
# print(b.shape)

# print(a+b)


# print(result.shape)
