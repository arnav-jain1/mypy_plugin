import numpy as np 
from typing import reveal_type

# ========== FAIL CASES ==========

# Final 2 elems mismatch
x1 = np.ones((5, 3))
y1 = np.ones((2, 3, 5, 4))
try:
    z1 = x1 @ y1
except ValueError as e:
    print("FAIL x1 @ y1:", e)

# Broadcasting error
x2 = np.ones((4, 3, 2))
y2 = np.ones((5, 2, 6))
try:
    z2 = x2 @ y2
except ValueError as e:
    print("FAIL x2 @ y2:", e)

# Broadcasting error
x3 = np.ones((2, 3, 4, 5))
y3 = np.ones((4, 1, 5, 6))
try:
    z3 = x3 @ y3
except ValueError as e:
    print("FAIL x3 @ y3:", e)

# Final 2 elems mismatch
x4 = np.ones((2, 2, 2, 3, 4))
y4 = np.ones((2, 3, 5))
try:
    z4 = x4 @ y4
except ValueError as e:
    print("FAIL x4 @ y4:", e)


# Broadcasting error
x5 = np.ones((4, 6, 3))
y5 = np.ones((2, 5))
try:
    z5 = x5 @ y5
except ValueError as e:
    print("FAIL x5 @ y5:", e)

# Broadcasting error
x6 = np.ones((2, 1, 4, 2, 3))
y6 = np.ones((3, 2, 1, 3, 6))
try:
    z6 = x6 @ y6
except ValueError as e:
    print("FAIL x6 @ y6:", e)

# Final 2 elems mismatch
x7 = np.ones((3, 4))
y7 = np.ones((4, 3, 2))
try:
    z7 = x7 @ y7
except ValueError as e:
    print("FAIL x7 @ y7:", e)

x8 = np.ones((3, 4))
y8 = np.ones((3, 3))
try:
    z8 = x8 @ y8
except ValueError as e:
    print("FAIL x8 @ y8:", e)

# ========== PASS CASES ==========

x11 = np.ones((3, 4))
y11 = np.ones((4, 2))
z11 = x11 @ y11
print("PASS x11 @ y11:", z11.shape)

x12 = np.ones((5, 3, 4))
y12 = np.ones((5, 4, 2))
z12 = x12 @ y12
print("PASS x12 @ y12:", z12.shape)

x13 = np.ones((1, 2, 3, 6))
y13 = np.ones((5, 2, 6, 4))
z13 = x13 @ y13
print("PASS x13 @ y13:", z13.shape)

x14 = np.ones((4, 6))
y14 = np.ones((1, 6, 5))
z14 = x14 @ y14
print("PASS x14 @ y14:", z14.shape)

x15 = np.ones((3, 6, 7))
y15 = np.ones((7, 2))
z15 = x15 @ y15
print("PASS x15 @ y15:", z15.shape)

x16 = np.ones((2, 1, 4, 2, 3))
y16 = np.ones((2, 3, 1, 3, 6))
z16 = x16 @ y16
print("PASS x16 @ y16:", z16.shape)

x17 = np.ones((3, 1, 2, 8))
y17 = np.ones((1, 8, 4))
z17 = x17 @ y17
print("PASS x17 @ y17:", z17.shape)

x18 = np.ones((2, 5, 3))
y18 = np.ones((1, 2, 3, 6))
z18 = x18 @ y18
print("PASS x18 @ y18:", z18.shape)

x19 = np.ones((1, 1, 3, 4, 7))
y19 = np.ones((7, 5))
z19 = x19 @ y19
print("PASS x19 @ y19:", z19.shape)

x20 = np.ones((1, 9, 6))
y20 = np.ones((2, 3, 1, 6, 10))
z20 = x20 @ y20
print("PASS x20 @ y20:", z20.shape)

# EDGE CASES

# vec by vec is just an int
a = np.ones(5)
b = np.ones(1)
c = a @ b
reveal_type(c)
print("PASS a @ b:", c)



# # vec times tensor: Vec gets changed to (1, vec) and the 1 gets removed after calc
# # So essentially the vec has to match with -2 and the -2 elem gets dropped
# a1 = np.ones((5))
# b1 = np.ones((3, 2, 5,1))
# c1 = a1 @ b1
# reveal_type(c1)
# print("PASS a1 @ b1: ", c1.shape)


# a2 = np.ones((4))
# b2 = np.ones((3, 2, 5,1))
# try: 
#     c2 = a2 @ b2
# except ValueError as e:
#     print("FAIL a2 @ b2: ", e)



# tensor times vec: Vec gets changed to (vec, 1) and the 1 gets removed after calc
# So essentially the vec has to match with -1 and the result size is just remove the last elem of lhs