
import numpy as np
from typing_extensions import reveal_type
from typing import *




def func2(x: np.ndarray[Tuple[int, Literal[4]]], a : int):
    y = x[0:a, :]
    reveal_type(y)
    z = x[0:4, 1:3]
    reveal_type(z)
    integer = x[0, 0]
    reveal_type(integer)
    return

# ---------------------------------------------------------
# Test Suite 1: 1D Arrays & Basic Stepping
# ---------------------------------------------------------
def test_1d_static(x: np.ndarray[Tuple[Literal[10]], Any]):
    # Basic slice
    a = x[2:7]
    reveal_type(a)  # Expected: ndarray[Tuple[Literal[5]]]
    
    # Slice with omitted boundaries
    b = x[:4]
    reveal_type(b)  # Expected: ndarray[Tuple[Literal[4]]]
    
    # Stepping
    c = x[2:7:2]
    reveal_type(c)  # Expected: ndarray[Tuple[Literal[3]]]
    
    # Integer indexing (Dimension reduction)
    d = x[5]
    reveal_type(d)  # Expected: builtins.int (or scalar type)

# ---------------------------------------------------------
# Test Suite 2: 2D Arrays & Dimension Reduction
# ---------------------------------------------------------
def test_2d_mixed(x: np.ndarray[Tuple[int, Literal[6]]], dyn_idx: int):
    # Slice both dimensions with literals
    a = x[0:2, 1:4]
    reveal_type(a)  # Expected: ndarray[Tuple[Literal[2], Literal[3]]]
    
    # Slice one with literal, one with dynamic variable
    b = x[0:dyn_idx, :]
    reveal_type(b)  # Expected: ndarray[Tuple[int, Literal[6]]]
    
    # Integer index on axis 0, slice on axis 1 (Reduces to 1D)
    c = x[2, 1:4]
    reveal_type(c)  # Expected: ndarray[Tuple[Literal[3]]]
    
    # Slice on axis 0, integer index on axis 1 (Reduces to 1D)
    d = x[1:4, 3]
    reveal_type(d)  # Expected: ndarray[Tuple[Literal[3]]]

    # Double integer indexing (Reduces to 0D / scalar)
    e = x[1, 1]
    reveal_type(e)  # Expected: builtins.int

# ---------------------------------------------------------
# Test Suite 3: 3D Arrays & Ellipsis (...)
# ---------------------------------------------------------
def test_3d_ellipsis(x: np.ndarray[Tuple[Literal[4], Literal[5], Literal[6]]]):
    # Ellipsis at the end
    a = x[1:3, ...]
    reveal_type(a)  # Expected: ndarray[Tuple[Literal[2], Literal[5], Literal[6]]]
    
    # Ellipsis at the beginning
    b = x[..., 2:4]
    reveal_type(b)  # Expected: ndarray[Tuple[Literal[4], Literal[5], Literal[2]]]
    
    # Ellipsis in the middle
    c = x[1, ..., 3]
    reveal_type(c)  # Expected: ndarray[Tuple[Literal[5]]]
    
    # Ellipsis with steps
    d = x[::2, ..., ::3]
    reveal_type(d)  # Expected: ndarray[Tuple[Literal[2], Literal[5], Literal[2]]]

# ---------------------------------------------------------
# Test Suite 4: Negative Indices and Steps
# ---------------------------------------------------------
def test_negatives(x: np.ndarray[Tuple[Literal[10]], Any]):
    # Negative indexing
    a = x[-1]
    reveal_type(a)  # Expected: builtins.int
    
    # Negative slicing boundaries
    b = x[-4:-1]
    reveal_type(b)  # Expected: ndarray[Tuple[Literal[3]]]
    
    # Negative stepping (reversing)
    c = x[::-1]
    reveal_type(c)  # Expected: ndarray[Tuple[Literal[10]]]

    # Negative stepping with boundaries
    d = x[8:2:-2]
    reveal_type(d)  # Expected: ndarray[Tuple[Literal[3]]]

# ---------------------------------------------------------
# Test Suite 5: Expected Z3 Solver Failures (Out of Bounds)
# ---------------------------------------------------------
def test_out_of_bounds_and_errors(x: np.ndarray[Tuple[Literal[3], Literal[3]]]):
    # These should theoretically trigger your `ctx.api.fail("Slicing Error...", ...)`
    
    # Index out of bounds
    error1 = x[5, 0]
    reveal_type(error1) # Expected: Any (or whatever default_return_type falls back to)
    
    # Slice completely out of bounds
    error2 = x[10:15, :]
    reveal_type(error2) # Expected: ndarray[Tuple[Literal[0], Literal[3]]] OR an error if your solver rejects 0-size arrays

    # Too many indices
    error3 = x[0, 0, 0]
    reveal_type(error3) # Expected: Mypy failure or Z3 index error

