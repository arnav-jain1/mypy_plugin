import numpy as np
from typing import *
from typing_extensions import reveal_type

def func(x: np.ndarray[Tuple[int, int]], 
         y: np.ndarray[Tuple[int, int]]):
    err = x @ y
    return err

x = np.zeros((10,4))
y = np.zeros((5,8))

func(x, y)


def act(self, obs: np.ndarray[Tuple[int]]):
    E, P = self.env_info, self.parameters
    W : np.ndarray[Tuple[int, int]] = P["W"]
    b : np.ndarray[Tuple[int]] = P["b"]

    s = self._obs2num[obs]
    s = np.array([s]) if E["obs_dim"] == 1 else s

    s_transpose = np.transpose(s)
    temp = s_transpose @ W
    Z = temp + b # Type: np.ndarray[Tuple[int]]

    # Type: np.ndarray[Tuple[Literal[1]]]
    temp = np.max(Z, axis=-1, keepdims=True)
    Z_temp = Z-temp
    
    e_Z : np.ndarray[Tuple[int]] = np.exp(Z_temp)
    e_Z_temp = np.sum(e_Z, axis=-1, keepdims=True)
    
    action_probs = e_Z / e_Z_temp

    # Type: int (Scalar)
    a = np.random.multinomial(1, action_probs).argmax()     

    return self._num2action[a]

