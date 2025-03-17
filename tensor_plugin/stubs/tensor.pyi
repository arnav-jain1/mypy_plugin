# tensor.pyi
from typing import Any, Tuple, TypeVar, Generic

S = TypeVar("S", bound=Tuple[int, ...])  # Shape as a tuple of ints

class Tensor(Generic[S]):
    def __init__(self, data: Any) -> None: 
        self._data = data
    
    @property
    def shape(self) -> S: 
        pass
