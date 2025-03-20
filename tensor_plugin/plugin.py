from typing import Callable, Dict, List, Optional, Tuple, Union, cast
from mypy.plugin import Plugin, FunctionContext, MethodContext, MethodSigContext, AttributeContext, ClassDefContext
from mypy.types import Type, Instance, AnyType, TypeOfAny, CallableType
from mypy.nodes import Expression, ListExpr, TupleExpr, IntExpr, CallExpr, NameExpr, MemberExpr, RefExpr, AssignmentStmt
from mypy.checker import TypeChecker

class NumPyArrayPlugin(Plugin):
    def __init__(self, options) -> None:
        super().__init__(options)
        self.vars = dict()
    
    
    def infer_shape(self, node: ListExpr) -> Tuple[List[int], int]:
        print(node)
        """Infer the shape of a nested list expression."""
        current_nodes = [node]
        shape = []
        rank = 0

        while current_nodes:
            # Check if all nodes at current level are ListExpr
            if not all(isinstance(n, ListExpr) for n in current_nodes):
                break

            rank += 1
            first_node = current_nodes[0]
            current_length = len(first_node.items)
            shape.append(current_length)

            # Flatten to next level of nodes
            current_nodes = [child for n in current_nodes for child in n.items]

        return shape, rank
    
    def get_dynamic_class_hook(self, fullname):
        if fullname.strip() == "numpy._core.multiarray.array":
            return self.reg_var
        return None
    
    def reg_var(self, ctx):
        shape, rank = self.infer_shape(ctx.call.args[0])
        self.vars[ctx.name] = shape
        self.print_vars()
        return None
    
    def print_vars(self):
        print("Current vars: ")
        for key, val in self.vars.items():
            print(f"\tVariable name: {key} Shape: {val}")

def plugin(version):
    return NumPyArrayPlugin