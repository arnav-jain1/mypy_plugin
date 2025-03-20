from mypy.plugin import Plugin, FunctionContext, MethodContext
from mypy.types import Instance, Type , TupleType, TypeVarType, AnyType, TypeOfAny, get_proper_type, LiteralType
from mypy.nodes import TypeInfo, ARG_POS, Var, SYMBOL_FUNCBASE_TYPES, SymbolTableNode, IntExpr, ListExpr
from mypy.plugins.common import add_method_to_class
from mypy import nodes
from typing import Tuple, List



array_types = ["numpy.random.mtrand.randint", "numpy._core.multiarray.array"]
class CustomPlugin(Plugin):
    def get_function_hook(self, fullname: str):
        # print(f"debug fullname {fullname}")
        if fullname == "numpy._core.multiarray.array":
            return self.transform_array
        return None

    def transform_array(self, ctx: FunctionContext) -> Type:
        print(f"DEBUG: transform_ndarray called: {ctx}")
        
        input_type = ctx.api.named_type("numpy.ndarray")

        if ctx.args and ctx.args[0] and ctx.args[0][0]:
            
            shape, ranks = self.infer_shape(ctx.args[0][0])

            print(f"DEBUG: Inferred shape: {shape} with rank {ranks}")
            literal_dims = [LiteralType(dim, ctx.api.named_generic_type("builtins.int", [])) for dim in shape]

            shape_tuple = TupleType(literal_dims, fallback=ctx.api.named_generic_type("builtins.tuple", []))
            # print(literal_dims)
            # print(shape_tuple)

            final_type = ctx.api.named_generic_type("numpy.ndarray", [shape_tuple])
            print(f"Type: {ndarray_type}")
            # print(final_type.args[0])

            return final_type
        else:
            print("DEBUG: WEIRD ERROR HAPPENED")   
            print(ctx.args)
            print(ctx.args[0])
            print(ctx.args[0][0])
            return ctx.default_return_type

    def infer_shape(self, node):
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
def plugin(version):
    return CustomPlugin