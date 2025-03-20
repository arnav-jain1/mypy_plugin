from mypy.plugin import Plugin, FunctionContext, MethodContext, CheckerPluginInterface
from mypy.types import Instance, Type , TupleType, TypeVarType, AnyType, TypeOfAny, get_proper_type, LiteralType
from mypy.nodes import TypeInfo, ARG_POS, Var, SYMBOL_FUNCBASE_TYPES, SymbolTableNode, IntExpr, ListExpr
from mypy.plugins.common import add_method_to_class
from mypy import nodes
from typing import Tuple, List, Literal



array_types = ["numpy.random.mtrand.randint", "numpy._core.multiarray.array"]
class CustomPlugin(Plugin):
    def get_function_hook(self, fullname: str):
        # print(f"debug fullname {fullname}")
        if fullname == "numpy._core.multiarray.array":
            return self.base_array
        return None
    def get_method_hook(self, fullname):
        # print(f"debug fullname {fullname}")
        if fullname == "numpy.ndarray.__add__":
            return self.add_array
        return None

    def add_array(self, ctx):

        print(f"DEBUG: add ndarray called: {ctx}")
        # Save the args
        lhs = ctx.type
        rhs = ctx.arg_types[0][0]

        proper_lhs = get_proper_type(lhs)
        proper_rhs = get_proper_type(rhs)

        
        # If one or the other is just a constant
        if (rhs.type.fullname == 'builtins.int'):
            return proper_lhs
        elif (lhs.type.fullname == 'builtins.int'):
            return proper_rhs
        # If both are same dim
        elif proper_lhs == proper_rhs:
            return proper_lhs
        
        # Otherwise they are unequal, check for broadcasting
        else:
            # Get the shapes as a list and the sizes
            lhs_shape = lhs.args[0].items
            rhs_shape = rhs.args[0].items
            lhs_size = len(lhs_shape)
            rhs_size = len(rhs_shape)

            # If the lhs is bigger then set this to true (for later)
            lhs_vs_rhs = True if lhs_size > rhs_size else False
            output = []

            # Go through (backwards) each element
            for i in range(1, min(lhs_size, rhs_size)+1):
                # If either equals 1, then put the opposite element in the output list
                if lhs_shape[-i].value == 1:
                    output.insert(0, rhs_shape[-i])
                elif rhs_shape[-i].value == 1:
                    output.insert(0, lhs_shape[-i])
                # if they are both the same, put the element as well
                elif lhs_shape[-i] == rhs_shape[-i]:
                    output.insert(0, lhs_shape[-i])
                # Otherwise, show that this is a shape mismatch error NOT DONE YETT
                else:
                    ctx.api.fail("Shape mismatch", ctx.context)
                    return AnyType(TypeOfAny.from_error)
            # Attach the remaining of whatever is bigger to the front
            if lhs_vs_rhs:
                output = lhs_shape[:lhs_size-rhs_size] + output
            else:
                output = rhs_shape[:rhs_size-lhs_size] + output
            
            # return the final typing
            shape_tuple = TupleType(output, fallback=ctx.api.named_generic_type("builtins.tuple", []))
            final_type = ctx.api.named_generic_type("numpy.ndarray", [shape_tuple])
            print(f"Final output: {final_type}")

            return final_type






    def base_array(self, ctx: FunctionContext) -> Type:
        print(f"DEBUG: array() called: {ctx}")

        if ctx.args and ctx.args[0] and ctx.args[0][0]:
            
            shape, ranks = self.infer_shape(ctx.args[0][0])

            print(f"DEBUG: Inferred shape: {shape} with rank {ranks}")
            literal_dims = [LiteralType(dim, ctx.api.named_generic_type("builtins.int", [])) for dim in shape]

            shape_tuple = TupleType(literal_dims, fallback=ctx.api.named_generic_type("builtins.tuple", []))

            final_type = ctx.api.named_generic_type("numpy.ndarray", [shape_tuple])
            print(f"Type: {final_type}")
            

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