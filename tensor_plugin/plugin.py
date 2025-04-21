from mypy.plugin import Plugin, FunctionContext, MethodContext, CheckerPluginInterface
from mypy.types import Instance, Type , TupleType, TypeVarType, AnyType, TypeOfAny, get_proper_type, LiteralType
from mypy.nodes import TypeInfo, ARG_POS, Var, SYMBOL_FUNCBASE_TYPES, SymbolTableNode, IntExpr, ListExpr
from mypy.plugins.common import add_method_to_class
from mypy import nodes
from typing import Tuple, List, Literal, final
from typing_extensions import Never
from mypy.errorcodes import ErrorCode, OVERRIDE



array_types = ["numpy.random.mtrand.randint", "numpy._core.multiarray.array"]
class CustomPlugin(Plugin):

    rand_names = ["numpy.random.mtrand.rand", "numpy.random.mtrand.randn"]
    rand_other_names = ["numpy.random.mtrand.randint", "numpy.random.mtrand.uniform", 
    "numpy.random.mtrand.normal", "numpy.random.mtrand.binomial", "numpy.random.mtrand.poisson", 
    "numpy.random.mtrand.exponential", "numpy.random.mtrand.beta", "numpy.random.mtrand.gamma", 
    "numpy.random.mtrand.chisquare", "numpy.random.mtrand.choice"]

    broadcasting_funcs = ["numpy.ndarray.__mul__", "numpy.ndarray.__add__"]
    broadcasting_funcs_direct = ["numpy.multiply", "numpy.add"]

    check = True
    prev = 0

    def get_dynamic_class_hook(self, fullname):
        # print(f"debug fullname {fullname}")
        if fullname in self.broadcasting_funcs_direct:
            return self.add_array_direct
        return None

    def get_function_hook(self, fullname: str):
        # print(f"debug fullname {fullname}")
        if fullname == "numpy._core.multiarray.array":
            return self.base_array
        elif fullname in self.rand_names:
            return self.rand
        elif fullname in self.rand_other_names:
            return self.rand_other
        return None
    def get_method_hook(self, fullname):
        print(f"debug fullname {fullname}")
        if fullname in self.broadcasting_funcs:
            return self.add_array
        elif fullname == "numpy._core.multiarray._ConstructorEmpty.__call__":
            return self.constructor
        elif fullname == "numpy.ndarray.__matmul__":
            return self.matmul
        return None
    
    # Other rand (randint, uniform, normal, binomial, poisson, exp, beta, gamma, chi, choice)
    def rand_other(self, ctx):
        index = ctx.callee_arg_names.index("size")
        
        # If there is no "size" argument then it is just an float
        # TODO change this to a number
        if not ctx.args[index]:
            print(ctx.api.named_generic_type("builtins.int", []))
            return ctx.api.named_generic_type("builtins.int", [])
        param = ctx.args[index][0]

        literal_dims = []

        if isinstance(param, IntExpr):
            literal = LiteralType(value=param.value, fallback=ctx.api.named_generic_type('builtins.int', []))
            literal_dims.append(literal)
        else:
            for elem in param.items:
                if isinstance(elem, IntExpr):
                    literal = LiteralType(value=elem.value, fallback=ctx.api.named_generic_type('builtins.int', []))
                    literal_dims.append(literal)

        shape_tuple = TupleType(literal_dims, fallback=ctx.api.named_generic_type("builtins.tuple", []))

        final_type = ctx.api.named_generic_type("numpy.ndarray", [shape_tuple])
        # print(f"Type: {final_type}")
            
        return final_type

    # For rand, randn
    def rand(self, ctx):
        params = ctx.args[0]
        # print(params)
        # print(type(params))

        literal_dims = []
        for param in params:
            literal = LiteralType(value=param.value, fallback=ctx.api.named_generic_type('builtins.int', []))
            literal_dims.append(literal)

        shape_tuple = TupleType(literal_dims, fallback=ctx.api.named_generic_type("builtins.tuple", []))

        final_type = ctx.api.named_generic_type("numpy.ndarray", [shape_tuple])
        # print(f"Type: {final_type}")


        return final_type

    # For ones
    def constructor(self, ctx):

        param = ctx.args[0][0]
        # print(param)
        # print(type(param))

        literal_dims = []

        if isinstance(param, IntExpr):
            literal = LiteralType(value=param.value, fallback=ctx.api.named_generic_type('builtins.int', []))
            literal_dims.append(literal)
        else:
            for elem in param.items:
                if isinstance(elem, IntExpr):
                    literal = LiteralType(value=elem.value, fallback=ctx.api.named_generic_type('builtins.int', []))
                    literal_dims.append(literal)

        shape_tuple = TupleType(literal_dims, fallback=ctx.api.named_generic_type("builtins.tuple", []))

        final_type = ctx.api.named_generic_type("numpy.ndarray", [shape_tuple])
        # print(f"Type: {final_type}")
            


        return final_type

    def matmul(self, ctx):
        lhs = ctx.type
        rhs = ctx.arg_types[0][0]

        # If one or the other is just a constant, error, use * instead
        if (rhs.type.fullname == 'builtins.int'):
            ctx.api.msg.note("Cant use scalar with matmul, use * instead", ctx.context)
            return AnyType(TypeOfAny.from_error)
        elif (lhs.type.fullname == 'builtins.int'):
            # print(proper_rhs)
            ctx.api.msg.note("Cant use scalar with matmul, use * instead", ctx.context)
            return AnyType(TypeOfAny.from_error)

        # # Get the shapes as a list and the sizes
        # print(lhs)
        # print(lhs.args)
        # print(lhs.args[0])
        lhs_shape = lhs.args[0].items
        rhs_shape = rhs.args[0].items
        lhs_size = len(lhs_shape)
        rhs_size = len(rhs_shape)
        print(lhs_shape)
        print(rhs_shape)

        # Save the lhs and check for repeat
        if self.prev == lhs_shape:
            ctx.api.fail("yuh", ctx.context)
            return AnyType(TypeOfAny.from_error)
        else:
            self.prev = rhs_shape

        output = []

        # both are one then it returns a scalar
        # TODO find a generic number type
        if lhs_size == 1 and rhs_size == 1:
            return_type = ctx.api.named_generic_type("builtins.int", [])
            print(return_type)
            return return_type
        elif lhs_size == 1:
            print("lhs")
            print(lhs_shape, rhs_shape)
            print(lhs_size)
            # If the lhs is a vec, essentially the second to last elem of rhs gets removed for the shape (if match)
            if lhs_shape[0] == rhs_shape[-2]:
                output = rhs_shape[:-2]
                output.append(rhs_shape[-1])

                shape_tuple = TupleType(output, fallback=ctx.api.named_generic_type("builtins.tuple", []))
                final_type = ctx.api.named_generic_type("numpy.ndarray", [shape_tuple])
                print(f"Final output: {final_type}")
                return final_type
            else: 
                ctx.api.msg.fail("Shape mismatch (vector so LHS prepends 1 for dim and gets removed later)", ctx.context, code=OVERRIDE)
                return AnyType(TypeOfAny.from_error)
        elif rhs_size == 1:
            print("rhs")
            print(lhs_shape, rhs_shape)
            print(rhs_size)
            # If the rhs is a vec, essentially the last elem of LHS gets removed (if match)
            if lhs_shape[-1] == rhs_shape[0]:
                output = lhs_shape[:-1]

                shape_tuple = TupleType(output, fallback=ctx.api.named_generic_type("builtins.tuple", []))
                final_type = ctx.api.named_generic_type("numpy.ndarray", [shape_tuple])
                print(f"Final output: {final_type}")
                return final_type
            else: 
                ctx.api.msg.fail("Shape mismatch (vector so LHS prepends 1 for dim and gets removed later)", ctx.context, code=OVERRIDE)
                return AnyType(TypeOfAny.from_error)

            
        lhs_broadcast_shape = lhs_shape[:-2]
        rhs_broadcast_shape = rhs_shape[:-2]

        # Check basic matmul rules
        if lhs_shape[-1] != rhs_shape[-2]:
            ctx.api.msg.fail("matmul error (the final 2 elems)", ctx.context, code=OVERRIDE)
            return AnyType(TypeOfAny.from_error)

        # Everything except the last 2 are just broadcasting so use that code

        # If the lhs is bigger then set this to true (for later)
        lhs_vs_rhs = True if lhs_size > rhs_size else False


        
        # Go through (backwards) each element
        for i in range(1, min(lhs_size-2, rhs_size-2)+1):
            # If either equals 1, then put the opposite element in the output list
            if lhs_broadcast_shape[-i].value == 1:
                output.insert(0, rhs_broadcast_shape[-i])
            elif rhs_broadcast_shape[-i].value == 1:
                output.insert(0, lhs_broadcast_shape[-i])
            # if they are both the same, put the element as well
            elif lhs_broadcast_shape[-i] == rhs_broadcast_shape[-i]:
                output.insert(0, lhs_broadcast_shape[-i])
            # Otherwise, show that this is a shape mismatch error NOT DONE YETT
            else:
                ctx.api.msg.fail("Shape mismatch", ctx.context, code=OVERRIDE)
                return AnyType(TypeOfAny.from_error)
        # Attach the remaining of whatever is bigger to the front
        if lhs_vs_rhs:
            output = lhs_shape[:len(lhs_broadcast_shape)-len(rhs_broadcast_shape)] + output
        else:
            output = rhs_shape[:len(rhs_broadcast_shape)-len(lhs_broadcast_shape)] + output
        
        # Add the m and l from m * n by n * l operation 
        output.append(lhs_shape[-2])
        output.append(rhs_shape[-1])

        # return the final typing
        shape_tuple = TupleType(output, fallback=ctx.api.named_generic_type("builtins.tuple", []))
        final_type = ctx.api.named_generic_type("numpy.ndarray", [shape_tuple])
        print(f"Final output: {final_type}")

        return final_type
        

    # For np.add and np.multiply, doesnt work rn
    def add_array_direct(self, ctx):
        print(f"DEBUG: add ndarray called: {ctx}")
        print(f"DEBUG: add ndarray called: {ctx.api}")
        print(f"DEBUG: add ndarray called: {ctx.call}")

    # For addition (broadcast and element wise) called via * or +
    def add_array(self, ctx):

        # print(f"DEBUG: add ndarray called: {ctx}")
        # Save the args
        lhs = ctx.type
        rhs = ctx.arg_types[0][0]

        proper_lhs = get_proper_type(lhs)
        proper_rhs = get_proper_type(rhs)

        
        # If one or the other is just a constant
        if (rhs.type.fullname == 'builtins.int'):
            # print(proper_lhs)
            return proper_lhs
        elif (lhs.type.fullname == 'builtins.int'):
            # print(proper_rhs)
            return proper_rhs
        # If both are same dim
        elif proper_lhs == proper_rhs:
            return proper_lhs
        
        # Otherwise they are unequal, check for broadcasting
        else:
            # # Get the shapes as a list and the sizes
            # print(lhs)
            # print(lhs.args)
            # print(lhs.args[0])
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
            # print(f"Final output: {final_type}")

            return final_type


    # For np.array
    def base_array(self, ctx: FunctionContext) -> Type:
        # print(f"DEBUG: array() called: {ctx}")

        if ctx.args and ctx.args[0] and ctx.args[0][0]:
            
            shape, ranks = self.infer_shape(ctx.args[0][0])

            # print(f"DEBUG: Inferred shape: {shape} with rank {ranks}")
            literal_dims = [LiteralType(dim, ctx.api.named_generic_type("builtins.int", [])) for dim in shape]

            shape_tuple = TupleType(literal_dims, fallback=ctx.api.named_generic_type("builtins.tuple", []))

            final_type = ctx.api.named_generic_type("numpy.ndarray", [shape_tuple])
            # print(f"Type: {final_type}")
            

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