from mypy.plugin import Plugin, FunctionContext, MethodContext, CheckerPluginInterface, DynamicClassDefContext, SemanticAnalyzerPluginInterface
from mypy.types import Instance, Type , TupleType, TypeVarType, AnyType, TypeOfAny, get_proper_type, LiteralType, NoneType
from mypy.nodes import TypeInfo, ARG_POS, Var, SYMBOL_FUNCBASE_TYPES, SymbolTableNode, IntExpr, ListExpr, UnaryExpr, TupleExpr, NameExpr
from mypy.plugins.common import add_method_to_class
from mypy import nodes
from typing import Tuple, List, Literal, final
from typing_extensions import Never
from mypy.errorcodes import ErrorCode, OVERRIDE


ERROR_TYPE = NoneType()

class CustomPlugin(Plugin):

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.func_hooks = {
            "numpy._core.multiarray.array": self.base_array,
            "numpy.random.mtrand.rand": self.rand,
            "numpy.random.mtrand.randn": self.rand,
            "numpy.random.mtrand.randint": self.rand_other,
            "numpy.random.mtrand.uniform": self.rand_other, 
            "numpy.random.mtrand.normal": self.rand_other, 
            "numpy.random.mtrand.binomial": self.rand_other,
            "numpy.random.mtrand.poisson": self.rand_other, 
            "numpy.random.mtrand.exponential": self.rand_other, 
            "numpy.random.mtrand.beta": self.rand_other, 
            "numpy.random.mtrand.gamma": self.rand_other, 
            "numpy.random.mtrand.chisquare": self.rand_other, 
            "numpy.random.mtrand.choice": self.rand_other }

        self.method_hooks = {
            "numpy.ndarray.__mul__": self.add_array, 
            "numpy.ndarray.__add__": self.add_array,
            "numpy._core.multiarray._ConstructorEmpty.__call__": self.constructor,
            "numpy.ndarray.__matmul__": self.matmul,
            "numpy.ndarray.reshape": self.reshape,
            "numpy.ndarray.__truediv__": self.add_array
            }

        self.broadcasting_funcs_direct = ["numpy.multiply", "numpy.add"]

    def get_dynamic_class_hook(self, fullname):
        # print(f"debug fullname {fullname}")
        if fullname in self.broadcasting_funcs_direct:
            return self.add_array_direct
        elif fullname == "numpy.maximum":
            return self.maximum
        return None


    def get_function_hook(self, fullname: str):
        # print(f"DEBUG fullname: {fullname}")
        return self.func_hooks.get(fullname, None)

    def get_method_hook(self, fullname):
        # print(f"debug fullname {fullname}")
        return self.method_hooks.get(fullname, None)
    
    #     # --- attribute access hooks ---
    # def get_attribute_hook(self, fullname):
    #     print(f"DEBUG fullname: {fullname}")
    #     return None

    # def get_class_attribute_hook(self, fullname):
    #     print(f"DEBUG fullname: {fullname}")
    #     return None

    # # --- class‐decorator hooks (two phases) ---
    # def get_class_decorator_hook(self, fullname):
    #     print(f"DEBUG fullname: {fullname}")
    #     return None

    # def get_class_decorator_hook_2(self, fullname):
    #     print(f"DEBUG fullname: {fullname}")
    #     return None

    # # --- metaclass / base‐class / MRO hooks ---
    # def get_metaclass_hook(self, fullname):
    #     print(f"DEBUG fullname: {fullname}")
    #     return None

    # def get_base_class_hook(self, fullname):
    #     print(f"DEBUG fullname: {fullname}")
    #     return None

    # def get_customize_class_mro(self, fullname):
    #     print(f"DEBUG fullname: {fullname}")
    #     return None

    # --- “type”‐analyze hook (e.g. for typing.Annotated) ---
    def get_type_analyze_hook(self, fullname):
        print(f"DEBUG fullname: {fullname}")
        return None

    # # --- signature‐altering hooks ---
    # def get_function_signature_hook(self, fullname):
    #     print(f"DEBUG fullname: {fullname}")
    #     return None

    # def get_method_signature_hook(self, fullname):
    #     print(f"DEBUG fullname: {fullname}")
    #     return None

    
    def maximum(self, ctx):
        name = ctx.call.args[0].name
        print(name)
        print("MARKER")
        print(ctx)
        
    
    # reshape
    def reshape(self, ctx):
        # print(f"Debug: Reshape called ctx {ctx}")
        args = ctx.args
        params = []
        for index in range(len(ctx.callee_arg_names)):
            if ctx.callee_arg_names[index] is None:
                params.append(args[index][0])
        new = []

        for param in params:
            print("MARKER")
            print(param)
            if isinstance(param, UnaryExpr):
                new.append(-1)
            elif isinstance(param, IntExpr):
                new.append(param.value)
            elif isinstance(param, TupleExpr):
                for item in param.items:
                    if isinstance(item, UnaryExpr):
                        new.append(-1)
                    elif isinstance(item, IntExpr):
                        new.append(item.value)
                break

        # TODO make sure oldtup is nonempty
        old_tup = ctx.type.args[0].items
        old_total = 1
        for dim in old_tup:
            old_total = old_total * dim.value
        
        placeholder = None
        
        # Go through new, if it is not -1 then we are good just divide the old num
        # Otherwise if is -1 and placeholder is none, save the index
        # Otherwise error
        for i, num in enumerate(new):
            if num != -1:
                old_total = old_total / num
            elif num == -1 and placeholder is None:
                placeholder = i
            elif num == -1 and placeholder is not None:
                ctx.api.fail("2 -1s", ctx.context)
                return ERROR_TYPE

        
        # If there is no placeholder and the old total is not 1, again error
        if placeholder is None and old_total != 1:
            ctx.api.fail("Bad dim (new does not equal old)", ctx.context)
            return ERROR_TYPE 
        
        # The -1 is the old total
        placeholder = old_total

        # Make sure -1 will become an int
        if placeholder == int(placeholder):
            placeholder = int(placeholder)
        else: 
            ctx.api.fail("Bad dim, -1 does not become a whole number", ctx.context)
            return ERROR_TYPE

        print(placeholder)

        output = []

        for number in new:
            if number != -1:
                output.append(LiteralType(number, ctx.api.named_generic_type("builtins.int", [])))
            else:
                print("HALLO", placeholder)
                output.append(LiteralType(placeholder, ctx.api.named_generic_type("builtins.int", [])))

        final_type = self.type_creator(ctx, output)
        print(f"Type: {final_type}")
            

        return final_type
    
    # Other rand (randint, uniform, normal, binomial, poisson, exp, beta, gamma, chi, choice)
    def rand_other(self, ctx):
        index = ctx.callee_arg_names.index("size")
        
        # If there is no "size" argument then it is just an float
        # TODO change this to a number like float
        if not ctx.args[index]:
            # print(ctx.api.named_generic_type("builtins.int", []))
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

        final_type = self.type_creator(ctx, literal_dims)
        # print(f"Type: {final_type}")
            
        return final_type

    # For rand, randn
    def rand(self, ctx):
        # print("rand2")
        params = ctx.args[0]
        # print(params)
        # print(type(params))

        literal_dims = []
        for param in params:
            literal = LiteralType(value=param.value, fallback=ctx.api.named_generic_type('builtins.int', []))
            literal_dims.append(literal)

        final_type = self.type_creator(ctx, literal_dims)
        # print(f"Type: {final_type}")


        return final_type

    # For ones
    def constructor(self, ctx):
        # print("DEBUG: ones/zeros/empty")

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

        # print(f"Type: {final_type}")
        final_type = self.type_creator(ctx, literal_dims)
            
        return final_type

    def matmul(self, ctx):
        lhs = ctx.type
        rhs = ctx.arg_types[0][0]

        # If one or the other is just a constant, error, use * instead
        # TODO NOT JUST INTS
        if (rhs.type.fullname == 'builtins.int'):
            ctx.api.msg.note("Cant use scalar with matmul, use * instead", ctx.context)
            return ERROR_TYPE
        elif (lhs.type.fullname == 'builtins.int'):
            # print(proper_rhs)
            ctx.api.msg.note("Cant use scalar with matmul, use * instead", ctx.context)
            return ERROR_TYPE

        # # Get the shapes as a list and the sizes
        lhs_shape = lhs.args[0].items
        rhs_shape = rhs.args[0].items
        lhs_size = len(lhs_shape)
        rhs_size = len(rhs_shape)
        # print(lhs_shape)
        # print(rhs_shape)

        output = []

        # both are one then it returns a scalar
        # TODO find a generic number type
        if lhs_size == 1 and rhs_size == 1:
            return_type = ctx.api.named_generic_type("builtins.int", [])
            return return_type
        elif lhs_size == 1:
            # If the lhs is a vec, essentially the second to last elem of rhs gets removed for the shape (if match)
            if lhs_shape[0] == rhs_shape[-2]:
                output = rhs_shape[:-2]
                output.append(rhs_shape[-1])

                final_type = self.type_creator(ctx, output)
                # print(f"Final output: {final_type}")
                return final_type
            else: 
                ctx.api.msg.fail("Shape mismatch (vector so LHS prepends 1 for dim and gets removed later)", ctx.context, code=OVERRIDE)
                return ERROR_TYPE
        elif rhs_size == 1:
            # If the rhs is a vec, essentially the last elem of LHS gets removed (if match)
            if lhs_shape[-1] == rhs_shape[0]:
                output = lhs_shape[:-1]

                final_type = self.type_creator(ctx, output)
                # print(f"Final output: {final_type}")
                return final_type
            else: 
                ctx.api.msg.fail("Shape mismatch (vector so LHS prepends 1 for dim and gets removed later)", ctx.context, code=OVERRIDE)
                return ERROR_TYPE

            
        lhs_broadcast_shape = lhs_shape[:-2]
        rhs_broadcast_shape = rhs_shape[:-2]

        # Check basic matmul rules
        if lhs_shape[-1] != rhs_shape[-2]:
            ctx.api.msg.fail("matmul error (the final 2 elems)", ctx.context, code=OVERRIDE)
            return ERROR_TYPE

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
                return ERROR_TYPE
        # Attach the remaining of whatever is bigger to the front
        if lhs_vs_rhs:
            output = lhs_shape[:len(lhs_broadcast_shape)-len(rhs_broadcast_shape)] + output
        else:
            output = rhs_shape[:len(rhs_broadcast_shape)-len(lhs_broadcast_shape)] + output
        
        # Add the m and l from m * n by n * l operation 
        output.append(lhs_shape[-2])
        output.append(rhs_shape[-1])

        # return the final typing
        final_type = self.type_creator(ctx, output)
        # print(f"Final output: {final_type}")

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
        # print(lhs.type.fullname)
        if (rhs.type.fullname != 'numpy.ndarray'):
            # print(proper_lhs)
            return proper_lhs
        elif (lhs.type.fullname != 'numpy.ndarray'):
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
                # Otherwise, show that this is a shape mismatch error
                else:
                    ctx.api.fail("Shape mismatch", ctx.context)
                    return ERROR_TYPE
            # Attach the remaining of whatever is bigger to the front
            if lhs_vs_rhs:
                output = lhs_shape[:lhs_size-rhs_size] + output
            else:
                output = rhs_shape[:rhs_size-lhs_size] + output
            
            # return the final typing
            final_type = self.type_creator(ctx, output)

            # print(f"Final output: {final_type}")
            return final_type


    # For np.array
    def base_array(self, ctx: FunctionContext) -> Type:
        # print(f"DEBUG: array() called: {ctx}")

        if ctx.args and ctx.args[0] and ctx.args[0][0]:
            
            # Get the info and then return the final tyep
            shape, ranks = self.infer_shape(ctx.args[0][0])

            # print(f"DEBUG: Inferred shape: {shape} with rank {ranks}")
            literal_dims = [LiteralType(dim, ctx.api.named_generic_type("builtins.int", [])) for dim in shape]

            final_type = self.type_creator(ctx, literal_dims)

            # print(f"Type: {final_type}")
            return final_type
        else:
            print("DEBUG: WEIRD ERROR HAPPENED")   
            print(ctx.args)
            print(ctx.args[0])
            print(ctx.args[0][0])
            return ctx.default_return_type

    def type_creator(self, ctx, literal_dims):
        shape_tuple = TupleType(literal_dims, fallback=ctx.api.named_generic_type("builtins.tuple", [AnyType(TypeOfAny.special_form)]))


        # Default type
        float64 = ctx.api.named_generic_type("numpy.float64", [])
        dtype = ctx.api.named_generic_type("numpy.dtype", [float64])
        
        # Go throught the args and find the dtype if listed
        for i, name_list in enumerate(ctx.arg_names):
            if name_list and name_list[0] == "dtype":
                if ctx.arg_types[i]:              
                    dtype = ctx.arg_types[i][0]     
                break
        
        final_type = ctx.api.named_generic_type("numpy.ndarray", [shape_tuple, dtype])
        return final_type


    def infer_shape(self, node):
        # print("DEBUG: infer shape")
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