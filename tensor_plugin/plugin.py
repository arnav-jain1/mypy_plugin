from mypy.plugin import Plugin, FunctionContext, MethodContext, CheckerPluginInterface, DynamicClassDefContext, SemanticAnalyzerPluginInterface
from mypy.types import Instance, Type , TupleType, TypeVarType, AnyType, TypeOfAny, get_proper_type, LiteralType, NoneType, UnionType
from mypy.nodes import TypeInfo, ARG_POS, Var, SYMBOL_FUNCBASE_TYPES, SymbolTableNode, IntExpr, ListExpr, UnaryExpr, TupleExpr, NameExpr
from mypy.nodes import FuncDef, ReturnStmt, NameExpr, CallExpr
from mypy.nodes import FuncDef, AssignmentStmt, OpExpr, NameExpr
from mypy.plugins.common import add_method_to_class
from mypy import nodes
from typing import Tuple, List, Literal, final, Any
from typing_extensions import Never
from mypy.errorcodes import ErrorCode, OVERRIDE

from z3_solver import NumpySolver

ERROR_TYPE = NoneType()

class CustomPlugin(Plugin):

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.func_hooks = {
            "numpy._core.multiarray.array": self.base_array,
            "numpy._core.numeric.ones": self.constructor,
            "numpy._core.multiarray.zeros": self.constructor,
            "numpy._core.multiarray.empty": self.constructor,
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
            "numpy.ndarray.__mul__": self.broadcast, 
            "numpy.ndarray.__add__": self.broadcast,
            "numpy._core.multiarray._ConstructorEmpty.__call__": self.constructor,
            "numpy.ndarray.__matmul__": self.matmul,
            # "numpy.ndarray.reshape": self.reshape,
            "numpy.ndarray.__truediv__": self.broadcast
            }

        self.broadcasting_funcs_direct = ["numpy.multiply", "numpy.add"]

# region important_hooks
    def get_dynamic_class_hook(self, fullname):
        # print(f"debug fullname {fullname}")
        # if fullname in self.broadcasting_funcs_direct:
        #     return self.add_array_direct
        # elif fullname == "numpy.maximum":
        #     return self.maximum
        return None

    def get_function_hook(self, fullname: str):
        # print(f"DEBUG func: {fullname}")
        if ".func" in fullname:
            return self.test
        return self.func_hooks.get(fullname, None)

    def get_method_hook(self, fullname):
        # print(f"debug fullname {fullname}")
        return self.method_hooks.get(fullname, None)
# endregion
    
# region other_hooks
    # --- attribute access hooks ---
    def get_attribute_hook(self, fullname):
        # print(f"DEBUG fullname: {fullname}")
        return None
    def get_class_attribute_hook(self, fullname):
        # print(f"DEBUG fullname: {fullname}")
        return None
    # --- class‐decorator hooks (two phases) ---
    def get_class_decorator_hook(self, fullname):
        # print(f"DEBUG fullname: {fullname}")
        return None
    def get_class_decorator_hook_2(self, fullname):
        # print(f"DEBUG fullname: {fullname}")
        return None
    # --- metaclass / base‐class / MRO hooks ---
    def get_metaclass_hook(self, fullname):
        # print(f"DEBUG fullname: {fullname}")
        return None
    def get_base_class_hook(self, fullname):
        # print(f"DEBUG fullname: {fullname}")
        return None
    def get_customize_class_mro(self, fullname):
        # print(f"DEBUG fullname: {fullname}")
        return None
    # --- “type”‐analyze hook (e.g. for typing.Annotated) ---
    def get_type_analyze_hook(self, fullname):
        # print(f"DEBUG type analyze: {fullname}")
        return None
    # # --- signature‐altering hooks ---
    def get_function_signature_hook(self, fullname):
        # print(f"DEBUG func sig: {fullname}")
        if ".func" in fullname:
            return self.test2
        # if fullname == 'test3.func':
        #     return self.test
        return None
    def get_method_signature_hook(self, fullname):
        # print(f"DEBUG fullname: {fullname}")
        return None
# endregion

# region array_creation
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
    
    # For np.array
    def base_array(self, ctx):
        # print(f"DEBUG: array() called: {ctx}")
        if ctx.args and ctx.args[0] and ctx.args[0][0]:
            # Get the info and then return the final tyep
            shape, ranks = self.infer_shape(ctx.args[0][0])
            # print(f"DEBUG: Inferred shape: {shape} with rank {ranks}")

            final_type = self.type_creator(ctx, shape, False)
            # print(f"Type: {final_type}")
            return final_type
# endregion
    def matmul(self, ctx):
        # print(ctx)
        lhs = ctx.type
        rhs = ctx.arg_types[0][0]
        print(lhs)
        print(rhs)

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
        lhs_shape = self.get_shape(lhs.args[0])
        rhs_shape = self.get_shape(rhs.args[0])

        solver = NumpySolver(lhs_shape, rhs_shape)
        lhs_new, rhs_new, output = solver.solve_matmul()

        if output == None:
            return ERROR_TYPE


        final_type = self.type_creator(ctx, output, False)
        print(f"Final output: {final_type}")
        return final_type

    def broadcast(self, ctx):
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
        # # Get the shapes as a list and the sizes
        lhs_shape = self.get_shape(lhs.args[0])
        rhs_shape = self.get_shape(rhs.args[0])

        solver = NumpySolver()
        lhs_new, rhs_new, output = solver.solve_broadcast(lhs_shape, rhs_shape)

        if output == None:
            return ERROR_TYPE

        final_type = self.type_creator(ctx, output, False)
        # print(f"Final output: {final_type}")
        return final_type

    def test(self, ctx):
        func_def_node = ctx.context.callee.node

        for stmt in func_def_node.body.body:
            if isinstance(stmt, ReturnStmt):
                if isinstance(stmt.expr, NameExpr):
                    variable_name = stmt.expr.name
                    
                    print(variable_name)
                    ctx.api.msg.note(f"Function returns variable named: '{variable_name}'", ctx.context)
                    
        return ctx.default_return_type

    def test2(self, ctx):
        print(dir(ctx))
        
        print(ctx._fields)
        print(ctx.context)
        print(ctx.default_signature)
        return ctx.default_signature


# region tools
    def type_creator(self, ctx, shape, is_literal=True):
        if not is_literal:
            literal_dims = []
            for dim in shape:
                if isinstance(dim, int):
                    literal_dims.append(LiteralType(dim, ctx.api.named_generic_type("builtins.int", [])))
                elif isinstance(dim, tuple):
                    literal_dims.append(UnionType.make_union([LiteralType(d, ctx.api.named_generic_type("builtins.int", [])) for d in dim]))
                elif dim == int:
                    literal_dims.append(ctx.api.named_generic_type("builtins.int", []))
        else:
            literal_dims = shape

        shape_tuple = TupleType(literal_dims, fallback=ctx.api.named_generic_type("builtins.tuple", [AnyType(TypeOfAny.special_form)]))


        # TODO Default type (add the flaot type thing)
        # float64 = ctx.api.named_generic_type("numpy.float64", [])
        # dtype = ctx.api.named_generic_type("numpy.dtype", [float64])
        
        # Go throught the args and find the dtype if listed
        for i, name_list in enumerate(ctx.arg_names):
            if name_list and name_list[0] == "dtype":
                if ctx.arg_types[i]:              
                    dtype = ctx.arg_types[i][0]     
                break
        
        final_type = ctx.api.named_generic_type("numpy.ndarray", [shape_tuple])
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

    def get_shape(self, shape):
        if isinstance(shape, AnyType):
            return []
        shape = shape.items
        shape_output = [dim.value for dim in shape]

        return shape_output
# endregion

def plugin(version):
    return CustomPlugin