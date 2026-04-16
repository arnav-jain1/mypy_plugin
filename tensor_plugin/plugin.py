from mypy.plugin import (
    Plugin, FunctionContext, MethodContext, AnalyzeTypeContext, 
    CheckerPluginInterface, DynamicClassDefContext, SemanticAnalyzerPluginInterface
)
from mypy.types import Instance, Type , TupleType, TypeVarType, AnyType, TypeOfAny, get_proper_type, LiteralType, NoneType, UnionType, EllipsisType
from mypy.nodes import TypeInfo, ARG_POS, Var, SYMBOL_FUNCBASE_TYPES, SymbolTableNode, IntExpr, ListExpr, UnaryExpr, TupleExpr, NameExpr, MemberExpr
from mypy.nodes import FuncDef, ReturnStmt, NameExpr, CallExpr, SliceExpr, EllipsisExpr, SymbolTableNode, GDEF, IndexExpr
from mypy.errorcodes import ErrorCode, OVERRIDE, MISC

from z3_solver import NumpySolver, UnboundedType, Unbounded
from typing import *
import numpy as np
from copy import deepcopy

ERROR_TYPE = NoneType()

class CustomPlugin(Plugin):

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

        self.context = dict()
        self.file = None

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
            "numpy.random.mtrand.choice": self.rand_other,
            "numpy.random.mtrand.multinomial": self.multinomial,
            "numpy.random.mtrand.multivariate_normal": self.multivariate_normal,
            "numpy._core.multiarray.arange": self.arange,
            "numpy._core.multiarray.repeat": self.repeat,
            "numpy._core.fromnumeric.repeat": self.fromnumeric_repeat,
            "numpy.lib._function_base_impl.insert": self.insert,
            "numpy.lib._shape_base_impl.tile": self.numpy_tile,
            "numpy._core.fromnumeric.sum": self.numpy_sum,
            "numpy._core.fromnumeric.mean": self.numpy_sum,
            "numpy._core.fromnumeric.var": self.numpy_sum,
            "numpy._core.fromnumeric.prod": self.numpy_sum,
            "numpy._core.fromnumeric.max": self.maximum_func,
            "numpy._core.multiarray.dot": self.dot_prod,
            "numpy._core.fromnumeric.transpose": self.transpose,
            "numpy.lib._type_check_impl.nan_to_num": self.nan_to_none,
            "numpy.lib._shape_base_impl.expand_dims": self.expand_dims,
            }

        self.method_hooks = {
            "numpy.ndarray.__mul__": self.broadcast, 
            "numpy.ndarray.__rmul__": self.broadcast,
            "numpy.ndarray.__add__": self.broadcast,
            "numpy.ndarray.__radd__": self.broadcast,
            "numpy.ndarray.__sub__": self.broadcast,
            "numpy.ndarray.__rsub__": self.broadcast,
            "numpy._core.multiarray._ConstructorEmpty.__call__": self.constructor,
            "numpy.ndarray.__matmul__": self.matmul,
            "numpy.ndarray.__rmatmul__": self.fail,
            "numpy.ndarray.reshape": self.reshape,
            "numpy.ndarray.__truediv__": self.broadcast,
            "numpy.ndarray.__rtruediv__": self.broadcast,
            "numpy.ndarray.argmax": self.argmax_method,
            'numpy.ndarray.__getitem__': self.slicing,
            "numpy.ndarray.swapaxes": self.swapaxes,
            "numpy.ndarray.mean": self.method_mean,
            "numpy.ndarray.var": self.method_mean,
            "numpy.ndarray.sum": self.method_mean,
            "numpy.ndarray.transpose": self.method_transpose,
            }

        self.dynamic_class_hooks = {
            "numpy.maximum": self.maximum,
            "numpy.exp": self.exp,
            "numpy.log": self.exp,
            "numpy.sqrt": self.exp,
        }


# region important_hooks
    def get_dynamic_class_hook(self, fullname):
        # print(f"Class_hook: {fullname}")
        return self.dynamic_class_hooks.get(fullname, None)

    def get_function_hook(self, fullname: str):
        # print(f"Func_hook: {fullname}")
        # print(f"File: {self.file}")
        if not self.file:
            self.file = next(iter(self._modules))
        if self.file in fullname:
            return self.custom_func
        return self.func_hooks.get(fullname, None)

    def get_method_hook(self, fullname):
        # print(f"Method_hook: {fullname}")
        # print(f"File: {self.file}")
        if not self.file:
            self.file = next(iter(self._modules))
        if self.file in fullname:
            return self.custom_method
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
        if fullname == 'numpy.ndarray':
            return self.analyze_ndarray
        return None
    # # --- signature‐altering hooks ---
    def get_function_signature_hook(self, fullname):
        # print(f"DEBUG func sig: {fullname}")
        return None
    def get_method_signature_hook(self, fullname):
        # print(f"DEBUG method sig: {fullname}")
        if fullname == "numpy.ndarray.__getitem__":
            return self.slicing_sig
        return None
# endregion

# region array_creation
    def analyze_ndarray(self, ctx):
        args = []
        if str(ctx.type).strip("?") == "np.ndarray" and not ctx.type.args:
            any_type = AnyType(TypeOfAny.special_form)
            shape_type = ctx.api.named_type("builtins.tuple", [any_type])
            # dtype_type = ctx.api.named_type("numpy.dtype", [any_type])
            
            return_val = ctx.api.named_type("numpy.ndarray", [shape_type])
        else:
            for arg in ctx.type.args:
                analyzed_arg = ctx.api.anal_type(arg)
                args.append(analyzed_arg)
            return_val = ctx.api.named_type("numpy.ndarray", args)

        
        return return_val
            
    def arange(self, ctx):
        output = [int]
        final_type = self.type_creator(ctx, output, False)

        return final_type

    def repeat(self, ctx):
        # print(f"DEBUG repeat: arg_types={ctx.arg_types}")
        # Simple case for 1D array and int repeats
        input_shape = self.get_shape(ctx.arg_types[0][0].args[0])
        repeats_type = ctx.arg_types[1][0]
        # print(f"DEBUG repeat: input_shape={input_shape}, repeats_type={repeats_type}")

        if len(input_shape) == 1 and isinstance(repeats_type, (LiteralType, Instance)):
            input_len = input_shape[0]
            if isinstance(repeats_type, LiteralType):
                repeats_val = repeats_type.value
            else: # Is an int
                repeats_val = int

            if input_len == int or repeats_val == int:
                output_shape = [int]
            else:
                output_shape = [input_len * repeats_val]
            return self.type_creator(ctx, output_shape, False)

        output = [int]
        final_type = self.type_creator(ctx, output, False)
        return final_type

    def fromnumeric_repeat(self, ctx):
        # print(f"DEBUG fromnumeric_repeat: arg_types={ctx.arg_types}")
        # Simple case for 1D array and int repeats
        input_shape = self.get_shape(ctx.arg_types[0][0].args[0])
        repeats_type = ctx.arg_types[1][0]
        # print(f"DEBUG fromnumeric_repeat: input_shape={input_shape}, repeats_type={repeats_type}")

        if len(input_shape) == 1 and isinstance(repeats_type, (LiteralType, Instance)):
            input_len = input_shape[0]
            if isinstance(repeats_type, LiteralType):
                repeats_val = repeats_type.value
            else: # Is an int
                repeats_val = int

            if input_len == int or repeats_val == int:
                output_shape = [int]
            else:
                output_shape = [input_len * repeats_val]
            return self.type_creator(ctx, output_shape, False)

        output = [int]
        final_type = self.type_creator(ctx, output, False)
        return final_type

    def numpy_tile(self, ctx):
        # print(f"DEBUG tile: arg_types={ctx.arg_types}")
        # Simple case for 1D array and int reps
        input_shape = self.get_shape(ctx.arg_types[0][0].args[0])
        reps_type = ctx.arg_types[1][0]
        # print(f"DEBUG tile: input_shape={input_shape}, reps_type={reps_type}")

        if len(input_shape) == 1 and isinstance(reps_type, (LiteralType, Instance)):
            input_len = input_shape[0]
            if isinstance(reps_type, LiteralType):
                reps_val = reps_type.value
            else: # is an int
                reps_val = int

            if input_len == int or reps_val == int:
                output_shape = [int]
            else:
                output_shape = [input_len * reps_val]
            return self.type_creator(ctx, output_shape, False)

        output = [int]
        final_type = self.type_creator(ctx, output, False)
        return final_type
    
    def insert(self, ctx):
        arg = ctx.args
        if len(arg) == 3:
            shape = [int]
        else:
            input_mat = ctx.arg_types[0][0]
            shape = self.get_shape(input_mat.args[0])
            dim = str(ctx.arg_types[-1][0])
            axis = int(dim.replace('Literal[', '').rstrip('?').rstrip(']'))

            shape[axis] = int

        final_type = self.type_creator(ctx, shape, False)

        return final_type
        # print(arg[0][0])

    # TODO implement this
    def multinomial(self, ctx):
        shape = []
        if isinstance(ctx.args[0][0], IntExpr):
            shape.append(ctx.args[0][0].value)
        else:
            raise NotImplementedError
            return ctx.default_return_type

        final_type = self.type_creator(ctx, shape, False)
        return final_type

    def multivariate_normal(self, ctx):
        shape = []
        mu_type = ctx.arg_types[0][0]
        # TODO get mu properly
        mu = int
        if len(ctx.args) > 3:
            arg = ctx.args[2][0]
            if isinstance(arg, IntExpr):
                shape.append(arg.value)
            elif isinstance(arg, TupleExpr):
                raise NotImplementedError
                return ctx.default_return_type
            elif isinstance(arg, NameExpr):
                arg = ctx.arg_types[2][0]
                if isinstance(arg, LiteralType):
                    shape.append(arg.value)
                else:
                    shape.append(int)
        shape.append(mu)
        
        final_type = self.type_creator(ctx, shape, False)
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
        elif isinstance(param, NameExpr):
            literal_dims.append(ctx.api.named_generic_type("builtins.int", []))
        else:
            # If param is a member expr then it is a var
            if isinstance(param, MemberExpr):
                arg_type = ctx.arg_types[index][0]
                if isinstance(arg_type, AnyType):
                    output = [Unbounded]
                    final_type = self.type_creator(ctx, output, False)
                    return final_type
                elif isinstance(arg_type, IntExpr):
                    literal = LiteralType(value=arg_type.value, fallback=ctx.api.named_generic_type('builtins.int', []))
                    literal_dims.append(literal)
                #TODO Tuple
                else:
                    raise NotImplementedError
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
        if not ctx.args:
            return ctx.default_return_type
        params = ctx.args[0]
        param_types = ctx.arg_types[0]
        # print(params)
        # print(type(params))

        literal_dims = []
        for i, param in enumerate(params):
            if isinstance(param, LiteralType):
                literal = LiteralType(value=param.value, fallback=ctx.api.named_generic_type('builtins.int', []))
                literal_dims.append(literal)
            elif isinstance(param, NameExpr):
                # print(param_types[i])
                if isinstance(param_types[i], AnyType):
                    literal_dims.append(ctx.api.named_generic_type("builtins.int", []))
                elif param_types[i].type.fullname in ('builtins.float', 'builtins.int'):
                    literal_dims.append(ctx.api.named_generic_type("builtins.int", []))
                else:
                    return param_types[i]

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
            literal_dims.append(param.value)
        elif isinstance(param, NameExpr):
            typ = ctx.arg_types[0][0]
            if isinstance(typ, TupleType):
                for i, elem in enumerate(typ.items):
                    if isinstance(elem, LiteralType):
                        literal_dims.append(elem.value)
                    else:
                        literal_dims.append(int)
            elif typ.type.fullname == "builtins.int":
                literal_dims.append(int)
            elif typ.type.fullname == "numpy.ndarray":
                return typ

        else:
            typ = ctx.arg_types[0][0]
            if str(typ) == 'builtins.int':
                literal_dims.append(int)
            elif isinstance(typ, (AnyType, UnionType)):
                literal_dims.append(int)
            # For whatever reason typ is None wont work???? 
            elif str(typ) == "None":
                literal_dims.append(int)
            else:
                typ = ctx.arg_types[0][0].items
                for i, elem in enumerate(param.items):
                    if isinstance(elem, IntExpr):
                        literal_dims.append(elem.value)
                    else:
                        curr_type = typ[i]
                        if isinstance(curr_type, LiteralType):
                            literal_dims.append(curr_type.value)
                        else:
                            literal_dims.append(int)

        # print(f"Type: {final_type}")
        final_type = self.type_creator(ctx, literal_dims, False)
            
        return final_type
    
    # For np.array
    def base_array(self, ctx):
        # print(f"DEBUG: array() called: {ctx}")
        if ctx.args and ctx.args[0] and ctx.args[0][0]:
            # TODO, probably need to check this
            
            # this checks to see if the input is a unknown list
            if str(ctx.arg_types[0][0]).startswith("builtins.list") and isinstance(ctx.arg_types[0][0].args[0], AnyType):
                shape = [Any]
            # This is a check for the input to be an unknown singular val
            elif isinstance(ctx.arg_types[0][0], AnyType):
                shape = [int]
            # Get the info and then return the final tyep
            elif isinstance(ctx.args[0][0], NameExpr):
                shape = self.get_shape(ctx.arg_types[0][0].args[0])
            else:
                shape, ranks = self.infer_shape(ctx.args[0][0])
            # print(f"DEBUG: Inferred shape: {shape}")

            final_type = self.type_creator(ctx, shape, False)
            # print(f"Type: {final_type}")
            return final_type
# endregion

# region method_callbacks
    # TODO add support for unbounded and keep_dim
    def method_mean(self, ctx):
        lhs = ctx.type
        if ctx.arg_names[0] and ctx.arg_names[0][0] == 'axis':
            dims = str(ctx.arg_types[0][0]).replace("tuple[", "").rstrip("]").split(",")
            axis = []
            for dim in dims:
                # Clean the var and check what it is
                cleaned_dim = dim.replace('Literal[', '').rstrip('?').rstrip(']').strip()
                
                # If its any, then we dont know what we are deleting so we just have to return any
                if cleaned_dim == "Any":
                    lhs_shape = [Unbounded]
                    final_type = self.type_creator(ctx, lhs_shape, False)
                    return final_type
                # Otherwise its an int and we good
                else:
                    axis.append(int(cleaned_dim))
        else:
            int_type = ctx.api.named_generic_type("builtins.int", [])
            float_type = ctx.api.named_generic_type("builtins.float", [])
            # TODO change this to union but requires a lot of work
            # return UnionType.make_union([int_type, float_type])
            return int_type
        
        if isinstance(lhs, AnyType):
            return ctx.default_return_type
        
        lhs_shape = self.get_shape(lhs.args[0])

        if lhs_shape[0] == Unbounded and len(lhs_shape)-1 < len(axis):
            lhs_shape = [Unbounded]
        elif lhs_shape[0] == Unbounded:
            lhs_shape.pop(0)
            for elim_axis in axis[::-1]:
                lhs_shape.pop(elim_axis)
            lhs_shape.insert(0, Unbounded)
        else:
            for elim_axis in axis[::-1]:
                lhs_shape.pop(elim_axis)

        final_type = self.type_creator(ctx, lhs_shape, False)
        # print(f"Final output: {final_type}")
        return final_type

    def swapaxes(self, ctx):    
        lhs = ctx.type
        rhs = ctx.args
        lhs_shape= self.get_shape(lhs.args[0])
        is_unbounded = False
        if lhs_shape[0] == Unbounded:
            is_unbounded = True
            lhs_shape.pop(0)

        arguments = []
        for arg in rhs:
            elem = arg[0]
            if isinstance(elem, UnaryExpr):
                arguments.append(-elem.expr.value)
            elif isinstance(elem, IntExpr):
                arguments.append(elem.value)

        lhs_shape[arguments[0]], lhs_shape[arguments[1]] = lhs_shape[arguments[1]], lhs_shape[arguments[0]]

        if is_unbounded:
            lhs_shape.insert(0, Unbounded)
        
        output = self.type_creator(ctx, lhs_shape, False)
        return output
            
    def matmul(self, ctx):
        func_name = self.get_func_name(ctx)
        
        if func_name not in self.context:
            self.context[func_name] = dict()

        lhs = ctx.type
        rhs = ctx.arg_types[0][0]
        lhs_name = ctx.context.left.name if hasattr(ctx.context.left, 'name') else 'tmp_lhs'
        rhs_name = ctx.context.right.name if hasattr(ctx.context.right, 'name') else 'tmp_rhs'

        # If one or the other is just a constant, error, use * instead
        # TODO NOT JUST INTS
        if (rhs.type.fullname == 'builtins.int'):
            ctx.api.msg.note("Cant use scalar with matmul, use * instead", ctx.context)
            return ctx.default_return_type
        elif (lhs.type.fullname == 'builtins.int'):
            # print(proper_rhs)
            ctx.api.msg.note("Cant use scalar with matmul, use * instead", ctx.context)
            return ctx.default_return_type

        # Get the shapes as a list and the sizes, if its in the context use that
        # When adding input for dim and the dtype, will require replumbing
        if lhs_name in self.context[func_name]:
            lhs_shape = self.get_shape(self.context[func_name][lhs_name].args[0])
        else:
            lhs_shape = self.get_shape(lhs.args[0])
        if rhs_name in self.context[func_name]:
            rhs_shape = self.get_shape(self.context[func_name][rhs_name].args[0])
        else:
            rhs_shape = self.get_shape(rhs.args[0])

        if (all(elem == Unbounded for elem in lhs_shape) or not lhs_shape) and (all(elem == Unbounded for elem in rhs_shape) or not rhs_shape):
            output = [Any]
            lhs_new = [Any]
            rhs_new = [Any]
        else:
            solver = NumpySolver(lhs_shape, rhs_shape)
            lhs_new, rhs_new, output = solver.solve_matmul()

            if output == None:
                ctx.api.fail("Mismatch", ctx.context, code=MISC)
                return ctx.default_return_type

        # This sets the context for the lhs and rhs
        lhs_new_type = self.type_creator(ctx, lhs_new, False)
        rhs_new_type = self.type_creator(ctx, rhs_new, False)
        self.context[func_name][lhs_name] = lhs_new_type
        self.context[func_name][rhs_name] = rhs_new_type

        final_type = self.type_creator(ctx, output, False)
        # print(f"Final output: {final_type}")
        return final_type

    def broadcast(self, ctx):
        func_name = self.get_func_name(ctx)
        
        if func_name not in self.context:
            self.context[func_name] = dict()

        lhs = ctx.type
        rhs = ctx.arg_types[0][0]
        lhs_name = ctx.context.left.name if hasattr(ctx.context.left, 'name') else 'tmp_lhs'
        rhs_name = ctx.context.right.name if hasattr(ctx.context.right, 'name') else 'tmp_rhs'
        if isinstance(lhs, UnionType):
            lhs_items = lhs.items
            for item in lhs_items:
                if isinstance(item, AnyType):
                    continue
                elif item.type.fullname == "numpy.ndarray":
                    lhs = item
                    break
                elif item.type.fullname == "builtins.int":
                    lhs= item
        if isinstance(rhs, UnionType):
            rhs_items = rhs.items
            for item in rhs_items:
                if isinstance(item, AnyType):
                    continue
                elif item.type.fullname == "numpy.ndarray":
                    rhs = item
                    break
                elif item.type.fullname == "builtins.int":
                    rhs= item

        # If one or the other is just a constant, then it is just the opposite one
        if isinstance(rhs, UnionType) or (rhs.type.fullname in ['builtins.int', 'builtins.float', 'numpy.floating', "numpy.float64"]):
            return lhs
        elif (lhs.type.fullname == 'builtins.int' or lhs.type.fullname == 'builtins.float'):
            return rhs

        # Get the shapes as a list and the sizes, if its in the context use that
        # When adding input for dim and the dtype, will require replumbing
        if lhs_name in self.context[func_name]:
            lhs_shape = self.get_shape(self.context[func_name][lhs_name].args[0])
        else:
            lhs_shape = self.get_shape(lhs.args[0])
        if rhs_name in self.context[func_name]:
            rhs_shape = self.get_shape(self.context[func_name][rhs_name].args[0])
        else:
            rhs_shape = self.get_shape(rhs.args[0])

        solver = NumpySolver(lhs_shape, rhs_shape)
        lhs_new, rhs_new, output = solver.solve_broadcast()

        if output == None:
            ctx.api.fail("Mismatch", ctx.context, code=MISC)
            return ctx.default_return_type

        # This sets the context for the lhs and rhs
        lhs_new_type = self.type_creator(ctx, lhs_new, False)
        rhs_new_type = self.type_creator(ctx, rhs_new, False)
        self.context[func_name][lhs_name] = lhs_new_type
        self.context[func_name][rhs_name] = rhs_new_type

        final_type = self.type_creator(ctx, output, False)
        # print(f"Final output: {final_type}")
        return final_type

    # TODO Dont let this be any but like an int or smth instead
    def slicing_sig(self, ctx):    
        any_type = AnyType(TypeOfAny.explicit)
    
        # Force the expected argument types to Any so validation passes
        new_arg_types = [any_type] * len(ctx.default_signature.arg_types)
    
        return ctx.default_signature.copy_modified(arg_types=new_arg_types)

    def slicing(self, ctx):
        func_name = self.get_func_name(ctx)
        if func_name not in self.context:
            self.context[func_name] = dict()

        slicing_raw = ctx.args[0][0]
        lhs = ctx.type
        if isinstance(ctx.context.base, CallExpr) or self.is_default(lhs):
            return ctx.default_return_type
        if isinstance(ctx.context.base, IndexExpr):
            #TODO implement
            # print(ctx.context.base)
            pass
        lhs_name = ctx.context.base.name

        if lhs_name in self.context[func_name]:
            lhs_shape = self.get_shape(self.context[func_name][lhs_name].args[0])
        else:
            lhs_shape = self.get_shape(lhs.args[0])


        slicing = []
        slicing_raw = slicing_raw.items if isinstance(slicing_raw, TupleExpr) else [slicing_raw]
        arg_types = ctx.arg_types[0][0].items if isinstance(ctx.arg_types[0][0], TupleType) else [ctx.arg_types[0][0]]

        for i, elem in enumerate(slicing_raw):
            if isinstance(elem, IntExpr):
                slicing.append(elem.value)
            elif isinstance(elem, SliceExpr):
                start = self.args_of_slice(elem.begin_index, arg_types, i, 0)
                stop = self.args_of_slice(elem.end_index, arg_types, i, 1)
                stride = self.args_of_slice(elem.stride, arg_types, i, 2)

                slicing.append(slice(start, stop, stride))
            elif isinstance(elem, EllipsisExpr):
                slicing.append(Ellipsis)
            elif isinstance(elem, UnaryExpr) and isinstance(elem.expr, IntExpr):
                slicing.append(-elem.expr.value)
            else:
                # Check if its a literal and if so append the value
                # otherwise assume it is an int TODO: HANDLE SLICING OF Op expr (<=, 1+2, etc)

                # print(arg_types[i])
                arg = arg_types[i]
                if isinstance(arg, LiteralType):
                    slicing.append(arg.value)
                elif str(arg) == "builtins.int":
                    slicing.append(int)
                else:
                    slicing.append(slice(None, None, None))

        # try:
        #     output = slice_output(lhs_shape, tuple(slicing))
        # except TabError:
        #     ctx.api.fail("Ellipses Error or too many slices", ctx.context, code=MISC)
        #     return ctx.default_return_type
        # except IndexError:
        #     ctx.api.fail("Slicing Error", ctx.context, code=MISC)
        #     return ctx.default_return_type
        solver = NumpySolver(lhs=lhs_shape, rhs=None)
        output = solver.solve_slicing(tuple(slicing))
        # print(f"{ctx.api.path}:{ctx.context.line}: LHS {lhs_shape}, slice: {slicing}, output: {output}")

        # If None, Z3 proved an IndexError or invalid syntax
        if output is None:
            ctx.api.fail("Slicing Error or Index out of bounds", ctx.context, code=MISC)
            return ERROR_TYPE

        if not output:
            return ctx.api.named_generic_type("builtins.int", [])
        final_type = self.type_creator(ctx, output, False)

        # print(final_type)
        return final_type

    def reshape(self, ctx):
        func_name = self.get_func_name(ctx)
        if func_name not in self.context:
            self.context[func_name] = dict()

        rhs = []
        arg_types = []
        for i, item in enumerate(ctx.args):
            if item:
                rhs.append(item[0])
                arg_types.append(ctx.arg_types[i][0].items if isinstance(ctx.arg_types[i][0], TupleType) else ctx.arg_types[i][0])

        lhs = ctx.type
        if isinstance(ctx.context.callee.expr, CallExpr):
            output = [Unbounded]
            final_type = self.type_creator(ctx, output, False)
            return final_type

        lhs_name = ctx.context.callee.expr.name
    

        if lhs_name in self.context[func_name]:
            lhs_shape = self.get_shape(self.context[func_name][lhs_name].args[0])
        else:
            lhs_shape = self.get_shape(lhs.args[0])
        
        rhs_shape = []
        minus_1 = False
        rhs_items = rhs.items if hasattr(rhs, 'items') else rhs
        if isinstance(rhs_items[0], TupleExpr):
            rhs_items = rhs_items[0].items  
            arg_types = arg_types[0]

        for i, item in enumerate(rhs_items):
            if isinstance(item, IntExpr):
                rhs_shape.append(item.value)
            elif isinstance(item, NameExpr):
                arg = arg_types[i]
                if isinstance(arg, LiteralType):
                    rhs_shape.append(arg.value)
                else:
                    rhs_shape.append(int)
            elif isinstance(item, UnaryExpr):
                if minus_1:
                    ctx.api.fail("2 -1s when reshaping", ctx.context, code=MISC)
                    return ctx.default_return_type
                minus_1 = True
                rhs_shape.append(int)
            elif isinstance(item, IndexExpr):
                rhs_shape.append(int)
            elif isinstance(item, MemberExpr):
                rhs_shape = [Unbounded]
                break
            else:
                print("ERROR reshape for loop")
                print(item)
            
        solver = NumpySolver(lhs_shape, rhs_shape)
        lhs_new, rhs_new = solver.solve_reshape()
        
        if rhs_new == None:
            ctx.api.fail("Invalid reshape", ctx.context, code=MISC)
            return ctx.default_return_type
        
        lhs_new_type = self.type_creator(ctx, lhs_new, False)
        self.context[func_name][lhs_name] = lhs_new_type

        final_type = self.type_creator(ctx, rhs_new, False)
        # print(f"Final output: {final_type}")
        return final_type

    def argmax_method(self, ctx):
        if not ctx.args[1] and not ctx.arg_names[1]:
            int_type = ctx.api.named_generic_type("builtins.int", [])
            return int_type

        raise NotImplementedError
        return ctx.default_return_type

    def custom_method(self, ctx):
        if isinstance(ctx.context.callee, CallExpr):
            return ctx.default_return_type

        func_def_node = ctx.type.type.get(ctx.context.callee.name)
        if func_def_node is None:
            return ctx.default_return_type

        func_def_node = func_def_node.node
        if not isinstance(func_def_node, FuncDef):
            return ctx.default_return_type
        var_node = None
        for stmt in func_def_node.body.body:
            if isinstance(stmt, ReturnStmt) and isinstance(stmt.expr, NameExpr):
                var_node = stmt.expr.node.type
        return var_node if var_node else ctx.default_return_type

    # Not currently being used, but can be implemented in the future
    def custom_func_sig(self, ctx):
        func_name = ctx.context.callee.name
        
        # If we encounter a func that we havent seen before, it likely doesnt use numpy so unchange
        cur = ctx.default_signature
        if func_name not in self.context:
            return cur

        new_types = []
        for name, cur_type in zip(cur.arg_names, cur.arg_types):
            if name in self.context[func_name]:
                new_types.append(self.context[func_name][name])
            else:
                new_types.append(cur_type)
        new_sig = cur.copy_modified(arg_types=new_types)

        # print("SIG: ", new_sig)
        return new_sig

    def method_transpose(self, ctx):
        func_name = self.get_func_name(ctx)
        if func_name not in self.context:
            self.context[func_name] = dict()

        arg_types = []
        for i, item in enumerate(ctx.args[0]):
            if item:
                if isinstance(item, TupleType):
                    arg_types.append(item.items)
                elif isinstance(item, IntExpr):
                    arg_types.append(item.value)
                elif isinstance(item, UnaryExpr):
                    arg_types.append(-item.expr.value)
                else:
                    # TODO if it is an int or smth
                    raise NotImplementedError

        lhs = ctx.type
        if isinstance(ctx.context.callee.expr, CallExpr):
            output = [Unbounded]
            final_type = self.type_creator(ctx, output, False)
            return final_type

        lhs_name = ctx.context.callee.expr.name
    

        if lhs_name in self.context[func_name]:
            lhs_shape = self.get_shape(self.context[func_name][lhs_name].args[0])
        else:
            lhs_shape = self.get_shape(lhs.args[0])

        if lhs_shape[0] == Unbounded:
            if arg_types:
                max_elem = len(arg_types)
                output = [int] * max_elem
                output.insert(0, Unbounded)
                final_type = self.type_creator(ctx, output, False)
            else:
                #TODO just invert the list
                raise NotImplementedError
            return final_type
        
        output = deepcopy(lhs_shape)

        if arg_types:
            for j, i in enumerate(arg_types):
                output[j] = lhs_shape[i]
        else:
            output = output[::-1]
    
        final_type = self.type_creator(ctx, output, False)
        return final_type

# endregion
    
# region function_callbacks
    def expand_dims(self, ctx):
        lhs = ctx.arg_types[0][0]
        dim = str(ctx.arg_types[1][0])
        if "Literal" in dim:
            axis = int(dim.replace('Literal[', '').rstrip('?').rstrip(']'))
        elif "UnaryExpr" in dim:
            axis = -1
        elif "Any" in dim:
            output = [Unbounded]
            final_type = self.type_creator(ctx, output, False)
            return final_type
            
        if isinstance(lhs, AnyType):
            output = [Unbounded]
            final_type = self.type_creator(ctx, output, False)
            return final_type

        lhs_shape = self.get_shape(lhs.args[0])
        ub = False
        if lhs_shape[0] == Unbounded:
            ub = True
            lhs_shape.pop(0)

        lhs_shape.insert(axis, 1)

        if ub:
            lhs_shape.insert(0, Unbounded)
        final_type = self.type_creator(ctx, lhs_shape, False)
        # print(f"Final output: {final_type}")
        return final_type

    def maximum_func(self, ctx):
        lhs = ctx.arg_types[0][0]
        if ctx.arg_names[1] and ctx.arg_names[1][0] == 'axis':
            dim = str(ctx.arg_types[1][0])
            if "Literal" in dim:
                axis = int(dim.replace('Literal[', '').rstrip('?').rstrip(']'))
            elif "UnaryExpr" in dim:
                axis = -1
            elif "Any" in dim:
                output = [Unbounded]
                final_type = self.type_creator(ctx, output, False)
                return final_type
        else:
            int_type = ctx.api.named_generic_type("builtins.int", [])
            float_type = ctx.api.named_generic_type("builtins.float", [])
            # TODO change this to union but requires a lot of work
            # return UnionType.make_union([int_type, float_type])
            return int_type
            
        
        lhs_shape = self.get_shape(lhs.args[0])
        output = list(lhs_shape)

        # This is the keepdims part
        keep_dim = False
        # print(ctx.arg_names)
        if ctx.arg_types[3]:
            keep_dim = str(ctx.arg_types[3][0])
            keep_dim = bool(keep_dim.replace('Literal[', '').rstrip('?').rstrip(']'))

        if keep_dim:
            output[axis] = 1
        else:
            output.pop(axis)

        final_type = self.type_creator(ctx, output, False)
        # print(f"Final output: {final_type}")
        return final_type

    def custom_func(self, ctx):
        func_def_node = ctx.context.callee.node
        if isinstance(func_def_node, (TypeInfo, Var)):
            return ctx.default_return_type
        var_node = None
        for stmt in func_def_node.body.body:
            if isinstance(stmt, ReturnStmt) and isinstance(stmt.expr, NameExpr):
                var_node = stmt.expr.node.type
        return var_node if var_node else ctx.default_return_type

    def numpy_sum(self, ctx):
        lhs = ctx.arg_types[0][0]
        if ctx.arg_names[1] and ctx.arg_names[1][0] == 'axis':
            dim = str(ctx.arg_types[1][0])
            axis = int(dim.replace('Literal[', '').rstrip('?').rstrip(']'))
        else:
            int_type = ctx.api.named_generic_type("builtins.int", [])
            float_type = ctx.api.named_generic_type("builtins.float", [])
            # TODO change this to union but requires a lot of work
            # return UnionType.make_union([int_type, float_type])
            return int_type
        
        if isinstance(lhs, AnyType):
            return ctx.default_return_type
        
        # This is the keepdims part
        keep_dim = False
        # print(ctx.arg_names)
        if ctx.arg_types[4]:
            keep_dim = str(ctx.arg_types[4][0])
            keep_dim = bool(keep_dim.replace('Literal[', '').rstrip('?').rstrip(']'))

        lhs_shape = self.get_shape(lhs.args[0])
        ub = False
        if lhs_shape[0] == Unbounded and len(lhs_shape) == 1:
            output = [Unbounded]
            final_type = self.type_creator(ctx, output, False)
            return final_type

        if lhs_shape[0] == Unbounded:
            lhs_shape.pop(0)
            ub = True

        if keep_dim:
            lhs_shape[axis] = 1
        else:
            lhs_shape.pop(axis)


        if ub:
            lhs_shape.insert(0, Unbounded)
        final_type = self.type_creator(ctx, lhs_shape, False)
        # print(f"Final output: {final_type}")
        return final_type

    def dot_prod(self, ctx):
        func_name = self.get_func_name(ctx)
        if func_name not in self.context:
            self.context[func_name] = dict()

        lhs = ctx.arg_types[0][0]
        rhs = ctx.arg_types[1][0]
        if (rhs.type.fullname == 'builtins.int'):
            return lhs
        elif (lhs.type.fullname == 'builtins.int'):
            return rhs

        lhs_name = ctx.args[0][0].name
        rhs_name = ctx.args[1][0].name

        if lhs_name in self.context[func_name]:
            lhs_shape = self.get_shape(self.context[func_name][lhs_name].args[0])
        else:
            lhs_shape = self.get_shape(lhs.args[0])
        if rhs_name in self.context[func_name]:
            rhs_shape = self.get_shape(self.context[func_name][rhs_name].args[0])
        else:
            rhs_shape = self.get_shape(rhs.args[0])

        if len(lhs_shape) > 2 or len(rhs_shape) > 2:
            raise NotImplementedError
            return ctx.default_return_type

        solver = NumpySolver(lhs_shape, rhs_shape)
        lhs_new, rhs_new, output = solver.solve_matmul()

        if output == None:
            ctx.api.fail("Mismatch", ctx.context, code=MISC)
            return ctx.default_return_type

        # This sets the context for the lhs and rhs
        lhs_new_type = self.type_creator(ctx, lhs_new, False)
        rhs_new_type = self.type_creator(ctx, rhs_new, False)
        self.context[func_name][lhs_name] = lhs_new_type
        self.context[func_name][rhs_name] = rhs_new_type

        final_type = self.type_creator(ctx, output, False)
        # print(f"Final output: {final_type}")
        return final_type

    def transpose(self, ctx):
        func_name = self.get_func_name(ctx)
        if func_name not in self.context:
            self.context[func_name] = dict()

        lhs = ctx.arg_types[0][0]
        if isinstance(lhs, UnionType):
            lhs_items = lhs.items
            for item in lhs_items:
                if item.type.fullname == "numpy.ndarray":
                    lhs = item
                    break
        elif isinstance(lhs, AnyType):
            output = [Unbounded]
            final_type = self.type_creator(ctx, output, False)
            return final_type
                
        if (lhs.type.fullname == 'builtins.int'):
            ctx.api.fail("Transposing an int", ctx.context, code=MISC)
            return ctx.default_return_type

        lhs_name = ctx.args[0][0].name

        if lhs_name in self.context[func_name]:
            lhs_shape = self.get_shape(self.context[func_name][lhs_name].args[0])
        else:
            lhs_shape = self.get_shape(lhs.args[0])
        
        if isinstance(lhs_shape[0], UnboundedType) and len(lhs_shape) == 1:
            output = [Unbounded]
            final_type = self.type_creator(ctx, output, False)
            return final_type
            

        if isinstance(lhs_shape[0], UnboundedType):
            lhs_shape = lhs_shape[1:]
        lhs_new = lhs_shape[::-1]

        lhs_new_type = self.type_creator(ctx, lhs_new, False)
        self.context[func_name][lhs_name] = lhs_new_type

        return lhs_new_type

    def nan_to_none(self,ctx):
        lhs = ctx.arg_types[0][0]
        # print(lhs)
        return lhs
# endregion

# region dynamic_class_callbacks
    def maximum(self, ctx):
        lhs = ctx.call.args[0]
        rhs = ctx.call.args[1]
        if isinstance(rhs, NameExpr):
            rhs = ctx.api.lookup_current_scope(rhs.name).type
            var = Var(ctx.name, rhs)
            var._fullname = ctx.api.qualified_name(ctx.name)
            ctx.api.add_symbol_table_node(
                ctx.name,
                SymbolTableNode(GDEF, var)
            )
            return rhs
        elif isinstance(lhs, NameExpr):
            lhs = ctx.api.lookup_current_scope(lhs.name).type
            var = Var(ctx.name, lhs)
            var._fullname = ctx.api.qualified_name(ctx.name)
            ctx.api.add_symbol_table_node(
                ctx.name,
                SymbolTableNode(GDEF, var)
            )
            return lhs

        # TODO NOT JUST INTS
        # When neither are ints, broadcast them
        raise NotImplementedError
        return ctx.default_return_type

    def exp(self, ctx):
        lhs = ctx.call.args[0]
        if isinstance(lhs, NameExpr):
            lhs = ctx.api.lookup_current_scope(lhs.name).type
            if lhs:
                var = Var(ctx.name, lhs)
                var._fullname = ctx.api.qualified_name(ctx.name)
                ctx.api.add_symbol_table_node(
                    ctx.name,
                    SymbolTableNode(GDEF, var)
                )
            return lhs

        # TODO when it is just ints
        # raise NotImplementedError
        # return ctx.default_return_type
# endregion

# region tools
    def is_default(self, arg):

        if arg.type.fullname == "numpy.ndarray":
            arg = arg.args[0]
        else:
            return False

        if "Any" in str(arg):
            return True

        return False
    
    def args_of_slice(self, index, arg_types, i, elem):
        if index is None:
            output = None
        elif isinstance(index, IntExpr):
            output = index.value
        elif isinstance(index, UnaryExpr) and isinstance(index.expr, IntExpr):
            output = -index.expr.value
        elif isinstance(index, NameExpr):
            output = arg_types[i].args[elem].value if isinstance(arg_types[i].args[elem], LiteralType) else int 
        else:
            output = None

        
        return output

    def fail(self, ctx):
        ctx.api.fail("Mismatch", ctx.context, code=MISC)
        return ctx.default_return_type

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
                    literal_dims.append(AnyType(TypeOfAny.special_form))

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
        
        dtype = ctx.api.named_generic_type("numpy.dtype", [AnyType(TypeOfAny.special_form)])
        final_type = ctx.api.named_generic_type("numpy.ndarray", [shape_tuple, dtype])
        return final_type

    def infer_shape(self, node):
        # print("DEBUG: infer shape")
        current_nodes = [node]
        shape = []
        rank = 0

        while current_nodes:
            # Check if all nodes at current level are ListExpr
            if not all(isinstance(n, (ListExpr, TupleExpr)) for n in current_nodes):
                break

            # print(current_nodes)
            rank += 1
            first_node = current_nodes[0]
            current_length = len(first_node.items)
            if current_length == 1 and isinstance(first_node.items[0], NameExpr):
                shape.append(int)
            else:
                shape.append(current_length)

            # Flatten to next level of nodes
            current_nodes = [child for n in current_nodes for child in n.items]

        return shape, rank

    def get_shape(self, shape):
        # If no input, use unbounded type
        shape = get_proper_type(shape)
        if isinstance(shape, AnyType) or isinstance(shape, Instance):
            return [Unbounded]
        shape = shape.items
        shape_output = []
        for dim in shape:
            # print(dim)
            if isinstance(dim, Instance):
                shape_output.append(int)
            elif isinstance(dim, LiteralType):
                shape_output.append(dim.value)
            elif isinstance(dim, UnionType):
                shape_output.append(tuple(d.value for d in dim.items))
            elif isinstance(dim, AnyType):
                shape_output.append(Unbounded)
            

        return shape_output
    
    def get_func_name(self, ctx):
        class_obj = ctx.api.scope.enclosing_class()
        func_obj = ctx.api.scope.current_function()
        if class_obj:
            class_name = class_obj.name
        else:
            class_name = "global"

        if func_obj:
            func_name = func_obj.name
        else:
            func_name = "global"
        
        return f"{class_name}_{func_name}"
# endregion

def plugin(version):
    return CustomPlugin
