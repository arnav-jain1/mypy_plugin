from mypy.plugin import Plugin, FunctionContext, MethodContext, CheckerPluginInterface, DynamicClassDefContext, SemanticAnalyzerPluginInterface
from mypy.types import Instance, Type , TupleType, TypeVarType, AnyType, TypeOfAny, get_proper_type, LiteralType, NoneType, UnionType, EllipsisType
from mypy.nodes import TypeInfo, ARG_POS, Var, SYMBOL_FUNCBASE_TYPES, SymbolTableNode, IntExpr, ListExpr, UnaryExpr, TupleExpr, NameExpr
from mypy.nodes import FuncDef, ReturnStmt, NameExpr, CallExpr, SliceExpr, EllipsisExpr, SymbolTableNode, GDEF, ArgKind
from mypy.plugins.common import add_method_to_class
from mypy.errorcodes import ErrorCode, OVERRIDE

from z3_solver import NumpySolver
from slicing import slice_output

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
            "numpy.lib._function_base_impl.insert": self.insert,
            "numpy._core.fromnumeric.sum": self.numpy_sum,
            "numpy._core.fromnumeric.mean": self.numpy_sum,
            "numpy._core.fromnumeric.var": self.numpy_sum,
            "numpy._core.fromnumeric.prod": self.numpy_sum,
            "numpy._core.fromnumeric.max": self.maximum_func,
            "numpy._core.multiarray.dot": self.dot_prod,
            "numpy._core.fromnumeric.transpose": self.transpose,
            "numpy.lib._type_check_impl.nan_to_num": self.nan_to_none,
            }

        self.method_hooks = {
            "numpy.ndarray.__mul__": self.broadcast, 
            "numpy.ndarray.__rmul__": self.fail,
            "numpy.ndarray.__add__": self.broadcast,
            "numpy.ndarray.__radd__": self.fail,
            "numpy.ndarray.__sub__": self.broadcast,
            "numpy.ndarray.__rsub__": self.fail,
            "numpy._core.multiarray._ConstructorEmpty.__call__": self.constructor,
            "numpy.ndarray.__matmul__": self.matmul,
            "numpy.ndarray.__rmatmul__": self.fail,
            "numpy.ndarray.reshape": self.reshape,
            "numpy.ndarray.__truediv__": self.broadcast,
            "numpy.ndarray.__rtruediv__": self.fail,
            "numpy.ndarray.argmax": self.argmax_method,
            'numpy.ndarray.__getitem__': self.slicing,
            }

        self.dynamic_class_hooks = {
            "numpy.maximum": self.maximum,
            "numpy.exp": self.exp,
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
        return None
    # # --- signature‐altering hooks ---
    def get_function_signature_hook(self, fullname):
        # print(f"DEBUG func sig: {fullname}")
        return None
    def get_method_signature_hook(self, fullname):
        # print(f"DEBUG method sig: {fullname}")
        return None
# endregion

# region array_creation
    def arange(self, ctx):
        output = [int]
        final_type = self.type_creator(ctx, output, False)

        return final_type

    def repeat(self, ctx):
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
                if param_types[i].type.fullname == 'builtins.float':
                    literal_dims.append(ctx.api.named_generic_type("builtins.int", []))
                elif param_types[i].type.fullname == 'builtins.int':
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
            # print(type(typ))
            if typ.type.fullname == "builtins.int":
                literal_dims.append(int)
                final_type = self.type_creator(ctx, literal_dims, False)
            elif typ.type.fullname == "numpy.ndarray":
                # TODO: This assumes the input is a numpy array, also add list/tuple
                return typ

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
            # Get the info and then return the final tyep
            if isinstance(ctx.args[0][0], NameExpr):
                shape = self.get_shape(ctx.arg_types[0][0].args[0])
            else:
                shape, ranks = self.infer_shape(ctx.args[0][0])
            # print(f"DEBUG: Inferred shape: {shape}")

            final_type = self.type_creator(ctx, shape, False)
            # print(f"Type: {final_type}")
            return final_type
# endregion

# region method_callbacks
    def matmul(self, ctx):
        func_name = self.get_func_name(ctx)
        
        if func_name not in self.context:
            self.context[func_name] = dict()

        lhs = ctx.type
        rhs = ctx.arg_types[0][0]
        lhs_name = ctx.context.left.name
        rhs_name = ctx.context.right.name

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

        solver = NumpySolver(lhs_shape, rhs_shape)
        lhs_new, rhs_new, output = solver.solve_matmul()

        if output == None:
            ctx.api.fail("Mismatch", ctx.context, code=OVERRIDE)
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
        lhs_name = ctx.context.left.name
        rhs_name = ctx.context.right.name

        # For union types, numpy arrays get priority, then ints, TODO: account for any
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
        if (rhs.type.fullname == 'builtins.int' or rhs.type.fullname == 'builtins.float'):
            return lhs
        elif (lhs.type.fullname == 'builtins.int' or rhs.type.fullname == 'builtins.float'):
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
            ctx.api.fail("Mismatch", ctx.context, code=OVERRIDE)
            return ctx.default_return_type

        # This sets the context for the lhs and rhs
        lhs_new_type = self.type_creator(ctx, lhs_new, False)
        rhs_new_type = self.type_creator(ctx, rhs_new, False)
        self.context[func_name][lhs_name] = lhs_new_type
        self.context[func_name][rhs_name] = rhs_new_type

        final_type = self.type_creator(ctx, output, False)
        # print(f"Final output: {final_type}")
        return final_type

    def slicing(self, ctx):
        func_name = self.get_func_name(ctx)
        if func_name not in self.context:
            self.context[func_name] = dict()

        slicing_raw = ctx.args[0][0]
        lhs = ctx.type
        if isinstance(ctx.context.base, CallExpr) or self.is_default(lhs):
            return ctx.default_return_type
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
            else:
                # Check if its a literal and if so append the value
                # otherwise assume it is an int TODO: HANDLE SLICING OF Op expr (<=, 1+2, etc)

                # print(arg_types[i])
                arg = arg_types[i]
                if isinstance(arg, LiteralType):
                    slicing.append(arg.value)
                else:
                    slicing.append(int)

        try:
            output = slice_output(lhs_shape, tuple(slicing))
        except TabError:
            ctx.api.fail("Ellipses Error or too many slices", ctx.context, code=OVERRIDE)
            return ctx.default_return_type
        except IndexError:
            ctx.api.fail("Slicing Error", ctx.context, code=OVERRIDE)
            return ctx.default_return_type

        

        if output == int:
            return ctx.api.named_generic_type("builtins.int", [])
        final_type = self.type_creator(ctx, output, False)
        return final_type

    def reshape(self, ctx):
        func_name = self.get_func_name(ctx)
        if func_name not in self.context:
            self.context[func_name] = dict()

        rhs = ctx.args[0][0]
        lhs = ctx.type
        lhs_name = ctx.context.callee.expr.name
    

        if lhs_name in self.context[func_name]:
            lhs_shape = self.get_shape(self.context[func_name][lhs_name].args[0])
        else:
            lhs_shape = self.get_shape(lhs.args[0])
        
        rhs_shape = []
        arg_types = ctx.arg_types[0][0].items if isinstance(ctx.arg_types[0][0], TupleType) else [ctx.arg_types[0][0]]
        minus_1 = False
        for i, item in enumerate(rhs.items):
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
                    ctx.api.fail("2 -1s when reshaping", ctx.context, code=OVERRIDE)
                    return ctx.default_return_type
                minus_1 = True
                rhs_shape.append(int)
            else:
                print("ERROR reshape for loop")
                print(item)
            
        solver = NumpySolver(lhs_shape, rhs_shape)
        lhs_new, rhs_new = solver.solve_reshape()
        
        if rhs_new == None:
            ctx.api.fail("Invalid reshape", ctx.context, code=OVERRIDE)
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
        func_def_node = ctx.type.type.get(ctx.context.callee.name).node
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

# endregion
    
# region function_callbacks
    def maximum_func(self, ctx):
        lhs = ctx.arg_types[0][0]
        if ctx.arg_names[1] and ctx.arg_names[1][0] == 'axis':
            dim = str(ctx.arg_types[1][0])
            if "Literal" in dim:
                axis = int(dim.replace('Literal[', '').rstrip('?').rstrip(']'))
            elif "UnaryExpr" in dim:
                axis = -1
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
        if isinstance(func_def_node, TypeInfo):
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
        
        lhs_shape = self.get_shape(lhs.args[0])
        output = lhs_shape[0:axis] + lhs_shape[axis+1:]

        lhs_shape = self.get_shape(lhs.args[0])
        output = list(lhs_shape)

        # This is the keepdims part
        keep_dim = False
        # print(ctx.arg_names)
        if ctx.arg_types[4]:
            keep_dim = str(ctx.arg_types[4][0])
            keep_dim = bool(keep_dim.replace('Literal[', '').rstrip('?').rstrip(']'))

        if keep_dim:
            output[axis] = 1
        else:
            output.pop(axis)

        final_type = self.type_creator(ctx, output, False)
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
            ctx.api.fail("Mismatch", ctx.context, code=OVERRIDE)
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

                
        if (lhs.type.fullname == 'builtins.int'):
            ctx.api.fail("Transposing an int", ctx.context, code=OVERRIDE)
            return ctx.default_return_type

        lhs_name = ctx.args[0][0].name

        if lhs_name in self.context[func_name]:
            lhs_shape = self.get_shape(self.context[func_name][lhs_name].args[0])
        else:
            lhs_shape = self.get_shape(lhs.args[0])

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
        raise NotImplementedError
        return ctx.default_return_type
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
        elif isinstance(index, NameExpr):
            output = arg_types[i].args[elem].value if isinstance(arg_types[i].args[elem], LiteralType) else int 

        
        return output

    def fail(self, ctx):
        ctx.api.fail("Mismatch", ctx.context, code=OVERRIDE)
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
        # If no input, assume a 2x2 matrix
        if isinstance(shape, AnyType) or isinstance(shape, Instance):
            return [int, int]
        shape = shape.items
        shape_output = []
        for dim in shape:
            if isinstance(dim, Instance):
                shape_output.append(int)
            elif isinstance(dim, LiteralType):
                shape_output.append(dim.value)
            elif isinstance(dim, UnionType):
                shape_output.output(tuple(d.value for d in dim.items))

        return shape_output
    
    def get_func_name(self, ctx):
        func = ctx.api.scope.current_function()
        if func:
            return func.name
        else:
            return "global"
# endregion

def plugin(version):
    return CustomPlugin