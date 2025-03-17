from mypy.plugin import Plugin, FunctionContext, MethodContext
from mypy.types import Instance, Type , TupleType, TypeVarType, AnyType, TypeOfAny, get_proper_type, LiteralType
from mypy.nodes import TypeInfo, ARG_POS, Var, SYMBOL_FUNCBASE_TYPES, SymbolTableNode, IntExpr
from mypy.plugins.common import add_method_to_class
from mypy import nodes


class CustomPlugin(Plugin):
    def get_function_hook(self, fullname: str):
        print(f"debug fullname {fullname}")
        if fullname == "numpy._core.multiarray.array":
            return self.transform_array
        return None

    def transform_array(self, ctx: FunctionContext) -> Type:
        print("DEBUG: transform_ndarray called")
        
        # THIS WONT WORK AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA
        tensor_type = ctx.api.named_type("tensor.Tensor")
        
        if not (isinstance(tensor_type.node, TypeInfo)):
            print("DEBUG: Could not find tensor.Tensor")
            return ctx.default_return_type

        if ctx.arg_types and ctx.arg_types[0]:
            data_type = ctx.arg_types[0][0]
            print(f"DEBUG: Input data type: {data_type}")

            shape = self.infer_shape(data_type)
            print(f"DEBUG: Inferred shape: {shape}")

            ranks = [ctx.api.named_type("builtins.int") for _ in shape]

            shape_tuple = TupleType(ranks, ctx.api.named_generic_type("builtins.tuple", [ctx.api.named_type("builtins.int")]))

            return Instance(tensor_type.node, [shape_tuple])
        else:
            print("DEBUG: No arguments provided")   
            return Instance(tensor_type.node, [])

    def infer_shape(self, data_type: Type) -> list[Type]:
        if isinstance(data_type, Instance) and data_type.type.fullname == "builtins.list":
            if data_type.args:
                sub_shape = self.infer_shape(data_type.args[0])
                return [1] + sub_shape
        return []

def plugin(version):
    return CustomPlugin