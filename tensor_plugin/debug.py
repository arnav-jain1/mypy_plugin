from mypy.plugin import Plugin

class DebugPlugin(Plugin):
    def __init__(self, options):
        super().__init__(options)
        print("DEBUG: Plugin initialized successfully!")
        
    def get_function_hook(self, fullname: str):
        print(f"DEBUG: Function hook called for {fullname}")
        return None

def plugin(version):
    return DebugPlugin