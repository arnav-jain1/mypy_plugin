from mypy.plugin import Plugin

class DebugPlugin(Plugin):
    def __init__(self, options):
        super().__init__(options)
        print("DEBUG: Plugin initialized successfully!")

def plugin(version):
    return DebugPlugin
