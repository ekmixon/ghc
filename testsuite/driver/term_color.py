from enum import Enum

enable_color = True

class Color(Enum):
    BLACK   = 30
    RED     = 31
    GREEN   = 32
    YELLOW  = 33
    BLUE    = 34
    MAGENTA = 35
    CYAN    = 36
    WHITE   = 37

def colored(color: Color, s: str) -> str:
    return f'\033[1m\033[{color.value}m{s}\033[0m' if enable_color else s

