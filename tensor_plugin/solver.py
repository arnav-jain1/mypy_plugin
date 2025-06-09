from z3 import *
import typing
import numpy as np


# Unknown is to tell which is unknown and needs to be solved for. Ie lhs is completely unknown or rhs is compeletely unknown
# unknown being true means lhs is unknown
def matmul(lhs, rhs, unknown: bool):
    s = Solver()
    output = []
    var = []
    if unknown and lhs == None:
        size = len(rhs)

        # Edge case of rhs being 1dim needed

        
        if size == 2:
            var = [Any, rhs[0]]
            output = [Any, rhs[1]]
            return var, output
        
        rhs_broadcasting = rhs[:-2]
        var = [int, rhs[-2]]
        output = [int, rhs[-1]]

        for i in range(1, size-1):
            if rhs_broadcasting[-i] == 1:
                output.insert(0, int)
                var.insert(0, int)
            else:
                # could also be 1, but ignoring
                output.insert(0, rhs_broadcasting[-i])
                var.insert(0, rhs_broadcasting[-i])
            

    elif unknown:
        size = len(rhs)

        # Edge case of rhs being 1dim needed

        
        if size == 2:
            var = [Any, rhs[0]]
            output = [Any, rhs[1]]
            return var, output
        
        rhs_broadcasting = rhs[:-2]
        var = [int, rhs[-2]]
        output = [int, rhs[-1]]

        for i in range(1, size-1):
            if rhs_broadcasting[-i] == 1:
                output.insert(0, int)
                var.insert(0, int)
            else:
                # could also be 1, but ignoring
                output.insert(0, rhs_broadcasting[-i])
                var.insert(0, rhs_broadcasting[-i])
        var = [Any, rhs[0]]
        output = [Any, rhs[1]]
        return var, output
    
    rhs_broadcasting = rhs[:-2]
    var = [int, rhs[-2]]
    output = [int, rhs[-1]]

    for i in range(1, size-1):
        if rhs_broadcasting[-i] == 1:
            output.insert(0, int)
            var.insert(0, int)
        else:
            # could also be 1, but ignoring
            output.insert(0, rhs_broadcasting[-i])
            var.insert(0, rhs_broadcasting[-i])
    return var, output

def checkmatmul(guess, rhs):
    rhs = np.zeros(rhs)
    unknowns = []
    for i, num in enumerate(guess):
        if num == Any or num == int:
            unknowns.append(i)
            guess[i] = 1
    
    for idx in unknowns:
        for number in range(1, 10):
            guess[idx] = number
            _guess = np.zeros(guess)
            try:
                temp = _guess @ rhs
            except:
                print(_guess.shape)
                print(rhs.shape)
                return False
    return True

rhs = (2,3,4)
var, output = matmul(None, rhs, True)
print(f"{var} @ {rhs} = {output}")

correct = checkmatmul(var, rhs)
print(correct)
