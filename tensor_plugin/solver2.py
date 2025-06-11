from z3 import *



class MatMulRHSKnown:
    def __init__(self, lhs, rhs):
        self.rhs = rhs
        self.lhs = lhs if lhs else []
        self.rhs_rank = len(rhs)
        self.results = []
        self.analyzed_ranks = set()


    def solve(self, lhs_rank = None):
        if self.lhs:
            rank = lhs_rank if lhs_rank else len(self.lhs)
        else:
            rank = lhs_rank if lhs_rank else self.rhs_rank
        
        if self.rhs_rank == 1 and rank == 1:
            lhs, output = self.solve1x1()
        else:
            lhs, output = self.solve_ndim(rank)

    
        return lhs, output
    
    def solve1x1(self):
        s = Solver()

        # Init the solver
        lhs_vars = [Int(f"lhs_0")]
        s.add([d > 0 for d in lhs_vars])

        if self.lhs:
            for i, elem in enumerate(self.lhs):
                if isinstance(elem, int):
                    s.add(lhs_vars[i] == elem)
                elif (isinstance(elem, tuple)):
                    or_clauses = [lhs_vars[i] == val for val in elem]
                    s.add(Or(or_clauses))



        # Split the shape
        M, N = lhs_vars[-1], self.rhs[-1]

        s.add(M == N)

        if s.check() == sat:
            output = [int]
            lhs = self.summarize_nd_lhs(s, 1)
            return lhs, output

        return None, None

    def solve_ndim(self, lhs_rank):

        s = Solver()

        # Init the solver
        lhs_vars = [Int(f"lhs_{i}") for i in range(lhs_rank)]
        s.add([d > 0 for d in lhs_vars])

        if self.lhs:
            for i, elem in enumerate(self.lhs):
                if isinstance(elem, int):
                    s.add(lhs_vars[i] == elem)
                elif (isinstance(elem, tuple)):
                    or_clauses = [lhs_vars[i] == val for val in elem]
                    s.add(Or(or_clauses))



        # Split the shape
        lhs_broadcasting_vars = lhs_vars[:-2]
        M, K = lhs_vars[-2], lhs_vars[-1]

        rhs_broadcasting_vars = self.rhs[:-2]
        Kr, N = self.rhs[-2], self.rhs[-1]


        s.add(K == Kr)

        broadcasting_constraints, output = self._broadcasting(lhs_broadcasting_vars, rhs_broadcasting_vars)
        if self.lhs and self.lhs[-2]:
            output.append(self.lhs[-2])
        else: 
            output.append(int)
        output.append(N)
        s.add(broadcasting_constraints)

        


        if s.check() == sat:
            # print(s)
            # print(broadcasting_constraints)
            lhs = self.summarize_nd_lhs(s, lhs_rank)
            # print(f"output: {output}")
        else:
            lhs = None
            output = None
        
        return lhs, output
    

    def _broadcasting(self, lhs_broadcasting, rhs_broadcasting):
        constraints = []
        output = []

        lhs_dim = len(lhs_broadcasting)
        rhs_dim = len(rhs_broadcasting)

        for i in range(max(rhs_dim, lhs_dim)):

            lhs_idx = lhs_dim -1 -i
            rhs_idx = rhs_dim -1 -i

            if lhs_idx >= 0 and rhs_idx >= 0:
                lhs_d = lhs_broadcasting[lhs_idx]
                rhs_d = rhs_broadcasting[rhs_idx]
                if rhs_d == 1:
                    if self.lhs:
                        output.append(self.lhs[lhs_idx])
                    else:
                        output.append(int)
                else:
                    constraints.append(Or(lhs_d == 1, lhs_d == rhs_d))
                    output.append(rhs_d)
            elif lhs_idx >= 0:
                # This is the scenario where the LHS is bigger than the rhs, can be anything so we append anything
                if self.lhs:
                    output.append(self.lhs[lhs_idx])
                else:
                    output.append(int)
            elif rhs_idx >= 0:
                output.append(rhs_broadcasting[rhs_idx])
        

        # reverse the output 
        return constraints, output[::-1]

    def summarize_nd_lhs(self, s, lhs_rank):
        constraints = s.assertions()
        # print(constraints)

        # Lowkey from Chatgpt, just turns the constraints into usable output 
        lhs_output = [None for _ in range(lhs_rank)]
        for c in constraints:
            # Handle the special 'Or' case first
            if is_or(c):
                # The children of 'Or' are the inner equality expressions
                # e.g., [lhs_0 == 1, lhs_0 == 2]
                options = []
                # We get the index from the first child expression (e.g., lhs_0 == 1)
                # arg(0) is the variable (lhs_0)
                variable_node = c.children()[0].arg(0)
                index = int(str(variable_node).split('_')[1])
                
                # Loop through the inner expressions to get their values
                for option_expr in c.children():
                    # arg(1) is the value (e.g., 1, then 2)
                    # .as_long() converts the Z3 number to a Python int
                    value = option_expr.arg(1).as_long()
                    options.append(value)
                
                # Store all options as a tuple in the results 
                # make sure that the thing is not more specific
                if not isinstance(lhs_output[index], int):
                    lhs_output[index] = tuple(options)

            # Handle simple binary expressions like '>' or '=='
            else:
                # Get the variable (e.g., lhs_0) and its index
                variable_node = c.arg(0)
                index = int(str(variable_node).split('_')[1])
                
                # Get the operation name (e.g., '>', '==')
                operation = c.decl().name()
                
                # Get the value node (e.g., 0, 3)
                value_node = c.arg(1)

                # Apply your rules
                if operation == '=':
                    lhs_output[index] = value_node.as_long()
                elif operation == '>' and value_node.as_long() == 0:
                    # We only update if a more specific rule (like '==' or 'Or')
                    # hasn't already filled the spot.
                    if lhs_output[index] is None:
                        lhs_output[index] = int
        # print(f"LHS: {lhs_output}")
        return lhs_output



x_shape = [int]
y_shape = [6]
inference = MatMulRHSKnown(None, y_shape)
lhs, output = inference.solve()
print(f"{x_shape} @ {y_shape} = {output} and lhs (should be y_shape): {lhs}")


# print("--- Test Case 1: Standard Case (Same Rank) ---")
# print("RHS: (2, 3, 4)")
# inference1 = MatMulRHSKnown(None, (2, 3, 4))
# inference1.solve()
# # Expected LHS: [2, <class 'int'>, 3]
# # Expected Output: [2, <class 'int'>, 4]


# print("--- Test Case 2: Standard Case (RHS Rank > LHS Rank) ---")
# print("RHS: (10, 8, 5, 6), solving for a compatible LHS of Rank 2")
# inference2 = MatMulRHSKnown(None, (10, 8, 5, 6))
# # We explicitly ask to find a compatible LHS of rank 2
# lhs1, out1 = inference2.solve(5)
# Expected LHS: [<class 'int'>, 5]
# Expected Output: [10, 8, <class 'int'>, 6]

# inference3 = MatMulRHSKnown(out1, (10, 8, 6, 10))
# inference3.solve()


# print("--- Test Case 3: Standard Case (LHS Rank > RHS Rank) ---")
# print("RHS: (5, 6), solving for a compatible LHS of Rank 4")
# inference3 = MatMulRHSKnown(None, (5, 6))
# inference3.solve(lhs_rank=4)
# # Expected LHS: [<class 'int'>, <class 'int'>, <class 'int'>, 5]
# # Expected Output: [<class 'int'>, <class 'int'>, <class 'int'>, 6]


# print("--- Test Case 4: Broadcasting Case ---")
# print("RHS: (1, 8, 5, 6)")
# inference4 = MatMulRHSKnown(None, (1, 8, 5, 6))
# inference4.solve()
# # The first broadcasting dim of LHS must be 1. The second can be 1 or 8.
# # The solver will find a valid instance.
# # Expected LHS: [1, 8, <class 'int'>, 5] (or a variation where dim 1 is 1)
# # Expected Output: [1, 8, <class 'int'>, 6]


# print("--- Test Case 5: Edge Case (2D Matrix) ---")
# print("RHS: (5, 6)")
# inference5 = MatMulRHSKnown(None, (5, 6))
# inference5.solve()
# # Expected LHS: [<class 'int'>, 5]
# # Expected Output: [<class 'int'>, 6]


# # 1
# x1 = (5, 3)
# y1 = (2, 3, 5, 4)

# # 2
# x2 = (4, 3, 2)
# y2 = (5, 2, 6)

# # 3
# x3 = (2, 3, 4, 5)
# y3 = (4, 1, 5, 6)

# # 4
# x4 = (2, 2, 2, 3, 4)
# y4 = (2, 3, 5)

# # 5
# x5 = (4, 6, 3)
# y5 = (2, 5)

# # 6
# x6 = (2, 1, 4, 2, 3)
# y6 = (3, 2, 1, 3, 6)

# # 7
# x7 = (3, 4)
# y7 = (4, 3, 2)

# # 8
# x8 = (3, 4)
# y8 = (3, 3)

# # 11
# x11 = (3, 4)
# y11 = (4, 2)

# # 12
# x12 = (5, 3, 4)
# y12 = (5, 4, 2)

# # 13
# x13 = (1, 2, 3, 6)
# y13 = (5, 2, 6, 4)

# # 14
# x14 = (4, 6)
# y14 = (1, 6, 5)

# # 15
# x15 = (3, 6, 7)
# y15 = (7, 2)

# # 16
# x16 = (2, 1, 4, 2, 3)
# y16 = (2, 3, 1, 3, 6)

# # 17
# x17 = (3, 1, 2, 8)
# y17 = (1, 8, 4)

# # 18
# x18 = (2, 5, 3)
# y18 = (1, 2, 3, 6)

# # 19
# x19 = (1, 1, 3, 4, 7)
# y19 = (7, 5)

# # 20
# x20 = (1, 9, 6)
# y20 = (2, 3, 1, 6, 10)

# test_cases = [
    # # failing
    # (x1, y1), (x2, y2), (x3, y3), (x4, y4),
    # (x5, y5), (x6, y6), (x7, y7), (x8, y8),

    # # passing
    # (x11, y11), (x12, y12), (x13, y13), (x14, y14),
    # (x15, y15), (x16, y16), (x17, y17), (x18, y18),
    # (x19, y19), (x20, y20),
# ]

# for x_shape, y_shape in test_cases:
    # inference = MatMulRHSKnown(x_shape, y_shape)
    # lhs, output = inference.solve()
    # print(f"{x_shape} @ {y_shape} = {output} and lhs (should be y_shape): {lhs}")

# inference = MatMulRHSKnown((int, 4,6), (1,6,5))
# lhs, output = inference.solve()
# print(f"{(int, 4, 6)} @ {(1, 6, 5)} = {output} and lhs (should be y_shape): {lhs}")