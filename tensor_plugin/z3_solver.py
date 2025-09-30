from z3 import *

class NumpySolver:
    def __init__(self, lhs, rhs, lhs_rank=None, rhs_rank=None):
        self.lhs = lhs if lhs else []
        self.rhs = rhs if rhs else []

        if (not lhs) and (not lhs_rank) and (not rhs) and (not rhs_rank):
            print("Need at least one of lhs, lhs_rank, rhs, rhs_rank")
            raise RuntimeError         

        # inputed rank gets priority
        self.lhs_rank = lhs_rank if lhs_rank else len(lhs)
        self.rhs_rank = rhs_rank if rhs_rank else len(rhs)
        
        self.solver = Solver()
    
    def solve_matmul(self):
        # This is for vectors, essentially we add a dim that works and remove it later
        self.rhs_vec = False
        self.lhs_vec = False
        if self.rhs_rank == 1:
            self.rhs_vec = True
            self.rhs.append(int)
            self.rhs_rank += 1
        if self.lhs_rank == 1:
            self.lhs_vec = True
            self.lhs.insert(0, int)
            self.lhs_rank += 1

        # We then make everything the same rank (temporarily, remove it later)
        self.rank = max(self.lhs_rank, self.rhs_rank)
        if len(self.lhs) < self.rank:
            for _ in range(self.rank - len(self.lhs)):
                self.lhs.insert(0, int)

        if len(self.rhs) < self.rank:
            for _ in range(self.rank - len(self.rhs)):
                self.rhs.insert(0, int)
        
        # if self.lhs_rank < len(self.lhs):
        #     print("LHS rank must be >= length of lhs")
        #     print(self.lhs_rank, self.lhs)
        #     raise RuntimeError
        # elif self.rhs_rank < len(self.rhs):
        #     print(self.rhs_rank, self.rhs)
        #     print("RHS rank must be >= length of rhs")
        #     raise RuntimeError


        self.output = [int for _ in range(self.rank)]
        self.lhs_vars = [Int(f"lhs_{i}") for i in range(self.rank)]
        self.rhs_vars = [Int(f"rhs_{i}") for i in range(self.rank)]


        self._solve_matmul()
        
        # If its a satisfiable, get all the lhs/rhs
        lhs, rhs, output = None, None, None
        if self.solver.check() == sat:
            lhs, rhs = self.get_lhs_rhs()
            output = self.output
            
            # Remove the extra ones we added
            while self.lhs_rank < len(lhs):
                lhs.pop(0)
            while self.rhs_rank < len(rhs):
                rhs.pop(0)

            if self.lhs_vec and self.rhs_vec:
                output = int
                lhs.pop(0)
                rhs.pop(-1)
                
            elif self.lhs_vec:
                output.pop(-2)
                lhs.pop(0)
            elif self.rhs_vec:
                output.pop(-1)
                rhs.pop(-1)

        return lhs, rhs, output

    # Pretty much the same logic, just don't need extra dim add/remove for vecs
    def solve_broadcast(self):
        self.rank = max(self.lhs_rank, self.rhs_rank)

        if len(self.lhs) < self.rank:
            for _ in range(self.rank - len(self.lhs)):
                self.lhs.insert(0, int)

        if len(self.rhs) < self.rank:
            for _ in range(self.rank - len(self.rhs)):
                self.rhs.insert(0, int)
        

        self.output = [int for _ in range(self.rank)]
        self.lhs_vars = [Int(f"lhs_{i}") for i in range(self.rank)]
        self.rhs_vars = [Int(f"rhs_{i}") for i in range(self.rank)]


        self._solve_broadcast()
        lhs, rhs, output = None, None, None
        if self.solver.check() == sat:
            lhs, rhs = self.get_lhs_rhs()
            output = self.output
            while self.lhs_rank < len(lhs):
                lhs.pop(0)
            while self.rhs_rank < len(rhs):
                rhs.pop(0)

        return lhs, rhs, output
    
    
    def _solve_matmul(self):
        
        # Add the last 2 dims to the solver
        if isinstance(self.lhs[-2], int):
            self.solver.add(self.lhs_vars[-2] == self.lhs[-2])
        elif (isinstance(self.lhs[-2], tuple)):
            or_clauses = [self.lhs_vars[-2] == val for val in self.lhs[-2]]
            self.solver.add(Or(or_clauses))
        if isinstance(self.lhs[-1], int):
            self.solver.add(self.lhs_vars[-1] == self.lhs[-1])
        elif (isinstance(self.lhs[-1], tuple)):
            or_clauses = [self.lhs_vars[-1] == val for val in self.lhs[-1]]
            self.solver.add(Or(or_clauses))

        if isinstance(self.rhs[-2], int):
            self.solver.add(self.rhs_vars[-2] == self.rhs[-2])
        elif (isinstance(self.rhs[-2], tuple)):
            or_clauses = [self.rhs_vars[-2] == val for val in self.rhs[-2]]
            self.solver.add(Or(or_clauses))
        if isinstance(self.rhs[-1], int):
            self.solver.add(self.rhs_vars[-1] == self.rhs[-1])
        elif (isinstance(self.rhs[-1], tuple)):
            or_clauses = [self.rhs_vars[-1] == val for val in self.rhs[-1]]
            self.solver.add(Or(or_clauses))
        
        self.solver.add(self.lhs_vars[-1] == self.rhs_vars[-2])
        

        # The output of m * n @ n * k becomes m * k
        self.output[-2] = self.lhs[-2]
        self.output[-1] = self.rhs[-1]

        # Work back from the third to last element 
        i = 3
        while i <= self.rank:
            idx = -i

            # _d gets the dim value, var gets the var for the solver
            lhs_d = self.lhs[idx]
            rhs_d = self.rhs[idx]
            lhs_var = self.lhs_vars[idx]
            rhs_var = self.rhs_vars[idx]

            # Then we go through the possibilites, int * tup, any * tup, tup * tup, etc

            # Edge case both 1
            if isinstance(lhs_d, int) and lhs_d == 1 and isinstance(rhs_d, int) and rhs_d == 1:
                self.solver.add(lhs_var == 1)
                self.solver.add(rhs_var == 1)
                self.solver.add(lhs_var == rhs_var)
                self.output[idx] = 1

            # Edge case both tuple
            elif isinstance(lhs_d, tuple) and isinstance(rhs_d, tuple):
                # If they are both tups, we get all the possible vals from both and combine them
                # Lets say lhs has (1,3) and rhs has (1,2). If lhs is 1, then output can be 1 or 2, 
                # If lhs is 3, then the output is 3, so we want to combine them all and sort,
                # then just add the constraints
                lhs_or_clauses = [lhs_var == val for val in lhs_d]
                rhs_or_clauses = [rhs_var == val for val in rhs_d]

                possible_outputs = set()
                possible_outputs.update(lhs_d)
                possible_outputs.update(rhs_d)
                possible_outputs = tuple(sorted(list(possible_outputs)))
                self.output[idx] = possible_outputs

                self.solver.add(Or(lhs_or_clauses))
                self.solver.add(Or(rhs_or_clauses))
                self.solver.add(Or([lhs_var == 1, rhs_var == 1, lhs_var == rhs_var]))

            # Case 1 is lhs being a specific int int
            elif isinstance(lhs_d, int):
                self.solver.add(lhs_var == lhs_d)

                # If rhs is an int, add that to the solver
                # If it is a tup, add the possible vals
                # If it is any int, then just skip
                if isinstance(rhs_d, int):
                    self.solver.add(rhs_var == rhs_d)
                elif isinstance(rhs_d, tuple):
                    or_clauses = [rhs_var == val for val in rhs_d]
                    self.solver.add(Or(or_clauses))
                
                # If lhs is not 1, then add that rhs has to be 1 or lhs, output has to have it be lhs
                if lhs_d != 1:
                    self.solver.add(Or(rhs_var == 1, rhs_var == lhs_d))
                    self.output[idx] = lhs_d
                # If lhs is 1, then rhs can be anything and output is the rhs
                else:
                    self.output[idx] = rhs_d

            # Case 2: RHS is a tup
            # Issue here is if lhs is 1 or 5, then if lhs is 1 rhs can be anything if lhs is 5 then rhs has to be 1 or 5
            # False positives better than false negs, so let rhs be anything, maybe add a warning here? Look at later
            # Also the output is anything
            elif isinstance(lhs_d, tuple):
                or_clauses = [lhs_var == val for val in lhs_d]
                self.solver.add(Or(or_clauses))

                # If rhs is an int, add that to the solver 
                # If it is any int, then just skip
                if isinstance(rhs_d, int):
                    self.solver.add(rhs_var == rhs_d)
                    # If the int is not 1, then the output is rhs and if the int is 1, then the output is lhs
                    if rhs_d != 1:
                        self.solver.add(Or(lhs_var == rhs_var, lhs_var == 1))
                        self.output[idx] = rhs_d
                    else:
                        self.output[idx] = lhs_d
                # This is where it becomes tricky. Lets say lhs is (1,3) and rhs is anything. Then if lhs is 1, rhs is anything
                # but if lhs is 3, then rhs has to be 3. For now we just keep it anything and continue along
                else:
                    pass

            # Last case, lhs is any int
            elif lhs_d == int:
                # If rhs is an int, add that to the solver and the fact that rhs == lhs
                # If it is a tup, then similar for before, just cont
                # If it is any int, then just skip
                if isinstance(rhs_d, int):
                    self.solver.add(rhs_var == rhs_d)
                    # If rhs is not 1, then lhs has to be 1 or rhs, if it is 1 then cont
                    if rhs_d != 1:
                        self.solver.add(Or(lhs_var == 1, lhs_var == rhs_d))
                        self.output[idx] = rhs_d

                elif isinstance(rhs_d, tuple):
                    or_clauses = [rhs_var == val for val in rhs_d]
                    self.solver.add(Or(or_clauses))
                    
            i += 1
    
    # Broadcasting is the same but start frm the last elem
    def _solve_broadcast(self):
        i = 1

        while i <= self.rank:
            idx = -i

            lhs_d = self.lhs[idx]
            rhs_d = self.rhs[idx]
            lhs_var = self.lhs_vars[idx]
            rhs_var = self.rhs_vars[idx]

            # Edge case both 1
            if isinstance(lhs_d, int) and lhs_d == 1 and isinstance(rhs_d, int) and rhs_d == 1:
                self.solver.add(lhs_var == 1)
                self.solver.add(rhs_var == 1)
                self.solver.add(lhs_var == rhs_var)
                self.output[idx] = 1

            # Edge case both tuple
            elif isinstance(lhs_d, tuple) and isinstance(rhs_d, tuple):
                lhs_or_clauses = [lhs_var == val for val in lhs_d]
                rhs_or_clauses = [rhs_var == val for val in rhs_d]

                possible_outputs = set()
                possible_outputs.update(lhs_d)
                possible_outputs.update(rhs_d)
                possible_outputs = tuple(sorted(list(possible_outputs)))
                self.output[idx] = possible_outputs

                self.solver.add(Or(lhs_or_clauses))
                self.solver.add(Or(rhs_or_clauses))
                self.solver.add(Or([lhs_var == 1, rhs_var == 1, lhs_var == rhs_var]))

            # Case 1 is lhs being an int, add that lhs has to be that int to the solver
            elif isinstance(lhs_d, int):
                self.solver.add(lhs_var == lhs_d)

                # If rhs is an int, add that to the solver
                # If it is a tup, add the possible vals
                # If it is any int, then just skip
                if isinstance(rhs_d, int):
                    self.solver.add(rhs_var == rhs_d)
                elif isinstance(rhs_d, tuple):
                    or_clauses = [rhs_var == val for val in rhs_d]
                    self.solver.add(Or(or_clauses))
                
                # If lhs is not 1, then add that rhs has to be 1 or lhs, output has to have it be lhs
                if lhs_d != 1:
                    self.solver.add(Or(rhs_var == 1, rhs_var == lhs_d))
                    self.output[idx] = lhs_d
                # If lhs is 1, then rhs can be anything and output is the rhs
                else:
                    self.output[idx] = rhs_d

            # Case 2: RHS is a tup
            # Issue here is if lhs is 1 or 5, then if lhs is 1 rhs can be anything if lhs is 5 then rhs has to be 1 or 5
            # False positives better than false negs, so let rhs be anything, maybe add a warning here? Look at later
            # Also the output is anything
            elif isinstance(lhs_d, tuple):
                or_clauses = [lhs_var == val for val in lhs_d]
                self.solver.add(Or(or_clauses))

                # If rhs is an int, add that to the solver 
                # If it is any int, then just skip
                if isinstance(rhs_d, int):
                    self.solver.add(rhs_var == rhs_d)
                    # If the int is not 1, then the output is rhs and if the int is 1, then the output is lhs
                    if rhs_d != 1:
                        self.solver.add(Or(lhs_var == rhs_var, lhs_var == 1))
                        self.output[idx] = rhs_d
                    else:
                        self.output[idx] = lhs_d
                # This is where it becomes tricky. Lets say lhs is (1,3) and rhs is anything. Then if lhs is 1, rhs is anything
                # but if lhs is 3, then rhs has to be 3. For now we just keep it anything and continue along
                else:
                    pass
            # Last case, lhs is any int
            elif lhs_d == int:
                # If rhs is an int, add that to the solver and the fact that rhs == lhs
                # If it is a tup, then similar for before, just cont
                # If it is any int, then just skip
                if isinstance(rhs_d, int):
                    self.solver.add(rhs_var == rhs_d)
                    # If rhs is not 1, then lhs has to be 1 or rhs, if it is 1 then cont
                    if rhs_d != 1:
                        self.solver.add(Or(lhs_var == 1, lhs_var == rhs_d))
                        self.output[idx] = rhs_d

                elif isinstance(rhs_d, tuple):
                    or_clauses = [rhs_var == val for val in rhs_d]
                    self.solver.add(Or(or_clauses))
                    
            i += 1

    def get_lhs_rhs(self):
        """
        Gets the lhs and rhs but satisfying over and over again and keeping track
        Only caviat is if there are 10 or more possible sols then we assume its an int, can change

        First find all sols
        Format the sols into an output for the user
        """
        SOLUTION_LIMIT = 5



        # Track vars that are unconstrained, also keep sets for all possible sols
        lhs_solutions = [set() for _ in range(self.rank)]
        rhs_solutions = [set() for _ in range(self.rank)]

        unconstrained_vars = set()

        while self.solver.check() == sat:
            model = self.solver.model()
            
            # Where to hold the constraints to prevent repeat
            blocking_clauses = []

            # Process LHS variables
            for i, var in enumerate(self.lhs_vars):
                if var in unconstrained_vars:
                    continue 
                
                # Get the value from the model and add it to the solutions, then add it to the clauses
                val = model.eval(var, model_completion=True).as_long()
                lhs_solutions[i].add(val)
                
                blocking_clauses.append(var != val)

                # If more than the limit then add to unconstrained
                if len(lhs_solutions[i]) > SOLUTION_LIMIT:
                    unconstrained_vars.add(var)

            # Process RHS variables (same way)
            for i, var in enumerate(self.rhs_vars):
                if var in unconstrained_vars:
                    continue
                
                val = model.eval(var, model_completion=True).as_long()
                rhs_solutions[i].add(val)
                blocking_clauses.append(var != val)
                
                if len(rhs_solutions[i]) > SOLUTION_LIMIT:
                    unconstrained_vars.add(var)

            self.solver.add(Or(blocking_clauses))


        lhs_output = [None] * self.rank
        rhs_output = [None] * self.rank

        for i in range(self.rank):
            # Format LHS output

            lhs_var = self.lhs_vars[i]
            solutions = lhs_solutions[i]
            # If unconstrained or theres, then int. I had a reason for or not solutions, but I dont remember
            if lhs_var in unconstrained_vars or not solutions:
                lhs_output[i] = int
            elif len(solutions) == 1:
                lhs_output[i] = solutions.pop() # A single, concrete integer
            else:
                lhs_output[i] = tuple(sorted(list(solutions))) # A tuple of possibilities

            # Format RHS output
            rhs_var = self.rhs_vars[i]
            solutions = rhs_solutions[i]
            if rhs_var in unconstrained_vars or not solutions:
                rhs_output[i] = int
            elif len(solutions) == 1:
                rhs_output[i] = solutions.pop()
            else:
                rhs_output[i] = tuple(sorted(list(solutions)))
                
        return lhs_output, rhs_output
    