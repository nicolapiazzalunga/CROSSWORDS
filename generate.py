import sys
import random
import time
import copy
from crossword import *


class CrosswordCreator():

    def __init__(self, crossword):
        """
        Create new CSP crossword generate.
        """
        self.crossword = crossword
        self.domains = {
            var: self.crossword.words.copy()
            for var in self.crossword.variables
        }

    def letter_grid(self, assignment):
        """
        Return 2D array representing a given assignment.
        """
        letters = [
            [None for _ in range(self.crossword.width)]
            for _ in range(self.crossword.height)
        ]
        for variable, word in assignment.items():
            direction = variable.direction
            for k in range(len(word)):
                i = variable.i + (k if direction == Variable.DOWN else 0)
                j = variable.j + (k if direction == Variable.ACROSS else 0)
                letters[i][j] = word[k]
        return letters

    def print(self, assignment):
        """
        Print crossword assignment to the terminal.
        """
        letters = self.letter_grid(assignment)
        for i in range(self.crossword.height):
            for j in range(self.crossword.width):
                if self.crossword.structure[i][j]:
                    print(letters[i][j] or " ", end="")
                else:
                    print("█", end="")
            print()

    def save(self, assignment, filename):
        """
        Save crossword assignment to an image file.
        """
        from PIL import Image, ImageDraw, ImageFont
        cell_size = 100
        cell_border = 2
        interior_size = cell_size - 2 * cell_border
        letters = self.letter_grid(assignment)

        # Create a blank canvas
        img = Image.new(
            "RGBA",
            (self.crossword.width * cell_size,
             self.crossword.height * cell_size),
            "black"
        )
        font = ImageFont.truetype("assets/fonts/OpenSans-Regular.ttf", 80)
        draw = ImageDraw.Draw(img)

        for i in range(self.crossword.height):
            for j in range(self.crossword.width):

                rect = [
                    (j * cell_size + cell_border,
                     i * cell_size + cell_border),
                    ((j + 1) * cell_size - cell_border,
                     (i + 1) * cell_size - cell_border)
                ]
                if self.crossword.structure[i][j]:
                    draw.rectangle(rect, fill="white")
                    if letters[i][j]:
                        w, h = draw.textsize(letters[i][j], font=font)
                        draw.text(
                            (rect[0][0] + ((interior_size - w) / 2),
                             rect[0][1] + ((interior_size - h) / 2) - 10),
                            letters[i][j], fill="black", font=font
                        )

        img.save(filename)

    def solve(self):
        """
        Enforce node and arc consistency, and then solve the CSP.
        """
        self.enforce_node_consistency()
        self.ac3()
        return self.backtrack(dict())

    def enforce_node_consistency(self):
        """
        Update `self.domains` such that each variable is node-consistent.
        (Remove any values that are inconsistent with a variable's unary
         constraints; in this case, the length of the word.)
        """
        for var in self.crossword.variables:
            for value in self.crossword.words:
                if len(value) != var.length:
                    self.domains[var].remove(value)

    def revise(self, x, y):
        """
        Make variable `x` arc consistent with variable `y`.
        To do so, remove values from `self.domains[x]` for which there is no
        possible corresponding value for `y` in `self.domains[y]`.

        Return True if a revision was made to the domain of `x`; return
        False if no revision was made.
        """
        revised = False
        overlap = self.crossword.overlaps[x, y]
        for xvalue in self.domains[x].copy():
            self.domains[x].remove(xvalue)
            revised = True
            for yvalue in self.domains[y]:
                if xvalue[overlap[0]] == yvalue[overlap[1]]:
                    self.domains[x].add(xvalue)
                    revised = False
                    break
        return revised

    def ac3(self, arcs=None):
        """
        Update `self.domains` such that each variable is arc consistent.
        If `arcs` is None, begin with initial list of all arcs in the problem.
        Otherwise, use `arcs` as the initial list of arcs to make consistent.

        Return True if arc consistency is enforced and no domains are empty;
        return False if one or more domains end up empty.
        """        
        # Check if arguments arc is passed. If not create arcs
        if arcs == None:
            queue = self.create_arcs()
        else:
            queue = arcs

        # AC-3 iteration
        while queue:
            x, y = queue.pop()
            if self.revise(x, y):
                if len(self.domains[x]) == 0:
                    return False
                for z in self.crossword.neighbors(x) - {y}:
                    if (z, x) not in queue:
                        queue.append((z, x))
        return True

    def assignment_complete(self, assignment):
        """
        Return True if `assignment` is complete (i.e., assigns a value to each
        crossword variable); return False otherwise.
        """
        if len(assignment) == len(self.crossword.variables):
            return True
        return False

    def consistent(self, assignment):
        """
        Return True if `assignment` is consistent (i.e., words fit in crossword
        puzzle without conflicting characters); return False otherwise.
        """
        # Check if every value in assignment is distinct
        for element in assignment:
            for confront in {key:val for key, val in assignment.items() if key != element}:
                if assignment[element] == assignment[confront]:
                    return False

        # Check if node consistency is maintained
        for element in assignment:
            if len(assignment[element]) != element.length:
                return False

        # Check if arc-consistency with other assigned variables is maintained
        for element in assignment:
            element_value = assignment[element]
            for neighbor in self.crossword.neighbors(element):
                if neighbor in assignment:
                    overlap = self.crossword.overlaps[element, neighbor]
                    neighbor_value = assignment[neighbor]
                    if element_value[overlap[0]] != neighbor_value[overlap[1]]:
                        return False

        return True

    def order_domain_values(self, var, assignment):
        """
        Return a list of values in the domain of `var`, in order by
        the number of values they rule out for neighboring variables.
        The first value in the list, for example, should be the one
        that rules out the fewest values among the neighbors of `var`.
        """
        helper_list = list()
        values = self.domains[var].copy()
        neighbors_to_check = self.crossword.neighbors(var) - set(assignment)
        while values:
            count = 0
            value = values.pop()
            for neighbor in neighbors_to_check:
                overlap = self.crossword.overlaps[var, neighbor]
                for confront in self.domains[neighbor]:
                    if value[overlap[0]] != confront[overlap[1]]:
                        count += 1
            helper_list.append((value, count))
        helper_list.sort(key=lambda x: x[1])
        return [key for key, val in helper_list]

    def select_unassigned_variable(self, assignment):
        """
        Return an unassigned variable not already part of `assignment`.
        Choose the variable with the minimum number of remaining values
        in its domain. If there is a tie, choose the variable with the highest
        degree. If there is a tie, any of the tied variables are acceptable
        return values.
        """
        threshold = 0
        for variable in self.crossword.variables:
            if variable not in assignment:
                number_of_neighbors = len(self.crossword.neighbors(variable))
                if number_of_neighbors > threshold:
                    selected_variable = variable
                    threshold = number_of_neighbors
        return selected_variable        

    def backtrack(self, assignment):
        """
        Using Backtracking Search, take as input a partial assignment for the
        crossword and return a complete assignment if possible to do so.

        `assignment` is a mapping from variables (keys) to words (values).

        If no assignment is possible, return None.
        """
        if self.assignment_complete(assignment):
            return assignment
        var = self.select_unassigned_variable(assignment)
        orderedlist = self.order_domain_values(var, assignment)
        for value in orderedlist:
            assignment[var] = value            
            if self.consistent(assignment):

                # Inference
                arcs = self.create_arcs(var, assignment)
                if arcs != []:
                    domains_backup = copy.deepcopy(self.domains)
                    for element in assignment:
                        self.domains[element] = {assignment[element]}
                    if self.ac3(arcs) == False:
                        self.domains = copy.deepcopy(domains_backup)

                result = self.backtrack(assignment)
                if result != None:
                    return result
            assignment.pop(var)
        return None
    
    def create_arcs(self, var=None, assignment=set()):
        """
        Creates arcs to be used in AC-3. If neither 'var' or 'assignment' are passed
        arcs among all variables are computed, else only the arcs which connect variable 'var'
        to the 'neighbors' not in 'assignment' are computed
        """
        arcs = []
        if var is None:
            variables = self.crossword.variables
            for var in variables:
                for neighbor in (self.crossword.neighbors(var) - set(assignment)):
                    arc = (var, neighbor)
                    if arc in arcs:
                        continue
                    arcs.append(arc)
            return arcs
        else:
            variables = {var}       
            for var in variables:
                for neighbor in (self.crossword.neighbors(var) - set(assignment)):
                    arc = (neighbor, var)
                    if arc in arcs:
                        continue
                    arcs.append(arc)
            return arcs


def main():

    # Check usage
    if len(sys.argv) not in [3, 4]:
        sys.exit("Usage: python generate.py structure words [output]")

    # Parse command-line arguments
    structure = sys.argv[1]
    words = sys.argv[2]
    output = sys.argv[3] if len(sys.argv) == 4 else None

    # Generate crossword
    crossword = Crossword(structure, words)
    creator = CrosswordCreator(crossword)
    assignment = creator.solve()

    # Print result
    if assignment is None:
        print("No solution.")
    else:
        creator.print(assignment)
        if output:
            creator.save(assignment, output)


if __name__ == "__main__":
    start_time = time.time()
    main()
    print("--- %s seconds ---" % (time.time() - start_time))
