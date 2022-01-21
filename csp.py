"""CSP (Constraint Satisfaction Problems) problems and solvers. (Chapter 6)"""
"kratisa mono ton kodika me tous algorithmous pou einai aparaititos gia tin askisi kai oxi tin ilopoiisi ton paradeigmaton"
#from _typeshed import NoneType
import itertools
import random
import re
import string
from collections import defaultdict, Counter
from functools import reduce, total_ordering
from operator import eq, neg
import pprint

from sortedcontainers import SortedSet

import search
from utils import argmin_random_tie, count, first, extend


class CSP(search.Problem):
    """This class describes finite-domain Constraint Satisfaction Problems.
    A CSP is specified by the following inputs:
        variables   A list of variables; each is atomic (e.g. int or string).
        domains     A dict of {var:[possible_value, ...]} entries.
        neighbors   A dict of {var:[var,...]} that for each variable lists
                    the other variables that participate in constraints.
        constraints A function f(A, a, B, b) that returns true if neighbors
                    A, B satisfy the constraint when they have values A=a, B=b

    In the textbook and in most mathematical definitions, the
    constraints are specified as explicit pairs of allowable values,
    but the formulation here is easier to express and more compact for
    most cases (for example, the n-Queens problem can be represented
    in O(n) space using this notation, instead of O(n^4) for the
    explicit representation). In terms of describing the CSP as a
    problem, that's all there is.

    However, the class also supports data structures and methods that help you
    solve CSPs by calling a search function on the CSP. Methods and slots are
    as follows, where the argument 'a' represents an assignment, which is a
    dict of {var:val} entries:
        assign(var, val, a)     Assign a[var] = val; do other bookkeeping
        unassign(var, a)        Do del a[var], plus other bookkeeping
        nconflicts(var, val, a) Return the number of other variables that
                                conflict with var=val
        curr_domains[var]       Slot: remaining consistent values for var
                                Used by constraint propagation routines.
    The following methods are used only by graph_search and tree_search:
        actions(state)          Return a list of actions
        result(state, action)   Return a successor of state
        goal_test(state)        Return true if all constraints satisfied
    The following are just for debugging purposes:
        nassigns                Slot: tracks the number of assignments made
        display(a)              Print a human-readable representation
    """

    def __init__(self, variables, domains, neighbors, constraints):
        """Construct a CSP problem. If variables is empty, it becomes domains.keys()."""
        super().__init__(())
        variables = variables or list(domains.keys())
        self.variables = variables
        self.domains = domains
        self.neighbors = neighbors
        self.constraints = constraints
        self.curr_domains = None
        self.nassigns = 0


    def assign(self, var, val, assignment):
        """Add {var: val} to assignment; Discard the old value if any."""
        assignment[var] = val
        self.nassigns += 1

    def unassign(self, var, assignment):
        """Remove {var: val} from assignment.
        DO NOT call this if you are changing a variable to a new value;
        just call assign for that."""
        if var in assignment:
            del assignment[var]

    def nconflicts(self, var, val, assignment):
        """Return the number of conflicts var=val has with other variables."""

        # Subclasses may implement this more efficiently
        def conflict(var2):
            return var2 in assignment and not self.constraints(var, val, var2, assignment[var2])

        return count(conflict(v) for v in self.neighbors[var])

    def display(self, assignment):
        """Show a human-readable representation of the CSP."""
        # Subclasses can print in a prettier way, or display with a GUI
        print(assignment)
        
    # These methods are for the tree and graph-search interface:

    def actions(self, state):
        """Return a list of applicable actions: non conflicting
        assignments to an unassigned variable."""
        if len(state) == len(self.variables):
            return []
        else:
            assignment = dict(state)
            var = first([v for v in self.variables if v not in assignment])
            return [(var, val) for val in self.domains[var]
                    if self.nconflicts(var, val, assignment) == 0]

    def result(self, state, action):
        """Perform an action and return the new state."""
        (var, val) = action
        return state + ((var, val),)

    def goal_test(self, state):
        """The goal is to assign all variables, with all constraints satisfied."""
        assignment = dict(state)
        return (len(assignment) == len(self.variables)
                and all(self.nconflicts(variables, assignment[variables], assignment) == 0
                        for variables in self.variables))

    # These are for constraint propagation

    def support_pruning(self):
        """Make sure we can prune values from domains. (We want to pay
        for this only if we use it.)"""
        if self.curr_domains is None:
            self.curr_domains = {v: list(self.domains[v]) for v in self.variables}

    def suppose(self, var, value):
        """Start accumulating inferences from assuming var=value."""
        self.support_pruning()
        removals = [(var, a) for a in self.curr_domains[var] if a != value]
        self.curr_domains[var] = [value]
        return removals

    def prune(self, var, value, removals):
        """Rule out var=value."""
        self.curr_domains[var].remove(value)
        if removals is not None:
            removals.append((var, value))

    def choices(self, var):
        """Return all values for var that aren't currently ruled out."""
        return (self.curr_domains or self.domains)[var]

    def infer_assignment(self):
        """Return the partial assignment implied by the current inferences."""
        self.support_pruning()
        return {v: self.curr_domains[v][0]
                for v in self.variables if 1 == len(self.curr_domains[v])}

    def restore(self, removals):
        """Undo a supposition and all inferences from it."""
        for B, b in removals:
            self.curr_domains[B].append(b)

    # This is for min_conflicts search

    def conflicted_vars(self, current):
        """Return a list of variables in current assignment that are in conflict"""
        return [var for var in self.variables
                if self.nconflicts(var, current[var], current) > 0]
    
# ______________________________________________________________________________
# Constraint Propagation with AC3


def no_arc_heuristic(csp, queue):
    return queue


def dom_j_up(csp, queue):
    return SortedSet(queue, key=lambda t: neg(len(csp.curr_domains[t[1]])))


def AC3(csp, queue=None, removals=None, arc_heuristic=dom_j_up):
    """[Figure 6.3]"""
    if queue is None:
        queue = {(Xi, Xk) for Xi in csp.variables for Xk in csp.neighbors[Xi]}
    csp.support_pruning()
    queue = arc_heuristic(csp, queue)
    checks = 0
    while queue:
        (Xi, Xj) = queue.pop()
        revised, checks = revise(csp, Xi, Xj, removals, checks)
        if revised:
            if not csp.curr_domains[Xi]:
                return False, checks  # CSP is inconsistent
            for Xk in csp.neighbors[Xi]:
                if Xk != Xj:
                    queue.add((Xk, Xi))
    return True, checks  # CSP is satisfiable


def revise(csp, Xi, Xj, removals, checks=0):
    """Return true if we remove a value."""
    revised = False
    for x in csp.curr_domains[Xi][:]:
        # If Xi=x conflicts with Xj=y for every possible y, eliminate Xi=x
        # if all(not csp.constraints(Xi, x, Xj, y) for y in csp.curr_domains[Xj]):
        conflict = True
        for y in csp.curr_domains[Xj]:
            if csp.constraints(Xi, x, Xj, y):
                conflict = False
            checks += 1
            if not conflict:
                break
        if conflict:
            csp.prune(Xi, x, removals)
            revised = True
        #tis epomenes 3 grammes tis prosthesa ego
        if (csp.curr_domains[Xi]=={}):
            #print("domain wipeout");
            csp.weights[(Xi, Xj)] += 1
            csp.weights[(Xj, Xi)] += 1
    return revised, checks


# Constraint Propagation with AC3b: an improved version
# of AC3 with double-support domain-heuristic

def AC3b(csp, queue=None, removals=None, arc_heuristic=dom_j_up):
    if queue is None:
        queue = {(Xi, Xk) for Xi in csp.variables for Xk in csp.neighbors[Xi]}
    csp.support_pruning()
    queue = arc_heuristic(csp, queue)
    checks = 0
    while queue:
        (Xi, Xj) = queue.pop()
        # Si_p values are all known to be supported by Xj
        # Sj_p values are all known to be supported by Xi
        # Dj - Sj_p = Sj_u values are unknown, as yet, to be supported by Xi
        Si_p, Sj_p, Sj_u, checks = partition(csp, Xi, Xj, checks)
        if not Si_p:
            return False, checks  # CSP is inconsistent
        revised = False
        for x in set(csp.curr_domains[Xi]) - Si_p:
            csp.prune(Xi, x, removals)
            revised = True
        if revised:
            for Xk in csp.neighbors[Xi]:
                if Xk != Xj:
                    queue.add((Xk, Xi))
        if (Xj, Xi) in queue:
            if isinstance(queue, set):
                # or queue -= {(Xj, Xi)} or queue.remove((Xj, Xi))
                queue.difference_update({(Xj, Xi)})
            else:
                queue.difference_update((Xj, Xi))
            # the elements in D_j which are supported by Xi are given by the union of Sj_p with the set of those
            # elements of Sj_u which further processing will show to be supported by some vi_p in Si_p
            for vj_p in Sj_u:
                for vi_p in Si_p:
                    conflict = True
                    if csp.constraints(Xj, vj_p, Xi, vi_p):
                        conflict = False
                        Sj_p.add(vj_p)
                    checks += 1
                    if not conflict:
                        break
            revised = False
            for x in set(csp.curr_domains[Xj]) - Sj_p:
                csp.prune(Xj, x, removals)
                revised = True
            if revised:
                for Xk in csp.neighbors[Xj]:
                    if Xk != Xi:
                        queue.add((Xk, Xj))
    return True, checks  # CSP is satisfiable


def partition(csp, Xi, Xj, checks=0):
    Si_p = set()
    Sj_p = set()
    Sj_u = set(csp.curr_domains[Xj])
    for vi_u in csp.curr_domains[Xi]:
        conflict = True
        # now, in order to establish support for a value vi_u in Di it seems better to try to find a support among
        # the values in Sj_u first, because for each vj_u in Sj_u the check (vi_u, vj_u) is a double-support check
        # and it is just as likely that any vj_u in Sj_u supports vi_u than it is that any vj_p in Sj_p does...
        for vj_u in Sj_u - Sj_p:
            # double-support check
            if csp.constraints(Xi, vi_u, Xj, vj_u):
                conflict = False
                Si_p.add(vi_u)
                Sj_p.add(vj_u)
            checks += 1
            if not conflict:
                break
        # ... and only if no support can be found among the elements in Sj_u, should the elements vj_p in Sj_p be used
        # for single-support checks (vi_u, vj_p)
        if conflict:
            for vj_p in Sj_p:
                # single-support check
                if csp.constraints(Xi, vi_u, Xj, vj_p):
                    conflict = False
                    Si_p.add(vi_u)
                checks += 1
                if not conflict:
                    break
    return Si_p, Sj_p, Sj_u - Sj_p, checks


# Constraint Propagation with AC4

def AC4(csp, queue=None, removals=None, arc_heuristic=dom_j_up):
    if queue is None:
        queue = {(Xi, Xk) for Xi in csp.variables for Xk in csp.neighbors[Xi]}
    csp.support_pruning()
    queue = arc_heuristic(csp, queue)
    support_counter = Counter()
    variable_value_pairs_supported = defaultdict(set)
    unsupported_variable_value_pairs = []
    checks = 0
    # construction and initialization of support sets
    while queue:
        (Xi, Xj) = queue.pop()
        revised = False
        for x in csp.curr_domains[Xi][:]:
            for y in csp.curr_domains[Xj]:
                if csp.constraints(Xi, x, Xj, y):
                    support_counter[(Xi, x, Xj)] += 1
                    variable_value_pairs_supported[(Xj, y)].add((Xi, x))
                checks += 1
            if support_counter[(Xi, x, Xj)] == 0:
                csp.prune(Xi, x, removals)
                revised = True
                unsupported_variable_value_pairs.append((Xi, x))
        if revised:
            if not csp.curr_domains[Xi]:
                return False, checks  # CSP is inconsistent
    # propagation of removed values
    while unsupported_variable_value_pairs:
        Xj, y = unsupported_variable_value_pairs.pop()
        for Xi, x in variable_value_pairs_supported[(Xj, y)]:
            revised = False
            if x in csp.curr_domains[Xi][:]:
                support_counter[(Xi, x, Xj)] -= 1
                if support_counter[(Xi, x, Xj)] == 0:
                    csp.prune(Xi, x, removals)
                    revised = True
                    unsupported_variable_value_pairs.append((Xi, x))
            if revised:
                if not csp.curr_domains[Xi]:
                    return False, checks  # CSP is inconsistent
    return True, checks  # CSP is satisfiable


# ______________________________________________________________________________
# CSP Backtracking Search

# Variable ordering


def first_unassigned_variable(assignment, csp):
    """The default variable order."""
    return first([var for var in csp.variables if var not in assignment])


def mrv(assignment, csp):
    """Minimum-remaining-values heuristic."""
    return argmin_random_tie([v for v in csp.variables if v not in assignment],
                             key=lambda var: num_legal_values(csp, var, assignment))


def num_legal_values(csp, var, assignment):
    if csp.curr_domains:
        return len(csp.curr_domains[var])
    else:
        return count(csp.nconflicts(var, val, assignment) == 0 for val in csp.domains[var])

#------------------------dom/wdeg heuristic----------------------------------

#ipologizoume to athroisma ton weights ton periorismon pou simmetexei i metavliti var
def compute_sum(csp, var, assignment):
    sum=0
    for B in csp.neighbors[var]:
        if B not in assignment:
            sum += csp.weights[(var, B)]
    return sum

#simfona me to paper kathe variable exei ena weighted degree to 
#opoio isoutai me to athroisma olon ton 
#periorismon ston opoio simmetexei / to sinoliko tou weight
#epilegetai to variable me to mikrotero weighted degree
#allios xrisimopoioume tin first_unassigned_variable

def dom_wdeg(assignment, csp):
    dom_wdeg={}
    min = float("inf")
    choosen_var = None
    for var in csp.variables:
        if var in assignment:
            continue
        dom_wdeg[var]= compute_sum(csp, var, assignment)
        if dom_wdeg[var]==0:
            continue
        if(csp.curr_domains != None):
            available_values = len(csp.curr_domains[var])
        else:
            available_values = 1
        if (available_values/dom_wdeg[var])<min:
            min = (available_values/dom_wdeg[var])
            choosen_var = var
    if choosen_var!=None:
        return choosen_var
    else:
        return first_unassigned_variable(assignment, csp)


# Value ordering


def unordered_domain_values(var, assignment, csp):
    """The default value order."""
    return csp.choices(var)


def lcv(var, assignment, csp):
    """Least-constraining-values heuristic."""
    return sorted(csp.choices(var), key=lambda val: csp.nconflicts(var, val, assignment))


# Inference


def no_inference(csp, var, value, assignment, removals):
    return True


def forward_checking(csp, var, value, assignment, removals):
    """Prune neighbor values inconsistent with var=value."""
    csp.support_pruning()
    for B in csp.neighbors[var]:
        if B not in assignment:
            for b in csp.curr_domains[B][:]:
                if not csp.constraints(var, value, B, b):
                    csp.prune(B, b, removals)
            #tis epomenes 3 grammes tis prosthesa ego
            if not csp.curr_domains[B]:
                #print("domain wipeout");
                csp.weights[(B, var)]+=1
                csp.weights[(var, B)]+=1
                return False
    return True



#allaksa to orisma oste na kalei o mac ton AC3 kai oxi ton AC3b
def mac(csp, var, value, assignment, removals, constraint_propagation=AC3):
    """Maintain arc consistency."""
    return constraint_propagation(csp, {(X, var) for X in csp.neighbors[var]}, removals)


# The search, proper


def backtracking_search(csp, select_unassigned_variable=first_unassigned_variable,
                        order_domain_values=unordered_domain_values, inference=no_inference):
    """[Figure 6.5]"""

    def backtrack(assignment):
        if len(assignment) == len(csp.variables):
            return assignment
        var = select_unassigned_variable(assignment, csp)
        for value in order_domain_values(var, assignment, csp):
            if 0 == csp.nconflicts(var, value, assignment):
                csp.assign(var, value, assignment)
                removals = csp.suppose(var, value)
                if inference(csp, var, value, assignment, removals):
                    result = backtrack(assignment)
                    if result is not None:
                        return result
                csp.restore(removals)
        csp.unassign(var, assignment)
        return None
    result = backtrack({})
    assert result is None or csp.goal_test(result)
    return result


# ______________________________________________________________________________
# Min-conflicts Hill Climbing search for CSPs


def min_conflicts(csp, max_steps=100000):
    """Solve a CSP by stochastic Hill Climbing on the number of conflicts."""
    # Generate a complete assignment for all variables (probably with conflicts)
    csp.current = current = {}
    for var in csp.variables:
        val = min_conflicts_value(csp, var, current)
        csp.assign(var, val, current)
    # Now repeatedly choose a random conflicted variable and change it
    for i in range(max_steps):
        conflicted = csp.conflicted_vars(current)
        if not conflicted:
            return current
        var = random.choice(conflicted)
        val = min_conflicts_value(csp, var, current)
        csp.assign(var, val, current)
        if(i == max_steps-1):#prosthesa auti tin grammi gia na fainetai posa constraints paraviazontai otan den vriskei lisi o min-con
            print("Constraints violated: ", end="")
            print(len(conflicted))
    return None


def min_conflicts_value(csp, var, current):
    """Return the value that will give var the least number of conflicts.
    If there is a tie, choose at random."""
    return argmin_random_tie(csp.domains[var], key=lambda val: csp.nconflicts(var, val, current))

# ______________________________________________________________________________

#-----------------------------exam timetable csp-------------------------------------------------

#auti i klasi apla deixnei me tin seira tin opoia einai apothikeumena 
#ta stoixeia kathe mathimatos sto string pou apotelei to variable tou csp
#den exei kapoia ousiastiki xrisimotita afou den kaleitai pouthena
class Course:
    def __init__(self, semester, name, teacher, difficulty, lab):
        self.semester = semester
        self.name = name
        self.teacher = teacher
        self.difficulty = difficulty
        self.lab = lab


"to domain einai ena dictionary apo tuple opou to tuple einai tis morfis(i,j) opou 'i' i mera eksetasis kai 'j' i ora pou ksekinaei i eksetasi"
startingtime = [9, 12, 3]

class examtimetable(CSP):
    def __init__(self, totaldays, variables):
        self.variables = variables
        self.domains = dict()
        self.neighbors = dict()
        self.weights = dict()
        self.constraintsch = 0
        self.totaldays = 21;

        "dimiourgia dictionary gia domain"
        for var in self.variables:
            tmp = var.split(",")
            domain = []
            for i in list(range(1, totaldays+1)):
                for j in startingtime:
                    #elegxo oste an ena mathima exei lab na min mporei na mpei sto slot ton 3
                    if((str(tmp[4]))=='TRUE' and (j==3)):
                        continue
                    #elegxo an ena variable anaparista lab na min mporei na mpei sto slot ton 9
                    if((str(tmp[4]))=='yes' and (j==9)):
                        continue
                    domain.append((i,j))
            self.domains[var] = domain
        "dimiourgia dictionary gia neighbors"
        for var in self.variables:
            neighbors = []
            for var2 in self.variables:
                if var!=var2:
                    neighbors.append(var2)
                    self.weights[var, var2]=1#oloi oi periorismoi exoun arxiko weight iso me 1
            self.neighbors[var] = neighbors
        CSP.__init__(self, self.variables, self.domains, self.neighbors, self.exam_constraint)
    

    def exam_constraint(self, A, a, B, b):
        self.constraintsch += 1

        #periorismos ena mathima se kathe slot
        if ((a[0]==b[0]) and (a[1]==b[1])):
            return False 

        var1 = A.split(",")
        var2 = B.split(",")

        #periorismos mathimata idiou etous na einai se diaforetikes meres, eksaireitai to zevgari lab-theoreia
        if ((int(var1[0]) == int(var2[0])) and (a[0]==b[0]) and (var1[1]!=var2[1])):
            return False

        #periorismos eksetasi lab kai mathimatos na einai tin idia mera
        if((var1[4]=='TRUE' or var2[4]=='TRUE') and var1[1]==var2[1] and a[0]!=b[0]):
            return False

        #periorismos i eksetasi tou lab na einai amesos meta tin theoreia
        if(var1[4]=='TRUE' and var1[1]==var2[1] and a[0]==b[0] and a[1]+3!=b[1]):
            return False

        if(var2[4]=='TRUE' and var1[1]==var2[1] and a[0]==b[0] and b[1]+3!=a[1]):
            return False

        #"periorismos mathimata megalis diskolias na apexoun toulaxiston ena etos"
        if((var1[3]== var2[3]) and (abs(int(a[0])-int(b[0]))<2) and (var1[3]==str('TRUE')) and (var1[1]!=var2[1])):
            return False

        #periorismos mathimata idiou kathigiti se diaforetikes meres"
        #"an exoun idio onoma simainei oti einai mathima kai ergastirio ara den theloume na isxisei gia auto to zevgari o periorismos"
        if ((var1[2]== var2[2]) and (a[0]==b[0]) and (var1[1]!=var2[1])):
            return False

        
        return True
        
    "allaksa tin display gia na einai pio eukolo na diavastoun ta assignments tou algorithmou"
    def display(self, assignment):
        for i in range(1, self.totaldays+1):
            for j in startingtime:
                for var in self.variables:
                    if(i==assignment[var][0] and j == assignment[var][1]):
                        print('DAY ' + str(i) + ' TIME ' + str(j) + ': ' + var)
            print("\n")

    

