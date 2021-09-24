import state
from functools import partial

DEBUG = False

class Solver:
  def __init__(self):
    # (str, func(puzzle))
    self._deducers = []
    self._disabled_deducers = set()
  def make_deduction(self, puzzle):
    for deducer_name, deducer in self._deducers:
      if deducer_name in self._disabled_deducers:
        continue
      deduction = deducer(puzzle)
      if deduction:
        return deducer_name, deduction
    return None
  @property
  def deducers(self):
    return self._deducers
  @property
  def disabled_deducers(self):
    return self._disabled_deducers

def get_bifurcation_deducer(base_solver, max_depth):
  def recursive_deduce(puzzle, depth, max_depth):
    if depth > max_depth:
      return None
    opt_counts = [(cid, len(opts)) for cid, opts in puzzle.cell_options.items() if len(opts)>1]
    opt_counts.sort(key = lambda x: x[1])
    for cid, _ in opt_counts:
      opts = puzzle.cell_options[cid]
      for opt in opts:
        puzzle.cell_options[cid] = [opt]
        state = puzzle.save()   
        deduction = True
        while deduction and not puzzle.broken() and puzzle.constraints_satisfied():
          deduction = base_solver.make_deduction(puzzle) 
          if not deduction:
            deduction = recursive_deduce(puzzle, depth+1, max_depth)
        ruled_out = puzzle.broken() or not puzzle.constraints_satisfied()
        puzzle.load(state)
        if ruled_out:
          puzzle.cell_options[cid] = [o for o in opts if o != opt]
          return '{} ruled out from {}'.format(opt, cid)
      puzzle.cell_options[cid] = opts
    return None
  name = 'Bifurcation ({})'.format(max_depth)
  def deducer(puzzle):
    base_solver.disabled_deducers.add(name)
    lvl = 1
    deduction = recursive_deduce(puzzle, 1, max_depth=lvl)
    while not deduction and lvl < max_depth:
      lvl += 1
      print('Raising bifurcation level to {}.'.format(lvl)) 
      deduction = recursive_deduce(puzzle, 1, max_depth=lvl)
    base_solver.disabled_deducers.remove(name)
    return deduction
  return name, deducer

def get_constraint_violation_deducer():
  def deducer(puzzle):
    for constraint_name, constraint in puzzle.constraints.items():
      for cid in puzzle.cell_options.keys():
        opts = puzzle.cell_options[cid]
        for opt in opts:
          puzzle.cell_options[cid] = [opt]
          if not constraint(puzzle):
            puzzle.cell_options[cid] = [o for o in opts if o != opt]
            return '{} ruled out from {} via {}'.format(opt, cid, constraint_name)
        puzzle.cell_options[cid] = opts
    return None
  return 'Constraint Violation', deducer

def get_only_opt_deducer():
  def deducer(puzzle):
    oec_constraints = 0
    for constraint_name, constraint in puzzle.constraints.items():
      if type(constraint) != state.OneEachConstraint:
        continue
      oec_constraints += 1
      opt_counts = {}
      for opt in constraint.options:
        opt_counts[opt] = 0
      fixed = set()
      last_seen = {}
      for cid in constraint.cells:
        opts = puzzle.cell_options[cid]
        if len(opts) == 1:
          fixed.add(opts[0])
        for opt in opts:
          opt_counts[opt] += 1
          last_seen[opt] = cid
      for opt, cnt in opt_counts.items():
        if cnt == 1 and opt not in fixed:
          cid = last_seen[opt]
          puzzle.cell_options[cid] = [opt]
          return '{} only option for {} in {}'.format(cid, opt, constraint_name)
    return None
  return "Only Option", deducer

def combinations(choices, options, minimum=0):
  """
  Returns all ordered of length 'choices' that can be made from range(options)
  for which all elements are greater than or equal to 'minimum'.
  """
  for first_choice in range(minimum, options):
    if choices == 1:
      yield [first_choice]
    else:
      for sub_combination in combinations(choices-1, options, minimum=first_choice+1):
        yield [first_choice]+sub_combination

def get_tuple_deducer():
  def deducer(puzzle):
    # TODO: clean up previous tuple deduction data that has become irrelevant
    for constraint_name, constraint in list(puzzle.constraints.items()):
      if type(constraint) != state.OneEachConstraint:
        continue
      # find unlocked cells
      cell_options = ((cid, puzzle.cell_options[cid]) for cid in constraint.cells)
      unlocked_cells = filter(lambda x: len(x[1])>1, cell_options)
      # remove known tuples from unlocked cells
      if 'tuple_cell_sets' not in puzzle.deductions:
        puzzle.deductions['tuple_cell_sets'] = dict()
      tuple_cell_sets = puzzle.deductions['tuple_cell_sets'].get(constraint_name, set())
      if tuple_cell_sets:
        unlocked_cells = filter(lambda x: x[0] not in tuple_cell_sets, unlocked_cells)
      unlocked_cells = list(unlocked_cells)
      # find tuples
      # example:
      # [123, 12, 567, 13, 235, 67] -> 0, 1, and 3 are a tuple, rulling out 2 and 3 from 4
      for tuple_length in range(2, len(unlocked_cells)-1):
        for combination in combinations(tuple_length, len(unlocked_cells)):
          tup = [unlocked_cells[i][0] for i in combination]
          tup_opts = set()
          for cell in tup:
            for opt in puzzle.cell_options[cell]:
              tup_opts.add(opt)
          if len(tup) != len(tup_opts):
            continue
          # tuple found
          # remember to skip cells in this tuple on next pass
          puzzle.deductions['tuple_cell_sets'][constraint_name] = tuple_cell_sets.union(tup)
          # add deduced OneEachConstraint to puzzle
          name = '{} Tuple in {}'.format(sorted(list(tup_opts)), constraint_name)
          puzzle.constraints[name] = state.OneEachConstraint(tup, tup_opts)
          # remove options in this tuple from the other unlocked cells in this constraint
          removed = []
          tup_set = set(tup)
          for cid, options in unlocked_cells:
            if cid in tup_set:
              continue
            filtered_options = []
            for opt in options:
              if opt in tup_opts:
                removed.append('{} ruled out of {}'.format(opt, cid))
              else:
                filtered_options.append(opt)
            puzzle.cell_options[cid] = filtered_options
          return ', '.join(['Found {}'.format(name)]+removed)
  return 'Tuples', deducer

class SudokuSolver(Solver):
  def __init__(self, bifurcation_level=1):
    super().__init__()
    self.deducers.append(get_only_opt_deducer())
    self.deducers.append(get_constraint_violation_deducer())
    self.deducers.append(get_tuple_deducer())
    # TODO; generalize 'Pointing Pairs' strategy
    # I think pointing-pairs, xwings, swordfish, and jellyfish are generally part of the same strategic class
    # TODO: generalize Y-wing strategy
    if bifurcation_level != 0:
      self.deducers.append(get_bifurcation_deducer(self, bifurcation_level))

if __name__ == '__main__':
  puzzle = state.Sudoku()
  easy_data = [
    [7,4,0,0,3,0,0,1,0],
    [0,1,9,0,6,8,5,0,2],
    [0,0,0,0,0,4,3,0,0],
    [0,5,6,3,7,0,0,0,1],
    [0,0,1,8,0,0,0,9,5],
    [0,9,0,0,2,0,6,0,0],
    [1,0,3,4,0,7,2,0,0],
    [5,0,0,2,0,0,0,0,8],
    [0,8,0,0,0,1,4,7,0],
  ]
  hard_data = [
    [0,0,0,8,0,0,4,2,0],
    [5,0,0,6,7,0,0,0,0],
    [0,0,0,0,0,9,0,0,5],
    [7,4,0,1,0,0,0,0,0],
    [0,0,9,0,3,0,7,0,0],
    [0,0,0,0,0,7,0,4,8],
    [8,0,0,4,0,0,0,0,0],
    [0,0,0,0,9,8,0,0,3],
    [0,9,5,0,0,3,0,0,0],
  ]
  # best: bifurcation level 1 at step 350
  puzzle.load_from_list(hard_data)
  print(puzzle)
  
  deduction = True
  solver = SudokuSolver(bifurcation_level=1)
  i = 0
  while puzzle.free_cells() > 0 and deduction:
    deduction = solver.make_deduction(puzzle)
    if deduction:
      print('{}, {}: {}'.format(i, deduction[0], deduction[1]))
      print(puzzle)
    i += 1
