import state
from functools import partial
import re

class Solver:
  def __init__(self):
    # (str, func(puzzle))
    self._deducers = []
    self._disabled_deducers = []
  def _disable_after(self, deducer_name):
    for disabled in self._disabled_deducers:
      if re.match(disabled, deducer_name):
        return True
    return False
  def make_deduction(self, puzzle):
    for deducer_name, deducer in self._deducers:
      if self._disable_after(deducer_name):
        break
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

class Deduction:
  def __init__(self, name, cells_affected):
    self.name = name
    self.cells_affected = cells_affected
  def __str__(self):
    return '{}. Affected {}'.format(self.name, self.cells_affected)

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
        puzzle_state = puzzle.save()   
        deduction = True
        while deduction and not puzzle.broken() and puzzle.constraints_satisfied():
          deduction = base_solver.make_deduction(puzzle) 
          if not deduction:
            deduction = recursive_deduce(puzzle, depth+1, max_depth)
        ruled_out = puzzle.broken() or not puzzle.constraints_satisfied()
        puzzle.load(puzzle_state)
        if ruled_out:
          puzzle.cell_options[cid] = [o for o in opts if o != opt]
          return Deduction('{} ruled out'.format(opt), [cid])
      puzzle.cell_options[cid] = opts
    return None
  name = 'Bifurcation ({})'.format(max_depth)
  def deducer(puzzle):
    base_solver.disabled_deducers.append(r'Bifurcation.*')
    lvl = 1
    deduction = recursive_deduce(puzzle, 1, max_depth=lvl)
    while not deduction and lvl < max_depth:
      lvl += 1
      print('Raising bifurcation level to {}.'.format(lvl)) 
      deduction = recursive_deduce(puzzle, 1, max_depth=lvl)
    base_solver.disabled_deducers.pop(-1)
    return deduction
  return name, deducer

def get_constraint_violation_deducer():
  def deducer(puzzle):
    for constraint_name, constraint in puzzle.constraints.items():
      for cid in puzzle.cell_options.keys():
        opts = puzzle.cell_options[cid]
        if len(opts) <= 1:
          continue
        cell_violations = set()
        for opt in opts:
          puzzle.cell_options[cid] = [opt]
          if not constraint(puzzle) or constraint.broken(puzzle):
            cell_violations.add(opt)
        if len(cell_violations) == len(opts)-1:
          solution = list((set(opts)-cell_violations))[0]
          puzzle.cell_options[cid] = [solution]
          return Deduction('Naked single, {}'.format(solution), [cid])
        elif cell_violations:
          puzzle.cell_options[cid] = [o for o in opts if o not in cell_violations]
          return Deduction('{} ruled out'.format(sorted(list(cell_violations))), [cid])
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
          return Deduction('Only one cell for {} in {}'.format(opt, constraint_name), [cid])
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
          name = '{} tuple in {}'.format(sorted(list(tup_opts)), constraint_name)
          puzzle.constraints[name] = state.OneEachConstraint(tup, tup_opts)
          # remove options in this tuple from the other unlocked cells in this constraint
          affected = set()
          tup_set = set(tup)
          for cid, options in unlocked_cells:
            if cid in tup_set:
              continue
            filtered_options = []
            for opt in options:
              if opt in tup_opts:
                affected.add(cid)
              else:
                filtered_options.append(opt)
            puzzle.cell_options[cid] = filtered_options
          return Deduction('Found {}'.format(name), list(affected))
  return 'Tuples', deducer

def get_pointy_fish_deducer(min_size, max_size):
  # TODO: figure out how to incorperate non-unique constraints that constraint an option (n times) to a region that overlaps uniqueness constraints.
  def intersects(constraint_a, constraint_b):
    sa = set(constraint_a[1].cells)
    return any(cb in sa for cb in constraint_b[1].cells)
  def pointy_fish_set_iter(uniqueness_constraints, min_length, max_length, base_a = None, base_b = None):
    """
    Returns all combinations of sets of constraints, (a,b) such that each element of 'a'
    does not intersect with any other element of 'a', each element of 'b' does not intersect
    with any other element of 'b', each element of 'a' intersects all elements of 'b', and
    each element of 'b' intersects all elements of 'a'.
    'uniqueness_constraints' is a list of tuples of the form (constraint_name, constraint)
    'min_length' is the minimum length of 'a' and 'b' which are returned
    'max_length' is the maximum length of 'a' and 'b' which are returned
    'a' and 'b' are lists of integer indexes
    'base_a' and 'base_b' are used internally for recursion
    """
    a = [] if base_a is None else base_a
    b = [] if base_b is None else base_b
    if len(a) >= min_length and len(b) >= min_length:
      yield a,b
    if len(a) == max_length and len(b) == max_length:
      return
    # add all distinct constraint to 'a' that intersects all of 'b' and iterate on the resulting possibilities
    # avoid double counting combinations of a [1,3] and [3,1] for example
    min_new_a = 0 if not a else a[-1]+1 
    for i in range(min_new_a, len(uniqueness_constraints)):
      if i in b:
        continue
      if any(intersects(uniqueness_constraints[i], uniqueness_constraints[ai]) for ai in a):
        continue
      if any(not intersects(uniqueness_constraints[i], uniqueness_constraints[bi]) for bi in b):
        continue
      new_a = a+[i]
      min_new_b = new_a[0]+1 if not b else b[-1]+1
      for j in range(min_new_b, len(uniqueness_constraints)):
        if any(not intersects(uniqueness_constraints[j], uniqueness_constraints[ai]) for ai in new_a):
          continue
        if any(intersects(uniqueness_constraints[j], uniqueness_constraints[bi]) for bi in b):
          continue
        new_b = b+[j]
        for result in pointy_fish_set_iter(uniqueness_constraints, min_length, max_length, base_a = new_a, base_b = new_b):
          yield result
      
  def deducer(puzzle):
    DEBUG = False
    uniqueness_constraints = [(name, con) for name, con in puzzle.constraints.items() if con.implies_uniqueness()]
    for a, b in pointy_fish_set_iter(uniqueness_constraints, min_size, max_size):
      a_names = [uniqueness_constraints[i][0] for i in a]
      b_names = [uniqueness_constraints[i][0] for i in b]
      # find all free cells
      a_cells, b_cells = [], []
      for i in a:
        a_cells.extend(cid for cid in uniqueness_constraints[i][1].cells if len(puzzle.cell_options[cid])>1)
      for i in b:
        b_cells.extend(cid for cid in uniqueness_constraints[i][1].cells if len(puzzle.cell_options[cid])>1)
      a_cells, b_cells = set(a_cells), set(b_cells)
      if not a_cells or not b_cells:
        continue
      # find their intersection and differences
      ab_opts, ao_opts, bo_opts = set(), set(), set()
      for cid in (a_cells | b_cells):
        opts = puzzle.cell_options[cid]
        in_a = cid in a_cells
        in_b = cid in b_cells
        if in_a and in_b:
          ab_opts.update(opts)
        elif in_a:
          ao_opts.update(opts)
        else: #in_b
          bo_opts.update(opts)
      if DEBUG:
        print('a: {}'.format(a_names))
        print('ab_opts: {}'.format(ab_opts)) 
        print('ao_opts: {}'.format(ao_opts)) 
        print('bo_opts: {}'.format(bo_opts)) 
      # options present in the intersection of a and b but not in a-only
      # cells are ruled out of b-only cells if they are present in each
      # distinct intersection of (a_i, b) constraints.
      constrained_a_opts = ab_opts-ao_opts
      if constrained_a_opts:
        # check for presence in each distinct intersection
        for i in a:
          int_opts = set()
          for j in b:
            intersection = set(uniqueness_constraints[i][1].cells) & set(uniqueness_constraints[j][1].cells)
            for cid in intersection:
              int_opts.update(puzzle.cell_options[cid])
          constrained_a_opts &= int_opts
          if not constrained_a_opts:
            break
      ruled_out_b_opts = bo_opts & constrained_a_opts
      if constrained_a_opts and ruled_out_b_opts:
        found = []
        for cid in (b_cells-a_cells):
          init_len = len(puzzle.cell_options[cid])
          puzzle.cell_options[cid] = [opt for opt in puzzle.cell_options[cid] if opt not in constrained_a_opts]
          final_len = len(puzzle.cell_options[cid])
          if final_len != init_len:
            found.append(cid)
        ret = Deduction("(a) Ruled out {} from cells in {} but not {}".format(ruled_out_b_opts, b_names, a_names), found)
        if DEBUG:
          print('a: {}'.format(a_names))
          print('ab_opts: {}'.format(ab_opts)) 
          print('ao_opts: {}'.format(ao_opts)) 
          print('bo_opts: {}'.format(bo_opts)) 
          print(constrained_a_opts)
          print(ruled_out_b_opts)
          print('a intersect b options: {}'.format(ab_opts))
          print('a only options: {}'.format(ao_opts))
          print('b only options: {}'.format(bo_opts))
          for cid in sorted(list(a_cells)):
            print("{}: {}".format(cid, puzzle.cell_options[cid]))
        return ret

      # ... and vice versa
      constrained_b_opts = ab_opts-bo_opts
      if constrained_b_opts:
        # check for presence in each distinct intersection
        for j in b:
          int_opts = set()
          for i in a:
            intersection = set(uniqueness_constraints[i][1].cells) & set(uniqueness_constraints[j][1].cells)
            for cid in intersection:
              int_opts.update(puzzle.cell_options[cid])
          constrained_b_opts &= int_opts
          if not constrained_b_opts:
            break
      ruled_out_a_opts = ao_opts & constrained_b_opts
      if constrained_b_opts and ruled_out_a_opts:
        found = []
        for cid in (a_cells-b_cells):
          init_len = len(puzzle.cell_options[cid])
          puzzle.cell_options[cid] = [opt for opt in puzzle.cell_options[cid] if opt not in constrained_b_opts]
          final_len = len(puzzle.cell_options[cid])
          if final_len != init_len:
            found.append(cid)
        ret = Deduction("(b) Ruled out {} from cells in {} but not {}".format(ruled_out_a_opts, a_names, b_names), found)
        if DEBUG:
          print('a: {}'.format(a_names))
          print('ab_opts: {}'.format(ab_opts)) 
          print('ao_opts: {}'.format(ao_opts)) 
          print('bo_opts: {}'.format(bo_opts)) 
          print(constrained_b_opts)
          print(ruled_out_a_opts)
          print('a intersect b options: {}'.format(ab_opts))
          print('a only options: {}'.format(ao_opts))
          print('b only options: {}'.format(bo_opts))
          for cid in sorted(list(b_cells)):
            print("{}: {}".format(cid, puzzle.cell_options[cid]))
        return ret
  return "Pointy-Fish", deducer

def get_odd_wing_deducer(base_solver, max_depth=5, max_split=2):
  def deduce(puzzle, solver, max_depth):
    for cur_cid in puzzle.cell_options.keys():
      opts = puzzle.cell_options[cur_cid]
      if len(opts) > max_split:
        continue
      # cid in here if cid affected in every opt choice
      joint_cells_affected = None
      # values are sets of the union of options at the end of deduction chains
      joint_cell_options = None
      for opt in opts:
        puzzle_state = puzzle.save()   
        puzzle.cell_options[cur_cid] = [opt]
        cells_affected = set()
        steps = 0
        deduction = True
        while steps < max_depth and deduction and puzzle.constraints_satisfied() and not puzzle.broken():
          deduction = solver.make_deduction(puzzle)
          if deduction:
            cells_affected.update(deduction[1].cells_affected)
          steps+=1
        cell_options = {}
        for cid in cells_affected:
          cell_options[cid] = set(puzzle.cell_options[cid])
        puzzle.load(puzzle_state)
        if not puzzle.constraints_satisfied() or puzzle.broken():
          puzzle.cell_options[cur_cid] = [o for o in opts if o != opt]
          return Deduction('Chain of length {} ruled out {}'.format(steps, opt), [cur_cid])
        if joint_cells_affected is not None:
          for cid in (joint_cells_affected-cells_affected):
            del joint_cell_options[cid]
          joint_cells_affected = joint_cells_affected & cells_affected
          for cid in joint_cells_affected:
            joint_cell_options[cid] = joint_cell_options[cid] | cell_options[cid]
        else:
          joint_cells_affected = cells_affected
          joint_cell_options = cell_options
        if not joint_cells_affected:
          break
      if joint_cells_affected:
        real_affected = []
        ruled_out = []
        for cid in joint_cells_affected:
          if len(joint_cell_options[cid]) < len(puzzle.cell_options[cid]):
            real_affected.append(cid)
            old = set(puzzle.cell_options[cid])
            puzzle.cell_options[cid] = sorted(list(joint_cell_options[cid]))
            ruled_out.append(old-joint_cell_options[cid])
        if real_affected:
          return Deduction('For every option ({}) in {}, ruled out {} from cells respectively.'.format(puzzle.cell_options[cur_cid], cur_cid, ruled_out), real_affected)
  name = 'Odd Wing ({}, {})'.format(max_depth, max_split)
  def deducer(puzzle):
    base_solver.disabled_deducers.append(r'Bifurcation.*')
    base_solver.disabled_deducers.append(r'Odd Wing.*')
    deduction = None
    # TODO: it would be more efficient to deduce at max depth and backtrack to minimum depth needed for the deduced cell.
    depth = 0 
    while depth < max_depth and deduction is None:
      depth += 1
      deduction = deduce(puzzle, base_solver, depth)
    base_solver.disabled_deducers.pop(-1)
    base_solver.disabled_deducers.pop(-1)
    return deduction
  return name, deducer

class SudokuSolver(Solver):
  def __init__(self, bifurcation_level=0):
    super().__init__()
    self.deducers.append(get_only_opt_deducer())
    self.deducers.append(get_constraint_violation_deducer())
    self.deducers.append(get_tuple_deducer())
    # pointing pairs and x-wings
    for i in range(1,3):
      self.deducers.append(get_pointy_fish_deducer(i, i))
    # Y-wing, skyscraper, winged x-wings, etc.
    self.deducers.append(get_odd_wing_deducer(self))
    # swordfish and jellyfish
    for i in range(3,5):
      self.deducers.append(get_pointy_fish_deducer(i, i))
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
  # Requires jellyfish:
  super_hard_data = [
    [0,2,0,0,0,0,0,3,0],
    [4,0,0,0,0,0,0,0,7],
    [0,0,1,2,3,0,4,0,0],
    [0,0,4,1,5,0,3,0,0],
    [0,0,5,6,4,0,1,0,0],
    [0,0,0,0,0,0,0,0,0],
    [0,0,2,5,1,0,6,0,0],
    [5,0,0,0,0,0,0,9,0],
    [0,8,0,0,0,0,0,0,5],
  ]
  puzzle.load_from_list(super_hard_data)
  #for cid, opts in xwing_cell_options.items():
  #  puzzle.cell_options[cid] = opts
  print(puzzle)
  
  deduction = True
  solver = SudokuSolver(bifurcation_level=0)
  i = 0
  slow = False
  enable_slow = True
  while puzzle.free_cells() > 0 and deduction:
    deduction = solver.make_deduction(puzzle)
    if deduction:
      if re.match('Odd Wing.*', deduction[0]):
        slow = True
      print('{}, {}: {}'.format(i, deduction[0], deduction[1]))
      print(puzzle)
      if slow and enable_slow:
        print('[press enter]', end='')
        input()
    i += 1
  assert not puzzle.broken()
  assert puzzle.constraints_satisfied()
  assert puzzle.free_cells() == 0
  print("Solved.")
