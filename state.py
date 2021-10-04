from functools import partial
import pickle

class PuzzleState:
  def __init__(self):
    self._cell_options = {}
    self._constraints = {}
    self._deductions = {}
  @ property
  def cell_options(self):
    return self._cell_options
  @ property
  def constraints(self):
    return self._constraints
  @ property
  def deductions(self):
    return self._deductions
  def broken(self):
    return not all(self._cell_options.values())
  def constraints_satisfied(self):
    return all(c(self) for c in self._constraints.values())
  def free_cells(self):
    return sum(1 for opts in self._cell_options.values() if len(opts) > 1)
  def save(self):
    return pickle.dumps((self._cell_options, self._constraints, self._deductions))
  def load(self, data):
    self._cell_options, self._constraints, self._deductions = pickle.loads(data)

class Constraint:
  def __init__(self, cells, options):
    self._cells = list(cells)
  @ property
  def cells(self):
    return self._cells
  def __call__(self, puzzle):
    raise NotImplementedError('__call__ not implemented for {}'.format(type(self)))
  def implies_uniqueness(self):
    return False
  def broken(self, puzzle):
    # Returns true if the constraint is impossible to satisfy with the
    # current cell options, even if it's not currently violated.
    if self.implies_uniqueness():
      opt_set = set()
      for cid in self.cells:
        opt_set.update(puzzle.cell_options[cid])
      return len(opt_set) != len(self.cells)
    return False

class OneEachConstraint(Constraint):
  def __init__(self, cells, options):
    self._cells = list(cells)
    self._options = list(options)
  def __call__(self, puzzle):
    options = (puzzle._cell_options[cid] for cid in self.cells)
    locked_cells = [opts[0] for opts in options if len(opts) == 1]
    return len(locked_cells) == len(set(locked_cells))
  @ property
  def options(self):
    return self._options
  def implies_uniqueness(self):
    return True

class Sudoku(PuzzleState):
  def __init__(self):
    super().__init__()
    # Set up the cell states
    for r in range(1,10):
      for c in range(1,10):
        self._cell_options[(r,c)] = list(range(1,10))
    opt_it = partial(range, 1, 10)
    # Set up the row constraints
    def row_it(r):
      for c in range(1,10):
        yield (r,c)
    for r in range(1,10):
      self._constraints['Row {}'.format(r)] = OneEachConstraint(row_it(r), opt_it())
    # Set up column constraints
    def col_it(c):
      for r in range(1,10):
        yield (r,c)
    for c in range(1,10):
      self._constraints['Col {}'.format(c)] = OneEachConstraint(col_it(c), opt_it())
    # Set up box constraints
    def box_it(r_off, c_off):
      for i in range(9):
        r = r_off+int(i/3)+1
        c = c_off+i%3+1
        yield (r, c)
    for box_num in range(1,10):
      r_off = 3*int((box_num-1)/3)
      c_off = 3*((box_num-1)%3)
      self._constraints['Box {}'.format(box_num)] = OneEachConstraint(box_it(r_off, c_off), opt_it())
  def __str__(self):
    def char_iter():
      for r in range(1,10):
        if r != 1:
          yield '\n'
        if r == 4 or r == 7:
          yield '------+------+------\n'
        for c in range(1,10):
          if c != 1:
            yield ' '
          if c == 4 or c == 7:
            yield '|'
          opts = self._cell_options[(r,c)]
          if len(opts) == 1:
            yield str(opts[0])
          else:
            yield '.'
    return ''.join(char_iter())
  def load_from_list(self, data):
    for r in range(1,10):
      for c in range(1,10):
        v = data[r-1][c-1]
        if v != 0:
          self._cell_options[(r,c)] = [v]

if __name__=='__main__':
  puzzle = Sudoku()
  print(puzzle.broken())
  print(puzzle.constraints_satisfied())
  print(puzzle.free_cells())
  puzzle.cell_options[(1,1)] = [2]
  puzzle.cell_options[(1,4)] = [2]
  print(puzzle.broken())
  print(puzzle.constraints_satisfied())
  print(puzzle.free_cells())
  puzzle.cell_options[(1,4)] = [3]
  print(puzzle.broken())
  print(puzzle.constraints_satisfied())
  print(puzzle.free_cells())
  puzzle.cell_options[(2,2)] = [2]
  print(puzzle.broken())
  print(puzzle.constraints_satisfied())
  print(puzzle.free_cells())
  print(puzzle)
