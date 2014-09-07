"""Here is my solution to Problem 83 of Project Euler:
https://projecteuler.net/problem=83

This pathfinding algorithm may not be ideal. I haven't gotten to graph
algorithms in CLRS yet, so I devised an algorithm that runs in about half a second
using a data structure that I HAVE studied (min_heaps). The running time appears to
be dominated by min_heapify
(see command "python -m cProfile -s time solve.py matrix.txt").
"""
import time
import math

class ID_10_T_Error(Exception): pass
class AimlessWandererError(Exception): pass

class PriorityQueue:
    """Min-heap implementation of priority queue.

    In this implementation we will assume that the objects have magic
    comparators defined so that we can compare objects with the
    operators <, >, <=, or >=.
    """
    def __getitem__(self, key):
        """This is going to be used to create a layer of abstraction,
        so that we can pretend our indexes are between 1 and n instead of
        0 and n-1
        """
        return self.heap[key-1]

    def __setitem__(self, key, value):
        self.heap[key-1] = value
    
    def __init__(self):
        """Creates an empty min-heap."""
        self.heap = []

    def is_empty(self):
        return self.heap == []

    def __len__(self):
        """Returns the length of the heap"""
        return len(self.heap)

    def end_heap(self):
        """The last element of the heap is at index n - 1."""
        return len(self)

    def parent(self, i):
        """Returns the index of the parent of the node index given."""
        return (i // 2)

    def left(self, i):
        """Returns the index of the left child of the node index given."""
        return (2*i)

    def right(self, i):
        """Returns the index of the right child of the node index given."""
        return (2*i + 1)

    def min_heapify(self, i):
        """Min heapify assumes that rooted at the left and right children of
        the given nodes are two min heaps. In order to preserve the min heap
        property, min_heapify compares the value of the key of the given node
        with the key of the nodes below. If i is the highest value, then
        we have a min heap rooted at i, and we can stop. Otherwise, we switch
        i with the higher of the two children, and recursively call min heapify
        with the index of the child that was exchanged with node i. O(lgn)
        """
        lowest = i
        r = self.right(i)
        l = self.left(i)
        if (l <= self.end_heap()) and (self[i] > self[l]):
            lowest = l
        if (r <= self.end_heap()) and (self[lowest] > self[r]):
            lowest = r
        if lowest != i:
            temp = self[i]
            self[i] = self[lowest]
            self[lowest] = temp
            self.min_heapify(lowest)

    def min(self):
        """The max heap property assures us that the minimum element is
        located at the root of the heap. O(1) running time

        raises: ValueError if the heap is empty.
        """
        if len(self) <= 0:
            raise ValueError('Cannot call min on an empty heap')
        return self[1]

    def extract_min(self):
        """We can extract the min element in O(lgn) time by switching
        the first and last element in the self.heap, and then popping
        the last element and calling max-heapify(1).

        raises: ValueError if the heap is empty.
        """
        if len(self) <= 0:
            raise ValueError('Cannot call pop on an empty heap')
        min = self[1]
        self[1] = self[self.end_heap()]
        self.heap.pop()
        self.min_heapify(1)
        return min

    def insert(self, obj):
        """Insert an element into the queue by placing it at the end
        and increasing its position until it obeys the min-heap property.
pppp        """
        self.heap.append(obj)
        c = self.end_heap()
        p = self.parent(c)
        while (p >= 1) and (obj < self[p]):
            self[c] = self[p]
            c = p
            p = self.parent(p)
        self[c] = obj


class Matrix:
    """A matrix takes a newline seperated csv file and acts as a
    layer of abstraction between the board and other objects
    """

    def __init__(self, file_descriptor):
        """Creates a matrix from an opened file descriptor."""
        self.build_matrix(file_descriptor)

    def build_matrix(self, f):
        """The matrix will be represented as a 2-d array."""
        self.m = []
        r = 0
        line = f.readline().strip().split(',')
        row = self.to_nodes(line, r)
        self.width = len(row)
        self.m.append(row)
        r = 1
        for line in f:
            line = line.strip().split(',')
            row = self.to_nodes(line, r)
            if len(row) != self.width:
                raise ValueError("Inconsistent row widths in input matrix file.")
            else:
                self.m.append(row)
            r += 1
        self.height = r

    def to_nodes(self, line, row):
        """Given a row of string or integer values, will
        return a row of Node objects.
        """
        return [Node(line[i], (row, i)) for i in range(len(line))]

    def get(self, loc):
        """Returns a node at the specified coordinates in the matrix."""
        row, col = loc
        if ((0 <= row) and (row <= self.height-1)) and \
           ((0 <= col) and (col <= self.width-1)):
            return self.m[row][col]
        else:
            return None

    def up(self, loc):
        row, col = loc
        return self.get((row-1, col))

    def down(self, loc):
        row, col = loc
        return self.get((row+1, col))

    def left(self, loc):
        row, col = loc
        return self.get((row, col-1))

    def right(self, loc):
        row, col = loc
        return self.get((row, col+1))

class Node:
    """A node will be represented with three attributes:
    loc, value, and min_path. The Key advantage
    of creating a node class is that they will be hashable
    by id, and that each node can store the shortest path
    to its location so far. This allows us to dispose of
    a huge proportion of the routes, as most will not
    be the fastest path to a particular node.
    """

    def __init__(self, value, loc):
        """Converts input value to an integer and saves
        row and column as attributes"""
        self.min = None
        self.loc = loc
        try:
            self.value = int(value)
        except:
            raise Exception("Input values in matrix must be an int" \
                            " or a string.")
    
    def __repr__(self):
        return "Node(Value: {}, Loc: {})".format(self.value, self.loc)

class Path:
    """Paths are the most complex object used in this algorithm.
    They will have all comparators defined which will return
    the weight of the path so far travelled, with ties broken
    by euclidean distance from the finish location
    (please see docstrings in PathFinder and PathFinder.run).
    They will also contain a mapping that will track the nodes
    that have already been travelled by the path.
    """

    def __init__(self, node, matrix=None, finish=None, nodes={}, weight=0):
        """__init__ has several defaults, so that our first path will be
        set up conveneniently. We keep a copy of the matrix so that propogate
        can access the relevant nodes. Each path tracks the nodes it has
        already crossed with a dictionary, for O(1) lookups. When a new path
        is created through Path.propogate, the new path takes on the attributes
        from the previous path, but adds the new node to weight, and the new
        node to nodes. Notice that Path.arrived tracks whether the current node
        is the specified finish, in which case arrived is True, and Pathfinder.run
        will terminate if the path is the minimum path in the Priority Queue
        after insertion.
        """
        if matrix is None:
            raise ID_10_T_Error("Woaaaa buddy, how can a path be initialzed" \
                                " without a matrix?")
        if finish is None:
            raise AimlessWandererError("This might take a while without a" \
                                       " destination.")
        self.node = node
        self.matrix = matrix
        self.finish = finish
        self.nodes = {}
        self.nodes.update(nodes)
        ## Add current node to nodes crossed
        self.nodes[self.node] = True
        ## Find euclidean distance between current node and finish
        self.dist = self.euc_dist(self.node.loc, self.finish.loc)
        ## Add this node's weight to total path weight
        self.weight = weight + self.node.value
        self.arrived = True if (self.node is self.finish) else False

    def propogate(self, pq):
        """Path has been given the responsibility to propogate itself.
        Path uses matrix to find the next nodes in each of the four possible
        directions. If the direction is valid (see make_new_path docstring),
        then propogate checks to see if the new path is the fastest route to
        the new node in focus. If it is, then we make p the new min path for
        the new node, and insert p into the priority queue.
        """
        directions = ['up', 'down', 'left', 'right']
        for d in directions:
            p = self.make_new_path(d, self.node)
            if p is not None:
                if (p.node.min is None) or (p < p.node.min):
                    p.node.min = p
                    pq.insert(p)

    def make_new_path(self, op, node):
        """Matrix returns none if the desired direction is out-of-bounds.
        Further, if the node in the desired direction has been crossed by
        this path already, we return None. This will result in the path
        being thrown out by propogate. If the path is valid, we return
        a new path which inherits the needed attributes from the path
        that called propogate.
        """
        needed_keys = ['matrix', 'finish', 'nodes', 'weight']
        result = getattr(self.matrix, op)(node.loc)
        if (result is None) or (result in self.nodes):
            return None
        set_up_dict = {k:v for k,v in self.__dict__.items() if k in needed_keys}
        return Path(result, **set_up_dict)
            
    def euc_dist(self, loc, finish):
        """Calculates the euclidean distance between current node and
        the destination node. This helps us to always prefer paths that
        are closer to the end, provided that their weights are minimum.
        """
        loc_row, loc_col = loc
        fin_row, fin_col = finish
        row_dist = math.pow((fin_row - loc_row), 2)
        col_dist = math.pow((fin_col - loc_col), 2)
        return math.sqrt(row_dist + col_dist)


    ### Rich comparison special methods to be used in comparing paths
    def __lt__(self, other):
        if self.weight == other.weight:
            return self.dist < other.dist
        return self.weight < other.weight

    def __le__(self, other):
        if self.weight == other.weight:
            return self.dist <= other.dist
        return self.weight <= other.weight

    def __eq__(self, other):
        return ((self.weight == other.weight) \
                and (self.dist == other.dist))

    def __ne__(self, other):
        return ((self.weight != other.weight) \
                and (self.dist != other.dist))

    def __gt__(self, other):
        if self.weight == other.weight:
            return self.dist > other.dist
        return self.weight > other.weight
        
    def __ge__(self, other):
        if self.weight == other.weight:
            return self.dist >= other.dist
        return self.weight >= other.weight

    def __repr__(self):
        return "Path(node: {}, weight: {})".format(self.node, self.weight)
        
class PathFinder:
    """PathFinder runs the whole show. It stores the matrix,
    and the priority queue. It will be responsible for 
    running the algorithm, which creates path objects and naively
    shoves them into the priority queue.
    """

    def __init__(self, matrix):
        self.matrix = matrix
        self.pq = PriorityQueue()

    def run(self, start, finish):
        """This method will run the entire algorithm.
        It creates a path object starting at the specified
        start point, inserts the object into the priority
        queue. Paths will have all comparators defined, so that
        a vanilla priority queue can evaluate expressions
        such as path1 > path2, etc. Thus, paths with the minimum
        weight will be favored by the priority queue, with ties
        broken by euclidean distance from the finish. Thus,
        we continually propogate our path from the minimum weight
        so far, always leaning towards the goal.
        """
        start_node = self.matrix.get(start)
        finish_node = self.matrix.get(finish)
        start_path = Path(start_node, finish=finish_node, matrix=self.matrix)
        self.pq.insert(start_path)

        while True:
            if (not self.pq.is_empty()) and (self.pq.min().arrived == True):
                return self.pq.min()
            p = self.pq.extract_min()
            p.propogate(self.pq)

def main():
    import sys
    if (len(sys.argv) == 1):
        raise Exception("An input matrix is required as the last command line argument.")
    filepath = sys.argv[-1]
    with open(filepath, 'r') as f:
        m = Matrix(f)
    print(PathFinder(m).run((0,0), (79,79)))

if __name__ == '__main__':
    start_time = time.time()
    main()
    print("Running time: {}".format(time.time()-start_time))
