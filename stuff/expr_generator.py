import operator
import itertools
import multiprocessing as mp
from abc import ABC, abstractmethod
from tqdm import tqdm

# TODO: repair everything related to Bool expressions
# TODO: what to do with kinda-infinite ITE ?


class Expr(ABC):
    @staticmethod
    def generator(variables=None, bool_variables=None):
        yield from Terminal.generator(variables)
        yield from NonTerminal.generator(variables, bool_variables)

    @abstractmethod
    def evaluate(self, **kwargs):
        pass

    @abstractmethod
    def simplify(self):
        pass

    @abstractmethod
    def size(self):
        pass


class Terminal(Expr):
    @staticmethod
    def generator(variables):
        for value in [1, 2]:
            yield Constant(value)
        if variables:
            for var in variables:
                yield Variable(var)

    def evaluate(self, **kwargs):
        if isinstance(self, Constant):
            return self.value
        elif isinstance(self, Variable):
            return kwargs[self.name]

    def simplify(self):
        return self

    def size(self):
        return 1


class Constant(Terminal):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return str(self.value)


class Variable(Terminal):
    def __init__(self, name):
        self.name = name

    def __str__(self):
        return self.name


class NonTerminal(Expr):
    @staticmethod
    def generator(variables, bool_variables):
        lhs_gen = Expr.generator(variables, bool_variables)
        rhs_gen = Expr.generator(variables, bool_variables)
        # bool_gen = BoolExpr.generator(variables, bool_variables)

        lhs = []
        rhs = []
        # bools = []

        while True:
            # bools.append(next(bool_gen))

            lhs.append(next(lhs_gen))
            # yield Neg(lhs[-1])
            for right in rhs:
                yield from NonTerminal.generate_ops(lhs[-1], right)
                # for bool_expr in bools:
                #     yield ITE(bool_expr, lhs[-1], right)

            rhs.append(next(rhs_gen))
            for left in lhs:
                yield from NonTerminal.generate_ops(left, rhs[-1])
                # for bool_expr in bools:
                #     yield ITE(bool_expr, left, rhs[-1])

    @staticmethod
    def generate_ops(left, right):
        yield Add(left, right)
        yield Sub(left, right)
        yield Mul(left, right)
        yield Div(left, right)


class UnaryOperation(NonTerminal):
    def __init__(self, op, value):
        self.op = op
        self.value = value

    def evaluate(self, **kwargs):
        return self.op(self.value.evaluate(**kwargs))

    def simplify(self):
        try:
            return Constant(self.op(self.value.simplify().evaluate()))
        except Exception:
            return self

    def size(self):
        return 1 + self.value.size()

    def __str__(self):
        if self.op is operator.neg:
            op_str = '-'
        else:
            op_str = 'UNKNOWN_OP'
        return f'({op_str} {self.value})'


class Neg(UnaryOperation):
    def __init__(self, value):
        super().__init__(operator.neg, value)


class BinaryOperation(NonTerminal):
    def __init__(self, op, lhs, rhs):
        self.op = op
        self.lhs = lhs
        self.rhs = rhs

    def evaluate(self, **kwargs):
        return self.op(self.lhs.evaluate(**kwargs),
                       self.rhs.evaluate(**kwargs))

    def simplify(self):
        simple_lhs = self.lhs.simplify()
        simple_rhs = self.rhs.simplify()
        try:
            return Constant(self.op(simple_lhs.evaluate(), simple_rhs.evaluate()))
        except KeyError:
            return BinaryOperation(self.op, simple_lhs, simple_rhs)

    def size(self):
        return 1 + self.lhs.size() + self.rhs.size()

    def __str__(self):
        if self.op is operator.add:
            op_str = '+'
        elif self.op is operator.sub:
            op_str = '-'
        elif self.op is operator.mul:
            op_str = '*'
        elif self.op is operator.truediv:
            op_str = '/'
        elif self.op is operator.and_:
            op_str = 'and'
        elif self.op is operator.or_:
            op_str = 'or'
        elif self.op is operator.le:
            op_str = '<='
        else:
            op_str = 'UNKNOWN_OP'
        return f'({op_str} {self.lhs} {self.rhs})'


class Add(BinaryOperation):
    def __init__(self, lhs, rhs):
        super().__init__(operator.add, lhs, rhs)


class Sub(BinaryOperation):
    def __init__(self, lhs, rhs):
        super().__init__(operator.sub, lhs, rhs)


class Mul(BinaryOperation):
    def __init__(self, lhs, rhs):
        super().__init__(operator.mul, lhs, rhs)


class Div(BinaryOperation):
    def __init__(self, lhs, rhs):
        super().__init__(operator.truediv, lhs, rhs)


class BoolExpr(Expr):
    @staticmethod
    def generator(variables, bool_variables):
        yield from BoolTerminal.generator(bool_variables)
        yield from BoolNonTerminal.generator(variables, bool_variables)


class BoolTerminal(Terminal):
    @staticmethod
    def generator(bool_variables):
        for var in bool_variables:
            yield Variable(var)


class BoolNonTerminal(Expr):
    @staticmethod
    def generator(variables, bool_variables):
        bool_lhs_gen = BoolExpr.generator(variables, bool_variables)
        bool_rhs_gen = BoolExpr.generator(variables, bool_variables)
        bool_lhs = []
        bool_rhs = []
        bools = []

        lhs_gen = Expr.generator(variables, bool_variables)
        rhs_gen = Expr.generator(variables, bool_variables)
        bool_gen = BoolExpr.generator(variables, bool_variables)
        lhs = []
        rhs = []
        bools = []

        while True:
            bool_lhs.append(next(bool_lhs_gen))
            # yield Neg(bool_lhs[-1])
            for right in bool_rhs:
                for bool_expr in bools:
                    yield from BoolNonTerminal.generate_bool_ops(bool_lhs[-1], right)

            bool_rhs.append(next(bool_rhs_gen))
            for left in bool_lhs:
                for bool_expr in bools:
                    yield from BoolNonTerminal.generate_bool_ops(left, bool_rhs[-1])

            # - -- --- -- - -- --- -- - -- --- -- - -- --- -- - -- --- -- -

            bools.append(next(bool_gen))

            lhs.append(next(lhs_gen))
            # yield BOOLNeg(lhs[-1])  ???
            for right in rhs:
                yield from BoolNonTerminal.generate_ops(lhs[-1], right)
                for bool_expr in bools:
                    yield ITE(bool_expr, lhs[-1], right)

            rhs.append(next(rhs_gen))
            for left in lhs:
                yield from BoolNonTerminal.generate_ops(left, rhs[-1])
                for bool_expr in bools:
                    yield ITE(bool_expr, left, rhs[-1])

    @staticmethod
    def generate_bool_ops(left, right):
        yield And(left, right)
        yield Or(left, right)

    @staticmethod
    def generate_ops(left, right):
        yield LE(left, right)


class And(BinaryOperation):
    def __init__(self, lhs, rhs):
        super().__init__(operator.and_, lhs, rhs)


class Or(BinaryOperation):
    def __init__(self, lhs, rhs):
        super().__init__(operator.or_, lhs, rhs)


class LE(BinaryOperation):
    def __init__(self, lhs, rhs):
        super().__init__(operator.le, lhs, rhs)


class ITE(NonTerminal):  # should inherit TernaryOperation
    def __init__(self, bool_expr, lhs, rhs):
        self.bool_expr = bool_expr
        self.lhs = lhs
        self.rhs = rhs

    def evaluate(self, **kwargs):
        if self.bool_expr.evaluate(**kwargs):
            return self.lhs.evaluate(**kwargs)
        else:
            return self.rhs.evaluate(**kwargs)

    def size(self):
        return 1 + self.bool_expr.size() + self.lhs.size() + self.rhs.size()

    def __str__(self):
        return f'(ite {self.bool_expr} {self.lhs} {self.rhs})'


# maxsize = 0
# needle = 27

# for expr in tqdm(itertools.islice(Expr.generator(), 1000000)):
#     # size = expr.size()
#     # if size > maxsize:
#     #     maxsize = size
#     #     print('[*] First expr of size {}: {}'.format(size, expr))
#     try:
#         value = expr.evaluate(x=20, b=True)
#         if value == needle:
#         # if abs(value - needle) < 1e-6:
#             print('[+] Found: {} = {}'.format(expr, value))
#             break
#         else:
#             # print('[-] {} = {} != {}'.format(expr, value, needle))
#             pass
#     except ZeroDivisionError:
#         pass

constraints = {(1 + 5,): 0, (2 + 5,): 1, (3 + 5,): 2, (4 + 5,): 3, (5 + 5,): 4}


def work(expr):
    try:
        expr = expr.simplify()
        for (t,), answer in constraints.items():
            value = expr.evaluate(t=t)
            if value != answer:
                return None
        return expr
    except ZeroDivisionError:
        return None


with mp.Pool() as pool:
    max_iters = 1_000_000
    data = itertools.islice(Expr.generator(('t',)), max_iters)

    for expr in tqdm(pool.imap_unordered(work, data, chunksize=1024), total=max_iters):
        if expr is not None:
            print('[+] Found: {}'.format(expr))
            break
