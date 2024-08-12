from dataclasses import dataclass
from typing import List, Union, Optional, Tuple
from typeguard import typechecked


"""
    This file provides the python data classes for working with LTL formulas and functions to build these formulas.

    The structure of the python data classes for LTL formulas is as follows:

    Expression :=           AtomicProposition | Predicate(Term, ..., Term) | BinExpression(BinOp, Expression, Expression) | UnExpression(UnOp, Expression) | MultiExpression(MulOp, List[Expression]) | Wahr | Falsch
    AtomicProposition :=    OnAccessRamp_V8 | IsCool_Paul | ...
    Term :=                 Variable | Constant
    Variable :=             x_o | X_{!ego}
    Constant :=             ego | v1 | v8 | ..
    Predicate :=            OnAccessRamp | Likes
    BinOp :=                TempBinOp | LogicBinOp
    UnOp :=                 TempUnOp | LogicUnOp
    TempBinOp :=            U [x,y]                     (Interval is optional)
    LogicBinOp :=           and | or | imp | iff 
    TempUnOp :=             G[x,y] | F[x,y] | X[x,y]    (Interval is optional)
    LogicUnOp :=            not
    MulOp :=                Conjunction | Disjunction

"""


@dataclass
class Variable:
    name : str

    def __str__(self):
        return self.name

    def __post_init__(self):
        assert isinstance(self.name, str)

    def __hash__(self):
        return hash(self.name)

@dataclass
class Constant:
    name : str

    def __str__(self):
        return self.name

    def __post_init__(self):
        assert isinstance(self.name, str)

    def __hash__(self):
        return hash(self.name)

Term = Union[Constant, Variable]

@dataclass
class TempBinOp:
    name : str
    interval: Optional[tuple] = None

    def __post_init__(self):
        assert self.name in ['U']
        assert isinstance(self.interval, Optional[tuple])

    def __str__(self) -> str:
        if not self.interval:
            return self.name
        else:
            return self.name + str(self.interval)

    def __hash__(self):
        return hash(self.name) + hash(self.interval)

@dataclass
class LogicBinOp:
    name : str

    def __post_init__(self):
        assert self.name in ['and', 'or', 'imp', 'iff']


    def __str__(self) -> str:
        match self.name:
            case 'and': return '&'
            case 'or': return '|'
            case 'imp': return '->'
            case 'iff': return '<->'
            case _: raise ValueError(f"operator {self.name} not defined")

    def __hash__(self):
        return hash(self.name)

@dataclass
class TempUnOp():
    name : str
    interval: Tuple[int,int]

    @typechecked
    def __init__(self, name : str, interval):
        self.name = name
        
        if interval == None:
            match name:
                case 'X':
                    self.interval = (1,None)
                case _:
                    self.interval = (0,None)
        else:
            self.interval = interval
                
    def __hash__(self):
        return hash(self.name)+ hash(tuple(self.interval))
        

    def __post_init__(self):
        assert self.name in ['G', 'F', 'X', 'P', 'O']
        assert isinstance(self.interval, Tuple)
        assert isinstance(self.interval[0], int) and (isinstance(self.interval[1], int) or self.interval == None)

    def __str__(self) -> str:
        if self.name == 'G':
            if self.interval == (0,None):
                return self.name
            else:
                end = "inf" if self.interval[1] == None else self.interval[1]
                return f"{self.name}[{self.interval[0]},{end}]"
                
        if self.interval[0] == 0 and self.interval[1] == None:
            return self.name
        elif self.name == 'X' or self.name == 'P':
            if self.interval[0] == 1:
                return self.name
            else:
                return f"{self.name}[{self.interval[0]}]"
        else:
            if self.interval[1] == None:
                return f"{self.name}[{self.interval[0]},inf]"
            else:
                return f"{self.name}[{self.interval[0]},{self.interval[1]}]"

@dataclass
class LogicUnOp:
    name : str

    def __post_init__(self):
        assert self.name in ['not']

    def __str__(self) -> str:    
        match self.name:
            case 'not': return '!'
            case _: raise ValueError(f"operator {self.name} not defined")

    def __hash__(self):
        return hash(self.name)

@dataclass
class LogicMultiOp:
    name : str 

    def __post_init__(self):
        assert self.name in ['conjunction' , 'disjunction']
    
    def __str__(self) -> str:
        match self.name:
            case 'conjunction': return '&'
            case 'disjunction': return '|'
            case _: raise ValueError(f"operator {self.name} not defined")

    def __hash__(self):
        return hash(self.name)

@dataclass
class Expression:

    def replace_variable(self, var:'Variable', const:'Constant'):
        match self:
            case BinaryExpression(operator, exp1, exp2): 
                return BinaryExpression(operator, exp1.replace_variable(var, const), exp2.replace_variable(var, const))
            case UnaryExpression(operator, exp):
                return UnaryExpression(operator, exp.replace_variable(var, const))
            case MultiExpression(operator, expressions):
                return MultiExpression(operator, [exp.replace_variable(var, const) for exp in expressions])
            case Predicate(operator, terms):
                replaced_terms = []
                for term in terms:
                    if term == var:
                        replaced_terms.append(const)
                    else:
                        replaced_terms.append(term)
                
                return Predicate(operator, replaced_terms)
            case AtomicProposition(name):
                return AtomicProposition(name)
            case _:
                raise ValueError("This Expression is not known")

    def replace_first_variable_with_predicate(self, variable:str, predicate:str):
        """
        Predicate(variable,variable) -> Predicate(predicate,variable)
        
        This allowes to model relationships between the variables to be replaced. For example:
        We want to replace all occurences of X with names = ["Paul", "Noah", "Julian"] to model that they do not want to share a car:
        
        formula = not_share_care(X,X)
        
        for name1 in names
            exp = .replace first(formula, X, name1)
            for name2 in names\name1:
                specifications.append(exp, X, name2)
        
        -> not_share_care(Paul,Noah), not_share_care(Paul,Julian),...
        """
        match self:
            case BinaryExpression(operator, exp1, exp2): 
                return BinaryExpression(operator, exp1.replace_variable_with_predicate(variable, predicate), exp2.replace_variable_with_predicate(variable, predicate))
            case UnaryExpression(operator, exp):
                return UnaryExpression(operator, exp.replace_variable_with_predicate(variable, predicate))
            case MultiExpression(operator, expressions):
                return MultiExpression(operator, [exp.replace_variable_with_predicate(variable, predicate) for exp in expressions])
            case Predicate(operator, terms):
                replaced_terms = []
                replaced_first = False
                for term in terms:
                    match term:
                        case Variable(name):
                            if not replaced_first:
                                replaced_terms.append(Predicate(predicate) if variable == name else Variable(name))
                                replaced_first = True
                        case Constant(name): 
                            replaced_terms.append(Constant(name))
                return Predicate(operator, replaced_terms)
            case AtomicProposition(name):
                return AtomicProposition(name)
            case _:
                raise ValueError("This Expression is not known")

    def contains_variable(self, variable : 'Variable'):
        match self:
            case BinaryExpression(operator, exp1, exp2): 
                return exp1.contains_variable(variable) or exp2.contains_variable(variable)
            
            case UnaryExpression(operator, exp):
                return exp.contains_variable(variable)

            case MultiExpression(operator, expressions):
                for exp in expressions:
                    if exp.contains_variable(variable):
                        return True
                return False
            case Predicate(operator, terms):
                return variable in terms
            case AtomicProposition(name):
                return False
            case _:
                raise ValueError("This Expression is not known")

    def contains_variable_by_name(self, var_name:str):
        return self.contains_variable(Variable(var_name))

@dataclass
class AtomicProposition(Expression):
    name: str

    def __str__(self):
        return self.name

    def __post_init__(self):
        assert isinstance(self.name, str)

    def __hash__(self):
        return hash(self.name)

@dataclass
class Predicate(Expression):
    name: str
    terms: List[Term]

    def __post_init__(self):
        assert isinstance(self.name, str)
        for term in self.terms:
            assert isinstance(term, Variable) or isinstance(term, Constant)

    def __str__(self):
        string = self.name
        for term in self.terms:
            string += f"_{term}"
        return string

    def __hash__(self):
        return hash(self.name)+ hash(tuple([term.__hash__() for term in self.terms]))

@dataclass
class BinaryExpression(Expression):
    operator : Union['TempBinOp', 'LogicBinOp']
    exp1: Expression
    exp2: Expression

    def __post_init__(self):
        assert isinstance(self.operator, TempBinOp) or isinstance(self.operator, LogicBinOp)
        assert isinstance(self.exp1, Expression)
        assert isinstance(self.exp2, Expression)


    def __str__(self):
        return f"({self.exp1} {self.operator} {self.exp2})"


    def __hash__(self):
        return self.operator.__hash__() + self.exp1.__hash__() + self.exp2.__hash__()

@dataclass
class Wahr(Expression):

    def __str__(self):
        return "True"

    def __hash__(self):
        return hash("wahr")

@dataclass
class Falsch(Expression):

    def __str__(self):
        return "False"

    def __hash__(self):
        return hash("falsch")

@dataclass
class UnaryExpression(Expression):
    operator : Union[TempUnOp, LogicUnOp]
    exp: Expression

    def __post_init__(self):
        assert isinstance(self.exp, Expression)
        assert isinstance(self.operator, TempUnOp) or isinstance(self.operator, LogicUnOp)

    def __str__(self):
        return f"({self.operator}({self.exp}))"

    def __hash__(self):
        # Combine hashes of individual fields
        return hash(self.operator.__hash__() + self.exp.__hash__())

@dataclass
class MultiExpression(Expression):
    operator : LogicMultiOp
    expressions: List[Expression]

    def __post_init__(self):
        assert isinstance(self.operator, LogicMultiOp)
        for exp in self.expressions:
            assert isinstance(exp, Expression)

        

    def __str__(self) -> str:
        op = self.operator.__str__()
        string = ""
        for i in range(len(self.expressions)-1):
            string += f"{self.expressions[i]} {op} "
        
        return "("+string + self.expressions[-1].__str__() + ")"

    def __hash__(self):
        # Combine hashes of individual fields
        return hash(self.operator.__hash__()) + hash(tuple([exp.__hash__() for exp in self.expressions]))
    

    
def _and(exp1 : Expression, exp2 : Expression):
        return BinaryExpression(LogicBinOp("and"), exp1, exp2)

    
def _or(exp1 : Expression, exp2 : Expression):
        return BinaryExpression(LogicBinOp('or'), exp1, exp2)


def _not(exp : Expression):
        return UnaryExpression(LogicUnOp('not'), exp)


def implies(exp1 : Expression, exp2 : Expression):
        return BinaryExpression(LogicBinOp('imp'), exp1, exp2)

    
def iff(exp1 : Expression, exp2 : Expression):
        return BinaryExpression(LogicBinOp('iff'), exp1, exp2)

    
def eventually(exp : Expression, I=None):
        if I == None:
            return UnaryExpression(TempUnOp('F', (0,None)), exp)
        else:
            if I[1] == "inf":
                I[1] = None
            return UnaryExpression(TempUnOp('F', I), exp)
    
    
def always(exp : Expression, I=None):
        if I == None:
            return UnaryExpression(TempUnOp('G', (0,None)), exp)
        else:
            if I[1] == "inf":
                I[1] = None
            return UnaryExpression(TempUnOp('G', I), exp)

    
def next(exp : Expression, a=None):
        if a == None:
            return UnaryExpression(TempUnOp('X', (1, None)), exp)
        else:
            return UnaryExpression(TempUnOp('X', (a, None)), exp)

    
def previously(exp : Expression, a=None):
        if a == None:
            return UnaryExpression(TempUnOp('P', (1, None)), exp)
        else:
            return UnaryExpression(TempUnOp('P', (a,None)), exp)


    
def once(exp : Expression, interval=None):
        return UnaryExpression(TempUnOp('O', interval), exp)

    
def conjunction(expressions : List[Expression]):
        if len(expressions) == 1:
            return expressions[0]
        else:
            return MultiExpression(LogicMultiOp('conjunction'), expressions)
        
    
def disjunction(expressions : List[Expression]):
        if len(expressions) == 1:
            return expressions[0]
        else:
            return MultiExpression(LogicMultiOp('disjunction'), expressions)

    
def until(exp1 : Expression, exp2 : Expression, interval=None):
        return BinaryExpression(TempBinOp("U", interval), exp1, exp2)

    
def const(name : str) -> Constant:
        return Constant(name)


def pred(name : str, terms : List[Term]):
        return Predicate(name, terms)


def var(name : str):
        return Variable(name)


def ap(name : str):
        return AtomicProposition(name)
