""" 
Lambda.py: A very simple implementation of Lambda-calculus in Python.
Author: ghao@cin.ufpe.br
"""

""" Variables avaiable on the interpreter. """
Vars = ['x', 'y', 'z', 'r', 's', 't', 'u', 'v', 'w']

def getNewBound(L, R):
    """ Returns a variable that is not free in (LR). """
    freeL = L.free()
    freeR = R.free()
    for i in Vars:
        if (not i in freeL) and (not i in freeR) :
            return i
    raise Error("Please add more variables")

## Exceptions
class Error:
    def __init__(self, value):
        self.value = value
    
    def __str__(self):
        return repr(self.value)

class Warning(Error):
    pass
##

## Lambda-Terms
class Term:
    """ Prototype of a Lambda-Term:
        == Atom        : a variable or a constant.
        == Application : (UV), where U, V are Lambda-Terms.
        == Abstraction: (\x.U), where x is a variable and U is a Lambda-Term.
        
        Methods:
           - to_string()   -> returns a string representation of the term.
           - replace(N, x) -> replaces all free occurences of x by N.
           - free(N, x)    -> returns a list of free variables of the term. 
    """
    pass

class Atom(Term):
    def __init__(self, val) :
        self.value = val
        
    def to_string(self):
        return "("+str(self.value)+")"
        
    def replace(self, N, x):
        if self.value == x:
            return N
        else:
            return self
            
    def free(self):
        return self.value

class Application(Term):
    def __init__(self, l, r):
        self.left = l
        self.right = r
        
    def to_string(self) :
        return "("+self.left.to_string()+self.right.to_string()+")"
        
    def replace(self, N, x):
        if isinstance(self.left, Atom) :
            self.left = self.left.replace(N, x)
        else:
            self.left.replace(N, x)
        if isinstance(self.right, Atom):
            self.right = self.right.replace(N, x)
        else:
            self.right.replace(N, x)
            
    def free(self):
        f = []
        f.append(self.left.free())
        f.append(self.right.free())
        return f

class Abstraction(Term):
    def __init__(self, lda, body) :
        self.bound = lda
        self.body = body
        
    def to_string(self) :
        return "(\\"+self.bound+"."+self.body.to_string()+")"
    
    def replace(self, N, x):
        if self.bound != x :
            if self.bound in N.free():
                new_bound = getNewBound(self, N)
                self.body.replace(new_bound, self.bound)
                self.bound = new_bound
            if isinstance(self.body, Atom):
                self.body = self.body.replace(N, x)
            else:
                self.body.replace(N, x)
                
    def free(self):
        tmp = self.body.free()
        return [x for x in tmp if x != self.bound]
##

## Parser
def tokenize(a) :
    """ Returns the tokens of the string representation 'a' of a Lambda-Term. """
    return a.replace("(", " ( ").replace(")", " ) ").replace(".", " . ").split()

def read_from(tokens) :
    """ Returns the parse-tree built from a list with the tokens of a Lambda-Term. """
    if len(tokens) == 0 :
        raise SyntaxError("Parse error")
    token = tokens.pop(0)
    if token == "(":
        L = []
        while tokens[0] != ")":
            L.append(read_from(tokens))
        tokens.pop(0)
        return L
    elif token == ")":
        raise SyntaxError("Unexpected ')'")
    else:
        return token

def generateTerm(tree):
    """ Returns the term built from the parse-tree. """
    if len(tree) == 1:
        if tree[0] in Vars:
            return Atom(tree[0])
        else:
            raise SyntaxError(tree[0]+" is not an Atom")
    elif len(tree) == 2:
        l = tree[0]
        r = tree[1]
        return Application(generateTerm(l), generateTerm(r))
    elif len(tree) == 3:
        if len(tree[0]) == 2 and tree[1] == '.':
            bind = tree[0][1]
            return Abstraction(bind, generateTerm(tree[2]))
        else:
            raise SyntaxError("Bad abstraction construction")

def parse(term):
    """ Returns a Lambda-Term built from its string representation. """
    tree = read_from(tokenize(term))
    t = generateTerm(tree)
    return t
##

## Computation
def beta_reduce(term, steps):
    """ Applies a beta-conversion to 'term' with at most 'steps' steps. """
    def reduce(term, count):
        if count > steps:
            return term
        elif isinstance(term, Atom):
            return term
        elif isinstance(term, Application):
            if isinstance(term.left, Abstraction):
                term.left.body.replace(term.right, term.left.bound)
                return reduce(term.left.body, count+1)
            else:
                term.left = reduce(term.left, count+1)
                term.right = reduce(term.right, count+1)
                return term
        elif isinstance(term, Abstraction):
            term.body = reduce(term.body, count+1)
            return term
        else:
            raise SyntaxError("'"+str(term)+"' is not a Lambda-Term")
    
    if isinstance(term, Term):
        return reduce(term, 0)
    else:
        return reduce(parse(term), 0)

def alpha_conversion(term, newVar=''):
    """ Applies a alpha-conversion to 'term', changing its bound variable to 'newVar'. """
    if isinstance(term, Abstraction):
        if newVar != '' and (newVar in term.free()):
            raise Error('Bad alpha-conversion: \''+repr(newVar)+'\' is free in '+term.body.to_string())
        if newVar == '':
            newVar = getNewBound(term, Atom(term.bound))
        
        old = term.bound
        term.bound = newVar
        term.body.replace(Atom(newVar), old)
##

"""
## Examples
a = "((x)(\\x.(\\z.(\\y.((x)(\s.sx))))))"
b = parse(a)
print b.to_string()

a = Atom('u')
b = Abstraction('x', a)
c = Application(b, b)

d = c.to_string()
print d

c.replace(Atom('x'), 'u')
print c.to_string()

a = Atom('x')
b = Abstraction('x', e)
c = Application(b, Atom('z'))
d = Application(a, a)

print b.to_string()
alpha_conversion(b, 't')
print b.to_string()
##
"""
