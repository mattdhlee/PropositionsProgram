from enum import Enum       # requires Python >= 3.4

#----------------------------
# reduce function, should you want to use it
#----------------------------
def reduce(f, iterable, initializer=None):
    it = iter(iterable)
    if initializer is None:
        try:
            initializer = next(it)
        except IndexError:
            raise TypeError('reduce() of empty iterable with no initial value')
    accumulator = initializer
    for item in it:
        accumulator = f(accumulator, item)
    return accumulator

#----------------------------
# code for representing logical propositions
#----------------------------
class Proposition:
    def __repr__(self):
        if isinstance(self, Var):
            return self.var
        elif isinstance(self, Neg):
            return '~' + repr(self.prop)
        elif isinstance(self, BinOp):
            return '( ' + repr(self.left) + ' ' + self.op.name + ' ' + repr(self.right) + ' )'
        else:
            return '<unrecognized instance of Proposition>'
            
    def __neg__(self):
        return Neg(self)
        
    def __invert__(self):
        return Neg(self)
        
    def eval(self, truthValues):
        ''' eval: (Proposition, dict(str: bool)) -> bool
            evaluates this proposition by substituting variables for the given truth values
        '''
        #var -> get value from dict
        if isinstance(self.prop, Var):
            return truthValues[self.prop]
        
        #if neg -> call eval on self.prop and then not the whole thing 
        elif isinstance(self.prop, Neg):
            return not eval(self.prop.eval(self.prop))
        
        # if binOP -> 1) AND ->  self.left.eval(left) a
        
        elif isinstance(self.prop, BinOp):
            if self.prop == LogOp(1):#AND
                return self.left.eval(self.left,truthValues) and self.right.eval(self.right,truthValues)
            elif self.prop == LogOp(2):#OR
                return self.left.eval(self.left,truthValues) or self.right.eval(self.right,truthValues)
        
        return None    # fill in code here

class Var(Proposition):
    def __init__(self, var):
        if not isinstance(var, str): raise TypeError("variable must be a string")
        self.var = var

class Neg(Proposition):
    def __init__(self, prop):
        if not isinstance(prop, Proposition): raise TypeError("only propositions can be negated")
        self.prop = prop
        
class LogOp(Enum):
    AND = 1
    OR = 2

class BinOp(Proposition):
    def __init__(self, op, left, right):
        if not isinstance(op, LogOp): raise TypeError("operation is invalid")
        if not isinstance(left, Proposition): raise TypeError("left operand is not a proposition")
        if not isinstance(right, Proposition): raise TypeError("right operand is not a proposition")
        self.op = op
        self.left = left
        self.right = right

#----------------------------
# convenience functions to build propositions with logical connectors
#----------------------------
def neg(p):
    if isinstance(p, Neg):
        return p.prop
    return Neg(p)


def conj(p, q):
    ''' conj: (Proposition, Proposition) -> Proposition
        returns a representation of p AND q
    '''
    return BinOp(LogOp.AND, p, q)

def disj(p, q):
    ''' disj: (Proposition, Proposition) -> Proposition
        returns a representation of p OR q
    '''
    return BinOp(LogOp.OR, p, q)

def cond(p, q):
    ''' cond: (Proposition, Proposition) -> Proposition
        returns a representation of p IMPLIES q
    '''
     
    return BinOp(LogOp.OR, neg(p), q)
    
#----------------------------
# functions to process & evaluate arguments
#----------------------------
def fromArgument(premises, conclusion):
    ''' argument: (iterable of Proposition, Proposition) -> Proposition
        make a single proposition from all the premises and the conclusion
    '''
    prop = premises[0]    #declaring the proposition variable 
    i = 1
    while i<len(premises):
        prop = conj(prop, premises[i])
        i+=1
    return prop


def negNorm(prop):
    ''' negNorm: Proposition -> Proposition
    
        return a negative-normal representation of the given proposition
        this is a form where negations are applied only to variables and not to more complex propositions
    '''
    if isinstance (prop, Var):
        return prop
    elif isinstance(prop, Neg):
        if isinstance(prop.prop, BinOp):
            #if the prop.prop is BinOp, create and return a new BinOp. 3 arguments: first negate the BinOp, then negNorm the left then the right.
            if(prop.prop.op == LogOp(1)):
                prop.prop.op = LogOp(2)
            elif(prop.prop.op == LogOp(2)):
                prop.prop.op = LogOp(1)
            return BinOp((prop.prop.op),negNorm(neg(prop.prop.left)),negNorm(neg(prop.prop.right)))
        else:
            print("returning prop from prop,Neg if")
            return prop
   
    else:
        print("Invalid argument!")
        return prop
    return 0
    
    

def toCNF(prop):
    ''' toCNF: Proposition -> Proposition
        convert prop to conjunctive normal form
    '''
  
    if isinstance(prop, Var) or isinstance(prop, Neg):
        print("just a variable")
        return prop
    elif isinstance(prop, BinOp):
        print("entering the recursion part...")
        prop.left = toCNF(prop.left)
        prop.right = toCNF(prop.right)
        if (prop.op)== LogOp(1): #logical op is AND
            return conj(prop.left,prop.right)
        
        elif (prop.op)== LogOp(2): #logical op is OR   
            return cnfHelper(prop.left, prop.right)
    else:
        return 0

def cnfHelper(L,R):
    '''helps the converting prop to cnf 
       specific to cse when of BinOp and when both or one side of the OR prop is an AND
    '''
    if(isinstance(L, Var) and isinstance(R,Var)):
        return conj(L,R)
    
    elif(isinstance(L, BinOp) and L.op == LogOp(1)):
        return(conj(cnfHelper(R,L.left),cnfHelper(R,L.right)))
    
    elif(isinstance(R, BinOp) and R.op== LogOp(1)):
        return(conj(cnfHelper(L, R.left),cnfHelper(L, R.right)))
    else:
        
        return disj(L,R)

def isValid(prop):
    ''' isValid: Proposition -> bool
        returns whether or not a given proposition is a tautology
    '''

    # start by converting the proposition to a negative-normal CNF formula
    prop = (negNorm(prop))
    prop = toCNF(prop)
    print(prop)
    print("sokso")
    
    if isinstance(prop,Var): 
        return True
    elif isinstance(prop,Neg):
        return True
    
    elif isinstance(prop,BinOp): #its a BinOp
        s1 = set() #pos set
        s2 = set() #neg set
        if prop.op == LogOp(2): #OR
            validHelper(prop.right,s1,s2)
            validHelper(prop.left,s1,s2)
            
        elif prop.op == LogOp(1): #AND
            print("in ANDDDD")
            return isValid(prop.left) and isValid(prop.right)
     
        
        if len(s1.intersection(s2)) > 0:
            return True
        else:
            return False
    else:
        return False
        

def validHelper(prop,s1,s2):
    if isinstance(prop, BinOp):
        validHelper(prop.right,s1,s2)
        validHelper(prop.left,s2,s2)
        
    elif isinstance(prop, Var):
     
        print("adding to pos")
        s1.add(prop.var)
    elif isinstance(prop,Neg):
        print("adding to neg")
        s2.add(neg(prop).var)
        
   
           
    
    
def checkArgument(premises, conclusion):
    ''' checkArgument: (iterable of Proposition, Proposition) -> bool
        returns whether or not an argument is valid
    '''
    return isValid(fromArgument(premises, conclusion))

def isSound(premises, conclusion, truthValues):
    ''' isSound: (iterable of Proposition, Proposition, dict(str: bool)) -> bool
        returns whether or not an argument is sound given truth values for variables
    '''
    return checkArgument(premises, conclusion) and reduce(lambda x, y: x and y.eval(truthValues), premises, True)



def main():
    a = Var('p')
    b = Var('q')
    c = Var('r')
    print (neg(a))
    ##n = Neg()
    #print (negNorm(neg(disj(a,b))))
    #print (toCNF(neg(disj(a,b))))
    #print (toCNF(disj((conj(a,b)),c)))
    #print (isValid(disj(neg(a),a)))
    print (isValid(disj(disj(a,b),conj(neg(a),neg(b)))))
    ##return negNorm(-(n or a))
    
    
    ##QUESTIONS TO ASK: 1. BinOp()-> does 'self' count as an argument. an error message wanted 4arguments.. I only passed in three but it works? 
    ## 2. How to write the case when the proposition is in the OR form... 