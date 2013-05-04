# NFAtoDFA.py :
# This is Python code for representing finite automata, DFAs and NFAs, 
# and for converting from an NFA into a DFA.  
#
# Harry Yan, 7/3/2013
#

class DFA:     
     """Class that encapsulates a DFA."""
     def __init__(self, transitionFunction, initialState, finalStates):
          self.delta = transitionFunction    
          self.q0 = initialState
          self.F = finalStates
          self.current_state = initialState
     def printDFA(self,test,Sigma):
          x = set([])
          for state in test:
               print "%s \t" %(state),
               for a in Sigma:
                    x = self.delta[state][a]
                    print "%s \t" %(x),
               print "\n"
     def deltaHat(self, state, inputString):
          for a in inputString: 
               state = self.delta[state][a]
          return state
     def inLanguage(self, inputString):
          return self.deltaHat(self.q0, inputString) in self.F

     def alphabet(self):
          """Returns the NFA's input alphabet, generated on the fly."""
          m_file = open('other4.txt','r')
          Sigma = moveT(open('other4.txt','r'))
          for a in Sigma:
               if a == "e":
                    Sigma.remove(a)
          m_file.close()
          return Sigma
     def eliminate(sele,classes):
          for x in classes:
               if x == []:
                    classes.remove(x)
          return classes
     def minimizeDFA(self,classes,dfaAlphabet,Sigma,f):
          new_states = []
          new_start = None
          new_delta = {}
          new_accepts = []
          new_current_state = None
          state_map = {}
          newdelta = {}

          for state_class in classes:
                  temp = state_class[0]
                  for small in state_class:
                          temp = temp | small
                  new_states.append(temp)
                  for state in new_states:
                    state_map[state] = temp
                    if state == M.q0:
                        new_start = temp

          for state_class in classes:
                  temp1 = state_class[0]
                  for small in state_class:
                          temp1 = temp1 | small
                  newdelta[temp1] = {}
                  for a in dfaAlphabet:
                          nextStates2 = reduce(lambda x,y: x|y, [M.deltaHat(q,a) for q in state_class])
                          if temp1 >= nextStates2:
                                  nextStates2 = temp1
                                  newdelta[temp1][a] = nextStates2
                          else:
                               if nextStates2 in new_states:
                                    for x in new_states:
                                         if x == nextStates2:
                                              nextStates2 = x
                                              newdelta[temp1][a] = nextStates2
                               else:
                                    for x in new_states:
                                         if x > nextStates2 :
                                              nextStates2 = x
                                              newdelta[temp1][a] = nextStates2

          for acc in M.F:
              if acc in new_states:
                  new_accepts.append(acc)
          print "The minimized DFA is as following:"
          print "\n"
          print "I \t\t\t\t\t\t\t\tI1 \t\t\t\t\t\t I0"
          print "###########################################################################################################################################"
          x = set([])
          for state in new_states:
               print "%s \t" %(state),
               for a in Sigma:
                    x = newdelta[state][a]
                    print "%s \t" %(x),
               print "\n"
          print "###########################################################################################################################################"        
          print("\n")
          print "The states which have %s are new accept states." %(f)
          return newdelta

     
     def classify(self,classes,dfaAlphabet):
          changed = True
          while changed:
               changed = False
               for cl in classes:
                    local_change = False
                    for alpha in dfaAlphabet:
                         next_class = None
                         new_class = []
                         for state in cl:
                              next = M.delta[state][alpha]
                              if next_class == None:
                                   for c in classes:
                                        if next in c:
                                             next_class = c
                              elif next not in next_class:
                                   new_class.append(state)
                                   changed = True
                                   local_change = True
                         if local_change == True:
                              old_class = []
                              for c in cl:
                                   if c not in new_class:
                                        old_class.append(c)
                              classes.remove(cl)
                              classes.append(old_class)
                              classes.append(new_class)
                              break
          return classes
     
class NFA: 
     """Class that encapsulates an NFA."""
     def __init__(self, transitionFunction, initialState, finalStates,epsilon):
          self.delta = transitionFunction    
          self.q0 = initialState
          self.epsilon = epsilon
          self.F = set(finalStates)
     def printNFA(self,test):
          x = set([])
          for state in test:
               print "%s \t" %(state),
               for a in self.alpha():
                    x = self.delta[state][a]
                    print "%s \t" %(x),
               print "\n"
     def eclosure(self,state):
                equal = self.deltaHat(state,self.epsilon)
                return equal
     def eclosureSet(self,state):
                equal = self.deltaHatSet(state,self.epsilon)
                return equal
     def deltaHat(self, state, inputString):
          """deltaHat is smart enough to return the empty set if no transition is defined."""
          states = set([state])
          for a in inputString: 
               newStates = set([])
               for state in states: 
                    try:
                         newStates = newStates | self.delta[state][a]
                    except KeyError: pass
               states = newStates
          return states
     def deltaHatSet(self, state, inputString):
           states = state
           for a in inputString: 
                newStates = set([])
                for state in states: 
                     try:
                          newStates = newStates | self.delta[state][a]
                     except KeyError: pass
                states = newStates
           return states
     def inLanguage(self, inputString):
          return len(self.deltaHat(self.q0, inputString) & self.F) > 0
     def alphabet(self):
          """Returns the NFA's input alphabet, generated on the fly."""
          m_file = open('other4.txt','r')
          Sigma = moveT(open('other4.txt','r'))
          for a in Sigma:
               if a == "e":
                    Sigma.remove(a)
          m_file.close()
          return Sigma
     def alpha(self):
          m_file = open('other4.txt','r')
          Sigma = moveT(open('other4.txt','r'))
          m_file.close()
          return Sigma
     def states(self):
          """Returns the NFA's set of states, generated on the fly."""
          Q = set([self.q0]) | set(self.delta.keys()) | reduce(lambda a,b:a|b, reduce(lambda a,b:a+b, [x.values() for x in self.delta.values()]))     # {q0, all states with outgoing arrows, all with incoming arrows}
          return Q
     def pop(self,temp,inputString):
          tempo = temp
          temps = temp.copy()
          temps = frozenset(temps)
          temps = set([temps])
          while len(temps) > 0:
               xSet = temps.pop()
               tempx = set([])
               for a in inputString:
                    for state in xSet:
                         tempx = self.delta[state][a]
                         tempx1 = frozenset(tempx)
                         if tempx1 <= xSet:
                              continue
                         else:
                              temps.add(tempx1)
                              tempo |= tempx
          return tempo
def convertNFAtoDFA(N,Sigma):
     """Converts the input NFA into a DFA.  
     
     The output DFA has a state for every *reachable* subset of states in the input NFA.  
     In the worst case, there will be an exponential increase in the number of states.
     """
     eclosureQ0 = N.eclosure(N.q0)
     temp = set([N.q0])
     temp |= eclosureQ0
     temp=N.pop(temp,N.epsilon)
     N.q0 = temp.copy() 
     q0 = frozenset(temp)   # frozensets are hashable, so can key the delta dictionary
     Q = set([q0])
     unprocessedQ = Q.copy() # unprocessedQ tracks states for which delta is not yet defined

     delta = {}
     F = []
     count = 0
     qSetM = set([])
     
     while len(unprocessedQ) > 0:
          if count >= 1:
               qSet = unprocessedQ.pop()
               qSetM = qSet
               qSetM |= N.eclosureSet(qSetM)
               qSetM =N.pop(qSetM,N.epsilon)
                    
          else:
               qSet = unprocessedQ.pop()
               qSetM = qSet
          
          count = count+1
          
          delta[qSet] = {}
          for a in Sigma:
               nextStates = reduce(lambda x,y: x|y, [N.deltaHat(q,a) for q in qSetM])
               nextStates = frozenset(nextStates)
               delta[qSet][a] = nextStates
               if not nextStates in Q: 
                    Q.add(nextStates)
                    unprocessedQ.add(nextStates)
     for qSet in Q:
          if len(qSet & N.F) > 0: 
               F.append(qSet)
     M = DFA(delta, q0, F)
     print "The DFA is as following:"
     print "\n"
     print "I \t\t\t\t\t\tI1 \t\t\t\t\t\tI0 "
     print "#########################################################################################################################"
     M.printDFA(Q,Sigma)
     print "#########################################################################################################################"
     return M


# get the transition function
def collect(file,move):
    result = {}
    for i in move:
        result[i] = {}
    for line in file.readlines( ):
        line=line.rstrip('\n') 
        left,right = line.split("|")     #left is q0
        left1,right1= right.split(":")   # left1 is 0, right1 are states
        states = right1.split(",")       #q1,q2,q3...

        for i in move:
            if i == left:
                temp = set([])
                for a in states:
                    temp.add(a)
                    result[i][left1] = temp
    return result

# procure all states
def getStates(file):
     temp = set([])
     for line in file.readlines( ):
          line=line.rstrip('\n') 
          left,right = line.split(":")
          element = right.split(",")
          if left == "Q":
               temp = states(temp,element)
     return temp   

def states(temp,element):
    for a in element:
        temp.add(a)
    return temp


def getStart(file):
     temp = set([])
     for line in file.readlines( ):
          line=line.rstrip('\n') 
          left,right = line.split(":")
          element = right.split(",")
          if left == "S":
               temp = states(temp,element)
               str1 = temp.pop()
     return str1


def getAccept(file):
     temp = []
     for line in file.readlines( ):
          line=line.rstrip('\n') 
          left,right = line.split(":")
          element = right.split(",")
          if left == "F":
               temp = accept(temp,element)
     return temp  
     
def accept(temp,element):
     for a in element:
        temp.append(a)
     return temp

def moveT(file):
     temp = set([])
     for line in file.readlines( ):
          line=line.rstrip('\n') 
          left,right = line.split(":")
          element = right.split(",")
          if left == "M":
               temp = moves(temp,element)
     return temp 
     
def moves(temp,element):
     for a in element:
        temp.add(a)
     return temp

def moveN(file):
     temp = set([])
     for line in file.readlines( ):
          line=line.rstrip('\n') 
          left,right = line.split(":")
          element = right.split(",")
          if left == "M":
               temp = movesN(temp,element)
     return temp 
     
def movesN(temp,element):
     for a in element:
         if a != "e":
              temp.add(a)
     return temp

location2 = 'other4.txt'
b_file = open(location2,'r')
test = getStates(open(location2,'r'))
b_file.close()
   
location='transitionTable.txt'
a_file=open(location,'r')
delta = collect(open(location,'r'),test)
a_file.close()

c_file = open(location2,'r')
s0 = getStart(open(location2,'r'))
c_file.close()

f_file = open(location2,'r')
f = getAccept(open(location2,'r'))
c_file.close()

m_file = open(location2,'r')
Sigma = moveN(open(location2,'r'))
m_file.close()


N = NFA(delta, s0, f, ['e'])
print "The predefined NFA is as following:"
print "\n"
print "I \t\tI1 \t\t I0 \t\t\t e"
print "#######################################################################"
N.printNFA(test)
print "#######################################################################"
print("\n")
print "The start state is %s" %(s0)
print "The accept state is %s" %(f)
print("\n\n")


M = convertNFAtoDFA(N,Sigma)
classes = [M.F, [x for x in set(M.delta).difference(set(M.F))]]
dfaAlphabet = Sigma
classes = M.eliminate(classes)
classes = M.classify(classes,dfaAlphabet)
newdelta2 = M.minimizeDFA(classes,dfaAlphabet,Sigma,f)


if __name__ == "__main__":
    import doctest
    doctest.testmod()
