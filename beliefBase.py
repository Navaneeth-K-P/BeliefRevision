from sympy.logic.boolalg import to_cnf, And, Or, Not, Implies, Equivalent
from sympy.abc import A, B, D
from typing import List
from sympy import *
from copy import deepcopy
from collections import namedtuple



class Belief_Base:

    def __init__(self):
        self.beliefBase = [] # Storing beliefs put into the belief base as list of lists
        self.CNF = [] # Storing CNF form of beliefs put into the belief base as list of lists
        self.Sympf = [] # Stores the sympify form of formulas
        self.beliefBaseVariableLimit = 8 # If there are more than 8 variables the flag must be set to True to simplify (default is False)
        
    #def form_to_cnf(self, formula: str) -> None:
    def form_to_cnf(self, formula):
        formula = formula
        cnf = to_cnf(formula)
        #print(self.cnf)
        return cnf 
    

    def query_belief(self, belief): # Checks if a belief is present in the belief base 
        b = sympify(belief)
        if b in self.Sympf:
            print(f"The belief {belief} is present in the belief base")
        elif belief in self.consequence():
            print(f"The belief {belief} is not present in the belief base but it is a consequence of the belief base.")
        elif self.entailement(belief):
            print(f"The belief {belief} is not present in the belief base or in the consequence of the belief base but is entailed by the belief base")
        else:
            print("The belief is not entailed by the belief base")
    

    def add(self, belief, score):
        b_symp = sympify(belief)
        if b_symp not in self.Sympf:
            belief = belief.replace(' ', '')  # Remove whitespace
            #belief = simplify(belief)
            self.beliefBase.append([belief, score])
            sympif = sympify(belief, evaluate=False)
            self.Sympf.append(sympif)
            CNF=self.form_to_cnf(belief)
            self.CNF.append(CNF)
            order = [s[1] for s in self.beliefBase]
            combined = list(zip(order, self.beliefBase,self.CNF, self.Sympf))
            sorted_combined = sorted(combined)
            self.beliefBase = [x[1] for x in sorted_combined]
            self.CNF = [x[2] for x in sorted_combined]
            self.Sympf = [x[3] for x in sorted_combined]

        
        #new_CNF = []
        #for i in range(len(CNF)):
           # if not is_tautology(CNF[i]):
                # Check that the CNF clause is not a tautology, and reduce it before adding
         #   new_CNF.append(CNF[i])
        #self.CNF.append(new_CNF_)
    
    
    def contract(self, new_belief):
        neg_belief = sympify(new_belief)
        # print(neg_belief)

        # if the negation of the 
        if neg_belief in self.Sympf:
            i_neg = self.Sympf.index(neg_belief)
            self.beliefBase.pop(i_neg)
            self.CNF.pop(i_neg)
            self.Sympf.pop(i_neg)

        bb_entry = namedtuple("bb_entry",["belief", "score", "Symf", "CNF"])
        bb_tup = []

        # Create a tuple of all remaining believes
        for belief, Symf, CNF in zip(self.beliefBase, self.Sympf, self.CNF):
            dum = bb_entry(deepcopy(belief[0]),deepcopy(belief[1]),deepcopy(Symf), deepcopy(CNF))
            bb_tup.append(dum)
        # print(bb_tup)


        bb_tup = sorted(bb_tup, key= lambda x:x.score) # A single belief base
        # print(bb_tup)

        bb_temp = [deepcopy(bb_tup)] # Array of belief bases

        while len(bb_temp)>0:
            new = []
            for i in range(0,len(bb_temp)):
                if(self.entailement_contract(bb_temp[i],new_belief)): # Checks if the belief entails the belief base
                    f = bb_temp[i] # belief base
                    for j in range(0,len(f)):
                        t = deepcopy(f)
                        t.pop(j)
                        new.append(t) # the belief base with one entry less is added to new
                else:
                    # return bb_temp[i]
                    # print(bb_temp[i])
                    self.beliefBase = [[a.belief,a.score] for a in bb_temp[i]]
                    self.CNF = [a.CNF for a in bb_temp[i]]
                    self.Sympf = [a.Symf for a in bb_temp[i]]
                    return
            bb_temp = deepcopy(new)


    def expansion(self, new_belief, score):
        self.add(new_belief, score)



    def revision(self, new_belief, score):
        bb_copy = deepcopy(self)
        bb_old = deepcopy(self)
        # print("bb after copy",bb_copy.beliefBase)
        bb_copy.contract("~("+new_belief+")")
        # print("bb after contract",bb_copy.beliefBase)
        bb_copy.expansion(new_belief, score)
        # print("bb after exp",bb_copy.beliefBase)
        # print(bb_copy.beliefBase)
        k1 = bb_copy.check_success(new_belief,score)
        k2 = bb_copy.check_inclusion(new_belief, score,bb_old) 
        k3 = bb_copy.check_vacuity(new_belief,score,bb_old) 
        k4 = bb_copy.check_consistency(new_belief, score)
        # print(k1,k2,k3,k4)
        if (k1 and k2 and k3 and k4):
            # print("Old BB: ", self.beliefBase)
            self.contract("~("+new_belief+")")
            # print("After contraction: ", self.beliefBase)
            self.expansion(new_belief, score)
            # print("After Expansion: ", self.beliefBase)
            print("Revision Done")
        else:
            print("Revision failed")
            


    def check_resolvable(self, c1,c2):
        c1_list = list(c1.args)
        if(len(c1_list)<2):
            c1_list = [c1]

        c2_list = list(c2.args)
        if(len(c2_list)<2):
            c2_list = [c2]

        # print("checking resolvability function: ",c1_list, c2_list)
        for c1_elem in c1_list:
            for c2_elem in c2_list:
                if c1_elem == Not(c2_elem):
                    # print("True")
                    return True
                    
                    
        # print("False")
        return False


    def presolve(self, c1, c2):
        # print("Entered presolve")
        flag = 0
        c1_list = list(c1.args)
        if(len(c1_list)<2):
            c1_list = [c1]

        c2_list = list(c2.args)
        if(len(c2_list)<2):
            c2_list = [c2]
        # print(c1_list, c2_list)
        
        while(self.check_resolvable(c1, c2)):
            for c1_elem in c1_list:
                for c2_elem in c2_list:
                    if c1_elem == Not(c2_elem):
                        c1_list.remove(c1_elem)
                        c2_list.remove(c2_elem)
                        # print(c1_list, c2_list)
                        if(len(c1_list)>0 and len(c1_list)>0):
                            c1 = Or(*c1_list)
                            c2 = Or(*c2_list)
                        else:
                            if len(c1_list) == 0:
                                return(Or(*self.unique(c2_list)))
                            else:
                                return(Or(*self.unique(c1_list)))
                
        combined = Or(*self.unique(c1_list + c2_list))

        return combined
    


    def check_subset(self, new, clause_list):

        for n in new:
            # print(n,clause_list)
            if n not in clause_list:
                # print("False")
                return False
        
        return True


    def entailement_contract(self, bb, alpha):
        CNF = [a.CNF for a in bb]
        # print("CNF: ",CNF)
        KB = And(*CNF)
        # print("KB: ",KB)
        # print(alpha)
        KB_alpha = And(KB, Not(alpha))
        # print("lol", KB_alpha)
        KB_alpha_CNF = self.form_to_cnf(KB_alpha)
        clauses = KB_alpha_CNF.args
        clauses_list = list(clauses)
        
        while True:
            new = []
            for i in range(0,len(clauses_list)):
                for j in range(i+1, len(clauses_list)):
                    # print(f"Checking {clauses_list[i]} and {clauses_list[j]}")
                    if(self.check_resolvable(clauses_list[i], clauses_list[j])):
                        # print(f"Resolving {clauses_list[i]} and {clauses_list[j]}")
                        resolvents = self.presolve(clauses_list[i], clauses_list[j])
                        # print("Result of resolution: ", resolvents)
                        if resolvents == False:
                            return True
                        new.append(resolvents)
                        # print("New after appending: ", new)

            # print(f"Checking if {new} is a subset of {clauses_list}")
            if(self.check_subset(new, clauses_list)):
                # print(f"{new} is a subset of {clauses_list}")
                return False
            # print(f"{new} is not a subset of {clauses_list}")
            clauses_list = self.unique(clauses_list + new)
            # print("clauses+new = ", clauses_list)




    # Alpha should be 
    def entailement(self, alpha):
        KB_alpha = self.conjugation_KB_alpha(alpha) # gives KB ∧ ¬α
        # print("KB_alpha: ", KB_alpha)
        KB_alpha_CNF = self.form_to_cnf(KB_alpha)
        # print("KB_alpha_CNF: ", KB_alpha_CNF)
        clauses = KB_alpha_CNF.args # gives the clauses in KB ∧ ¬α
        # print("clauses: ", clauses)
        clauses_list = list(clauses)
        # print("clauses_list: ", clauses_list)
        
        
        while True:
            new = []
            for i in range(0,len(clauses_list)):
                for j in range(i+1, len(clauses_list)):
                    # print(f"Checking {clauses_list[i]} and {clauses_list[j]}")
                    if(self.check_resolvable(clauses_list[i], clauses_list[j])):
                        # print(f"Resolving {clauses_list[i]} and {clauses_list[j]}")
                        resolvents = self.presolve(clauses_list[i], clauses_list[j])
                        # print("Result of resolution: ", resolvents)
                        if resolvents == False:
                            return True
                        new.append(resolvents)
                        # print("New after appending: ", new)

            # print(f"Checking if {new} is a subset of {clauses_list}")
            if(self.check_subset(new, clauses_list)):
                # print(f"{new} is a subset of {clauses_list}")
                return False
            # print(f"{new} is not a subset of {clauses_list}")
            clauses_list = self.unique(clauses_list + new)
            # print("clauses+new = ", clauses_list)
            




    def conjugation_KB_alpha(self, alpha):
        KB = And(*self.CNF)
        return And(KB, Not(alpha))
    
    def unique(self, a):
        un = list(set(a))
        return un
    

    def consequence(self):
        
        KB_list = deepcopy(self.Sympf)
        flag = True
        # count = 1
        while flag:
            # print("Count: ", count)
            new = []
            for i in range(0,len(KB_list)):
                for j in range(i+1, len(KB_list)):
                    if i == j:
                        continue

                    else:
                        # Hypothetical syllogism
                        # print(KB_list[i][0], KB_list[j][0])
                        a = KB_list[i]
                        b = KB_list[j]
                        # print("Evaluating: ", a,b)
                        # Hypothetical syllogism
                        if isinstance(a, Implies) and isinstance(b, Implies):
                            if(a.args[1] == b.args[0]):
                                # print(a,b)
                                hs = Implies(a.args[0],b.args[1])
                                new.append(hs)
                                # print("Hypothetical syllogism: ", hs )
                                # print(hs)
                            if(a.args[0] == b.args[1]):
                                # print(a,b)
                                hs = Implies(b.args[0],a.args[1])
                                new.append(hs)
                                # print("Hypothetical syllogism: ", hs )


                        # Conjugation
                        c = And(a,b)
                        new.append(c)
                        # print("Conjugation: ", c )

                        # modus ponens
                        if (isinstance(a, Implies) and isinstance(b,Symbol)):
                            if(a.args[0] == b):
                                mp = a.args[1]
                                new.append(mp)
                                # print("modus ponens: ", mp )

                        # modus ponens
                        if(isinstance(b, Implies) and isinstance(a,Symbol)):
                            mp = b.args[1]
                            new.append(mp)
                            # print("modus ponens: ", mp )

                        # disjunctive syllogism
                        if(isinstance(a,Or) and (isinstance(b,Symbol) or isinstance(b,Not))):
                            for k in range(0,len(a.args)):
                                if (a.args[k] == Not(b)):
                                    or_list = list(a.args)
                                    # print(or_list)
                                    # print(Not(b))
                                    or_list.remove(Not(b))
                                    # print(or_list)
                                    ds = Or(*or_list)
                                    # print(ds)
                                    new.append(ds)
                                    # print("disjunctive syllogism: ", ds )

                        
                        # disjunctive syllogism
                        if(isinstance(b,Or) and (isinstance(a,Symbol) or isinstance(a,Not))):
                            for k in range(0,len(b.args)):
                                if (b.args[k] == Not(a)):
                                    or_list = list(b.args)
                                    # print(or_list)
                                    # print(Not(b))
                                    or_list.remove(Not(a))
                                    # print(or_list)
                                    ds = Or(*or_list)
                                    # print(ds)
                                    new.append(ds)

            # print(new)
            # count = count +1
            if self.check_subset(new, KB_list):
                flag = False
            else:
                KB_list = list(set(KB_list + new))
                # print("New  KB list: ", KB_list)

        return(KB_list)
    


    def check_success(self, new_belief,score):
        dum = [new_belief,score]
        if ((dum in self.beliefBase) and (self.form_to_cnf(new_belief) in self.CNF) and (sympify(new_belief) in self.Sympf)):
            print('True. Success postulate is satisfied.')
            return True
        else:
            print('False. Success postulate is NOT satisfied.')
            return False
        
    
    def check_inclusion(self, new_belief, score, old_belief_base):
        old_belief_base.add(new_belief,score)
        result = self.check_subset(self.beliefBase,old_belief_base.beliefBase)
        if result:
            print('True. Inclusion postulate is satisfied.')
            return True
        else:
            print('False. Inclusion postulate is NOT satisfied.')
            return False


    def check_vacuity(self, new_belief,score, old_belief_base):
        if old_belief_base.entailement("~(" + new_belief + ")"):
            print("~(" + new_belief + ") "+"is entailed by the old belief base. Hence, vacuity check is not performed")
            return True
        else:
            # print(old_belief_base.beliefBase,self.beliefBase)
            old_belief_base.add(new_belief, score)
            # print(old_belief_base.beliefBase,self.beliefBase)
            if(old_belief_base.beliefBase == self.beliefBase):
                print('True. Vacuity postulate is satisfied.')
                return True
            else:
                print('False. Vacuity postulate is NOT satisfied.')
                return False
            
    def check_consistency(self, new_belief, score):
        nb_cnf = self.form_to_cnf(new_belief)
        if satisfiable(nb_cnf):
            kb_and = And(*self.CNF)
            if satisfiable(kb_and):
                print('True. Consistency postulate is satisfied.')
                return True
            else:
                print('False. Consistency postulate is NOT satisfied.')
                return False
        else:
            print("The new belief is not satisfiable. Hence consistency check is not done")
            return True
