###############################################################################
#
# Implementation of tightPROVE+ in SageMath
#
# tightPROVE+ is a formal verification tool for the tight register probing  
# security of masked implementations, introduced in https://ia.cr/2020/506
#
# File: TP.sage
# Description: this file contains the original implementation of tightPROVE,
# as well as some modifications allowing for more options such as 
# parallelisation or searching the minimal attack order.
#
# This file is partially based on the previous tightPROVE implementation available at
# https://github.com/CryptoExperts/tightPROVE/blob/master/tightPROVE.sage
#
# Author: Raphaël Wintersdorff
#
#
# Copyright (C) 2019 CryptoExperts
# 
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.
#
###############################################################################

#####################################################################################
####################################tightPROVE#######################################

###############################################################################
###############################################################################
###      OBJECT CLASSES                                                     ###
###############################################################################
###############################################################################


# --------------------------------------------------------------------------- #
#      CLASSES CIRCUIT                                                        #
#        * Variables: opA, opB (Boolean vectors)                              #
# --------------------------------------------------------------------------- #

def generate_list_ins_from_file(circuit_file):
    list_instructions = []
    splitlines=load_file(circuit_file)
    for args in splitlines:
        if len(args) == 2: list_instructions.append(Instruction(str(args[0]), int(args[1]), int(0)))
        elif len(args) == 3: list_instructions.append(Instruction(str(args[0]), int(args[1]), int(args[2])))
        else: raise Exception('Bad instruction')
    return list_instructions

def generate_list_ins_from_lines(splitlines):
    list_instructions = []
    for args in splitlines:
        if len(args) == 2: list_instructions.append(Instruction(str(args[0]), int(args[1]), int(0)))
        elif len(args) == 3: list_instructions.append(Instruction(str(args[0]), int(args[1]), int(args[2])))
        else: raise Exception('Bad instruction')
    return list_instructions

class Instruction:
    def __init__(self, ins, opA, opB):
        wrong_type = 'Wrong intruction type: only xor|and|refresh allowed'
        assert(ins in ['xor','not','and','or','ref','in','out']), wrong_type
        self.ins = ins
        self.opA = opA
        self.opB = opB
        
    def __repr__(self):
        return self.ins+" "+str(self.opA)+' '+str(self.opB)

    def __str__(self):
        return self.ins+" "+str(self.opA)+' '+str(self.opB)
    
def eval_all(filename,ltr=True,hexa=False):
    try:
        instr=generate_list_ins_from_file(filename)
    except:
        instr=generate_list_ins_from_lines(format_code(filename))
    c=Circuit(instr)
    L=[]
    for i in range(2**c.nb_inputs):
        if(ltr):
            L+=[c.evaluate(Integer(i),hexa)]
        else:
            L+=[c.evaluate2(Integer(i),hexa)]
    return L

class Circuit:
    def __init__(self, instructions):
        assert (type(instructions) == list), 'Instructions must be a list'
        self.instructions = instructions
        self.nb_inputs = sum([ins.ins == 'in' for ins in instructions])
        self.nb_outputs = sum([ins.ins == 'out' for ins in instructions])
        self.nb_refresh = sum([ins.ins == 'ref' for ins in instructions])
        self.nb_add = sum([ins.ins == 'xor' for ins in instructions])
        self.nb_mult = sum([(ins.ins == 'and' or ins.ins == 'or') for ins in instructions])

        # METHOD 'evaluate'
        # Evaluates the circuit for two types of input: - 'input' is an Integer and the circuit is evaluated on bits
        #                                               - 'input' is a list and the circuit is evaluated on bitslice registers                                
        # Returns the evaluation of the circuit on 'input'
        
    def evaluate(self, input, hexa=False):
        if type(input) == Integer:
            invar = map(GF(2),input.bits()) 
            invar += [GF(2)(0)]*(self.nb_inputs-input.nbits())
        elif type(input) == list:
            assert (len(input) == self.nb_inputs), 'Bad number of inputs'
            invar = map(GF(2),input)
        else:
            raise Exception('Bad input type')
        iv = [None]*len(self.instructions)
        outvar = []
        #pc = self.nb_inputs-1
        pc=0
        for ins in self.instructions:
            if   ins.ins == 'in' : iv[pc] = invar[0]; del(invar[0])
            elif ins.ins == 'xor': iv[pc] = iv[ins.opA] + iv[ins.opB]
            elif ins.ins == 'and': iv[pc] = iv[ins.opA] * iv[ins.opB]
            elif ins.ins == 'or': iv[pc] = iv[ins.opA] * iv[ins.opB] + iv[ins.opA] + iv[ins.opB]
            elif ins.ins == 'not': iv[pc] = iv[ins.opA] + GF(2)(1)
            elif ins.ins == 'ref': iv[pc] = iv[ins.opA]
            elif ins.ins == 'out': iv[pc] = iv[ins.opA]; outvar.append(iv[pc])
            else: raise Exception('Bad instruction')
            pc += 1
        if type(input) == Integer and hexa==False:
            return sum([Integer(outvar[i])*2^i for i in range(0,len(outvar))])
        elif type(input) == Integer:
            s=sum([Integer(outvar[i])*2^i for i in range(self.nb_outputs)])
            return s.hex()
        else: # type(input) == list
            return map(int,outvar)     
        
    def evaluate2(self, inputs, hexa=False):
        if type(inputs) == Integer:
            invar = map(GF(2),itob_rev(inputs,self.nb_inputs))
        elif type(inputs) == list:
            assert (len(inputs) == self.nb_inputs), 'Bad number of inputs'
            invar = map(GF(2),inputs)
        else:
            raise Exception('Bad input type')
        iv = [None]*len(self.instructions)
        outvar = []
        pc=0
        for ins in self.instructions:
            if   ins.ins == 'in' : iv[pc] = invar[0]; del(invar[0])
            elif ins.ins == 'xor': iv[pc] = iv[ins.opA] + iv[ins.opB]
            elif ins.ins == 'and': iv[pc] = iv[ins.opA] * iv[ins.opB]
            elif ins.ins == 'or': iv[pc] = iv[ins.opA] * iv[ins.opB] + iv[ins.opA] + iv[ins.opB]
            elif ins.ins == 'not': iv[pc] = iv[ins.opA] + GF(2)(1)
            elif ins.ins == 'ref': iv[pc] = iv[ins.opA]
            elif ins.ins == 'out': iv[pc] = iv[ins.opA]; outvar.append(iv[pc])
            else: raise Exception('Bad instruction')
            pc += 1

        if type(inputs) == Integer and hexa==False:
            return sum([Integer(outvar[i])*2^(self.nb_outputs-1-i) for i in range(self.nb_outputs)])
        elif type(inputs) == Integer:
            s=sum([Integer(outvar[i])*2^(self.nb_outputs-1-i) for i in range(self.nb_outputs)])
            return s.hex()
        else: # type(inputs) == list
            return map(int,outvar)   
        


        # METHOD 'generate_mult_set'
        # Transforms the circuit into a flattened circuit
        # Returns the list of pairs of operands that are inputs to multiplication in the flattened circuit

    def generate_pairs_operands(self):
        iv = [None]*(len(self.instructions)-self.nb_outputs)
        outlist = []
        pc = 0
        no_i=0
        for ins in self.instructions:
            if   ins.ins == 'in' : iv[pc] = 2**no_i; no_i += 1
            elif ins.ins == 'xor': iv[pc] = iv[ins.opA] ^^ iv[ins.opB]
            elif ins.ins == 'and': iv[pc] = 2**no_i; no_i += 1; outlist.append([iv[ins.opA],iv[ins.opB]]);
            elif ins.ins == 'or': iv[pc] = 2**no_i; no_i += 1; outlist.append([iv[ins.opA],iv[ins.opB]]);
            elif ins.ins == 'not': iv[pc] = iv[ins.opA]
            elif ins.ins == 'ref': iv[pc] = 2**no_i; no_i += 1
            elif ins.ins == 'out': continue
            else: raise Exception('Bad instruction')
            pc += 1
        return outlist,iv
                

# --------------------------------------------------------------------------- #
#      CLASS MULT                                                             #
#        * Variables: opA, opB (Boolean vectors)                              #
# --------------------------------------------------------------------------- #

def boolvec_to_int(v):
    try:
        l = len(v)
        return sum([int(v[i])*2^i for i in range(0,l)])
    except:
        return v

def boolvec_list_to_int_list(l):
    return [boolvec_to_int(v) for v in l]

class Mult:

    def __init__(self, opA, opB):
        if (len(opA) != len(opB)): 
            raise Exception('Operands must have the same length!')
        if (opA == opB).all(): 
            raise Exception('Operands must be different!')
        self.opA = opA
        self.opB = opB

    def __getitem__(self, i):
        if i!=0 and i!=1: 
            raise Exception('Operand index out of range')
        if i==0: return self.opA
        if i==1: return self.opB

    def __repr__(self):
        return '(' + str(boolvec_to_int(self.opA)) + ',' + str(boolvec_to_int(self.opB)) +')'

    def __str__(self):
        return '(' + str(boolvec_to_int(self.opA)) + ',' + str(boolvec_to_int(self.opB)) +')'

# --------------------------------------------------------------------------- #
#      CLASS SET                                                              #
#        * Variables: mult_list (list of Mult objects)                        #
# --------------------------------------------------------------------------- #

class MultSet:

    def __init__(self, mult_list):
        self.mult_list = mult_list

    def __getitem__(self, i):
        return self.mult_list[i]

    def size(self):
        return len(self.mult_list)

    # METHOD 'all_operands'
    #   - return the list of all operands (w/o duplicates)

    def all_operands(self):
        list_operands = [op for m in self.mult_list for op in [m[0], m[1]]]
        return delete_duplicates(list_operands)

    # METHOD 'iterate'
    # Iterate the attack search method for operand 'op' and (current) span 'span'
    # Return two sets of mult and a list of operands (Boolean vectors):
    #    - set of mults with one operand matching 'op' + 'span'
    #    - set of mults with no operand matching 'op' + 'span' (complement of the first set)
    #    - list of co-operands of operands matching 'op' + 'span'

    def iterate(self,op,span=[],order=False):

        match_mults = []
        mismatch_mults = []
        co_operand_list = []
        
        tested_op=[]
        tested_sol=[]
        
        for mult in self.mult_list:

            if span == []:
                if(mult.opA == op).all():
                    match_mults.append([mult])
                    co_operand_list.append(mult.opB)
                elif(mult.opB == op).all():
                    match_mults.append([mult])
                    co_operand_list.append(mult.opA)
                else:
                    mismatch_mults.append(mult)              

            else: # span != []:
                if(order):
                    LA=find_all_sol(span,[(mult.opA[i]^^op[i]) for i in range(len(op))])
                    LB=find_all_sol(span,[(mult.opB[i]^^op[i]) for i in range(len(op))])
                else:
                    LA=find_one_sol(span,[(mult.opA[i]^^op[i]) for i in range(len(op))])
                    if(LA==None):
                        LB=find_one_sol(span,[(mult.opB[i]^^op[i]) for i in range(len(op))])
                 
                if((order and LA==[] and LB==[]) or ((not order) and LA==None and LB==None)):
                    mismatch_mults.append(mult)
                else:
                    if(order):
                        if(LA!=[]):
                            match_mults.append([mult]+LA)
                            co_operand_list.append(mult.opB)
                        if(LB!=[]):
                            match_mults.append([mult]+LB)
                            co_operand_list.append(mult.opA)
                    else:
                        if(LA!=None):
                            match_mults.append(mult)
                            co_operand_list.append(mult.opB)
                        else:
                            match_mults.append(mult)
                            co_operand_list.append(mult.opA)

        return MultSet(match_mults), MultSet(mismatch_mults), co_operand_list

    def __repr__(self):
        return '[' + ','.join([str(m) for m in self.mult_list]) + ']'

    def __str__(self):
        return '[' + ','.join([str(m) for m in self.mult_list]) + ']'


###############################################################################
###############################################################################
###      SUBFUNCTIONS                                                       ###
###############################################################################
###############################################################################

# --------------------------------------------------------------------------- #
#         IMPORT SUBFUNCTIONS                                                 #
# --------------------------------------------------------------------------- #
    
    
def import_mult(pair_list):
    m = max(map(max,pair_list))  #maximum number among all pairs of OPs
    dim = m.nbits()
    list_mult = []

    for (a,b) in pair_list:
        opA = itob2(a,dim)
        opB = itob2(b,dim)
        list_mult+=[Mult(opA,opB)]

    return MultSet(list_mult)

def itob_rev(x,d):   #gives binary repr of x with size d
    L=[]
    for i in range(d):
        L=[x%2]+L
        x=x//2
    return L

def itob(x,d):   #gives binary repr of x with size d
    L=[]
    for i in range(d):
        L+=[x%2]
        x=x//2
    return L

def itob2(x,d):   #gives binary repr of x with size d using numpy arrays
    return np.array([x>>i&1 for i in range(d)] ,bool)

###############################################################################
###############################################################################
###      MAIN FUNCTIONS                                                    ###
###############################################################################
###############################################################################


# --------------------------------------------------------------------------- #
#         SEARCH ATTACK                                                       #
# --------------------------------------------------------------------------- #

def search_comb(ms,showtime,comb):
        G, O, U = [], [], []  
        span = []
        remaining_mults = copy(ms)
        
        tcomb=time()
        while(1):
            match_set, mismatch_set, co_operand_list = remaining_mults.iterate(comb,span)
            
            span += co_operand_list
            
            Lcomb=find_one_sol(span,comb)
            if(Lcomb!=None):
                print(time()-tcomb)
                return ['Attack found: %s in span %s'%(boolvec_to_int(comb), boolvec_list_to_int_list(span))]

            # Test stop condition 1
            
            if match_set.size() == 0: # M[i] empty => no attack on comb
                #print '=> NO ATTACK (G%s = G%s)'%(len(G),len(G)-1)
                if(showtime):print(time()-tcomb)
                return []
            
            # Test stop condition 2

            if remaining_mults.size() == 0: # no mult remaining
                if(showtime):print(time()-tcomb)
                return []

            # Remaining mults 

            remaining_mults = mismatch_set
            


def search_attack(mult_set,verbose=False,showtime=False,order=False,multiproc=False,approx=0):

    # --------------------------------------------------------------- #
    # 'mult_set' is the set of multiplications (MultSet object)       #
    # 'comb' is the target combination (if None, try all)             #
    # --------------------------------------------------------------- #

    attacks=[]
    tottime=time()
    attacks=[]
    
    if(multiproc):
        func = partial(search_comb, mult_set,showtime)
        pool = mp.Pool(processes=mp.cpu_count())
        all_A = pool.map(func, mult_set.all_operands())
        pool.close()
        if(showtime):
            print("total time : "+str(time()-tottime)+"s\n")   
        for A in all_A:
            attacks+=A
    
    else:  
        #some variables that check how much time each action takes
        t_iterate=0  
        t_GOU=0
        t_print=0
    
        ttest=time()
        count=0
        nbop=len(mult_set.all_operands())
        for comb in mult_set.all_operands():
            poa=0 #previous order of attack initialized to 0

            if(verbose or order):
                print ('--------------------------------------------------------')
                print ('comb = ', boolvec_to_int(comb))

            G, O, U = [], [], []  
            span = []
            remaining_mults = mult_set   
            
            step=1
            approx3=False

            while(1):
                ti=time()
                match_set, mismatch_set, co_operand_list = remaining_mults.iterate(comb,span,order)
                tf=time()
                t_iterate+=tf-ti
            
                ti=time()

                G+=(copy(match_set))
                span+=co_operand_list
            
                tf=time()
                t_GOU+=tf-ti

                ti=time()

                if(order):
                    Lcomb=find_all_sol(span,comb)
                else:
                    Lcomb=find_one_sol(span,comb)

                possible_attack='Attack found: '+str(boolvec_to_int(comb))+' in span ['
                bltil=boolvec_list_to_int_list(span)
                for i in range(len(bltil)-1):
                    possible_attack+=str(bltil[i])
                    possible_attack+=', '
                possible_attack+=str(bltil[-1])
                possible_attack+=']'
                
                if(((order and Lcomb!=[]) or ((not order) and Lcomb!=None)) and possible_attack not in attacks):
                    intspan=boolvec_list_to_int_list(span)
                    if(order):Lcomb=reduce_sols(Lcomb,intspan,poa)
                    if (verbose): 
                        print ('=> ATTACK')
                        if(verbose==2):
                            print ('   G:', G)
                            print ('   span : ', intspan)
                            print ('   sols : ', Lcomb)
                    attacks+=[possible_attack]
                    
                    if(order and (not(approx==3 and approx3))):
                        poa=attack_order(transform_G(G),Lcomb,intspan,boolvec_to_int(comb),approx)
                        approx3=True
                    if(order):
                        print("order of attack : "+str(poa))
                    if(not order):
                        break

                # Test stop condition 1
            
                if match_set.size() == 0: # M[i] empty => no attack on comb
                    if (verbose): 
                        if(attacks==[]):
                            print ('=> NO ATTACK (G%s = G%s)'%(step,step-1))
                        else:
                            print ('=> NO NEW ATTACK (G%s = G%s)'%(step,step-1))
                        if(verbose==2):
                            print ('   G:', G)
                            print ('   O:', boolvec_list_to_int_list(span))
                    break 
            
                # Test stop condition 2

                if remaining_mults.size() == 0: # no mult remaining
                    if (verbose): 
                        if(attacks==[]):
                            print ('=> NO ATTACK (G%s = G%s)'%(step,step-1))
                        else:
                            print ('=> NO NEW ATTACK (G%s = G%s)'%(step,step-1))
                        if(verbose==2):
                            print ('   G:', G)
                            print ('   O:', boolvec_list_to_int_list(span))
                    break 

                # Remaining mults 

                remaining_mults = copy(mismatch_set)
            
                tf=time()
                t_print+=tf-ti
                step+=1
            
            if verbose: print ('--------------------------------------------------------')
            if(showtime):
                count+=1
                print("var "+str(count)+" out of "+str(nbop)) 
                print("\t time : "+str(time()-ttest))
                ttest=time()
        
        if(showtime):
            print("iterate: "+str(t_iterate)+"s\n")  
            print("create GOU + span: "+str(t_GOU)+"s\n") 
            print("print attack: "+str(t_print)+"s\n") 
    
    return attacks