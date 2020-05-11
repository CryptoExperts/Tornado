###############################################################################
#
# Implementation of tightPROVE+ in SageMath
#
# tightPROVE+ is a formal verification tool for the tight register probing  
# security of masked implementations, introduced in https://ia.cr/2020/506
#
# File: TPV.sage
# Description: this file contains the implementation of tightPROVE+, as well
# as a function solving a linear algebra problem that is crucial for this
# implementation to work properly.
# Author: Raphaël Wintersdorff
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

def solve_register(S,A,O,rs,complete=False):
#if complete=0, returns the intersection between S and (<A> + <O>)
#if complete=1, returns the intersection between S and (<A>* + <O>) or the intersection between S and <O> if A is empty. Also verifies which Linear Combinations(LCs) can be used to obtain each element of the basis of the intersection
    lenS=S.nrows()
    if(lenS==0):
        return []
    
    if(A.rows() and O.rows()):
        m=block_matrix(3,1,[S,A,O])
    else:
        m=copy(S)
        if(A.rows()):
            m=add_block(m,A)
        if(O.rows()):
            m=add_block(m,O)

    m2=m.transpose()  #the columns of m2 are the different coordinates of the operands
    m2=m2.rref()      #calculating the row reduced echelon form of S||A||O, which gives information about the linear combinations that cancel each other out.
                      #equalities between columns stay true in the rref as there are only operations on the lines of the matrix, but these equalities are easier to detect


    bcolumns=[]   #contains the list of pivot indexes (first non null element index in each line)
    for l in m2:
        for i in range(len(l)):
            if l[i]!=0:
                bcolumns+=[i]
                break
    m2=m2.transpose()
    
    BLOCKS=[]
    LCs=[]

    #test which LCs really involve the operand A. Could be used to output how an attack is done without having to remake the calculations (not implemented yet)
    if(complete):
        Aisinvolved=np.array([0 for i in range(m2.nrows())])
        for i in range(m2.nrows()):
            blocks_involved=np.array([0 for t in range(1+1+O.nrows()//rs)])
            test_col=np.array([0 for t in range(S.nrows()+A.nrows()+O.nrows())])
            if i not in bcolumns:
                m2iarray=np.array(m2[i],bool)
                if (m2iarray[:lenS]==1).any():
                    test_col[i]=1
                    if(i<S.nrows()):
                        blocks_involved[0]=1
                    elif(i<S.nrows()+A.nrows()):
                        blocks_involved[1]=1
                        Aisinvolved[i]=1
                    else:
                        blocks_involved[2+(i-S.nrows()-A.nrows())//rs]=1

                    for j in range(len(m2[i])):
                        if(m2[i][j]==1):
                            test_col[bcolumns[j]]=1
                            if(bcolumns[j]<S.nrows()):
                                blocks_involved[0]=1
                            elif(bcolumns[j]<S.nrows()+A.nrows()):
                                blocks_involved[1]=1
                                Aisinvolved[i]=1
                            else:
                                blocks_involved[2+(bcolumns[j]-S.nrows()-A.nrows())//rs]=1

                    BLOCKS+=[blocks_involved]
                    LCs+=[test_col]

        mbasis=matrix([m2[i][:lenS] for i in range(m2.nrows()) if (i not in bcolumns and (Aisinvolved[i] or A.nrows()==0))])
    else:
        mbasis=matrix([m2[i][:lenS] for i in range(m2.nrows()) if i not in bcolumns])
    #mbasis contains the first elements of the non-pivot columns (which represents the columns of S that are needed to get the given column)
    #mbasis has lines that represent how to obtain linear combinations of columns of S that are in the span we are looking for
    

    #we then get a basis of mbasis
    mbasis.echelonize()
    mbasis=matrix([l for l in mbasis if 1 in l])
    
    if(mbasis.nrows()):
        return mbasis*m[:lenS],BLOCKS,LCs     #mbasis*m[:lenS] then gives us the actual values of basis vectors of the span we are looking for
    else:
        return [],[],[]


class Branch:
    def __init__(self,name,S,G,O):
        self.name = name
        self.parents=[]
        self.children=[]
        
        self.S=S  #each element is part of a row reduced basis (we could also add the LC that makes this element from the original S)
        self.G=G
        self.O=O
        
    def add_child(self,new_intersection,operand,multlist,op_list):   #for the operand A such that the intersection between S and (<A> + <O>) is not null, adds a node to the graph
        newO=copy(self.O)
        newG=copy(self.G)
        for mult in multlist:
            if(mult.ops[0]==operand):
                newG+=[mult]
                if(newO.rows()):
                    newO=add_block(newO,mult.ops[1].LC)   #here, O is a concatenation of blocks and not a set of blocks
                else:
                    newO=mult.ops[1].LC

            elif(mult.ops[1]==operand):
                newG+=[MultV(mult.line,mult.name,[mult.ops[1],mult.ops[0]])]
                if(newO.rows()):
                    newO=add_block(newO,mult.ops[0].LC)
                else:
                    newO=mult.ops[0].LC

        if self.name=="":
            newname=str(op_list.index(operand))
        else:
            newname=self.name+'-'+str(op_list.index(operand))
        child=Branch(newname,new_intersection,newG,newO)
        child.parents+=[self]
        self.children+=[child]
        
    def __repr__(self):
        return self.name
        
        
def attack_operand(W,multlist,op_list,countop,rs,verbose=0,firstattack=0,start=1,complete=0,showtime=0,returnG=0):
#for an operand W, creates the graph and finds attacks on that operand (intermediate function)
#returns lists of LCs of inputs that can be retrieved with an attack, or the corresponding Gi if returnG is True

    t=time()
    Wlistattacks=[]
    
    attacked=False
    if(verbose==1):
        sys.stdout.write("\t progress: %d/%d   \r" % (countop,len(op_list)) )
        sys.stdout.flush()
    if(verbose>=2):print ("operand : "+str(W))

    #creating a fictive Root node (layer 0), containing nothing, and adds a first child (layer 1)
    Root=Branch("",matrix([]),[],matrix([]))
    S1=find_basis(W.LC)                       #S1 is <W>
    Root.add_child(S1,W,multlist,op_list)     #creation of the sole node of layer 1, with operand W (G contains all the multiplications with W as an operand)
    branchlist=[[Root.children[0]]]           #branchlist contains a list of layers, which itself is a list of Branches
    										  #branchlist[0][0] contains all the informations about the graph, so we could return that 
    										  #but right now, it returns the list of the subspaces of <W> that can be attacked

    
    while(1):
        to_add_branchlist=[]
        for b in branchlist[-1]:  #from the last layer, create a new one
            solS,BLOCKS,LCs=solve_register(b.S,matrix([]),b.O,rs,complete=complete)
            if(solS!=[]):
                attacked=True
                if (solS not in Wlistattacks) and returnG==0:
                	Wlistattacks+=[solS]
                elif(returnG==1):
                    Wlistattacks+=[b.G]

                if(verbose>=2):
                    print ("attack on operand "+str(W)+"(dimension : "+str(solS.nrows())+")")
                    print ("step i = "+str(str(b).count('-')+1))
                if(verbose>=3):
                    print ("G : ")
                    for m in b.G:
                        print (m)
                if(firstattack):
                    if(returnG==0):
                        return [solS]
                    else:
                        return b.G
                else:
                    if(complete):
                        to_add_branchlist+=[b]    #if complete is True, a Branch that contains an attack will still be considered when creating new Branches
                    else:
                        pass
            else:
                to_add_branchlist+=[b]
        branchlist+=[to_add_branchlist]
        

        to_add_branchlist=[]
        for b in branchlist[-1]:
            if(verbose>=4):print ("\t branch : ",b)
            for A in op_list:
                if(verbose>=4):print ("\t \t operand : "+str(A))

                if(A not in [m.ops[0] for m in b.G]+[m.ops[1] for m in b.G]):    #no need to test free operands as we already test if S intersects with Oi before
                    newS,BLOCKS,LCs=solve_register(b.S,A.LC,b.O,rs,complete=complete)
                    if(newS!=[]):
                        b.add_child(newS,A,multlist,op_list)
                        bp=b.children[-1]
                        to_add_branchlist+=[bp]

        if(to_add_branchlist==[]):
            if(verbose>=4):
                if(attacked==False):
                    print ('no attack on operand '+str(W)+'\n')
                else:
                    print ('no new attack on operand '+str(W)+'\n')
            if(showtime>=2):
                print ("operand checked in %f s."%(time()-t))
            return Wlistattacks
        branchlist+=[to_add_branchlist]
        if(verbose>=3):print(str(len(to_add_branchlist))+" new branches to examine \n")
            


def search_attack_register(multlist,op_list,rs,verbose=0,showtime=0,firstattack=0,start=1,complete=0,multiproc=0,returnG=0):
    listattacks=[]

    countop=start
    
    if(multiproc):
        func=partial(attack_operand, multlist=multlist,op_list=op_list,countop=countop,rs=rs,verbose=0,showtime=showtime,firstattack=firstattack,start=start,complete=complete,returnG=returnG)
        pool = mp.Pool(processes=mp.cpu_count())
        all_attacks = pool.map(func, op_list[start-1:])
        pool.close()
        pool.join()
        for Wattacks in all_attacks:
            for attack in Wattacks:
                listattacks+=[attack]
    
    
    else:
        for W in op_list[start-1:]:
            t=time()
            Wlistattacks=attack_operand(W,multlist,op_list,countop,rs,verbose=verbose,firstattack=firstattack,start=start,complete=complete,showtime=showtime,returnG=returnG)
            countop+=1
            if(firstattack and Wlistattacks!=[]):
                return Wlistattacks
            for attack in Wlistattacks:
                listattacks+=[attack]

    return listattacks


def simple_search_register(filename,verbose=0,showtime=0,complete=0,multiproc=0,firstattack=0,start=1,returnG=0):
#searches for attacks for a given description of a circuit in a file called filename
#verbose=0 : prints nothing about the progression
#verbose=1 : prints the progress for the flatten operation, the number of multiplications, inputs and refresh, the nuber of operands to check, and the progression of the algorithm
#verbose=2 : prints which operands we create a graph of, and whether there is an attack (when there is one). Also gives the dimension of the attack
#verbose=3 : prints G when an attack is found
#verbose=4 : prints all the operands that are considered when trying to add a Branch
#showtime=1 : prints the time taken for the flatten operation, transforming arrays into boolean matrices, and the time taken for the search
#showtime=2 : prints the time it takes to check each operand
#multiproc=1 : allows the use of multuprocessing. makes verbose 1 maximum
#firstattack=1 : stops the search at the first attack found
#complete=1 : allows the algorithm to continue searching for attacks on Branches that already contain an attack
#start : allows the user to choose to skip some of theoperands to check. start=1 checks everything from the 1st operand to the last 
#returnG=1 : returns the Gi sets instead of Si when an attack is found
    t1=time()
    C=flatten(filename,progress=verbose)
    t2=time()
    if(showtime):print("flatten : "+str(t2-t1))
        
    op_list=multlist_to_oplist(C.multlist)
    if(verbose>=1):
        print(str(C.nbm)+" mults , "+str(C.nbi)+" inputs , "+str(C.nbr)+" refresh.")
        print(str(len(op_list))+" operands to check")
        
    for op in op_list:
        op.LC=matrix(GF(2),op.LC)
    
    t3=time()   
    if(showtime):print("define matrix : "+str(t3-t2))
    
    S=search_attack_register(C.multlist,op_list,C.rs,verbose=verbose,showtime=showtime,firstattack=firstattack,start=start,complete=complete,multiproc=multiproc,returnG=returnG)
    t4=time()
    if(showtime):print("search attack : "+str(t4-t3))
    return S        
        
        
        