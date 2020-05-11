###############################################################################
#
# Implementation of tightPROVE+ in SageMath
#
# tightPROVE+ is a formal verification tool for the tight register probing  
# security of masked implementations, introduced in https://ia.cr/2020/506
#
# File: graph.sage
# Description: this file contains functions to create and visualize graphs of
# circuits, used to have an insight on where to place refresh gadgets in small
# circuits.
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

##################################################################################
#######################################GRAPH#######################################

def ins_to_graph(L,size=0,highlight=[],dim3=False,root=0):  
#prints the graph of a circuit defined by a list of instruction L, and returns the graph. 
#'highlight' colors user-chosen gadgets
#root defines whether a root node (connected to all inputs) is present or not
    Lg=[['root',[]]] 
    countr=0
    l=len(L)
    nbr=sum([1 for ins in L if ins[0]=='ref'])
    for i in range(len(L)):
        if(L[i][0]=='in'):
            Lg+=[['in',[]]]
            Lg[0][1]+=[i+1-countr]
        elif(L[i][0]=='and'):
            Lg+=[['and',[]]]
            Lg[int(L[i][1])+1][1]+=[i+1-countr]
            Lg[int(L[i][2])+1][1]+=[i+1-countr]
        elif(L[i][0]=='xor'):
            Lg+=[['xor',[]]]
            Lg[int(L[i][1])+1][1]+=[i+1-countr]
            Lg[int(L[i][2])+1][1]+=[i+1-countr]
        elif(L[i][0]=='not'):
            Lg+=[['not',[]]]
            Lg[int(L[i][1])+1][1]+=[i+1-countr] 
        elif(L[i][0]=='ref'):
            countr+=1
            Lg+=[['ref',[]]]
            Lg[int(L[i][1])+1][1]+=[l+countr-nbr]  
     
    d_g={}
    indREF=[]
    indXOR=[]
    indAND=[]
    indNOT=[]
    indIN=[]
    countr=0
    
    #we create a graph from a dictionary d_g
    for i in range(1-root,len(Lg)):
        if(Lg[i][0]=='ref'):
            countr+=1
            d_g[l+countr-nbr]=Lg[i][1]
            indREF+=[l+countr-nbr]
        else:
            d_g[i-countr]=Lg[i][1]
            if(Lg[i][0]=='xor'):
                indXOR+=[i-countr]
            elif(Lg[i][0]=='and'):
                indAND+=[i-countr]
            elif(Lg[i][0]=='not'):
                indNOT+=[i-countr]
            elif(Lg[i][0]=='in'):
                indIN+=[i-countr]

    g=DiGraph(d_g)

    if(root):
        d_vc={
            'black':[0], 
            'lightgreen':[i for i in indIN if i not in highlight], 
            'lightblue':[i for i in indXOR if i not in highlight],
            'lightgrey':[i for i in indAND if i not in highlight],
            'yellow':[i for i in indREF if i not in highlight],
            'brown':[i for i in indNOT if i not in highlight],
            'red':highlight
            }
    else:
        d_vc={
            'lightgreen':[i for i in indIN if i not in highlight], 
            'lightblue':[i for i in indXOR if i not in highlight],
            'lightgrey':[i for i in indAND if i not in highlight],
            'yellow':[i for i in indREF if i not in highlight],
            'brown':[i for i in indNOT if i not in highlight],
            'red':highlight
            }

    if(dim3==False and size>0):
        g.show(pos=g.layout_acyclic(rankdir='down'),
               vertex_colors=d_vc,
               figsize=[size,size],
               vertex_size=100*size,              
              )
    elif(size>0):
        g.show3d(pos=g.layout_acyclic(rankdir='down'),vertex_colors=d_vc)
        
    return g



def circuit_subgraphs(filename,fsize=15,showoption=0,showtime=False):
#creates different subgraphs of the graph generated with a circuit defined in the file named filename
#there are different methods, and time can be printed to see which one is faster
    Ltest=format_code(filename)
    list_instructions = generate_list_ins_from_lines(Ltest) 
    test_circuit = Circuit(list_instructions)
    
    t=time()
    
    PO,IV=test_circuit.generate_pairs_operands()
    ni=test_circuit.nb_inputs
    nr=test_circuit.nb_refresh
    n=ni+len(PO)+nr #nb inputs of flattened circuit

    L=[itob(a|b,n) for (a,b) in PO]

    d_g={}
    for i in range(len(L)):
        d_g['M'+str(i)]=['IN'+str(j) for j in range(n) if L[i][j]==1]
    g=Graph(d_g)

    d_vc={
            'red':['M'+str(i) for i in range(len(PO))], 
            }
    
    if(showoption==0):
        CC=g.connected_components()
        if(showtime):
            print("time : "+str(time()-t))
        return CC

    if(showoption==1):
        CC=g.connected_components()
        g.show(vertex_colors=d_vc,
                figsize=[fsize,fsize],
                vertex_size=13*fsize*fsize)
        if(showtime):
            print("time : "+str(time()-t))
        return CC
    
    if(showoption==2):
        ccs=g.connected_components_subgraphs()
        if(showtime):
            print("time : "+str(time()-t))
        return ccs
        
    if(showoption==3):
        ccs=g.connected_components_subgraphs()
        d_vc={
            'red':['M'+str(i) for i in range(len(PO)) if 'M'+str(i) in ccs[0]], 
            }
        ccs[0].show(vertex_colors=d_vc,
                   figsize=[fsize,fsize],
                   vertex_size=13*fsize*fsize)
        if(showtime):
            print("time : "+str(time()-t))
        return ccs
    
def subgraphs_to_subcircuits(CC,LI,showtime=False,n=0):  
#separates the different subgraphs in CC into subcircuits (different lists of instructions), with the list of instructions LI 
    if(showtime):
        t=time()
    L=[]
    input_list=[]
    mult_list=[]
    for i in range(len(LI)):
        if(LI[i][0]=='in' or LI[i][0]=='and' or LI[i][0]=='ref'):
            input_list+=[i]
        if(LI[i][0]=='and'):
            mult_list+=[i]
    
    for i in range(len(CC)):
        if(showtime):
            print("subcircuit "+str(i)+" out of "+str(len(CC))+"\n")
        L+=[[]]
        I=[int(e[2:]) for e in CC[i] if e[0]=='I']
        M=[int(e[1:]) for e in CC[i] if e[0]=='M']
        
        inputs = sorted(I)
        mults  = sorted(M)
        traduction={input_list[inputs[j]]:j for j in range(len(inputs))}
        for j in range(len(inputs)):
            L[i]+=[['in',str(j)]]
        PILE=[[mult_list[m],LI[mult_list[m]]] for m in mults]
        
        while(PILE!=[]):
            lastelem=PILE[-1]
            if(len(lastelem[1])==2):
                op,a=lastelem[1]
                A=int(a)
                if(A in traduction or op=='in'):
                    traduction[lastelem[0]]=len(L[i])
                    L[i]+=[[op,str(traduction[A])]]
                    PILE.pop()        
                else:
                    PILE+=[[A,LI[A]]]
            else:
                op,a,b=PILE[-1][1]
                A=int(a)
                B=int(b)
                if(A in traduction and B in traduction):
                    traduction[PILE[-1][0]]=len(L[i])
                    L[i]+=[[op,str(traduction[A]),str(traduction[B])]]
                    PILE.pop()
                elif(A not in traduction):
                    PILE+=[[A,LI[A]]]
                else:
                    PILE+=[[B,LI[B]]]   

    if(showtime):
        print(time()-t)
    return L

def ins_to_flatgraph(L,size=0,highlight=[],dim3=False,root=0):
#transforms a list of instructions L into a graph of the corresponding flattened circuit
    l=len(L)+1
    Lg=[['root',[]]]
    countr=0
    nbr=sum([1 for ins in L if ins[0]=='ref'])
    nbm=sum([1 for ins in L if ins[0]=='and'])

    for i in range(len(L)):
        if(L[i][0]=='in'):
            Lg+=[['in',[]]]
            Lg[0][1]+=[i+1-countr]
        elif(L[i][0]=='and'):
            Lg+=[['and',[]]]
            Lg[int(L[i][1])+1][1]+=[i+1-countr]
            Lg[int(L[i][2])+1][1]+=[i+1-countr]
        elif(L[i][0]=='xor'):
            Lg+=[['xor',[]]]
            Lg[int(L[i][1])+1][1]+=[i+1-countr]
            Lg[int(L[i][2])+1][1]+=[i+1-countr]
        elif(L[i][0]=='not'):
            Lg+=[['not',[]]]
            Lg[int(L[i][1])+1][1]+=[i+1-countr] 
        elif(L[i][0]=='ref'):
            countr+=1
            Lg+=[['ref',[]]]
            Lg[int(L[i][1])+1][1]+=[l+nbm+countr-nbr-1]  
    
    for i in range(l):
        if(Lg[i][0]=='and'):
            outvertices=Lg[i][1]
            Lg[i][1]=[]
            Lg+=[['and',outvertices]]
        if(Lg[i][0]=='ref'):
            outvertices=Lg[i][1]
            Lg[i][1]=[]
            Lg+=[['ref',outvertices]]    

    d_g={}
    indREF=[]
    indXOR=[]
    indAND=[]
    indNOT=[]
    indIN=[]
    indSUPP=[]
    countr=0
    for i in range(1-root,len(Lg)):
        if(Lg[i][0]=='ref'):
            countr+=1
            d_g[l+nbm+countr-nbr-1]=Lg[i][1]
            indREF+=[l+nbm+countr-nbr-1]
        else:
            d_g[i-countr]=Lg[i][1]
            if(Lg[i][0]=='xor' and i<l):
                indXOR+=[i-countr]
            elif(Lg[i][0]=='and' and i<l):
                indAND+=[i-countr]
            elif(Lg[i][0]=='not' and i<l):
                indNOT+=[i-countr]
            elif(Lg[i][0]=='in' and i<l):
                indIN+=[i-countr]
            else:
                indSUPP+=[i-countr]
    g=DiGraph(d_g)
    

    if(root):
        d_vc={
            'black':[0], 
            'lightgreen':[i for i in indIN if i not in highlight], 
            'lightblue':[i for i in indXOR if i not in highlight],
            'lightgrey':[i for i in indAND if i not in highlight],
            'yellow':[i for i in indREF if i not in highlight],
            'brown':[i for i in indNOT if i not in highlight],
            'red':highlight
            }
    else:
        d_vc={
            'orange':[i for i in indSUPP if i not in highlight],
            'lightgreen':[i for i in indIN if i not in highlight], 
            'lightblue':[i for i in indXOR if i not in highlight],
            'lightgrey':[i for i in indAND if i not in highlight],
            'yellow':[i for i in indREF if i not in highlight],
            'brown':[i for i in indNOT if i not in highlight],
            'red':highlight
            }


    if(dim3==False and size>0):
        g.show(pos=g.layout_acyclic(rankdir='down'),
               vertex_colors=d_vc,
               figsize=[size,size],
               vertex_size=100*size,

              
              )
    elif(size>0):
        g.show3d(pos=g.layout_acyclic(rankdir='down'),vertex_colors=d_vc)
        
    return g

def findcolor(IV,multlist,G,nbinmult):
#from a list of mults called multlist, prints the 'color' of this list, 
#which is a list of gadgets' index that play a role in the calculation of
#their inputs
    hl=[]
    MG=G.adjacency_matrix()
    things_to_check=[]
    powers=[2^i for i in range(nbinmult)]
    for (i,j) in multlist:
        li=IV.index(i)
        lj=IV.index(j)
        if(li not in hl):
            hl+=[li]
            things_to_check+=[li]
        if(lj not in hl):
            hl+=[lj]
            things_to_check+=[lj]
        
    while(things_to_check!=[]):
        elem=things_to_check.pop()
        if(IV[elem] not in powers):
            for i in range(len(G)):
                if(MG[i][elem]==1):
                    if(i not in hl):
                        hl+=[i]
                        things_to_check+=[i]
    return [h+1 for h in hl]