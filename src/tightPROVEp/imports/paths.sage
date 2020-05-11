###############################################################################
#
# Implementation of tightPROVE+ in SageMath
#
# tightPROVE+ is a formal verification tool for the tight register probing  
# security of masked implementations, introduced in https://ia.cr/2020/506
#
# File: paths.sage
# Description: this file contains functions used to compute the minimal 
# attack order given the results of tightPROVE, in the bit-probing model.
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
#######################################PATHS#######################################

def extend_possibilities(mult,G,span):
    posslist=[]
    #if(len(mult)==1):
    #    return [[mult]]
    for i in range(1,len(mult)):
        L=[]
        try:
            l=len(mult[i])
            for j in range(l):
                if(mult[i][j]==1):
                    Llist=[]
                    for k in range(len(span)):
                        if(span[k]==span[j]):
                            Llist+=[G[k]]
                    L+=[Llist]
            posslist+=crossproduct(L)
        except:
            Llist=[]
            for k in range(len(span)):
                if(span[k]==span[0]):
                    Llist+=[G[k]]
            L+=[Llist]
            posslist+=crossproduct(L)
    return posslist

def crossproduct(L): #from a list of lists L, gives the cartesian product of these lists
    L=[l for l in L if l!=[]]
    if L==[[]]:
        return [[]]
    l=len(L)
    lens=[len(L[i])-1 for i in range(l)]
    var=[0 for i in range(l)]
    #print var
    #print lens
    CP=[]
    while(var!=lens):
        try:
            CP+=[[L[i][var[i]] for i in range(l) if lens[i]>=0]]
        except:
            print (L,var)
            raise Exception()
        var[-1]+=1
        pos=-1
        while(var[pos]>lens[pos]):
            var[pos]=0
            var[pos-1]+=1
            pos-=1
    CP+=[[L[i][var[i]] for i in range(l)]]
    return CP

def add_to_lists(elem,L):
    return [[elem]+lists for lists in L]

#The goal is to create a graph where each node represents a multiplication that can be used to make an attack. 
#Each child is a different way to get an operand, and they can be made of multiple nodes (when multiple multiplications are needed to get that operand) 
#We call F the recursive function that creates lists from a node : 
#the multiplication of the input node is the first element of the lists, and the other elements are, for each child (group of nodes), the cartesian product of F applied to all th nodes in the group.



class soloNode:
    def __init__(self,mult):
        self.mult=mult
        self.done=False
        self.children=[]
        self.parents=[]
    
    def __repr__(self):
        return '('+str(self.mult[0][0])+','+str(self.mult[0][1])+')'
    def __str__(self):
        return '('+str(self.mult[0][0])+','+str(self.mult[0][1])+')'
    
    def ancestry(self):
        node=self
        ancestors=[]
        while(node.parents!=[]):
            ancestors+=[node.parents[0].mult]
            node=node.parents[0]
        return ancestors
    
    def delete_ancestry(self):
        brothers = self.parents[0].children
        cpb=copy(brothers)
        for t in cpb:
            for n in t.listnode:
                if n.mult==self.mult:
                    brothers.remove(t)

        if(self.parents[0].children==[]):
            self.parents[0].delete_ancestry()

class groupNode:
    def __init__(self,listnode):
        self.listnode=listnode
        self.done=False

    def __repr__(self):
        return '[' + ','.join([str(node) for node in self.listnode]) + ']'
    
    def show_lineage(self,depth=0):
        for node in self.listnode:
            s=""
            for i in range(depth):
                s+="\t"
            print (s+str(node))
            for c in node.children:
                c.show_lineage(depth+1)
                print ("")

    def add_nodes(self,G,span,leaves=[],already_found=[]):
        #print 'h'
        #print already_found
        for node in self.listnode:
            #try: 
            #    multaf=[already_found[i].mult for i in range(len(already_found))]
            #    ind=multaf.index(node.mult)
            #    node=already_found[ind]
            #    print 'hhhh'
            #    print already_found[ind].children
            #    print node.children
            #    print 'hhhh'
            #    continue
            #except:   
                #print(node)
                
                
                listposs=extend_possibilities(node.mult,G,span)
                #print 'mult : ',node.mult,'poss',listposs
                for poss in listposs:
                #for poss in node.mult[1:]:
                    L=[]
                    for m in poss:
                        n=soloNode(m)
                        n.parents+=[node]
                        L+=[n]
                        if m in n.ancestry():
                            #print m,"  ztz ",n.parents[0].children,"zzz",n.parents[0].parents[0].children
                            L=[]
                            break
                    if(L!=[]):
                        newnode=groupNode(L)
                        multchild=[n.mult for n in newnode.listnode]
                        listmultchild=[[n.mult for n in GN.listnode] for GN in node.children]
                        if(multchild not in listmultchild):
                            node.children+=[newnode]
                        #print(newnode)
                        leaves=newnode.add_nodes(G,span,leaves,already_found)
                
                        #listgroup+=[newnode]
                already_found+=[node]
                if(node.children==[]):
                    leaves+=[node]
                    #print 'leaf',node,leaves
        
        return leaves
    
def createpaths(node,listmult=[],pathlist=[]):
    try: 
        ind=listmult.index(node.mult[0])
        return pathlist[ind]
    except:
        L=[]
        for child in node.children:
            pathsofchild=[]
            for n in child.listnode:
                P=createpaths(n,listmult,pathlist)
                pathsofchild+=[P]
            L+=add_to_lists(node.mult[0],crossproduct(pathsofchild))
        listmult+=node.mult[0]
        pathlist+=[L]
        
        return L
    
    
def all_paths(G,span,sols):
    
    initiallm=[m[0] for m in G if len(m)==1]
    initialpl=[[m[0]] for m in G if len(m)==1]
    
    PATHS=[]
    
    for sol in sols:
        root=nodegraph(G,span,sol)
        solpath=crossproduct([createpaths(n,initiallm,initialpl) for n in root.listnode])
        PATHS+=[solpath]
        
    return PATHS

def paths_to_listmult(PATHS):
    L=[]
    for P in PATHS:
        for p in P:
            cp=copy(p)
            addtoL=[]
            while(cp!=[]):
                while(type(cp[0])==list):
                    for elem in cp[0]:
                        cp+=[elem]
                    cp.pop(0)
                addtoL+=[cp.pop(0)]
            L+=[addtoL]
        
    return L

def lists_to_sets(L):
    #return [set(l) for l in L]
    sets=[]
    for l in L:
        s=set(l)
        if s not in sets:
            sets+=[s]
    return sets

def nodegraph(G,span,sol):
    L=[]
    for i in range(len(span)):
        if sol[i]:
            gi=soloNode(G[i])
            L+=[gi]
    root=groupNode(L)
    leaves=root.add_nodes(G,span,[],[])
    actual_leaves=[m for m in G if len(m)==1]
    
    for l in leaves:
        if l.mult not in actual_leaves:
            l.delete_ancestry()
    
    return root

def transform_G(G):
    for i in range(len(G)):
        a=boolvec_to_int(G[i][0][0])
        b=boolvec_to_int(G[i][0][1])
        G[i]=[(a,b)]+G[i][1:]
    return G

def augment_G(G,intspan,intcomb):
    newG=[]
    #G=transform_G(G)
    m = max(intspan)
    dim = m.nbits()
    binspan=[itob2(intspan[i],dim) for i in range(len(intspan))]
    bincomb=itob2(intcomb,dim)
    for i in range(len(G)):
        if len(G[i])==1:
            newG+=[G[i]]
        else:
            op=G[i][0][0]
            #print op,intspan[i]
            if op==intspan[i]:
                op=G[i][0][1]
            binop=itob2(op,dim)
            newG+=[[G[i][0]]+reduce_sols(find_all_sol(binspan,[(bincomb[i]^^binop[i]) for i in range(len(binop))]),intspan)]
    
    return newG

def orderfromaugmentedpaths(G,span,sols,comb):
    G=augment_G(G,span,comb)
    PATHS=all_paths(G,span,sols)
    lm=delete_duplicates2(paths_to_listmult(PATHS))
    t=len(lm[0])
    for path in lm:
        if(len(path)<t):
            t=len(path)
    return t

def orderfrompaths(G,span,sols):
    PATHS=all_paths(G,span,sols)
    lm=delete_duplicates2(paths_to_listmult(PATHS))
    t=len(lm[0])
    for path in lm:
        if(len(path)<t):
            t=len(path)
    return t