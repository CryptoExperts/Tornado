###############################################################################
#
# Implementation of tightPROVE+ in SageMath
#
# tightPROVE+ is a formal verification tool for the tight register probing  
# security of masked implementations, introduced in https://ia.cr/2020/506
#
# File: misc.sage
# Description: this file contains miscellaneous functions used in other
# files, as well as some functions that attempt to get the minimal 
# attack order for a given flawed circuit.
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
#######################################MISC#######################################
def load_file(circuit_file):
    with open(circuit_file,'r') as f:
        lines = f.readlines()
    return [l.split() for l in lines]

def write_file(circuit_file,splitlines):
    with open(circuit_file,'w') as f:
        for args in splitlines:
            for a in args:
                f.write(a+' ')
            f.write('\n')

def union_col(listcol):
# for a list of color, outputs the list of gadgets' indexes involved
    inter=listcol[0]
    for i in range(1,len(listcol)):
        inter=np.logical_or(inter,listcol[i])
    return inter

def change_repr(C):
#outputs a list telling in which colors a given index of a gadget can be found
    nbcol=len(C)
    Ecolor=[]
    for i in range(nbcol):
        for j in range(len(C[i])):
            if(C[i][j] not in [e[0] for e in Ecolor]):
                Ecolor+=[[C[i][j],np.array([0 for k in range(nbcol)],bool)]]
                Ecolor[-1][1][i]=True
            else:
                ind=[e[0] for e in Ecolor].index(C[i][j])
                Ecolor[ind][1][i]=True

    Ecolor.sort(key=lambda e: sum(e[1]),reverse=True)
    return Ecolor

def get_t_covering(C,t):
# if C is a list containing all the colors for all possible attacks, 
# this function outputs all the lists of multiplications of size t
# for which every color has an element in it
    nbcol=len(C)
    tcovering=[]
    Ecolor=change_repr(C)

    for c in combinations(Ecolor,t):
        sumcolor=union_col([elem[1] for elem in c])
        if(sumcolor.all()):
            tcovering+=[c]
    return [[l[i][0] for i in range(len(l))] for l in tcovering]

def reduce_sols(sols,span,poa=0):
    sols_redu=[]
    for sol in sols:
        to_add=True
        free_ops_involved=[]
        for i in range(len(sol)):
            if(sol[i]):
                if(span[i] in free_ops_involved):
                    to_add=False
                    break
                else:
                    free_ops_involved+=[span[i]]

        if(to_add):
            sols_redu+=[sol]
    return sols_redu

def attack_order(G,sols,span,comb,approx=0):
# returns the least attack order for a given operand
# G, span and comb are informations that can be found when the algorithm is finished considering the operand
# sols is the list of all the solutions the algorithm found
# multiple approximation options are available. approx=0 means that no approximation is done but
# it might take a long time to output a solution. approx=1 seems to work correctly and fast, but it is not guaranteed 
# to output the correct solution. approx=2 is fast, but counterexamples have been found that proves that it does
# not always output the correct solution.
    if(approx==0):
        return orderfromaugmentedpaths(G,span,sols,comb)
    elif(approx==1):
        return orderfrompaths(G,span,sols)
    elif(approx==2):
        t=0
        varorder=[1 for i in range(len(G))]
        for i in range(len(G)):
            if(len(G[i])>1):
                m=0
                for j in range(1,len(G[i])):
                    s=0  
                    try:
                        lGij=len(G[i][j])
                        for k in range(lGij):
                            s+=int(G[i][j][k])*varorder[k]
                    except:
                        s+=varorder[0]
                        
                    if(s<m or j==1):
                        m=s
                
                varorder[i]+=m
                
        for i in range(len(sols)):
            s=0
            for j in range(len(sols[i])):
                s+=int(sols[i][j])*varorder[j]

            if(s==2):return 2
            if(s<t or i==0):
                t=s
    
    elif(approx=='all' or approx=='a'):
        return [attack_order(G,sols,span,comb,approx=i) for i in range(3)]
    elif(approx=='pos' or approx=='p'):
        return [attack_order(G,sols,span,comb,approx=i) for i in range(1,3)]

    else:
        raise Exception("not a valid order approximation level")
    
    return t
    
def generate_simple_circuit_order_t(t):
#creates a file called order_t that contains the description of a circuit for which there exists one attack, of order t
    with open("order_"+str(t),"w") as f:    
        for i in range(t):
            f.write("in "+str(i)+"\n")
        f.write("xor "+str(0)+" "+str(1)+"\n")
        if(t>2):
            for i in range(2,t):
                f.write("xor "+str(i)+" "+str(t+i-2)+"\n")
        for i in range(t):
            f.write("and "+str(2*t-2)+" "+str(i)+"\n")

def insert_line(filename,line,content):
#inserts a line 'content' at the line number 'line' in a file named 'filename'
    with open(filename,"r") as f:
        contents = f.readlines()
        contents.insert(line, content)
    with open(filename,"w") as f:    
        f.writelines(contents)
        
def insert_line2(L,line,content):
    L.insert(line, content)
    
def get_nb_ref_before_line(L,l):
#outputs the number of refresh gadgets there is in the first l+1 elements of L
    c=0
    for i in range(l+1):
        if L[i][0]=='ref':
            c+=1
    return c
    
def separate_symbols(Lines):
#puts spaces around symbols
    list_symbols = ['+','^','*','&','.','~','!','|','=']
    L2=[]
    for args in Lines:
        if(len(args)>0 and 'in' not in args):
            for symbol in list_symbols:
                L=[]
                for a in args:
                    if(symbol in a):
                        A=a
                        while(symbol in A):
                            if(len(A[:A.index(symbol)])>0):
                                L+=[A[:A.index(symbol)]]
                            L+=[symbol]
                            A=A[A.index(symbol)+1:]
                        if(len(A)>0):
                            L+=[A]
                    else:
                        L+=[a]          
                args=L
        L2+=[args]
    return L2
    
def linef_to_lineo(lf,Lf,Lo):
#tells which line in the original list of instructions Lo corresponds to the line number lf 
#in the formatted list of instructions Lf
    current_l=-1  #line in the formatted file
    fileline=0    #line in the non-formatted file
    nb=['0','1','2','3','4','5','6','7','8','9']
    comms=['#','/','<','>',';']
    list_op_add = ["ADD","add","+","XOR","xor","Add","Xor","^"]
    list_op_mult = ["AND","and","And","*","&","MULT","mult","Mult","."]
    list_op_ref = ["R","r","REF","ref","Ref","REFRESH","Refresh","refresh"]
    list_op_not = ["NOT","Not","not","~","!"]
    list_op_or = ["OR","Or","or","|",]
    list_op = list_op_add+list_op_mult+list_op_ref+list_op_not+list_op_or
    list_symbols = ['+','^','*','&','.','~','!','|','=']
    list_separators=[',','(',')']
    
    targetvar=''
    targetl=0
    while(current_l<lf):
        #print"---"
        while(Lo[fileline]==[] or Lo[fileline][0][0] in comms or Lo[fileline][0]=='out'):
            fileline+=1
                        
        if(Lo[fileline][0]=='in'):
            for i in range(1,len(Lo[fileline])):
                if(Lo[fileline][i]!='...' and Lo[fileline][i-1]!='...' and '[' not in Lo[fileline][i] and ']' not in Lo[fileline][i]):
                    current_l+=1
                    if(current_l==lf):
                        targetvar=Lo[fileline][i]
                        targetl=fileline
                        break
                if(Lo[fileline][i-1]=='...'):
                    nbleft=0
                    nbright=0
                    pos=-1
                    while(Lo[fileline][i-2][pos] in nb):
                        pos-=1
                    nbleft=int(Lo[fileline][i-2][pos+1:])
                    varname=Lo[fileline][i-2][:pos+1]
                    pos=-1
                    while(Lo[fileline][i][pos] in nb):
                        pos-=1
                    nbright=int(Lo[fileline][i][pos+1:])
                    current_l+=abs(nbleft-nbright)
                    if(current_l>=lf):
                        if(nbleft<nbright):
                            targetvar=varname+str(nbright-(current_l-lf))
                            targetl=fileline
                            break
                        else:
                            targetvar=varname+str(nbright+(current_l-lf))
                            targetl=fileline
                            break    
                if('[' in Lo[fileline][i] or ']' in Lo[fileline][i]):
                    if('][' not in Lo[fileline][i]):
                        pos1=Lo[fileline][i].index('[')
                        pos2=Lo[fileline][i].index(']')
                        if(pos2<pos1):
                            pos1,pos2=pos2,pos1  #T]3[ would actually be accepted, but who cares?
                        varname=Lo[fileline][i][:pos1]
                        pos=pos2
                        while(Lo[fileline][i][pos-1] in nb):
                            pos-=1
                            
                        n2=int(Lo[fileline][i][pos:pos2])
                        pos=pos1
                        while(Lo[fileline][i][pos+1] in nb):
                            pos+=1
                        n1=int(Lo[fileline][i][pos1+1:pos+1])

                        if(n2<n1):
                            n1,n2=n2,n1
                        if(n1!=n2):
                            current_l+=n2-n1+1
                            if(current_l>=lf):
                                targetvar=varname+'['+str(n2-(current_l-lf))+']'
                                targetl=fileline
                                break
                        else:
                            current_l+=n2
                            if(current_l>=lf):
                                targetvar=varname+'['+str(n2-(current_l-lf)-1)+']'
                                targetl=fileline
                                break
                                
                    else:
                        dim=Lo[fileline][i].count('][')+1
                        pos_i=Lo[fileline][i].index('[')
                        pos_f=len(Lo[fileline][i])-1
                        pos_newdim=Lo[fileline][i].index('][')
                        base=Lo[fileline][i][:pos_i]
                        list_n=[]

                        pos_sep_d=0
                        pos_sep_g=0
                        for k in range(dim):
                            pos_sep_g+=Lo[fileline][i][pos_sep_g+1:].index('[')+1
                            pos_sep_d+=Lo[fileline][i][pos_sep_d+1:].index(']')+1
                            pos=pos_sep_d
                            while(Lo[fileline][i][pos-1] in nb):
                                pos-=1
                            n2=int(Lo[fileline][i][pos:pos_sep_d])
                            pos=pos_sep_g
                            while(Lo[fileline][i][pos+1] in nb):
                                pos+=1
                            n1=int(Lo[fileline][i][pos_sep_g+1:pos+1])
                            if(n1>n2):
                                list_n+=[[n2,n1]]
                            elif(n1<n2):
                                list_n+=[[n1,n2]]
                            elif(pos_sep_d-pos_sep_g==len(Lo[fileline][i][pos_sep_g+1:pos+1])+1):
                                list_n+=[[0,n1-1]]
                            else:
                                list_n+=[[n1,n1]]

                        list_n2=[[a,a] for a,b in list_n]
                        while(list_n2!=list_n):
                            
                            varname=base
                            for k in range(len(list_n)):
                                varname+='['+str(list_n2[k][1])+']'
                            current_l+=1
                            if(current_l==lf):
                                targetvar=varname
                                targetl=fileline
                                #break
                            list_n2[-1][1]+=1
                            for k in range(len(list_n2)-1,0,-1):
                                if(list_n2[k][1]>list_n[k][1]):
                                    list_n2[k][1]=list_n[k][0]
                                    list_n2[k-1][1]+=1

                        varname=base
                        for k in range(len(list_n)):
                            varname+='['+str(list_n[k][1])+']'
                        current_l+=1
                        if(current_l==lf):
                            targetvar=varname
                            targetl=fileline
    
        else:
            current_l+=1
            if(current_l==lf):
                #print Lo[fileline]
                if '=' in Lo[fileline]:
                    targetvar=Lo[fileline][0]  ##variable could not be affected with =
                elif Lo[fileline][0] in list_op:
                    targetvar=Lo[fileline][1]
                    
                targetl=fileline
                break
                
        fileline+=1
                            
    return targetvar,targetl

def delete_duplicates(L):
    return np.unique(L, axis=0)

def delete_duplicates2(L):
    Lr=[]
    for l in L:
        if l not in Lr:
            Lr+=[l]
    return Lr


def find_all_sol(Ml,v):
#returns all the solutions to Ml.x=v
#for the specific cases where Ml is a matrix made of 1 or 2 vectors,
#the method used to solve is different, for efficiency purposes
    if(len(Ml)==1):
        for i in range(len(v)):
            if(Ml[0][i]!=v[i]):
                return []
        return [vector(GF(2),[1])]
    
    if(len(Ml)==2):
        testv0=True
        testv1=True
        testsum=True
        for i in range(len(v)):
            if(Ml[0][i]!=v[i]):
                testv0=False
            if(Ml[1][i]!=v[i]):
                testv1=False
            if(Ml[0][i]^^Ml[1][i]!=v[i]):
                testsum=False
            if(not (testv0 or testv1 or testsum)):
                return []
        L=[]
        if(testv0):
            return [vector(GF(2),[1,0])]
        if(testv1):
            return [vector(GF(2),[0,1])]
        if(testsum):
            return [vector(GF(2),[1,1])]
        
        
    m=matrix(GF(2),Ml).transpose()
    b=vector(GF(2),v)
    sol=0
    L=[]
    try:
        sol=m.solve_right(b)
        k=m.right_kernel()
        for vz in k:
            L+=[sol+vz]
    except:
        return []
    return L

def find_one_sol(Ml,v):
#returns one solution to Ml.x=v
    if(len(Ml)==1):
        for i in range(len(v)):
            if(Ml[0][i]!=v[i]):
                return None
        return vector(GF(2),[1])
    
    if(len(Ml)==2):
        testv0=True
        testv1=True
        testsum=True
        for i in range(len(v)):
            if(Ml[0][i]!=v[i]):
                testv0=False
            if(Ml[1][i]!=v[i]):
                testv1=False
            if(Ml[0][i]^^Ml[1][i]!=v[i]):
                testsum=False
            if(not (testv0 or testv1 or testsum)):
                return None
        if(testv0):
            return vector(GF(2),[1,0])
        if(testv1):
            return vector(GF(2),[0,1])
        if(testsum):
            return vector(GF(2),[1,1])

        
    m=matrix(GF(2),Ml).transpose()
    b=vector(GF(2),v)
    sol=0
    L=[]
    try:
        sol=m.solve_right(b)
        return sol
    except:
        return None
        
        
        
        
        