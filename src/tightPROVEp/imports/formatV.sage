###############################################################################
#
# Implementation of tightPROVE+ in SageMath
#
# tightPROVE+ is a formal verification tool for the tight register probing  
# security of masked implementations, introduced in https://ia.cr/2020/506
#
# File: formatV.sage
# Description: this file contains a function that transforms code written in a 
# high-level language into a sequence of operations that corresponds to the 
# flattened version of the circuit given as input.
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

def copyandresize(d,varname,rs,count):
    int_repr=[]
    for rpos in range(rs):
        temp=np.copy(d[varname][rpos])
        temp.resize(count)
        int_repr+=[temp]
    d[varname]=np.array(int_repr)
    
def resizevar(varLC,rs,count):
    int_repr=[]
    for rpos in range(rs):
        temp=np.copy(varLC[rpos])
        temp.resize(count)
        int_repr+=[temp]
    return np.array(int_repr)
    
class OperandV:
    def __init__(self,line,name,LC):
        self.line=line
        self.name=name
        self.LC=LC
        
    def __str__(self):
        return self.name+'(line '+str(self.line)+')'

class MultV:
    def __init__(self, line,name,ops):
        self.line=line
        self.name=name
        self.ops=ops
        
    def __str__(self):
        return '('+str(self.ops[0])+','+str(self.ops[1])+')('+str(self.line)+')'
    
class CircuitV:
    def __init__(self,multlist,rs,full_list_op,nbi,nbm,nbr):
        self.multlist=multlist
        self.rs=rs
        self.full_list_op=full_list_op
        self.nbi=nbi
        self.nbm=nbm
        self.nbr=nbr


###All variables have a type 'x', '0' or '1', depending on whether they are a variable dependent from the input, a constant that equals 0 or a constant that equals 1

def find_type_XOR(type1,type2):
    if(type1=='x' or type2=='x'): return 'x'
    elif(type1 in ['0','1'] and type2 in ['0','1']): return str(int(type1)^^int(type2))
    else: raise Exception("error : invalid type.")
    
def find_type_AND(type1,type2):
    if(type1=='0' or type2=='0'): return '0'
    elif(type1=='x' or type2=='x'): return 'x'
    elif(type1=='1' and type2=='1'): return '1'
    else: raise Exception("error : invalid type.")
        
def find_type_OR(type1,type2):
    if(type1=='1' or type2=='1'): return '1'
    elif(type1=='x' or type2=='x'): return 'x'
    elif(type1=='0' and type2=='0'): return '0'
    else: raise Exception("error : invalid type.")
        
def find_type_NOT(type1):
    if(type1=='1'): return '0'
    elif(type1=='x'): return 'x'
    elif(type1=='0'): return '1'
    else: raise Exception("error : invalid type.")
        
        
def find_types_XOR(types1,types2):
    return [find_type_XOR(types1[i],types2[i]) for i in range(len(types1))]

def find_types_AND(types1,types2):
    return [find_type_AND(types1[i],types2[i]) for i in range(len(types1))]

def find_types_OR(types1,types2):
    return [find_type_OR(types1[i],types2[i]) for i in range(len(types1))]

def find_types_NOT(types1):
    return [find_type_NOT(types1[i]) for i in range(len(types1))]
        

def is_mask_op(types1,types2):  #a mask is an operation where all the coordinates of an operand are constants
    type1ismask=True
    type2ismask=True
    for i in range(len(types1)):
        if(types1[i]=='x'):
            type1ismask=False
            break
    if(type1ismask==False):
        for i in range(len(types2)):
            if(types2[i]=='x'):
                type2ismask=False
                break
    return (type1ismask or type2ismask)
    
def find_def_mult(line,name,op1,op2,oplist):
    multop=[0,0]
    i=len(oplist)
    while(i>=0 and 0 in multop):
        i-=1
        if op1==oplist[i].name and multop[0]==0:
            multop[0]=oplist[i]
        if op2==oplist[i].name and multop[1]==0:
            multop[1]=oplist[i]
    if i==-1:
        raise Exception("can't find operands of mult "+name+" = "+op1+" & "+op2)
    else:
        return MultV(line,name,multop)

def flatten(filename,progress=False):
#transforms a description of a circuit in a file (or a list of lines) into a Circuit
#progress=1 shows the number of line being processed during the algorithm
    
    list_input = ['in','IN','input','INPUT','Input','In','DATATYPE']
    list_cst=['DEF_CST','def_cst','CST_DEF','cst_def','CSTDEF','DEFCST','cstdef','defcst']
    list_op_add = ["ADD","add","+","XOR","xor","Add","Xor","^"]
    list_op_sub = ['SUB','Sub','sub','-']
    list_op_mult = ["AND","and","And","*","&","MULT","mult","Mult","."]
    list_op_ref = ["REF","ref","Ref","REFRESH","Refresh","refresh"]
    list_op_not = ["NOT","Not","not","~"]
    list_op_or = ["OR","Or","or","|",]
    list_op_rotr = ["rotr","rot_r","R_ROTATE",">>>"]
    list_op_rotl = ["rotl","rot_l","L_ROTATE","<<<"]
    list_op_shiftr = ["shiftr","shift_r","R_SHIFT",">>"]
    list_op_shiftl = ["shiftl","shift_l","L_SHIFT","<<"]
    list_op_rot = list_op_rotr + list_op_rotl
    list_op_shift = list_op_shiftr + list_op_shiftl
    list_op_setcst = ['setcst','SETCST','set_cst','SET_CST','cstset','CSTSET','cst_set','CST_SET']
    list_op_setcstall = ['setcstall','SETCSTALL','set_cst_all','SET_CST_ALL','cstsetall','CSTSETALL','cst_set_all','CST_SET_ALL']
    list_op = list_op_add+list_op_sub+list_op_mult+list_op_ref+list_op_not+list_op_or+list_op_rot+list_op_shift+list_op_setcst+list_op_setcstall
    list_symbols = ['+','^','*','&','.','~','!','|','=','-']
    list_r = ['>>>','<<<']
    list_s = ['<<','>>']
    list_comms = ['#','/',';','%']
    list_numbers = ['0','1','2','3','4','5','6','7','8','9']
    list_separators=[',','(',')']
    
    try:
        with open(filename , "r") as f:
            lines = f.readlines()
    except:
        lines=filename  #if we give a list of instructions instead of a file, the algorithm still works


    ###read size of register in the first line of the file
    try:
        firstline=lines[0]
        for comms in list_comms:
            if(comms in firstline):
                firstline.index(comms)
                firstline=firstline[:firstline.index(comms)]  
        while(len(firstline)>0 and firstline[0]==' '):
            firstline=firstline[1:]
        firstline=firstline.split('=')
        rs=int(firstline[1])
    except:
        raise Exception("couldn't read size of register")
    

    d={}            #contains the (latest) definition of each register as a table of linear combinations of the inputs
    full_list_op=[] #contains all informations needed on the operands to build the set of multiplications
    dict_type={}    #contains the type of the elements : 'x' '0' '1' for variable, 0 const and 1 const respectively
    count=0         #counts the number of input vectors 
    nbr=0           #number of refresh
    multlist=[]     #list of multiplications
        
    for i in range(1,len(lines)):
        if(progress):
            sys.stdout.write("\t progress: %d/%d   \r" % (i+1,len(lines)) )
            sys.stdout.flush()
        

        ###getting rid of comments and line breaks
        args = lines[i]
        if(args=="\n"):
            continue
        if(len(args)>0 and args[-1]=="\n"):args=args[:-1]
        for comms in list_comms:
            if(comms in args):
                args=args[:args.index(comms)]  
        while(len(args)>0 and args[0]==' '):
            args=args[1:]
            


        args=args.split()
            
        ###inputs and constants definitions
        if(len(args)>0 and args[0] in list_input+list_cst):
            isinput=args[0] in list_input
            args=args[1:]
            for j in range(len(args)):
                
                ###defining input tables
                if('[' in args[j] and ']' in args[j]):

                    ###tables of dimension 1
                    if('][' not in args[j]):
                        pos1=args[j].index('[')
                        pos2=args[j].index(']')
                        if(pos2<pos1):
                            pos1,pos2=pos2,pos1  #T]3[ would actually be a valid syntax, but it doesn't matter
                        base=args[j][:pos1]
                        pos=pos2
                        while(args[j][pos-1] in list_numbers):
                            pos-=1
                        try:
                            n2=int(args[j][pos:pos2])
                        except:
                            raise Exception("tab initialization went wrong. (line "+str(i+1)+")")
                        pos=pos1
                        while(args[j][pos+1] in list_numbers):
                            pos+=1
                        try:
                            n1=int(args[j][pos1+1:pos+1])
                        except:
                            raise Exception("tab initialization went wrong. (line "+str(i+1)+")")
                        if(n2<n1):
                            n1,n2=n2,n1
                        if(n1!=n2):
                            for k in range(n1,n2+1):
                                partial_repr=[]
                                for rpos in range(rs):
                                    if(isinput):count+=1
                                    var_repr=np.array([0 for sizeofarray in range(count)],bool)
                                    if(isinput):var_repr[count-1]=True
                                    partial_repr+=[var_repr]
                                d[base+'['+str(k)+']']=np.array(partial_repr)
                                full_list_op+=[OperandV(i,base+'['+str(k)+']',np.array(partial_repr))]
                                if(isinput):dict_type[base+'['+str(k)+']']=['x' for rpos in range(rs)]
                                else:dict_type[base+'['+str(k)+']']=['0' for rpos in range(rs)]           #we can technically define tables of constants, but that might not be useful

                        else:
                            for k in range(n1):
                                partial_repr=[]
                                for rpos in range(rs):
                                    if(isinput):count+=1
                                    var_repr=np.array([0 for sizeofarray in range(count)],bool)
                                    if(isinput):var_repr[count-1]=True
                                    partial_repr+=[var_repr]
                                d[base+'['+str(k)+']']=np.array(partial_repr)

                                full_list_op+=[OperandV(i,base+'['+str(k)+']',np.array(partial_repr))]
                                if(isinput):dict_type[base+'['+str(k)+']']=['x' for rpos in range(rs)]
                                else:dict_type[base+'['+str(k)+']']=['0' for rpos in range(rs)]

                    ###multidimensional tables
                    else:
                        dim=args[j].count('][')+1
                        pos_i=args[j].index('[')
                        pos_f=len(args[j])-1
                        pos_newdim=args[j].index('][')
                        base=args[j][:pos_i]
                        list_n=[]
                        if(pos_newdim<pos_i):
                            raise Exception("tab initialization went wrong. (line "+str(i+1)+")")
                        if(args[j][-1]!=']'):
                            raise Exception("tab initialization went wrong. (line "+str(i+1)+")")
                        pos_sep_d=0
                        pos_sep_g=0
                        for k in range(dim):
                            pos_sep_g+=args[j][pos_sep_g+1:].index('[')+1
                            pos_sep_d+=args[j][pos_sep_d+1:].index(']')+1
                            pos=pos_sep_d
                            while(args[j][pos-1] in list_numbers):
                                pos-=1
                            try:
                                n2=int(args[j][pos:pos_sep_d])
                            except:
                                raise Exception("tab initialization went wrong. (line "+str(i+1)+")")
                            pos=pos_sep_g
                            while(args[j][pos+1] in list_numbers):
                                pos+=1
                            try:
                                n1=int(args[j][pos_sep_g+1:pos+1])
                            except:
                                raise Exception("tab initialization went wrong. (line "+str(i+1)+")")
                            if(n1>n2):
                                list_n+=[[n2,n1]]
                            elif(n1<n2):
                                list_n+=[[n1,n2]]
                            elif(pos_sep_d-pos_sep_g==len(args[j][pos_sep_g+1:pos+1])+1):
                                list_n+=[[0,n1-1]]
                            else:
                                list_n+=[[n1,n1]]

                        list_n2=[[a,a] for a,b in list_n]
                        while(list_n2!=list_n):
                            stringvar=base
                            for k in range(len(list_n)):
                                stringvar+='['+str(list_n2[k][1])+']'
                            partial_repr=[]
                            for rpos in range(rs):
                                if(isinput):count+=1
                                var_repr=np.array([0 for sizeofarray in range(count)],bool)
                                if(isinput):var_repr[count-1]=True
                                partial_repr+=[var_repr]
                            d[stringvar]=np.array(partial_repr)
                            full_list_op+=[OperandV(i,stringvar,np.array(partial_repr))]
                            if(isinput):dict_type[stringvar]=['x' for rpos in range(rs)]
                            else:dict_type[stringvar]=['0' for rpos in range(rs)]
                            list_n2[-1][1]+=1
                            for k in range(len(list_n2)-1,0,-1):
                                if(list_n2[k][1]>list_n[k][1]):
                                    list_n2[k][1]=list_n[k][0]
                                    list_n2[k-1][1]+=1
                        stringvar=base
                        for k in range(len(list_n)):
                            stringvar+='['+str(list_n2[k][1])+']'
                        partial_repr=[]
                        for rpos in range(rs):
                            if(isinput):count+=1
                            var_repr=np.array([0 for sizeofarray in range(count)],bool)
                            if(isinput):var_repr[count-1]=True
                            partial_repr+=[var_repr]
                        d[stringvar]=np.array(partial_repr)
                        full_list_op+=[OperandV(i,stringvar,np.array(partial_repr))]
                        if(isinput):dict_type[stringvar]=['x' for rpos in range(rs)]
                        else:dict_type[stringvar]=['0' for rpos in range(rs)]

                        
                ###defining isolated inputs         
                elif((args[j]!="..." and j==0) or (j>0 and args[j]!="..." and args[j-1]!="...")):
                    partial_repr=[]
                    for rpos in range(rs):
                        if(isinput):count+=1
                        var_repr=np.array([0 for sizeofarray in range(count)],bool)
                        if(isinput):var_repr[count-1]=True
                        partial_repr+=[var_repr]
                    d[args[j]]=np.array(partial_repr)
                    full_list_op+=[OperandV(i,args[j],np.array(partial_repr))]
                    if(isinput):dict_type[args[j]]=['x' for rpos in range(rs)]
                    else:dict_type[args[j]]=['0' for rpos in range(rs)]

                ###defining lists of inputs   
                elif(j>0 and args[j-1]!="..."):
                    number_found1=False
                    for k in range(len(args[j-1])):
                        try:
                            n1=int(args[j-1][k:])
                            number_found1=True
                            break
                        except:
                            pass
                    if(number_found1==False):
                        raise Exception("... should be between indexed variable names.")
                        
                    base1=args[j-1][:k]
                            
                    number_found2=False
                    for k in range(len(args[j+1])):
                        try:
                            n2=int(args[j+1][k:])
                            number_found2=True
                            break
                        except:
                            pass
                    if(number_found2==False):
                        raise Exception("... should be between indexed variable names.")
                            
                    base2=args[j+1][:k]
                    if(base1!=base2):
                        raise Exception("variables around ... should have the same name ("+base1+" != "+base2+")")
                            
                    if(n2<n1):
                        for k in range(n1-1,n2-1,-1):
                            partial_repr=[]
                            for rpos in range(rs):
                                if(isinput):count+=1
                                var_repr=np.array([0 for sizeofarray in range(count)],bool)
                                if(isinput):var_repr[count-1]=True
                                partial_repr+=[var_repr]
                            d[base1+str(k)]=np.array(partial_repr)
                            full_list_op+=[OperandV(i,base1+str(k),np.array(partial_repr))]
                            if(isinput):dict_type[base1+str(k)]=['x' for rpos in range(rs)]
                            else:dict_type[base1+str(k)]=['0' for rpos in range(rs)]

                    elif(n2>n1):
                        for k in range(n1+1,n2+1):
                            partial_repr=[]
                            for rpos in range(rs):
                                if(isinput):count+=1
                                var_repr=np.array([0 for sizeofarray in range(count)],bool)
                                if(isinput):var_repr[count-1]=True
                                partial_repr+=[var_repr]
                            d[base1+str(k)]=np.array(partial_repr)
                            full_list_op+=[OperandV(i,base1+str(k),np.array(partial_repr))]
                            if(isinput):dict_type[base1+str(k)]=['x' for rpos in range(rs)]
                            else:dict_type[base1+str(k)]=['0' for rpos in range(rs)]
                            
                    else:
                        raise Exception("... should be between indexed variable names with different index.")
        
        

        ###other lines for formulas
        elif(len(args)>0):

            ###separates variables from symbols and removes unnecessary characters such as , ) and (
            for symbol in list_symbols+list_separators+list_s:
                L=[]
                for a in args:
                    if(symbol in a):
                        A=a
                        while(symbol in A):
                            if(len(A[:A.index(symbol)])>0):
                                L+=[A[:A.index(symbol)]]
                            if(symbol not in list_separators):
                                if(symbol+'<' in a):
                                    symbol+='<'
                                elif(symbol+'>' in a):
                                    symbol+='>'  
                                L+=[symbol]
                            A=A[A.index(symbol)+len(symbol):]
                        if(len(A)>0):
                            L+=[A]
                    else:
                        L+=[a]  
                args=L

                
            ###unused feature that could allow to change a specific coordinate directly : x$23 would mean 'the 23rd coordinate of x'
            if((np.array(['$' in args[j] for j in range(len(args))])==True).any()):  #if we only change one variable in a register
                pass
            
            else:    #we change whole registers (no $ anywhere)
                if (args[0] in list_op):  
                    #SYNTAX :  "op res var1 var2"   or   "op res var" for refresh and not operators


                    #XOR
                    if args[0] in list_op_add and len(args)>3:
                        copyandresize(d,args[3],rs,count)
                        copyandresize(d,args[2],rs,count)
                        d[args[1]]=np.copy(np.array([d[args[2]][rpos]^^d[args[3]][rpos] for rpos in range(rs)]))
                        full_list_op+=[OperandV(i,args[1],d[args[1]])]
                        dict_type[args[1]]=find_types_XOR(dict_type[args[2]],dict_type[args[3]])
                        if len(args)>4:
                            print("warning : \""+lines[i][:-1]+"\" has too many uncommented parts. (line "+str(i+1)+")")
                        
                    #AND
                    elif args[0] in list_op_mult and len(args)>3:
                        if(not is_mask_op(dict_type[args[2]],dict_type[args[3]])):
                            partial_repr=[]
                            for rpos in range(rs):
                                count+=1
                                var_repr=np.array([0 for sizeofarray in range(count)],bool)
                                var_repr[count-1]=True
                                partial_repr+=[var_repr]             
                            d[args[1]]=np.array(partial_repr)
                            full_list_op+=[OperandV(i,args[1],d[args[1]])]
                            multlist+=[find_def_mult(i,args[1],args[2],args[3],full_list_op)]
                            dict_type[args[1]]=['x' for rpos in range(rs)]
                        else:
                            partial_repr=[]
                            for rpos in range(rs):
                                if(dict_type[args[2]][rpos]=='0' or dict_type[args[3]][rpos]=='0'):
                                    var_repr=np.array([0 for sizeofarray in range(count)],bool)
                                elif(dict_type[args[2]][rpos]=='1'):
                                    var_repr=np.copy(d[args[3]][rpos])
                                else:
                                    var_repr=np.copy(d[args[2]][rpos])
                                partial_repr+=[var_repr]             
                            d[args[1]]=np.array(partial_repr)
                            full_list_op+=[OperandV(i,args[1],d[args[1]])]
                            dict_type[args[1]]=find_types_AND(dict_type[args[2]],dict_type[args[3]])
                        if len(args)>4:
                            print("warning : \""+lines[i][:-1]+"\" has too many uncommented parts. (line "+str(i+1)+")")

                    #REFRESH    
                    elif args[0] in list_op_ref and len(args)>2: 
                        nbr+=1
                        partial_repr=[]
                        for rpos in range(rs):
                            count+=1
                            var_repr=np.array([0 for sizeofarray in range(count)],bool)
                            var_repr[count-1]=True
                            partial_repr+=[var_repr]
                        d[args[1]]=np.array(partial_repr)
                        full_list_op+=[OperandV(i,args[1],d[args[1]])]
                        dict_type[args[1]]=['x' for rpos in range(rs)]
                        if len(args)>3:
                            print("warning : \""+lines[i][:-1]+"\" has too many uncommented parts. (line "+str(i+1)+")")

                    #NOT   
                    elif args[0] in list_op_not and len(args)>2:
                        #splitlines+=[["not",str(d[args[2]])]]
                        d[args[1]]=np.copy(d[args[2]])
                        full_list_op+=[OperandV(i,args[1],d[args[1]])]
                        dict_type[args[1]]=find_types_NOT(dict_type[args[2]])
                        if len(args)>3:
                            print("warning : \""+lines[i][:-1]+"\" has too many uncommented parts. (line "+str(i+1)+")")
                        
                    #OR
                    elif args[0] in list_op_or and len(args)>3:
                        if(not is_mask_op(dict_type[args[2]],dict_type[args[3]])):
                            partial_repr=[]
                            for rpos in range(rs):
                                count+=1
                                var_repr=np.array([0 for sizeofarray in range(count)],bool)
                                var_repr[count-1]=True
                                partial_repr+=[var_repr]                           
                            d[args[1]]=np.array(partial_repr)
                            full_list_op+=[OperandV(i,args[1],d[args[1]])]
                            multlist+=[find_def_mult(i,args[1],args[2],args[3],full_list_op)]
                            dict_type[args[1]]=['x' for rpos in range(rs)]
                        else:
                            partial_repr=[]
                            for rpos in range(rs):
                                if(dict_type[args[2]][rpos]=='1' or dict_type[args[3]][rpos]=='1'):
                                    var_repr=np.array([0 for sizeofarray in range(count)],bool)
                                elif(dict_type[args[2]][rpos]=='0'):
                                    var_repr=np.copy(d[args[3]][rpos])
                                else:
                                    var_repr=np.copy(d[args[2]][rpos])
                                partial_repr+=[var_repr]             
                            d[args[1]]=np.array(partial_repr)
                            full_list_op+=[OperandV(i,args[1],d[args[1]])]
                            dict_type[args[1]]=find_types_OR(dict_type[args[2]],dict_type[args[3]])
                        if len(args)>4:
                            print("warning : \""+lines[i][:-1]+"\" has too many uncommented parts. (line "+str(i+1)+")")
                        
                    #ROT
                    elif args[0] in list_op_rot and len(args)>3:
                        r=int(args[3])
                        if(args[0] in list_op_rotl):r=-r
                        if(r>=rs):r=r%rs
                        elif(r<0 and (-r)%rs==0):r=0
                        elif(r<0):r=rs-((-r)%rs)
                        partial_repr=[]
                        for rpos in range(rs):
                            partial_repr+=[np.copy(d[args[2]][(rpos+rs-r)%rs])]
                        d[args[1]]=np.array(partial_repr)
                        full_list_op+=[OperandV(i,args[1],d[args[1]])]
                        dict_type[args[1]]=[dict_type[args[2]][(rpos+rs-r)%rs] for rpos in range(rs)]
                        #d[args[1]]=np.copy(np.roll(np.copy(d[args[2]]),int(args[3]),axis=0))
                        if len(args)>4:
                            print("warning : \""+lines[i][:-1]+"\" has too many uncommented parts. (line "+str(i+1)+")")
                        
                    #SHIFT
                    elif args[0] in list_op_shift and len(args)>3:
                        #print args
                        r=int(args[3])
                        varname=args[2]
                        if(r>=rs or -r>=rs):
                            print ("warning : shift value exceeds register size.")
                            partial_repr=[]
                            for rpos in range(rs):
                                partial_repr+=[np.array([0 for sizeofarray in range(count)],bool)]
                            d[args[1]]=np.array(partial_repr)
                            full_list_op+=[OperandV(i,args[1],d[args[1]])]
                            dict_type[args[1]]=['0' for rpos in range(rs)]
                            
                        elif((args[0] in list_op_shiftl and r>=0) or (args[0] in list_op_shiftr and r<=0)):
                            if(r<0):
                                r=-r
                            partial_repr=[]
                            for rpos in range(rs):
                                if(rpos<rs-r):
                                    partial_repr+=[np.copy(d[varname][rpos+r])]
                                else:
                                    partial_repr+=[np.array([0 for sizeofarray in range(count)],bool)]
                            d[args[1]]=np.array(partial_repr)
                            full_list_op+=[OperandV(i,args[1],d[args[1]])]
                            dict_type[args[1]]=['x' for rpos in range(rs-r)]+['0' for rpos in range(rs-r,rs)]
                            
                        else:
                            if(r<0):
                                r=-r
                            partial_repr=[]
                            for rpos in range(rs):
                                if(rpos<r):
                                    partial_repr+=[np.array([0 for sizeofarray in range(count)],bool)]
                                else:
                                    partial_repr+=[np.copy(d[varname][rpos-r])]
                            d[args[1]]=np.array(partial_repr)
                            full_list_op+=[OperandV(i,args[1],d[args[1]])]
                            dict_type[args[1]]=['0' for rpos in range(r)]+['x' for rpos in range(r,rs)]   

                    #CST  
                    elif args[0] in list_op_setcst and len(args)>2:
                        try:
                            int(args[1],16)
                            constpos=1
                            varpos=2
                            if(args[constpos][:2]!='0b' and args[constpos][:2]!='0x'):
                                constpos=2
                                varpos=1
                        except:
                            varpos=1
                            constpos=2
                        partial_repr=[]
                        for rpos in range(rs):
                            var_repr=np.array([0 for sizeofarray in range(count)],bool)
                            partial_repr+=[var_repr]
                        d[args[varpos]]=np.array(partial_repr)
                        full_list_op+=[OperandV(i,args[varpos],d[args[varpos]])]
                        if args[constpos][:2]=='0b':
                            args[constpos]=args[constpos][2:]
                            while(len(args[constpos])<rs):
                                args[constpos]='0'+args[constpos]
                            if(len(args[constpos])==rs):
                                dict_type[args[varpos]]=[args[constpos][rpos] for rpos in range(rs)]
                            else:
                                raise Exception("\""+lines[i][:-1]+"\" : constant is too big. (in line "+str(i+1)+")")   
                        elif args[constpos][:2]=='0x':
                            args[constpos]=args[constpos][2:]
                            hexcst=args[constpos]
                            bincst=[b for b in bin(int(hexcst, 16))[2:].zfill(rs)]
                            if(len(bincst)==rs):
                                dict_type[args[varpos]]=bincst
                            else:
                                raise Exception("\""+lines[i][:-1]+"\" : constant is too big. (in line "+str(i+1)+")")
                        else:
                            raise Exception("\""+lines[i][:-1]+"\" is not a valid definition for a constant. (in line "+str(i+1)+")")
                        
                    #CSTALL
                    elif args[0] in list_op_setcstall and len(args)>2:
                        try:
                            int(args[1],16)
                            constpos=1
                            varpos=2
                            if(args[constpos][0] not in ['0','1']):
                                constpos=2
                                varpos=1
                        except:
                            varpos=1
                            constpos=2
                        partial_repr=[]
                        for rpos in range(rs):
                            var_repr=np.array([0 for sizeofarray in range(count)],bool)
                            partial_repr+=[var_repr]
                        d[args[varpos]]=np.array(partial_repr)
                        full_list_op+=[OperandV(i,args[varpos],d[args[varpos]])]
                        if(len(args[constpos])>1):
                            print("warning : setcstall only requires one bit. (in line "+str(i+1)+")")
                        if args[constpos][0] in ['0','1']:
                            dict_type[args[varpos]]=[args[constpos][0] for rpos in range(rs)] 
                        else:
                            raise Exception("\""+lines[i][:-1]+"\" is not a valid definition for a constant. (in line "+str(i+1)+")")
                            
                    else:
                        print("warning : \""+lines[i][:-1]+"\" is not a comment or a valid expression. (in line "+str(i+1)+")")
                        
                        
                        
                elif(len(args)>1 and args[1]=="="):  
                    #SYNTAX :  "res = var1 op var2" or "res = op var" or "res = op var1 var2"


                    if len(args)>4 and args[2] in list_op and args[2] not in list_op_rot and args[2] not in list_op_shift:
                        (args[2],args[3])=(args[3],args[2])
                    
                    #XOR
                    if len(args)>4 and args[3] in list_op_add:
                        copyandresize(d,args[4],rs,count)
                        copyandresize(d,args[2],rs,count)
                        d[args[0]]=np.copy([d[args[2]][rpos]^^d[args[4]][rpos] for rpos in range(rs)])
                        full_list_op+=[OperandV(i,args[0],d[args[0]])]
                        dict_type[args[0]]=find_types_XOR(dict_type[args[2]],dict_type[args[4]])
                        if len(args)>5:
                            print("warning : \""+lines[i][:-1]+"\" has too many uncommented parts. (line "+str(i+1)+")")
                        
                    #SUB
                    elif len(args)>3 and args[2] in list_op_sub: 
                        if(dict_type[args[3]][rs-1]!='x' or 'x' in [dict_type[args[3]][j] for j in range(rs-1)] or '1' in [dict_type[args[3]][j] for j in range(rs-1)]):
                            raise Exception('sub operator works with 1-bit values')
                        d[args[0]]=np.copy(np.array([d[args[3]][rs-1] for rpos in range(rs)]))
                        dict_type[args[0]]=['x' for rpos in range(rs)]
                        full_list_op+=[OperandV(i,args[0],d[args[0]])]
                        
                    #AND
                    elif len(args)>4 and args[3] in list_op_mult: 
                        if(not is_mask_op(dict_type[args[2]],dict_type[args[4]])):
                            partial_repr=[]
                            for rpos in range(rs):
                                count+=1
                                var_repr=np.array([0 for sizeofarray in range(count)],bool)
                                var_repr[count-1]=True
                                partial_repr+=[var_repr]       
                            d[args[0]]=np.array(partial_repr)
                            full_list_op+=[OperandV(i,args[0],d[args[0]])]
                            multlist+=[find_def_mult(i,args[0],args[2],args[4],full_list_op)]
                            dict_type[args[0]]=['x' for rpos in range(rs)]
                        else:
                            partial_repr=[]
                            for rpos in range(rs):
                                if(dict_type[args[2]][rpos]=='0' or dict_type[args[4]][rpos]=='0'):
                                    var_repr=np.array([0 for sizeofarray in range(count)],bool)
                                elif(dict_type[args[2]][rpos]=='1'):
                                    var_repr=np.copy(d[args[4]][rpos])
                                else:
                                    var_repr=np.copy(d[args[2]][rpos])
                                partial_repr+=[var_repr] 
                            d[args[0]]=np.array(partial_repr)
                            full_list_op+=[OperandV(i,args[0],d[args[0]])]
                            dict_type[args[0]]=find_types_AND(dict_type[args[2]],dict_type[args[4]])
                        if len(args)>5:
                            print("warning : \""+lines[i][:-1]+"\" has too many uncommented parts. (line "+str(i+1)+")")
                        
                    #REFRESH
                    elif len(args)>3 and args[2] in list_op_ref:
                        nbr+=1
                        partial_repr=[]
                        for rpos in range(rs):
                            count+=1
                            var_repr=np.array([0 for sizeofarray in range(count)],bool)
                            var_repr[count-1]=True
                            partial_repr+=[var_repr]
                        d[args[0]]=np.array(partial_repr)
                        full_list_op+=[OperandV(i,args[0],d[args[0]])]
                        dict_type[args[0]]=['x' for rpos in range(rs)]
                        if len(args)>4:
                            print("warning : \""+lines[i][:-1]+"\" has too many uncommented parts. (line "+str(i+1)+")")
                        
                    #NOT
                    elif len(args)>3 and args[2] in list_op_not:
                        d[args[0]]=np.copy(d[args[3]])
                        full_list_op+=[OperandV(i,args[0],d[args[0]])]
                        dict_type[args[0]]=find_types_NOT(dict_type[args[3]])
                        if len(args)>4:
                            print("warning : \""+lines[i][:-1]+"\" has too many uncommented parts. (line "+str(i+1)+")")
                        
                    #OR
                    elif len(args)>4 and args[3] in list_op_or:
                        if(not is_mask_op(dict_type[args[2]],dict_type[args[4]])):
                            partial_repr=[]
                            for rpos in range(rs):
                                count+=1
                                var_repr=np.array([0 for sizeofarray in range(count)],bool)
                                var_repr[count-1]=True
                                partial_repr+=[var_repr]    
                            d[args[0]]=np.array(partial_repr)
                            full_list_op+=[OperandV(i,args[0],d[args[0]])]
                            multlist+=[find_def_mult(i,args[0],args[2],args[4],full_list_op)]
                            dict_type[args[0]]=['x' for rpos in range(rs)]
                        else:
                            partial_repr=[]
                            for rpos in range(rs):
                                if(dict_type[args[2]][rpos]=='1' or dict_type[args[4]][rpos]=='1'):
                                    var_repr=np.array([0 for sizeofarray in range(count)],bool)
                                elif(dict_type[args[2]][rpos]=='0'):
                                    var_repr=np.copy(d[args[4]][rpos])
                                else:
                                    var_repr=np.copy(d[args[2]][rpos])
                                partial_repr+=[var_repr]             
                            d[args[0]]=np.array(partial_repr)
                            full_list_op+=[OperandV(i,args[0],d[args[0]])]
                            dict_type[args[0]]=find_types_OR(dict_type[args[2]],dict_type[args[4]])
                        if len(args)>5:
                            print("warning : \""+lines[i][:-1]+"\" has too many uncommented parts. (line "+str(i+1)+")")
                        
                    #ROT
                    elif len(args)>4 and (args[3] in list_op_rot or args[2] in list_op_rot):
                        if(args[3] in list_op_rot):
                            r=int(args[4])
                            varname=args[2]
                        else:
                            try:
                                r=int(args[4])
                                varname=args[3]
                            except:
                                r=int(args[3])
                                varname=args[4]
                        if(args[3] in list_op_rotl or args[2] in list_op_rotl):r=-r
                        if(r>=rs):r=r%rs
                        elif(r<0 and (-r)%rs==0):r=0
                        elif(r<0):r=rs-((-r)%rs)
                        partial_repr=[]
                        for rpos in range(rs):
                            partial_repr+=[np.copy(d[varname][(rpos+rs-r)%rs])]
                        d[args[0]]=np.array(partial_repr)
                        full_list_op+=[OperandV(i,args[0],d[args[0]])]
                        dict_type[args[0]]=[dict_type[varname][(rpos+rs-r)%rs] for rpos in range(rs)]
                        
                    #SHIFT
                    elif len(args)>4 and (args[3] in list_op_shift or args[2] in list_op_shift):
                        if(args[3] in list_op_shift):
                            r=int(args[4])
                            varname=args[2]
                        else:
                            try:
                                r=int(args[4])
                                varname=args[3]
                            except:
                                r=int(args[3])
                                varname=args[4]
                        if(r>=rs or -r>=rs):
                            print ("warning : shift value exceeds register size.")
                            partial_repr=[]
                            for rpos in range(rs):
                                partial_repr+=[np.array([0 for sizeofarray in range(count)],bool)]
                            d[args[0]]=np.array(partial_repr)
                            full_list_op+=[OperandV(i,args[0],d[args[0]])]
                            dict_type[args[0]]=['0' for rpos in range(rs)]
                            
                        elif(((args[3] in list_op_shiftl or args[2] in list_op_shiftl) and r>=0) or ((args[3] in list_op_shiftr or args[2] in list_op_shiftr) and r<=0)):
                            if(r<0):
                                r=-r
                            partial_repr=[]
                            for rpos in range(rs):
                                if(rpos<rs-r):
                                    partial_repr+=[np.copy(d[varname][rpos+r])]
                                else:
                                    partial_repr+=[np.array([0 for sizeofarray in range(count)],bool)]
                            d[args[0]]=np.array(partial_repr)
                            full_list_op+=[OperandV(i,args[0],d[args[0]])]
                            dict_type[args[0]]=['x' for rpos in range(rs-r)]+['0' for rpos in range(rs-r,rs)]
                            
                        else:
                            if(r<0):
                                r=-r
                            partial_repr=[]
                            for rpos in range(rs):
                                if(rpos<r):
                                    partial_repr+=[np.array([0 for sizeofarray in range(count)],bool)]
                                else:
                                    partial_repr+=[np.copy(d[varname][rpos-r])]
                            d[args[0]]=np.array(partial_repr)
                            full_list_op+=[OperandV(i,args[0],d[args[0]])]
                            dict_type[args[0]]=['0' for rpos in range(r)]+['x' for rpos in range(r,rs)]
                        
                    #CST
                    elif len(args)>3 and args[2] in list_op_setcst:
                        varpos=0
                        constpos=3
                        partial_repr=[]
                        for rpos in range(rs):
                            var_repr=np.array([0 for sizeofarray in range(count)],bool)
                            partial_repr+=[var_repr]
                        d[args[varpos]]=np.array(partial_repr)
                        full_list_op+=[OperandV(i,args[varpos],d[args[varpos]])]
                        if args[constpos][:2]=='0b':
                            args[constpos]=args[constpos][2:]
                            while(len(args[constpos])<rs):
                                args[constpos]='0'+args[constpos]
                            if(len(args[constpos])==rs):
                                dict_type[args[varpos]]=[args[constpos][rpos] for rpos in range(rs)]
                            else:
                                raise Exception("\""+lines[i][:-1]+"\" : constant is too big. (in line "+str(i+1)+")")   
                        elif args[constpos][:2]=='0x':
                            args[constpos]=args[constpos][2:]
                            hexcst=args[constpos]
                            bincst=[b for b in bin(int(hexcst, 16))[2:].zfill(rs)]
                            if(len(bincst)==rs):
                                dict_type[args[varpos]]=bincst
                            else:
                                raise Exception("\""+lines[i][:-1]+"\": constant is too big. (in line "+str(i+1)+")")
                        else:
                            raise Exception("\""+lines[i][:-1]+"\" is not a valid definition for a constant. (in line "+str(i+1)+")")
                        
                    #CSTALL
                    elif len(args)>3 and args[2] in list_op_setcstall:
                        varpos=0
                        constpos=3
                        partial_repr=[]
                        for rpos in range(rs):
                            var_repr=np.array([0 for sizeofarray in range(count)],bool)
                            partial_repr+=[var_repr]
                        d[args[varpos]]=np.array(partial_repr)
                        full_list_op+=[OperandV(i,args[varpos],d[args[varpos]])]
                        if(len(args[constpos])>1):
                            print("warning : setcstall only requires one bit. (in line "+str(i+1)+")")
                        if args[constpos][0] in ['0','1']:
                            dict_type[args[varpos]]=[args[constpos][0] for rpos in range(rs)] 
                        else:
                            raise Exception("\""+lines[i][:-1]+"\" is not a valid definition for a constant. (in line "+str(i+1)+")")
                        
                    #RENAME
                    elif(len(args)==3):
                        d[args[0]]=np.copy(d[args[2]])
                        full_list_op+=[OperandV(i,args[0],d[args[0]])]
                        dict_type[args[0]]=dict_type[args[2]]
                        
                    
                    
                    else:
                        print("warning : \""+lines[i][:-1]+"\" is not a comment or a valid expression. (line "+str(i+1)+")")     
                else:
                    print("warning : \""+lines[i][:-1]+"\" is not a comment or a valid expression. (line "+str(i+1)+")")

    for di in d:
        copyandresize(d,di,rs,count)
    for m in multlist:
        for op in m.ops:
            op.LC=resizevar(op.LC,rs,count)
            

    C=CircuitV(multlist,rs,full_list_op,count/rs-len(multlist)-nbr,len(multlist),nbr)
    return C