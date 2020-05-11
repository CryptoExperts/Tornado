##################################################################################
#######################################FORMAT#####################################
###############################################################################
#
# Implementation of tightPROVE+ in SageMath
#
# tightPROVE+ is a formal verification tool for the tight register probing  
# security of masked implementations, introduced in https://ia.cr/2020/506
#
# File: format.sage
# Description: this file contains a function that transforms code written in a 
# high-level language into a sequence of operations that can be fed to 
# tightPROVE, the precursor of tightPROVE+, working in the bit-probing model
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

def format_code(text_name , text_ext = "", save=False):
#takes as input a list of instructions in a rather natural language (close to the C language), 
#and outputs a list of instructions that can be read by tightPROVE. 
#It is possible to save the result in a file, named text_name_f
    list_op_add = ["ADD","add","+","XOR","xor","Add","Xor","^"]
    list_op_mult = ["AND","and","And","*","&","MULT","mult","Mult","."]
    list_op_ref = ["R","r","REF","ref","Ref","REFRESH","Refresh","refresh"]
    list_op_not = ["NOT","Not","not","~"]
    list_op_or = ["OR","Or","or","|",]
    list_op = list_op_add+list_op_mult+list_op_ref+list_op_not+list_op_or
    list_symbols = ['+','^','*','&','.','~','!','|','=']
    list_comms = ['#','/',';','%']
    list_numbers = ['0','1','2','3','4','5','6','7','8','9']
    list_separators=[',','(',')']
    
    with open(text_name+text_ext , "r") as fr:
        lines = fr.readlines()

    splitlines=[]     #lines of instructions split in 2 or 3 arguments
    d={}              #this dictionary stores the line number (in the formatted circuit) of each variable
    count=0           #count contains the number of the line of the input/variable in the formatted circuit that corresponds to what the algorithm is reading in the original file
    output_list=[]
        
    for i in range(len(lines)):
        args = lines[i]
    
        if(len(args)>0 and 'rs' in args):
            if(int(args.split('=')[1])!=1):
                raise Exception("wrong algorithm for this register size. (found rs=%d instead of rs=1)"%int(args.split('=')[1]))
            else:
                continue
    
        ###getting rid of comments and line breaks
        if(args=="\n"):
            continue
        for comms in list_comms:
            if(comms in args):
                args=args[:args.index(comms)]

        args=args.split()
          
            
        ###inputs
        if(len(args)>0 and args[0]=='in'):
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
                                splitlines+=[["in",str(count)]]
                                d[base+'['+str(k)+']']=count
                                count+=1
                        else:
                            for k in range(n1):
                                splitlines+=[["in",str(count)]]
                                d[base+'['+str(k)+']']=count
                                count+=1

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
                            splitlines+=[["in",str(count)]]
                            d[stringvar]=count
                            count+=1
                            list_n2[-1][1]+=1
                            for k in range(len(list_n2)-1,0,-1):
                                if(list_n2[k][1]>list_n[k][1]):
                                    list_n2[k][1]=list_n[k][0]
                                    list_n2[k-1][1]+=1
                        stringvar=base
                        for k in range(len(list_n)):
                            stringvar+='['+str(list_n2[k][1])+']'
                        splitlines+=[["in",str(count)]]
                        d[stringvar]=count
                        count+=1
                        
                ###defining isolated inputs 
                elif((args[j]!="..." and j==0) or (j>0 and args[j]!="..." and args[j-1]!="...")):
                    splitlines+=[["in",str(count)]]
                    d[args[j]]=count
                    count+=1
                    
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
                            splitlines+=[["in",str(count)]]
                            d[base1+str(k)]=count
                            count+=1

                    elif(n2>n1):
                        for k in range(n1+1,n2+1):
                            splitlines+=[["in",str(count)]]
                            d[base1+str(k)]=count
                            count+=1
                            
                    else:
                        raise Exception("... should be between indexed variable names with different index.")
    
                        
        ###outputs
        elif(len(args)>0 and args[0]=='out'):
            args=args[1:]
            for j in range(len(args)):

                ###defining output tables
                if('[' in args[j] and ']' in args[j]):

                    ###tables of dimension 1
                    if('][' not in args[j]):
                        pos1=args[j].index('[')
                        pos2=args[j].index(']')
                        if(pos2<pos1):
                            pos1,pos2=pos2,pos1 
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
                                output_list+=[base+'['+str(k)+']'] 
                        else:
                            for k in range(n1):
                                output_list+=[base+'['+str(k)+']'] 

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
                            output_list+=[stringvar]
                            list_n2[-1][1]+=1
                            for k in range(len(list_n2)-1,0,-1):
                                if(list_n2[k][1]>list_n[k][1]):
                                    list_n2[k][1]=list_n[k][0]
                                    list_n2[k-1][1]+=1
                        stringvar=base
                        for k in range(len(list_n)):
                            stringvar+='['+str(list_n2[k][1])+']'
                        output_list+=[stringvar]
                        
                ###defining isolated outputs 
                elif((args[j]!="..." and j==0) or (j>0 and args[j]!="..." and args[j-1]!="...")):
                    output_list+=[args[j]]
                    
                ###defining lists of outputs 
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
                            output_list+=[base1+str(k)]

                    else:
                        for k in range(n1+1,n2+1):
                            output_list+=[base1+str(k)]
                
                        
        ###other lines for formulas
        elif(len(args)>0):

            ###separates variables from symbols and removes unnecessary characters such as , ) and (
            for symbol in list_symbols+list_separators:
                L=[]
                for a in args:
                    if(symbol in a):
                        A=a
                        while(symbol in A):
                            if(len(A[:A.index(symbol)])>0):
                                L+=[A[:A.index(symbol)]]
                            if(symbol not in list_separators):
                                L+=[symbol]
                            A=A[A.index(symbol)+1:]
                        if(len(A)>0):
                            L+=[A]
                    else:
                        L+=[a]  
                args=L
                
            if (args[0] in list_op):  
                #SYNTAX : "op res var1 var2"   or   "op res var" for refresh and not operators

                #XOR
                if args[0] in list_op_add and len(args)>3:
                    splitlines+=[["xor",str(d[args[2]]),str(d[args[3]])]]
                    d[args[1]]=count
                    count+=1
                    if len(args)>4:
                        print("warning : \""+lines[i][:-1]+"\" has too many uncommented parts. (line "+str(i+1)+")")
                        
                #AND
                elif args[0] in list_op_mult and len(args)>3:
                    splitlines+=[["and",str(d[args[2]]),str(d[args[3]])]]
                    d[args[1]]=count
                    count+=1
                    if len(args)>4:
                        print("warning : \""+lines[i][:-1]+"\" has too many uncommented parts. (line "+str(i+1)+")")
                        
                #REF
                elif args[0] in list_op_ref and len(args)>2:
                    splitlines+=[["ref",str(d[args[2]])]]
                    d[args[1]]=count
                    count+=1
                    if len(args)>3:
                        print("warning : \""+lines[i][:-1]+"\" has too many uncommented parts. (line "+str(i+1)+")")
                        
                #NOT
                elif args[0] in list_op_not and len(args)>2:
                    splitlines+=[["not",str(d[args[2]])]]
                    d[args[1]]=count
                    count+=1
                    if len(args)>3:
                        print("warning : \""+lines[i][:-1]+"\" has too many uncommented parts. (line "+str(i+1)+")")
                        
                #OR
                elif args[0] in list_op_or and len(args)>3:
                    splitlines+=[["or",str(d[args[2]]),str(d[args[3]])]]
                    d[args[1]]=count
                    count+=1
                    if len(args)>4:
                        print("warning : \""+lines[i][:-1]+"\" has too many uncommented parts. (line "+str(i+1)+")")
                        
                else:
                    print("warning : \""+lines[i][:-1]+"\" is not a comment or a valid expression. (in line "+str(i+1)+")")
                        
                        
                        
            elif(len(args)>1 and args[1]=="="):  
                #SYNTAX : "res = var1 op var2" or "res = op var" or "res = op var1 var2"
                if len(args)>4 and args[2] in list_op:
                    (args[2],args[3])=(args[3],args[2])
                
                #XOR
                if len(args)>4 and args[3] in list_op_add:
                    splitlines+=[["xor",str(d[args[2]]),str(d[args[4]])]]
                    d[args[0]]=count
                    count+=1
                    if len(args)>5:
                        print("warning : \""+lines[i][:-1]+"\" has too many uncommented parts. (line "+str(i+1)+")")
                        
                #AND
                elif len(args)>4 and args[3] in list_op_mult:
                    splitlines+=[["and",str(d[args[2]]),str(d[args[4]])]]
                    d[args[0]]=count
                    count+=1
                    if len(args)>5:
                        print("warning : \""+lines[i][:-1]+"\" has too many uncommented parts. (line "+str(i+1)+")")
                        
                #REF
                elif len(args)>3 and args[2] in list_op_ref:
                    splitlines+=[["ref",str(d[args[3]])]]
                    d[args[0]]=count
                    count+=1
                    if len(args)>4:
                        print("warning : \""+lines[i][:-1]+"\" has too many uncommented parts. (line "+str(i+1)+")")
                        
                #NOT
                elif len(args)>3 and args[2] in list_op_not:
                    splitlines+=[["not",str(d[args[3]])]]
                    d[args[0]]=count
                    count+=1
                    if len(args)>4:
                        print("warning : \""+lines[i][:-1]+"\" has too many uncommented parts. (line "+str(i+1)+")")
                        
                #OR
                elif len(args)>4 and args[3] in list_op_or:
                    splitlines+=[["or",str(d[args[2]]),str(d[args[4]])]]
                    d[args[0]]=count
                    count+=1
                    if len(args)>5:
                        print("warning : \""+lines[i][:-1]+"\" has too many uncommented parts. (line "+str(i+1)+")")
                        
                #RENAME
                elif(len(args)==3):
                    d[args[0]]=d[args[2]]
                    
                else:
                    print("warning : \""+lines[i][:-1]+"\" is not a comment or a valid expression. (line "+str(i+1)+")")
                        
            else:
                print("warning : \""+lines[i][:-1]+"\" is not a comment or a valid expression. (line "+str(i+1)+")")
                   
    for o in output_list:
        try:
            splitlines+=[["out",str(d[o])]]
        except:
            print("warning : one of the output variables (" + o + ") is not used.")
                
    if(save==True):
        write_file(text_name+"_f"+text_ext,splitlines)
    return splitlines