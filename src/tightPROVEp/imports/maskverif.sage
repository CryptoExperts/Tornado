###############################################################################
#
# Implementation of tightPROVE+ in SageMath
#
# tightPROVE+ is a formal verification tool for the tight register probing  
# security of masked implementations, introduced in https://ia.cr/2020/506
#
# File: maskverif.sage
# Description: this file contains a function that encodes the description of a
# circuit into code that can be verified by maskverif for different masking
# orders.
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
#######################################MASKVERIF#######################################

def write_code(func,mo_i,mo_f):
#writes code in a file named "code" that can be verified by maskverif
#the function to be converted is func, and can be 'and', 'xor, 'ref, 
#or a file containing a set of these instructions
#it creates different masked implementations of func
#for masking orders ranging from mo_i to mo_f
    
    with open("code", "w") as fr:
        for mo in range(mo_i,mo_f+1):
            mostr=str(mo)
            if(func=='and'):
                fr.write("proc ISW_AND"+str(mo)+":\n")
                fr.write("  inputs: a[0:"+mostr+"], b[0:"+mostr+"]\n")
                fr.write("  outputs: c[0:"+mostr+"]\n")
                fr.write("  randoms: ")
                for i in range(mo+1):
                    for j in range(i+1,mo+1):
                        if(i<mo-1):
                            fr.write("r"+str(i)+str(j)+", ")
                        else:
                            fr.write("r"+str(i)+str(j)+";\n\n")
                for i in range(mo+1):
                    fr.write("  c["+str(i)+"] := a["+str(i)+"] * b["+str(i)+"];\n")
                for i in range(mo+1):
                    for j in range(i+1,mo+1):
                        fr.write("  c["+str(i)+"] := c["+str(i)+"] + r"+str(i)+str(j)+";\n")
                        fr.write("  a"+str(i)+"b"+str(j)+" := a["+str(i)+"] * b["+str(j)+"];\n")
                        fr.write("  a"+str(j)+"b"+str(i)+" := a["+str(j)+"] * b["+str(i)+"];\n")
                        fr.write("  aux := r"+str(i)+str(j) + " + a"+str(i)+"b"+str(j)+";\n")
                        fr.write("  aux := aux" + " + a"+str(j)+"b"+str(i)+";\n")
                        fr.write("  c["+str(j)+"] := c["+str(j)+"] + aux;\n")
                fr.write("end\n\n")
                
            elif(func=='xor'):
                fr.write("proc XOR"+str(mo)+":\n")
                fr.write("  inputs: a[0:"+mostr+"], b[0:"+mostr+"]\n")
                fr.write("  outputs: c[0:"+mostr+"];\n\n")
                fr.write("  c := a + b;\n")
                fr.write("end\n\n")
            
            elif(func=='ref'):
                fr.write("proc ISW_REF"+str(mo)+":\n")
                fr.write("  inputs: a[0:"+mostr+"]\n")
                fr.write("  outputs: c[0:"+mostr+"]\n")
                fr.write("  randoms: ")
                for i in range(mo+1):
                    for j in range(i+1,mo+1):
                        if(i<mo-1):
                            fr.write("r"+str(i)+str(j)+", ")
                        else:
                            fr.write("r"+str(i)+str(j)+";\n\n")
                for i in range(mo+1):
                    fr.write("  c["+str(i)+"] := a["+str(i)+"];\n")
                for i in range(mo+1):
                    for j in range(i+1,mo+1):
                        fr.write("  c["+str(i)+"] := c["+str(i)+"] + r"+str(i)+str(j)+";\n")
                        fr.write("  c["+str(j)+"] := c["+str(j)+"] + r"+str(i)+str(j)+";\n")
                fr.write("end\n\n")
                
                
            #elif(func=='not')
            
            else:
                L=load_file(func)
                if(L[0]!=['in','0']):
                    L=format_code(func)
                fr.write("proc "+func+"_"+str(mo)+":\n")
                inlist=[]
                outlist=[]
                auxlist=[]
                for i in range(len(L)):
                    if(L[i][0]=='in'):
                        inlist+=[i]
                    elif(L[i][0]=='out'):
                        outlist+=[i]
                    else:
                        auxlist+=[i]
                fr.write("  inputs: ")
                for i in range(len(inlist)-1):
                    fr.write('x'+str(inlist[i])+"_[0:"+mostr+"], ")
                fr.write('x'+str(inlist[-1])+"_[0:"+mostr+"]\n")

                fr.write("  outputs: ")
                if(len(outlist)>0):
                    for i in range(len(outlist)-1):
                        fr.write('out'+str(outlist[i])+"_[0:"+mostr+"], ")
                    fr.write('out'+str(outlist[-1])+"_[0:"+mostr+"]\n")
                else:
                    fr.write("\n")
                
                fr.write("  shares: ")
                for i in range(len(auxlist)-1):
                    fr.write('aux'+str(auxlist[i])+"_[0:"+mostr+"], ")
                fr.write('aux'+str(auxlist[-1])+"_[0:"+mostr+"];\n\n")
                
                for i in range(len(L)):
                    op=L[i][0]
                    a=L[i][1]
                    A=int(a)
                    if(len(L[i])==3):
                        b=L[i][2]
                        B=int(b)
                    if(i in auxlist):
                        fr.write('  aux'+str(i)+"_ = ")
                        if(op=='xor'):
                            fr.write("XOR"+mostr+"(")
                            if(A in inlist):
                                fr.write('x'+a+'_')
                            elif(A in auxlist):
                                fr.write('aux'+a+'_')
                            fr.write(",")
                            if(B in inlist):
                                fr.write('x'+b+'_')
                            elif(B in auxlist):
                                fr.write('aux'+b+'_')
                            fr.write(");\n")
                        elif(op=='and'):
                            fr.write("ISW_AND"+mostr+"(")
                            if(A in inlist):
                                fr.write('x'+a+'_')
                            elif(A in auxlist):
                                fr.write('aux'+a+'_')
                            fr.write(",")
                            if(B in inlist):
                                fr.write('x'+b+'_')
                            elif(B in auxlist):
                                fr.write('aux'+b+'_')
                            fr.write(");\n")
                        elif(op=='ref'):
                            fr.write("ISW_REF"+mostr+"(")
                            if(A in inlist):
                                fr.write('x'+a+'_')
                            elif(A in auxlist):
                                fr.write('aux'+a+'_')
                            fr.write(");\n")
                        #elif(op='not')
                    elif(i in outlist):
                        fr.write('  out'+str(i)+"_ = ")
                        if(A in inlist):
                            fr.write('x'+a+'_')
                        elif(A in auxlist):
                            fr.write('aux'+a+'_')
                        fr.write(";\n")
                fr.write("end\n\n")