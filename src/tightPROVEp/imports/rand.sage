###############################################################################
#
# Implementation of tightPROVE+ in SageMath
#
# tightPROVE+ is a formal verification tool for the tight register probing  
# security of masked implementations, introduced in https://ia.cr/2020/506
#
# File: rand.sage
# Description: this file contains functions that aim at creating descriptions
# of circuits created randomly with certain constraints such as the number of
# multiplication gadgets, for testing purposes.
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
#######################################RAND#######################################
#This part contains functions that can generate random circuits in different ways. Note that 
#the circuits generated with these methods do not exhibit any particular structure :
#each gadget is created iteratively by choosing its inputs at random among the previously created gadgets

#in each function, nbi denotes the number of inputs ,nbo the number of outputs (which does not affect a circuit security in any way//could be removed)
#nbgates the total number of gadgets used, p_axn a list containing the proportion of AND XOR and NOT gates (in this order)
#nb_axn a list containing the exact number of AND XOR and NOT gates 


def rand_circ(nbi,nbo,nb_gates,p_axn):
#creates a random circuit with a given proportion of gates and saves it in a file named "randC"
    with open("randC","w") as fr:
        for i in range(nbi):
            fr.write("in "+str(i)+"\n")
        for i in range(nb_gates):
            r=random()
            var1=randint(0,nbi-1+i)
            var2=var1
            while(var2==var1):
                var2=randint(0,nbi-1+i)
            if(r<p_axn[0]):
                fr.write("and "+str(var1)+" "+str(var2)+"\n")
            elif(r<p_axn[0]+p_axn[1]):
                fr.write("xor "+str(var1)+" "+str(var2)+"\n")
            else:
                fr.write("not "+str(var1)+"\n")
        for i in range(nbo):
            varo=randint(nbi,nbi+nb_gates-1)
            fr.write("out "+str(varo)+"\n")

def rand_circ2(nbi,nbo,nb_gates,p_axn):
#creates a random circuit with a given proportion of gates and returns the corresponding list of instructions
    splitlines=[]
    for i in range(nbi):
        splitlines+=[["in",str(i)]]
    for i in range(nb_gates):
        r=random()
        var1=randint(0,nbi-1+i)
        var2=var1
        while(var2==var1):
            var2=randint(0,nbi-1+i)
        if(r<p_axn[0]):
            splitlines+=[["and",str(var1),str(var2)]]
        elif(r<p_axn[0]+p_axn[1]):
            splitlines+=[["xor",str(var1),str(var2)]]
        else:
            splitlines+=[["not",str(var1)]]
    for i in range(nbo):
        varo=randint(nbi,nbi+nb_gates-1)
        splitlines+=[["out",str(varo)]]
    return splitlines

def exact_rand_circ(nbi,nbo,nb_axn):
#creates a random circuit with a given number of gates and saves it in a file named "randC"
    with open("randC","w") as fr:
        for i in range(nbi):
            fr.write("in "+str(i)+"\n")
        AXN=copy(nb_axn)
        for i in range(sum(nb_axn)):
            r=randint(1,len([n for n in AXN if n>0]))
            var1=randint(0,nbi-1+i)
            var2=var1
            while(var2==var1):
                var2=randint(0,nbi-1+i)
            if(r==1):
                if(AXN[0]!=0):
                    fr.write("and "+str(var1)+" "+str(var2)+"\n")
                    AXN[0]-=1
                elif(AXN[1]!=0):
                    fr.write("xor "+str(var1)+" "+str(var2)+"\n")
                    AXN[1]-=1
                else:
                    fr.write("not "+str(var1)+"\n")
                    AXN[2]-=1
            elif(r==2):
                if(AXN[0]==0 or AXN[1]==0):
                    fr.write("not "+str(var1)+"\n")
                    AXN[2]-=1
                else:
                    fr.write("xor "+str(var1)+" "+str(var2)+"\n")
                    AXN[1]-=1
            elif(r==3):
                fr.write("not "+str(var1)+"\n")
                AXN[2]-=1
        for i in range(nbo):
            varo=randint(nbi,nbi+sum(nb_axn)-1)
            fr.write("out "+str(varo)+"\n")

def exact_rand_circ2(nbi,nbo,nb_axn):
#creates a random circuit with a given number of gates and returns the corresponding list of instructions
    splitlines=[]
    for i in range(nbi):
        splitlines+=[["in",str(i)]]
    AXN=copy(nb_axn)
    for i in range(sum(nb_axn)):
        r=randint(1,len([n for n in AXN if n>0]))
        var1=randint(0,nbi-1+i)
        var2=var1
        while(var2==var1):
            var2=randint(0,nbi-1+i)
        if(r==1):
            if(AXN[0]!=0):
                splitlines+=[["and",str(var1),str(var2)]]
                AXN[0]-=1
            elif(AXN[1]!=0):
                splitlines+=[["xor",str(var1),str(var2)]]
                AXN[1]-=1
            else:
                splitlines+=[["not",str(var1)]]
                AXN[2]-=1
        elif(r==2):
            if(AXN[0]==0 or AXN[1]==0):
                splitlines+=[["not",str(var1)]]
                AXN[2]-=1
            else:
                splitlines+=[["xor",str(var1),str(var2)]]
                AXN[1]-=1
        elif(r==3):
            splitlines+=[["not",str(var1)]]
            AXN[2]-=1
    for i in range(nbo):
        varo=randint(nbi,nbi+sum(nb_axn)-1)
        splitlines+=[["out",str(varo)]]
    return splitlines

def gen_randC(nt,noa,nbi,nbo,nb_gates,p_axn):
#for a given number of attacks(noa) and a proportion p_axn, tries to generate a circuit that has 0 attacks if noa=0
#or a circuit that have more than noa attacks otherwise
#the algorithm stops after nt unsuccessful attempts
    for i in range(nt):
        rand_circ(nbi,nbo,nb_gates,p_axn)
        list_instructions = generate_list_ins_from_file("randC")      
        test_circuit = Circuit(list_instructions)
        try:
            import_mult(test_circuit.generate_pairs_operands()[0])
            mult_set = import_mult(test_circuit.generate_pairs_operands()[0])
        except:
            continue
    
        L=search_attack(mult_set,verbose=False)
        if(noa==0 and len(L)==0 or noa>0 and len(L)>noa):
            print(i,L)
            print("number of attacks found : "+str(len(L)))
            return 1
    print("unsuccessful attempt")
    return 0
            
def gen_exact_randC(nt,noa,nbi,nbo,nb_axn):
#for a given number of attacks(noa) and the repartition of gates nb_axn, tries to generate a circuit that has 
#0 attacks if noa=0 or a circuit that have more than noa attacks otherwise
#the algorithm stops after nt unsuccessful attempts
    for i in range(nt):
        splitlines=exact_rand_circ2(nbi,nbo,nb_axn)
        list_instructions = generate_list_ins_from_lines(splitlines)      
        test_circuit = Circuit(list_instructions)
        try:
            import_mult(test_circuit.generate_pairs_operands()[0])
            mult_set = import_mult(test_circuit.generate_pairs_operands()[0])
        except:
            continue
    
        L=search_attack(mult_set,verbose=False)
        if(noa==0 and len(L)==0 or noa>0 and len(L)>noa):
            print(i,L)
            print("number of attacks found : "+str(len(L)))
            write_file("randC",splitlines)
            return 1
    print("unsuccessful attempt")
    return 0