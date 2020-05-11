###############################################################################
#
# Implementation of tightPROVE+ in SageMath
#
# tightPROVE+ is a formal verification tool for the tight register probing  
# security of masked implementations, introduced in https://ia.cr/2020/506
#
# File: refresh.sage
# Description: this file contains functions used to find the placement of
# refresh gadgets in a given circuit and place them automatically until the
# circuit is secure.
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
#######################################REFRESH#######################################

def insert_ref(L,l):
#inserts a gadget to refresh the l_th element of L, and make changes to the other lines accordingly (the indexes of the following operations change)
    Lr=L[:(l+1)]
    Lr+=[["ref",str(l)]]
    for i in range(l+1,len(L)):
        op=L[i][0]
        opA=int(L[i][1])
        if(len(L[i])>2):
            opB=int(L[i][2])
        if(opA>l):
            opA+=1
        if(len(L[i])>2 and opB>l):
            opB+=1
        if(len(L[i])>2):
            Lr+=[[op,str(opA),str(opB)]]
        else:
            Lr+=[[op,str(opA)]]
    return Lr

def apply_refresh1(L,ref,verbose):
#for a line ref that is a refresh instruction in L, finds a 'good' set of gadgets it should be applied to
#by finding one line it can be applied to that yields the least number of attacks
    if(ref>len(L)-1 or ref<1):
        raise Exception("ref must be a line number in L refering to a previous gadget")
    if(L[ref][0]!="ref"):
        raise Exception("ref must refer to a line with a refresh gadget")
    list_instructions = generate_list_ins_from_lines(L)
    test_circuit = Circuit(list_instructions)
    PO,IV=test_circuit.generate_pairs_operands()
    mult_set = import_mult(PO)
    A=search_attack(mult_set,verbose=False)
    min_r = len(A)
    pos=-1

    for i in range(ref+1,len(L)):

        if(str(ref-1) in L[i]):  #trying to find a call to the original gadget after definition of refresh
            for j in range(1,len(L[i])):
                if(L[i][j]==str(ref-1)):
                    L[i][j]=str(ref) #once a line is found, replace call to gadget to a call to the refreshed gadget
                    break
            #then find the number of attacks
            list_instructions = generate_list_ins_from_lines(L)
            test_circuit = Circuit(list_instructions)
            PO,IV=test_circuit.generate_pairs_operands()
            try:
                import_mult(PO)
                mult_set = import_mult(PO)
            except:
                continue
            SA=search_attack(mult_set,verbose=False)
            noa = len(SA)
            if(noa<min_r):
                min_r=noa
                pos=i
                A=SA
            L[i][j]=str(ref-1)  #removing the refresh to try to apply it elsewhere
        else:
            continue
    if(pos!=-1):
        for j in range(len(L[pos])):
            if(L[pos][j]==str(ref-1)):
                L[pos][j]=str(ref)
        if(verbose==True):
            print("new noa : "+str(min_r))
    else:
        if(verbose==True):
            print("no good place found")
    return A

def apply_refresh2(L,ref,verbose):
#for a line ref that is a refresh instruction in L, finds a 'good' set of gadgets it should be applied to
#by applying it on every input of multiplication it can be applied to (sigificantly faster than the first one)
    if(ref>len(L)-1 or ref<1):
        raise Exception("ref must be a line number in L refering to a previous gadget")
    if(L[ref][0]!="ref"):
        raise Exception("ref must refer to a line with a refresh gadget")
    list_instructions = generate_list_ins_from_lines(L)
    test_circuit = Circuit(list_instructions)
    PO,IV=test_circuit.generate_pairs_operands()
    mult_set = import_mult(PO)
    A=search_attack(mult_set,verbose=False)
    min_r = len(A)
    pos=-1

    for i in range(ref+1,len(L)):

        if(L[i][0]=="and" and str(ref-1) in L[i]):  #apply the refreshed gadget on every AND gadget that calls the original unrefreshed gadget
            for j in range(1,len(L[i])):
                if(L[i][j]==str(ref-1)):
                    L[i][j]=str(ref)
                    break
    list_instructions = generate_list_ins_from_lines(L)
    test_circuit = Circuit(list_instructions)
    PO,IV=test_circuit.generate_pairs_operands()
    try:
        import_mult(PO)
    except:
        if(verbose==True):
            print("same operand error")
        return A
    mult_set = import_mult(PO)
    SA=search_attack(mult_set,verbose=False)
    noa = len(SA)
    if(verbose==True):
        print("new noa : "+str(noa))
    return SA

###WARNING : both of the previous functions are used to find a little number of refresh gadgets
#that get rid of all the attacks in a circuit, thanks to the functions below. However, none of them are optimal.
#there are counter-examples that show they do not yield the optimal number of refresh gadgets : see testR1 and testR2 in the test folder


def find_refresh_v1(filename,savef=False,verbose=False,save=False,saveto="",showgraph=False):
#uses apply_refresh1 to find a way to put refresh gadgets in a circuit described in a file
    t=time()
    noa=-1
    nor=0
    while(noa!=0):  #while some attacks exists, the method will try to add a refresh and apply it
        nor+=1
        if(noa==-1):
            L=load_file(filename)
            if(L[0]!=['in','0']): #if the file is not in tightPROVE format, format it
                Lorigin=separate_symbols(copy(L))
                L=format_code(filename)
        list_instructions = generate_list_ins_from_lines(L)
        test_circuit = Circuit(list_instructions)
        PO,IV=test_circuit.generate_pairs_operands()
        if(noa==-1):
            mult_set = import_mult(PO)
            A=search_attack(mult_set,verbose=False)
            noa=len(A)
            minmin=noa
            if(noa==0):
                if(verbose==True):
                    print("there's already no attack")
                if save:
                    if saveto == "":
                        saveto = filename + "_R1"
                    write_file(saveto,Lorigin)
                return L
        bestline=-1
        testops=[A[i].split()[2] for i in range(noa)] #this is the list of operands that can be attacked
        if(verbose==True):
            print(testops)
        incriminated_lines = [IV.index(int(testops[i])) for i in range(noa)]  #translates the list of faulty operands into the list of lines where we can find them
        if(verbose==True):
            print(incriminated_lines)
        if(showgraph==True):
            ins_to_graph(L,5,highlight=[i+1-get_nb_ref_before_line(L,i) for i in incriminated_lines])
        LL=[]
        for l in incriminated_lines:   #the method tries to apply a refresh on each faulty operand successively, and finds the one that makes the number of attacks minimal
            LL+=[insert_ref(L,l)]
            testmin=apply_refresh1(LL[-1],l+1,verbose)
            if(len(testmin)<minmin):
                minmin=len(testmin)
                bestline=l
                A=testmin
            if(len(testmin)==0):
                break
        if(bestline!=-1):
            L=LL[incriminated_lines.index(bestline)]
        else:
            if(verbose==True):
                print("can't find a way to place a refresh")
            break
        noa=minmin

        if(save):
            vartr,ltr=linef_to_lineo(bestline,L,Lorigin)
            insert_line2(Lorigin,ltr+1,[vartr+'_R = ref '+vartr])
            for i in range(bestline+2,len(L)):
                if(str(bestline+1) in L[i]):
                    v,linetochange=linef_to_lineo(i,L,Lorigin)
                    for j in range(len(Lorigin[linetochange])):
                        if(Lorigin[linetochange][j]==vartr):
                            Lorigin[linetochange][j]=vartr+'_R'
            if saveto == "":
                saveto = filename + "_R1"
            write_file(saveto,Lorigin)

    if(showgraph==True):
        ins_to_graph(L,5)

    list_instructions = generate_list_ins_from_lines(L)
    test_circuit = Circuit(list_instructions)
    PO,IV=test_circuit.generate_pairs_operands()
    mult_set = import_mult(PO)
    A=search_attack(mult_set,verbose=False)
    testops=[A[i].split()[2] for i in range(noa)]
    if(verbose==True):
        print(testops)
    incriminated_lines = [IV.index(int(testops[i])) for i in range(noa)]
    if(verbose==True):
        print(incriminated_lines)
        print("number of refresh placed : "+str(nor))
        print("time elapsed : "+str(time()-t)+"s")

    if(savef==True and nor>0):
        write_file(filename+"_f_r1",L)

    if save:
        if saveto == "":
            saveto = filename + "_R1"
        write_file(saveto,Lorigin)

    return L

def find_refresh_v2(filename,savef=False,verbose=False,save=False,showgraph=False):
#uses apply_refresh1 to find a way to put refresh gadgets in a circuit described in a file
    t=time()
    noa=-1
    nor=0
    while(noa!=0):
        nor+=1
        if(noa==-1):
            L=load_file(filename)
            if(L[0]!=['in','0']):
                Lorigin=separate_symbols(copy(L))
                L=format_code(filename)
        list_instructions = generate_list_ins_from_lines(L)
        test_circuit = Circuit(list_instructions)
        PO,IV=test_circuit.generate_pairs_operands()
        if(noa==-1):
            #print(PO,IV)
            mult_set = import_mult(PO)
            A=search_attack(mult_set,verbose=False)
            noa=len(A)
            minmin=noa
            if(noa==0):
                if(verbose==True):
                    print("there's already no attack")
                return L
        bestline=-1
        testops=[A[i].split()[2] for i in range(noa)]
        if(verbose==True):
            print(testops)
        incriminated_lines = [IV.index(int(testops[i])) for i in range(noa)]
        if(verbose==True):
            print(incriminated_lines)
        if(showgraph==True):
            ins_to_graph(L,5,highlight=[i+1-get_nb_ref_before_line(L,i) for i in incriminated_lines])
        LL=[]
        for l in incriminated_lines:
            LL+=[insert_ref(L,l)]
            testmin=apply_refresh2(LL[-1],l+1,verbose)
            if(len(testmin)<minmin):
                minmin=len(testmin)
                bestline=l
                A=testmin
            if(len(testmin)==0):
                break
        if(bestline!=-1):
            L=LL[incriminated_lines.index(bestline)]
        else:
            if(verbose==True):
                print("can't find a way to place a refresh")
            break
        noa=minmin

        if(save):
            vartr,ltr=linef_to_lineo(bestline,L,Lorigin)
            insert_line2(Lorigin,ltr+1,[vartr+'_R = ref '+vartr])
            for i in range(bestline+2,len(L)):
                if(str(bestline+1) in L[i]):
                    v,linetochange=linef_to_lineo(i,L,Lorigin)
                    for j in range(len(Lorigin[linetochange])):
                        if(Lorigin[linetochange][j]==vartr):
                            Lorigin[linetochange][j]=vartr+'_R'
            write_file(filename+"_R2",Lorigin)

    if(showgraph==True):
        ins_to_graph(L,5,highlight=[i+1-get_nb_ref_before_line(L,i) for i in incriminated_lines])


    list_instructions = generate_list_ins_from_lines(L)
    test_circuit = Circuit(list_instructions)
    PO,IV=test_circuit.generate_pairs_operands()
    mult_set = import_mult(PO)
    A=search_attack(mult_set,verbose=False)
    testops=[A[i].split()[2] for i in range(noa)]
    if(verbose==True):
        print(testops)
    incriminated_lines = [IV.index(int(testops[i])) for i in range(noa)]
    if(verbose==True):
        print(incriminated_lines)
        print("number of refresh placed : "+str(nor))
        print("time elapsed : "+str(time()-t)+"s")
        #print(L)

    if(savef==True and nor>0):
        write_file(filename+"_f_r2",L)

    return L
