###############################################################################
#
# Implementation of tightPROVE+ in SageMath
#
# tightPROVE+ is a formal verification tool for the tight register probing  
# security of masked implementations, introduced in https://ia.cr/2020/506
#
# File: search.sage
# Description: this file contains different ways to use tightPROVE, with
# different options and different levels of verbosity.
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
#######################################SEARCH#######################################

def simple_search(filename,verbose=False,showtime=False,multiproc=False,order=False,approx=0):
#from the description of a circuit in a file, searches for attacks
#*verbose determines how much information the algorithm prints about its current state and intermediate results
#*showtime enables the script to print the time it takes to finish each of its actions
#*multiproc enables the use of multiprocessing to speed up the search
#*order makes the algorithm search for the least attack order (warning : this slows down the search for attacks)
#*approx sets how the least attack order is searched. 0 means it will be exact, and higher numbers 
#means it will output an approximation
    t1=time()
    Ltest=format_code(filename)
    t2=time()
    if(showtime):
        print("format : "+str(t2-t1))
    list_instructions = generate_list_ins_from_lines(Ltest) 
    t3=time()
    if(showtime):
        print("list_ins : "+str(t3-t2))
    test_circuit = Circuit(list_instructions)
    t4=time()
    if(showtime):
        print("circuit : "+str(t4-t3))
    PO,IV=test_circuit.generate_pairs_operands()
    if(showtime):
        print(str(test_circuit.nb_mult)+" mults , "+str(test_circuit.nb_inputs)+" inputs.")
    t5=time()
    if(showtime):
        print("generate_pairs : "+str(t5-t4))
    mult_set = import_mult(PO)
    t6=time()
    if(showtime):
        print("import_mult : "+str(t6-t5))
    #print(IV)
    A=search_attack(mult_set,verbose,showtime,order,multiproc,approx)
    t7=time()
    if(showtime):
        print("search_attack : "+str(t7-t6))
    ms=[]
    return A

def simple_search_f(filename,verbose=False,showtime=False,order=False,multiproc=False,approx=0):
#same options as above, but the search is done from a formatted file (tightPROVE format)
    t2=time()
    list_instructions = generate_list_ins_from_file(filename)
    t3=time()
    if(showtime):
        print("list_ins : "+str(t3-t2))
    test_circuit = Circuit(list_instructions)
    t4=time()
    if(showtime):
        print("circuit : "+str(t4-t3))
    PO,IV=test_circuit.generate_pairs_operands()
    if(showtime):
        print(str(len(PO))+" mults")
    t5=time()
    if(showtime):
        print("generate_pairs : "+str(t5-t4))
    mult_set = import_mult(PO)
    t6=time()
    if(showtime):
        print("import_mult : "+str(t6-t5))
    #print(IV)
    A=search_attack(mult_set,verbose,showtime,order,multiproc,approx)
    t7=time()
    if(showtime):
        print("search_attack : "+str(t7-t6))
    return A

def simple_search_L(Lines,verbose=False,showtime=False,order=False,multiproc=False,approx=0):
#same options as above, but the search is done from a list of instructions
    t2=time()
    list_instructions = generate_list_ins_from_lines(Lines)
    t3=time()
    if(showtime):
        print("list_ins : "+str(t3-t2))
    test_circuit = Circuit(list_instructions)
    t4=time()
    if(showtime):
        print("circuit : "+str(t4-t3))
    PO,IV=test_circuit.generate_pairs_operands()
    if(showtime):
        print(str(len(PO))+" mults")
    t5=time()
    if(showtime):
        print("generate_pairs : "+str(t5-t4))
    mult_set = import_mult(PO)
    t6=time()
    if(showtime):
        print("import_mult : "+str(t6-t5))
    #print(IV)
    A=search_attack(mult_set,verbose,showtime,order,multiproc,approx)
    t7=time()
    if(showtime):
        print("search_attack : "+str(t7-t6))
    return A

def subgraph_search(filename,verbose=False,showtime=False,order=False,multiproc=False,approx=0):
#same options as above, but the algorithm first searches for subgraphs and then checks each subgraph independently
    t0=time()
    all_A=[]
    LItest=format_code(filename)
    CCtest=circuit_subgraphs(filename)
    t1=time()
    if(showtime):
        print(str(len(CCtest))+" subgraphs found")
        print("find subgraphs : "+str(t1-t0))

    list_instructions = generate_list_ins_from_lines(LItest) 
    test_circuit = Circuit(list_instructions)
    PO,IV=test_circuit.generate_pairs_operands()
    ni=test_circuit.nb_inputs
    nr=test_circuit.nb_refresh
    n=ni+len(PO)+nr #nb inputs of flattened circuit

    LS=subgraphs_to_subcircuits(CCtest,LItest,False,n)
    t2=time()
    if(showtime):
        print("create subcircuits : "+str(t2-t1))
    for i in range(len(LS)):
        t3=time()
        if(showtime):
            print("searching for attack on subgraph "+str(i)+" (out of "+str(len(LS)-1)+")")
        list_instructions = generate_list_ins_from_lines(LS[i]) 
        test_circuit = Circuit(list_instructions)
        PO,IV=test_circuit.generate_pairs_operands()
        mult_set = import_mult(PO)
        SA=search_attack(mult_set,verbose,False,order,multiproc,approx)
        print(SA)
        all_A+=[SA]
        if(showtime):
            print("done in "+str(time()-t3)+"s \n")
    tf=time()
    if(showtime):
        print("total time : "+str(tf-t0)+"s \n")
    return [[i,all_A[i]] for i in range(len(all_A)) if all_A[i]!=[]]


def lineattack(L):
#searches for an attack on a given circuit described with a list of instructions.
#the subgraph search can then be done with multiple threads by running this function
#on the different subgraphs
    list_instructions = generate_list_ins_from_lines(L) 
    test_circuit = Circuit(list_instructions)
    PO,IV=test_circuit.generate_pairs_operands()
    mult_set = import_mult(PO)
    return search_attack(mult_set)

def parallel_subgraph_search(filename,nbthread=mp.cpu_count(),verbose=False,showtime=False,order=False):
#this function searches for attacks on different subgraph by searching in all the subgraphs in parallel.
    t0=time()
    all_A=[]
    LItest=format_code(filename)
    #CCtest=parallel_circuit_subgraphs(filename,nbthread)
    CCtest=circuit_subgraphs(filename)
    t1=time()
    if(showtime):
        print(str(len(CCtest))+" subgraphs found")
        print("find subgraphs : "+str(t1-t0))

    list_instructions = generate_list_ins_from_lines(LItest) 
    test_circuit = Circuit(list_instructions)
    PO,IV=test_circuit.generate_pairs_operands()
    ni=test_circuit.nb_inputs
    nr=test_circuit.nb_refresh
    n=ni+len(PO)+nr #nb inputs of flattened circuit

    LS=subgraphs_to_subcircuits(CCtest,LItest,False,n)
    t2=time()
    if(showtime):
        print("create subcircuits : "+str(t2-t1))
    
    pool = mp.Pool(processes=nbthread)
    all_A = pool.map(lineattack, LS)
    pool.close()
    pool.join()
        
    tf=time()
    if(showtime):
        print("total time : "+str(tf-t0)+"s \n")
    return [[i,all_A[i]] for i in range(len(all_A)) if all_A[i]!=[]]