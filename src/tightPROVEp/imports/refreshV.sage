###############################################################################
#
# Implementation of tightPROVE+ in SageMath
#
# tightPROVE+ is a formal verification tool for the tight register probing  
# security of masked implementations, introduced in https://ia.cr/2020/506
#
# File: refreshV.sage
# Description: this file contains functions used to find the placement of
# refresh gadgets in a given circuit and place them automatically until the
# said circuit is secure.
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

#######################################################################################
#######################################REFRESH-V#######################################

def whichmult(multlist,line):
    for m in multlist:
        if m.line==line:
            return m


def change_lines_from_Gs(lines,Gs,refreshed_vars,verbose=0):
#finds the multiplication that appears the most in the Gis and applies a refresh on one of its operands if it doesn't use a refreshed operand already
#reiterating this function until the number of attacks is 0 is bound to terminate as refreshing every multiplication gadget once is guaranteed to protect the circuit
    listmult=[]
    d={}

    #calculate how frequently multiplications appear in the Gis
    for i in range(len(Gs)):
        for g in Gs[i]:
            try:
                d[g.line]+=1
            except:
                d[g.line]=1
                listmult+=[g]

    index_m=0
    for index_m in range(len(listmult)):
        lmult=sorted(d, key=d.__getitem__, reverse=True)[index_m]   #sort the multiplications by how frequently they appear
        mult=whichmult(listmult,lmult)
        if(mult.ops[0].name[-3:-1:1]=="_R" or mult.ops[1].name[-3:-1:1]=="_R"):  #if a refreshed operand is an input, go to the next multiplication
            continue
        else:
            op=mult.ops[0]   #we (arbitrarily) choose to refresh the left operand
            if(verbose>0):
                print ("variable "+op.name+" has been refreshed.\n")
            #the same operand can be refreshed multiple times. refreshed_vars counts how many times an operand has been refreshed, to name them differently
            try:
                refreshed_vars[op.name]+=1
            except:
                refreshed_vars[op.name]=1
            lop=op.line
            break

    #newref contains the info needed to change the .ua files : the variable to refresh, its new name after being refreshed, and where to apply it
    newref=[op.name,op.name+"_R"+str(refreshed_vars[op.name]),mult.name+" = and "+mult.ops[0].name+"_R"+str(refreshed_vars[op.name])+" "+mult.ops[1].name]

    return lines[:lop+1]+[op.name+"_R"+str(refreshed_vars[op.name])+" = ref "+op.name]+lines[lop+1:lmult:1]+[mult.name+" = and "+mult.ops[0].name+"_R"+str(refreshed_vars[op.name])+" "+mult.ops[1].name]+lines[lmult+1:],refreshed_vars,newref


def find_refreshV(filename,verbose=0,showtime=0,save=0,saveto="",multiproc=0):
#verbose = 1 gives basic infos on the placement of refresh at each step
#for verbose > 1, applies verbose-1 on the verbose of simple_search_register
#showtime = 1 gives the time it takes for each step (+total time)
#save=1 to save results in a new file
#multiproc=1 to enable multiprocessing
    ttime=time()

    with open(filename,"r") as f:
        lines=f.readlines()

    refreshed_vars={}
    listofrefresh=[]  #list that will be return. This should be used to change the .ua files
    step=0

    t=time()
    Gs=simple_search_register(lines,returnG=1,multiproc=multiproc,verbose=max(0,verbose-1))
    if(showtime):print("search at step %d took %fs."%(step,time()-t))

    lenG=len(Gs)
    while(lenG>0):
        if(verbose>0):
            print ("number of attacks left at step %d : %d"%(step,lenG))
        lines,refreshed_vars,newref=change_lines_from_Gs(lines,Gs,refreshed_vars,verbose=verbose)
        listofrefresh+=[newref]
        t=time()
        Gs=simple_search_register(lines,returnG=1,multiproc=multiproc,verbose=max(0,verbose-1))
        if(showtime):print("search at step %d took %fs."%(step,time()-t))
        lenG=len(Gs)
        step+=1

    if(verbose>0):
        print ("number of attacks left at step %d : %d"%(step,lenG))
        print ("%d refresh placed"%(sum([refreshed_vars[e] for e in refreshed_vars])))
    if(save):
        if saveto == "":
            saveto = filename + "_R"
        write_file_from_lines(saveto,lines)
    if(showtime):
        print ("total time : %fs."%(time()-ttime))
    return listofrefresh
