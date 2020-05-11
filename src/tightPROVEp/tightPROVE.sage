###############################################################################
#
# Implementation of tightPROVE+ in SageMath
#
# tightPROVE+ is a formal verification tool for the tight register probing  
# security of masked implementations, introduced in https://ia.cr/2020/506
#
# File: tightPROVE.sage
# Description: this file loads all the libraries and files needed for
# tightPROVE(+), and runs it on the inputs given by the user.
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

#######################################IMPORTS#######################################

from time import time
import numpy as np
import sys
from functools import partial
from itertools import combinations
import multiprocessing as mp
import matplotlib.pyplot as plt
from random import *

#############################LOAD FILES FOR BITSLICE#################################

load("imports/format.sage")
load("imports/graph.sage")
load("imports/maskverif.sage")
load("imports/misc.sage")
load("imports/paths.sage")
load("imports/rand.sage")
load("imports/refresh.sage")
load("imports/search.sage")
load("imports/TP.sage")

##############################LOAD FILES FOR VSLICE##################################

load("imports/formatV.sage")
load("imports/miscV.sage")
load("imports/TPV.sage")
load("imports/refreshV.sage")



######################################TESTING########################################
from datetime import datetime

def one_test(f,name,b_v):
    f.write("test on "+name+" :\n")
    print("test on "+name+" :\n")
    begintime=datetime.now()
    f.write(begintime.strftime("process started the %d/%m/%Y at %H:%M:%S"))
    f.write("\n")
    t=time()
    try:
        if(b_v=="bitsliced"):f.write(str(simple_search(b_v+"/"+name,multiproc=1)))
        if(b_v=="vsliced"):f.write(str(simple_search_register(b_v+"/"+name,multiproc=1)))
    except:
        f.write("some error occurred during search")
    f.write("\n")
    f.write("finished in "+str(time()-t)+" s.")
    print("finished in "+str(time()-t)+" s.")
    f.write("\n")
    f.write("\n")


def testing(long=False):
    b="bitsliced"
    v="vsliced"
    with open("LOG","w+") as f:
        one_test(f,"ace_vslice",v)
        one_test(f,"ascon_vslice",v)
        one_test(f,"clyde_vslice",v)
        one_test(f,"drygascon_vslice",v)
        one_test(f,"gift_vslice",v)
        #one_test(f,"gimli_vslice",v)
        one_test(f,"pyjamask_vslice",v)
        one_test(f,"xoodoo_vslice",v)

        #one_test(f,"ace",b)
        #one_test(f,"aes",b)
        #one_test(f,"aes_ks",b)
        one_test(f,"ascon",b)
        one_test(f,"clyde",b)
        one_test(f,"drygascon",b)
        #one_test(f,"gift",b)
        #one_test(f,"gimli",b)
        one_test(f,"photon",b)
        one_test(f,"present",b)
        one_test(f,"pyjamask",b)
        one_test(f,"skinny",b)
        one_test(f,"spongent_one_round",b)
        one_test(f,"spongent_ten_rounds",b)
        one_test(f,"subterranean",b)
        one_test(f,"xoodoo",b)

        if(long==True):
            one_test(f,"gimli_vslice",v)
            one_test(f,"gimli",b)
            one_test(f,"ace",b)
            one_test(f,"gift",b)
            one_test(f,"aes",b)
            one_test(f,"aes_ks",b)



filename = sys.argv[1]
if sys.argv[2] == "b":
    find_refresh_v1(filename,savef=False,verbose=False,save=1,showgraph=False)

if sys.argv[2] == "v":
    find_refreshV(filename,verbose=0,showtime=0,save=1,multiproc=0)
