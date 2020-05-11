###############################################################################
#
# Implementation of tightPROVE+ in SageMath
#
# tightPROVE+ is a formal verification tool for the tight register probing  
# security of masked implementations, introduced in https://ia.cr/2020/506
#
# File: tightprove-exec.sage
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
import os
from functools import partial
from itertools import combinations
import multiprocessing as mp
import matplotlib.pyplot as plt
from random import *

#############################LOAD FILES FOR BITSLICE#################################
base_dir = os.path.dirname(os.path.realpath(__file__))

load(base_dir + "/imports/format.sage")
load(base_dir + "/imports/graph.sage")
load(base_dir + "/imports/maskverif.sage")
load(base_dir + "/imports/misc.sage")
load(base_dir + "/imports/paths.sage")
load(base_dir + "/imports/rand.sage")
load(base_dir + "/imports/refresh.sage")
load(base_dir + "/imports/search.sage")
load(base_dir + "/imports/TP.sage")

##############################LOAD FILES FOR VSLICE##################################

load(base_dir + "/imports/formatV.sage")
load(base_dir + "/imports/miscV.sage")
load(base_dir + "/imports/TPV.sage")
load(base_dir + "/imports/refreshV.sage")



###########################RUN TIGHTPROVE ON INPUTS##################################

filename_in  = sys.argv[1]
filename_out = sys.argv[2]
slicing      = sys.argv[3]

if slicing == "b":
    find_refresh_v1(filename_in,savef=False,verbose=False,save=1,saveto=filename_out,showgraph=False)

if slicing == "v":
    find_refreshV(filename_in,verbose=0,showtime=0,save=1,saveto=filename_out,multiproc=1)
