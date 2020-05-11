###############################################################################
#
# Implementation of tightPROVE+ in SageMath
#
# tightPROVE+ is a formal verification tool for the tight register probing  
# security of masked implementations, introduced in https://ia.cr/2020/506
#
# File: miscV.sage
# Description: this file contains miscellaneous functions used in other
# files.
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

##################################MISCELLANEOUS FUNCTIONS#####################################


def write_file_from_lines(filename,lines):
    with open(filename,'w') as f:
        for l in lines:
            f.write(l)
            if(l[-1:]!='\n'):
                f.write('\n')

def showmat(M,size):
#plots the matrix in a figure. Matrix can be a numpy array of numpy array or a sage matrix
    try:
        npm=np.matrix(M,bool)
        plt.figure(figsize=size)
        plt.imshow(npm,Cmap='Greys')
    except:
        try:
            plt.figure(figsize=size)
            plt.imshow(M,Cmap='Greys')
        except:
            print ("failed to show matrix")
            
    plt.show(block=False)
              

def showmatall(L,size):
#plots a list of matrix by concatenating them
    try:
        npm=np.matrix(L[0],bool)
        for i in range(1,len(L)):
            npn=np.matrix(L[i],bool)
            npm=np.vstack((npm,npn))
        
        plt.figure(figsize=size)
        plt.imshow(npm,Cmap='Greys')
    except:
        pass
        
    plt.show(block=False)
        
def delete_duplicatesV(L):
    Lr=[]
    for l in L:
        if l not in Lr:
            Lr+=[l]
    return Lr
    
    
def find_basis(S):
    return matrix([l for l in S.echelon_form() if 1 in l])

def add_block(M1,M2):
    return block_matrix(2,1,[M1,M2])

def multlist_to_oplist(multlist):
    return delete_duplicatesV([op for mult in multlist for op in mult.ops])    
    
    
    
    