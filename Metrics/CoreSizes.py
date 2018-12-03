
#Extracts the core for tau=0.8 from a core-file (see CoreID.py)
#USAGE: CoreSizes.py <core-file>
#OUTPUT: (per line) node-id		original-centrality
from __future__ import division
import os
import math
import sys
from collections import defaultdict, Counter
from scipy import stats
from Lexis import *
import numpy as np
import networkx as nx

path = sys.argv[-1]
# for i in range(1,16):
    # print i
    # print float(i)/1000
    # f = open(path + '/cs_core_' + str(i) + '.txt','r').readlines()
f = open(path, 'r').readlines()

core_len = int(f[-1].split('\t')[1])
# print core_len, 'dsadsa'
# sys.exit()

for k in range(core_len):
    # print k
    print '{}\t{}'.format(len(f[k].split('\t')[0].split()), f[k].split('\t')[-1].rstrip())