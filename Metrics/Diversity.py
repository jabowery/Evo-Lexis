
#Prints the (normalized) diversity metric from a list of target strings
#USAGE: Diversity.py <path-to-target-list>
#OUTPUT:
    #Diversity     median-target-length     mean-target-length     min-target-length     max-target-length
from __future__ import division
import os
import math
import sys
from collections import defaultdict, Counter
from scipy import stats
from Lexis import *
import numpy as np
import networkx as nx

import editdistance
modoid = ''

dic = {}
counter = 1
target_lengths = []
with open(sys.argv[-1],'r') as f:
    lines = f.readlines()
    for i, l1 in enumerate(lines):
        target_lengths.append(len(l1.rstrip().split()))
        for c in l1.split():
            dic[c] = counter
            counter += 1
avg_sum = 0
with open(sys.argv[-1],'r') as f:
    lines = f.readlines()
    min_avg_sum = 200
    for i, l1 in enumerate(lines):
        avg_sum = 0.0
        for j, l2 in enumerate(lines):
            if i != j:
                l1_tmp = [dic[c] for c in l1.split()]
                l11 = ''.join(map(unichr, map(int, l1_tmp)))
                l2_tmp = [dic[c] for c in l2.split()]
                l22 = ''.join(map(unichr, map(int, l2_tmp)))
                tmp_dist = editdistance.eval(l11, l22)
                avg_sum += tmp_dist
        avg_sum = avg_sum / len(lines)
        if avg_sum < min_avg_sum:
            min_avg_sum = avg_sum
            medoid = ''.join(map(unichr, map(int, l1_tmp)))
    # avg_sum = 0.0
    avg_sum2 = 0.0
    for i, l1 in enumerate(lines):
        l1_tmp = [dic[c] for c in l1.split()]
        l11 = ''.join(map(unichr, map(int, l1_tmp)))
        tmp_dist = editdistance.eval(l11, medoid)
        # avg_sum += tmp_dist #unnormalized target diversity
        avg_sum2 += tmp_dist/float(max(len(l11),len(medoid))) #normalized target diversity
    # print target_lengths
print '{}\t{}\t{}\t{}\t{}'.format(avg_sum2 / len(lines),np.median(target_lengths),np.mean(target_lengths),min(target_lengths),max(target_lengths))
# print '{}\t{}'.format(np.median(target_lengths),np.mean(target_lengths))
# print '{}\t{}'.format(min(target_lengths),max(target_lengths))