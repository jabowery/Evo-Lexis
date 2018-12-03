
#Prints the core stability metric between two core-files (see CoreID.py)
#USAGE: CoreStabilty.py <core-file-1> <core-file-2>
#OUTPUT: Value of the Levenshtein-Jaccard Similarity between the two core-files

#NOTE: Code includes some redundant stuff for historical reasons. I will clean the code in future.

from __future__ import division
import os
import math
import sys
from collections import defaultdict, Counter
from scipy import stats
from Lexis import *
import numpy as np
import networkx as nx

#######Comparing core contents (fixed Jaccard similarity)
coreSets = [[],[]]
counter = 1
dic1 = {}
f = open(sys.argv[-2],'r').readlines()
for l in f:
    parts = l.split('\t')[0].split()
    for p in parts:
        if p not in dic1:
            dic1[p] = counter
            counter += 1
for _,l in enumerate(open(sys.argv[-2],'r').readlines()):
    if l == '':
        break
    try:
        coreSets[0].append(
            # (' '.join(map(unichr,map(int,l.split('\t')[0].split()))), int(l.split('\t')[2]))
            # (' '.join(map(unichr, map(int, l.split('\t')[0].split()))), len(l.split('\t')[0].split()))
            (' '.join(map(unichr, map(lambda x: dic1[x], l.split('\t')[0].split()))), len(l.split('\t')[0].split()))
        )
    except IndexError:
        break

counter = 1
dic2 = {}
f = open(sys.argv[-1],'r').readlines()
for l in f:
    parts = l.split('\t')[0].split()
    for p in parts:
        if p not in dic1:
            dic1[p] = counter
            counter += 1
for _,l in enumerate(open(sys.argv[-1], 'r').readlines()):
    if l == '':
        break
    try:
        coreSets[1].append(
            # (' '.join(map(unichr, map(int, l.split('\t')[0].split()))), int(l.split('\t')[2]))
            # (' '.join(map(unichr, map(int, l.split('\t')[0].split()))), len(l.split('\t')[0].split()))
            (' '.join(map(unichr, map(lambda x: dic1[x], l.split('\t')[0].split()))), len(l.split('\t')[0].split()))
        )
    except IndexError:
        break
# f1 = open(sys.argv[-4], 'r').readlines()
# f2 = open(sys.argv[-3], 'r').readlines()

# LEN1 = len([l for l in f1 if l.startswith('N0 ')]) * 200
# LEN2 = len([l for l in f2 if l.startswith('N0 ')]) * 200

LEN1 = 100 * 200
LEN2 = 100 * 200

totalPaths = [LEN1,
              LEN2]
# totalPaths = len(open(sys.argv[-3], 'r').readlines()) * 200
c_tau = [75,85,95]
c_sizes = [[0,0,0],[0,0,0]]

lines0 = open(sys.argv[-2], 'r').readlines()
c_sizes[0][0] = int(lines0[-1].split('\t')[0])
c_sizes[0][1] = int(lines0[-1].split('\t')[1])
c_sizes[0][2] = int(lines0[-1].split('\t')[2])
lines1 = open(sys.argv[-1], 'r').readlines()
c_sizes[1][0] = int(lines1[-1].split('\t')[0])
c_sizes[1][1] = int(lines1[-1].split('\t')[1])
c_sizes[1][2] = int(lines1[-1].split('\t')[2])

# for i in range(len(coreSets)):
#     cSet = coreSets[i]
#     for j in range(len(c_tau)):
#         tau = float(c_tau[j])/100
#         pathRemovedRatio = 0.0
#         for k in range(len(cSet)):
#             if pathRemovedRatio < tau:
#                 pathRemovedRatio += float(cSet[k][1])/totalPaths[i]
#                 # pathRemovedRatio += float(cSet[k][1]) / totalPaths
#                 print 'p', tau, pathRemovedRatio
#             else:
#                 c_sizes[i][j] = k
#                 break
# print c_sizes
jaccard_sims = [0,0,0]
weight_jaccard = True
sum_0 = 0.0
sum_1 = 0.0
# print 'd', dic1['BBa_R0051']
import editdistance
constant=20
for i in range(len(c_tau)):
    # tmp_csets = [coreSets[0][:c_sizes[0][i]], coreSets[1][:c_sizes[1][i]]]
    tmp_csets = [coreSets[0][20:20+constant], coreSets[1][20:20+constant]]
    # print tmp_csets
    if weight_jaccard:
        for j in range(len(tmp_csets[1])):
            minDist = 1.0
            for k in range(len(tmp_csets[0])):
                tmp_dist = editdistance.eval(tmp_csets[1][j][0], tmp_csets[0][k][0])
                maxDist = float(max(len(tmp_csets[1][j][0]),len(tmp_csets[0][k][0])))
                # print tmp_csets[1][j][0], tmp_csets[0][k][0], tmp_dist
                if float(tmp_dist)/maxDist < minDist:
                    minDist = float(tmp_dist)/maxDist
            # print 'a', minDist
            # weight_0 = float(tmp_csets[1][j][1])
            weight_0 = 1
            jaccard_sims[i] += (1-float(minDist)) * weight_0
            # print 'a', (1-float(minDist)) * weight_0
            sum_0 += weight_0
        for k in range(len(tmp_csets[0])):
            minDist = 1.0
            for j in range(len(tmp_csets[1])):
                tmp_dist = editdistance.eval(tmp_csets[1][j][0], tmp_csets[0][k][0])
                maxDist = float(max(len(tmp_csets[1][j][0]),len(tmp_csets[0][k][0])))
                # print tmp_csets[1][j][0], tmp_csets[0][k][0], tmp_dist
                if float(tmp_dist)/maxDist < minDist:
                    minDist = float(tmp_dist)/maxDist
            # print 'b', minDist
            # weight_1 = float(tmp_csets[0][k][1])
            weight_1 = 1
            jaccard_sims[i] += (1-float(minDist)) * weight_1
            # print 'b', (1 - float(minDist)) * weight_1
            sum_1 += weight_1
    else:
        for j in range(len(tmp_csets[1])):
            if tmp_csets[1][j][0] in [c_elem[0] for c_elem in tmp_csets[0]]:
                jaccard_sims[i] += 1
# for i in range(len(jaccard_sims)):
#     tmp_csets = [coreSets[0][:c_sizes[0][i]], coreSets[1][:c_sizes[1][i]]]
#     print str(jaccard_sims[i]/len(set((tmp_csets[0]+tmp_csets[1])))) + '\t',
# print '\t',


# print jaccard_sims[1]
# print sum_0
# print sum_1
# print str(float(jaccard_sims[1]) / float(c_sizes[0][1] + c_sizes[1][1])) + '\t'
# print str(float(jaccard_sims[1]) / float(constant*2)) + '\t'
# sys.exit()
#######Origianl
for i in range(len(jaccard_sims)):
    # print str(float(jaccard_sims[i]) / float(c_sizes[0][i] + c_sizes[1][i])) + '\t',
    print str(float(jaccard_sims[i]) / float(sum_0 + sum_1)) + '\t',

    # print str(jaccard_sims[i]/(min(c_sizes[0][i],c_sizes[1][i]))) + '\t',
    # print str(jaccard_sims[i] / (min(c_sizes[0][i], c_sizes[1][i]))),
    # print str(jaccard_sims[i]) + '\t',
print

# print tmp_g.DAGCost(CostFunction.EdgeCost)
#
# igemCharRelativeRank()o

# igemAgeReuseScatter()

# igem_length_distinctSymbols()