# -*- coding: utf-8 -*-

#Prints list of the nodes of a DAG
#USAGE: Nodes.py -l -t s -q <path-to-dag-file>
#OUTPUT: (per line) node-string

#NOTE: Code includes many redundant stuff for historical reasons. I will clean the code in future.

"""
@author: Payam Siyari
"""
from __future__ import division
import os
from os import listdir
from os.path import isfile, join
import random
from collections import defaultdict
from bisect import bisect_left
import fileinput
import sys
import getopt
import operator
import time
import subprocess
import networkx as nx
import copy
import numpy as np

class SequenceType:
    Character, Integer, SpaceSeparated = ('c', 'i', 's')
class CostFunction:
    ConcatenationCost, EdgeCost = ('c', 'e')
class RepeatClass:
    Repeat, MaximalRepeat, LargestMaximalRepeat, SuperMaximalRepeat = ('r', 'mr', 'lmr', 'smr')
class LogFlag:
    ConcatenationCostLog, EdgeCostLog = range(2)

class DAG(object):
    # preprocessedInput = [] #Original input as a sequence of integers
    # dic = {} #Dictionary for correspondence of integers to original chars (only when charSeq = 'c','s')
    # DAG = {} #Adjacency list of DAG
    # DAGGraph = nx.MultiDiGraph()
    # DAGStrings = {}#Strings corresponding to each node in DAG
    #
    # concatenatedDAG = [] #Concatenated DAG nodes with seperatorInts
    # concatenatedNTs = [] #For each DAG node, alongside the concatenated DAG
    # separatorInts = set([]) #Used for seperating DAG nodes in the concatenatedDAG
    # separatorIntsIndices = set([]) #Indices of separatorInts in the concatenated DAG
    # nextNewInt = 0 #Used for storing ints of repeat symbols and separators in odd numbers
    #
    # quietLog = False #if true, disables logging
    # iterations = 0

    def __init__(self, inputFile, loadDAGFlag, chFlag = SequenceType.Character, noNewLineFlag = True):
        self.preprocessedInput = []  # Original input as a sequence of integers
        self.dic = {}  # Dictionary for correspondence of integers to original chars (only when charSeq = 'c','s')
        self.DAG = {}  # Adjacency list of DAG
        self.DAGGraph = nx.MultiDiGraph()
        self.DAGStrings = {}  # Strings corresponding to each node in DAG

        self.concatenatedDAG = []  # Concatenated DAG nodes with seperatorInts
        self.concatenatedNTs = []  # For each DAG node, alongside the concatenated DAG
        self.separatorInts = set([])  # Used for seperating DAG nodes in the concatenatedDAG
        self.separatorIntsIndices = set([])  # Indices of separatorInts in the concatenated DAG
        self.nextNewInt = 0  # Used for storing ints of repeat symbols and separators in odd numbers

        self.quietLog = False  # if true, disables logging
        self.iterations = 0
        if loadDAGFlag:
            self.initFromDAG(inputFile)
        else:
            self.initFromStrings(inputFile, chFlag, noNewLineFlag)
    #Initializes (an unoptimized) DAG from inputFile. charSeq tells if inputFile is a char sequence, int sequence or space-separated sequence
    def initFromStrings(self, inputFile, chFlag = SequenceType.Character, noNewLineFlag = True):
        (self.preprocessedInput, self.dic) = self.preprocessInput(inputFile, charSeq = chFlag, noNewLineFlag = noNewLineFlag)
        allLetters = set(map(int,self.preprocessedInput.split()))
        #Setting odd and even values for nextNewInt and nextNewContextInt
        self.nextNewInt = max(allLetters)+1
        if self.nextNewInt % 2 == 0:
            self.nextNewInt += 1
        #Initializing the concatenated DAG
        for line in self.preprocessedInput.split('\n'):
            line = line.rstrip('\n')
            self.concatenatedDAG.extend(map(int,line.split()))
            self.concatenatedDAG.append(self.nextNewInt)
            self.concatenatedNTs.extend(0 for j in range(len(map(int,line.split()))))
            self.concatenatedNTs.append(self.nextNewInt)
            self.separatorInts.add(self.nextNewInt)
            self.separatorIntsIndices.add(len(self.concatenatedDAG)-1)
            self.nextNewInt += 2
    #Loads the DAG from an external file (The file should start from 'N0' line, without cost logs)
    def initFromDAG(self, inputFile):
        def RepresentsInt(s):
            try:
                int(s)
                return True
            except ValueError:
                return False
        textFile = inputFile.read().splitlines()
        maxInt = 0
        for line in textFile[2:]:
            nt = int(line.split(' ->  ')[0][1:])
            self.dic[nt] = nt
            if maxInt < nt:
                maxInt = nt
        maxInt += 1
        reverseDic = {}
        for line in textFile[2:]:
            nt = int(line.split(' ->  ')[0][1:])
            rhs = line.split(' ->  ')[1].split()
            for w in rhs:
                # sys.stderr.write(w + "\n")
                if w.startswith('N') and RepresentsInt(int(w[1:])):
                    ntInt = int(w[1:])
                    self.concatenatedDAG.append(ntInt)
                    self.concatenatedNTs.append(nt)
                else:
                    word = w
                    if word not in reverseDic:
                        reverseDic[word] = maxInt
                        self.dic[maxInt] = word
                        self.concatenatedDAG.append(maxInt)
                        self.concatenatedNTs.append(nt)
                        maxInt += 1
                    else:
                        self.concatenatedDAG.append(reverseDic[word])
                        self.concatenatedNTs.append(nt)
            self.concatenatedDAG.append(-1)
            self.concatenatedNTs.append(-1)
            self.separatorIntsIndices.add(len(self.concatenatedDAG) - 1)
        self.nextNewInt = maxInt + 1
        for i in self.separatorIntsIndices:
            self.concatenatedDAG[i] = self.nextNewInt
            self.concatenatedNTs[i] = self.nextNewInt
            self.separatorInts.add(self.nextNewInt)
            self.nextNewInt += 1
        # wordDict = {}
        # counterDict = {}
        # counter = 0
        # textFile = inputFile.read().splitlines()
        # tmpnode = []
        # for line in textFile:
        #     # if len(line.split(' ->  ')) < 2:
        #     #     tmpnode = ['\n'] + line.split(' ')
        #     #     newnode = []
        #     #     for w in tmpnode:
        #     #         if w not in counterDict:
        #     #             wordDict[counter] = w
        #     #             counterDict[w] = counter
        #     #             counter += 1
        #     #         newnode.append(counterDict[w])
        #     #     self.DAG[newNt] += newnode
        #     #     continue
        #     # else:
        #     nt = int(line.split(' ->  ')[0][1:])
        #     if counter % 2 == 0:
        #         if counter != 0:
        #             counter += 1
        #     if nt not in counterDict:
        #         wordDict[counter] = nt
        #         counterDict[nt] = counter
        #         counter += 1
        #     newNt = counterDict[nt]
        #     node = line.split(' ->  ')[1].split(' ')
        #     newnode = []
        #     for w in node:
        #         if w[0] == 'N':
        #             if w not in counterDict:
        #                 wordDict[counter] = w[1:]
        #                 counterDict[w[1:]] = counter
        #                 counter += 1
        #             newnode.append(counterDict[w[1:]])
        #         else:
        #             if w not in counterDict:
        #                 wordDict[counter] = w
        #                 counterDict[w] = counter
        #                 counter += 1
        #             newnode.append(counterDict[w])
        #     if newNt == 0:
        #         if newNt in self.DAG:
        #             self.DAG[newNt].append(newnode)
        #         else:
        #             self.DAG[newNt] = [newnode]
        #     else:
        #         self.DAG[newNt] = newnode
        # self.dic = wordDict
        # self.nextNewInt = counter
        # if self.nextNewInt % 2 == 0:
        #     self.nextNewContextInt = self.nextNewInt
        #     self.nextNewInt += 1
        # else:
        #     self.nextNewContextInt = self.nextNewInt + 1
        # for nt in self.DAG:
        #     self.concatenatedDAG.extend(self.DAG[nt])
        #     self.concatenatedDAG.append(self.nextNewInt)
        #     self.concatenatedNTs.extend(nt for j in range(len(self.DAG[nt])))
        #     self.concatenatedNTs.append(self.nextNewInt)
        #     self.separatorInts.add(self.nextNewInt)
        #     self.separatorIntsIndices.add(len(self.concatenatedDAG)-1)
        #     self.nextNewInt += 2
        # print self.DAG
        # print self.dic
        self.createAdjacencyList()
        # print 'self dag'
        # print self.DAG
        self.createDAGGraph()
        # print 'self graph'
        # print self.DAGGraph
        # print self.DAGGraph.nodes()
        # print self.DAGGraph.edges()
        self.nodeStringsGenerate()
        # print 'self strings'
        # print self.DAGStrings

    #...........Main G-Lexis Algorithm Functions........
    def GLexis(self, quiet, normalRepeatType, costFunction):
        # print self.concatenatedDAG
        self.quietLog = quiet
        while True: #Main loop
            #Logging DAG Cost
            self.logViaFlag(LogFlag.ConcatenationCostLog)
            self.logViaFlag(LogFlag.EdgeCostLog)

            #Extracting Maximum-Gain Repeat
            (maximumRepeatGainValue, selectedRepeatOccs) = self.retreiveMaximumGainRepeat(normalRepeatType, CostFunction.EdgeCost)
            if maximumRepeatGainValue == -1:
                break #No repeats, hence terminate

            self.logMessage('maxR ' + str(maximumRepeatGainValue) + ' : ' + str(self.concatenatedDAG[selectedRepeatOccs[1][0]:selectedRepeatOccs[1][0]+selectedRepeatOccs[0]]) + '\n')
            if maximumRepeatGainValue > 0:
                odd = True
                self.replaceRepeat(selectedRepeatOccs) #Replacing the chosen repeat
                self.iterations += 1
        self.logMessage('---------------')
        self.logMessage('Number of Iterations: ' + str(self.iterations))
        self.createAdjacencyList()
        self.createDAGGraph()
        self.nodeStringsGenerate()
    #Returns the cost of the DAG according to the selected costFunction
    def DAGCost(self, costFunction):
        if costFunction == CostFunction.ConcatenationCost:
            return len(self.concatenatedDAG)-2*len(self.separatorInts)
        if costFunction == CostFunction.EdgeCost:
            return len(self.concatenatedDAG)-len(self.separatorInts)
    #Replaces a repeat's occurrences with a new symbol and creates a new node in the DAG
    def replaceRepeat(self,(repeatLength, (repeatOccs))):
        repeat = self.concatenatedDAG[repeatOccs[0]:repeatOccs[0]+repeatLength]
        newTmpConcatenatedDAG = []
        newTmpConcatenatedNTs = []
        prevIndex = 0
        for i in repeatOccs:
            newTmpConcatenatedDAG += self.concatenatedDAG[prevIndex:i] + [self.nextNewInt]
            newTmpConcatenatedNTs += self.concatenatedNTs[prevIndex:i] + [self.concatenatedNTs[i]]
            prevIndex = i+repeatLength
        self.concatenatedDAG = newTmpConcatenatedDAG + self.concatenatedDAG[prevIndex:]
        self.concatenatedNTs = newTmpConcatenatedNTs + self.concatenatedNTs[prevIndex:]
        self.concatenatedDAG = self.concatenatedDAG + repeat
        self.concatenatedNTs = self.concatenatedNTs + [self.nextNewInt for j in range(repeatLength)]
        self.logMessage('Added Node: ' +  str(self.nextNewInt))
        self.nextNewInt += 2
        self.concatenatedDAG = self.concatenatedDAG + [self.nextNewInt]
        self.concatenatedNTs = self.concatenatedNTs + [self.nextNewInt]
        self.separatorInts.add(self.nextNewInt)
        self.separatorIntsIndices = set([])
        for i in range(len(self.concatenatedDAG)):
            if self.concatenatedDAG[i] in self.separatorInts:
                self.separatorIntsIndices.add(i)
        self.nextNewInt += 2
    #Retrieves the maximum-gain repeat (randomizes within ties).
    #Output is a tuple: "(RepeatGain, (RepeatLength, (RepeatOccurrences)))"
    #1st entry of output is the maximum repeat gain value
    #2nd entry of output is a tuple of form: "(selectedRepeatLength, selectedRepeatOccsList)"
    def retreiveMaximumGainRepeat(self, repeatClass, costFunction):
        repeats = self.extractRepeats(repeatClass)
        maxRepeatGain = 0
        candidateRepeats = []
        for r in repeats: #Extracting maximum repeat
            repeatStats = r.split()
            repeatOccs = self.extractNonoverlappingRepeatOccurrences(int(repeatStats[0]),map(int,repeatStats[2][1:-1].split(',')))
            if maxRepeatGain < self.repeatGain(int(repeatStats[0]), len(repeatOccs), costFunction):
                maxRepeatGain = self.repeatGain(int(repeatStats[0]), len(repeatOccs), costFunction)
                candidateRepeats = [(int(repeatStats[0]),len(repeatOccs),repeatOccs)]
            else:
                if maxRepeatGain > 0 and maxRepeatGain == self.repeatGain(int(repeatStats[0]), len(repeatOccs), costFunction):
                    candidateRepeats.append((int(repeatStats[0]),len(repeatOccs),repeatOccs))
        if(len(candidateRepeats) == 0):
            return (-1, (0, []))
        #Randomizing between candidates with maximum gain
        #selectedRepeatStats = candidateRepeats[random.randrange(len(candidateRepeats))]
        selectedRepeatStats = candidateRepeats[0]
        selectedRepeatLength = selectedRepeatStats[0]
        selectedRepeatOccs = sorted(selectedRepeatStats[2])
        return (maxRepeatGain, (selectedRepeatLength, selectedRepeatOccs))
    #Returns the repeat gain, according to the chosen cost function
    def repeatGain(self, repeatLength, repeatOccsLength, costFunction):
        # if costFunction == CostFunction.ConcatenationCost:
        return (repeatLength-1)*(repeatOccsLength-1)
        # if costFunction == CostFunction.EdgeCost:
        #     return (repeatLength-1)*(repeatOccsLength-1)-1
    #Extracts the designated class of repeats (Assumes ./repeats binary being in the same directory)
    #Output is a string, each line containing: "RepeatLength    NumberOfOccurrence  (CommaSeparatedOccurrenceIndices)"
    def extractRepeats(self, repeatClass):
        process = subprocess.Popen(["./repeats1/repeats11", "-i", "-r"+repeatClass, "-n2", "-psol"],stdout=subprocess.PIPE, stdin=subprocess.PIPE, stderr=subprocess.STDOUT)
        process.stdin.write(' '.join(map(str,self.concatenatedDAG)))
        text_file = ''
        while process.poll() is None:
            output = process.communicate()[0].rstrip()
            text_file += output
        process.wait()
        repeats=[]
        firstLine = False
        for line in text_file.splitlines():
            if firstLine == False:
                firstLine = True
                continue
            repeats.append(line.rstrip('\n'))
        return repeats
    #Extracts the non-overlapping occurrences of a repeat from a list of occurrences (scans from left to right)
    def extractNonoverlappingRepeatOccurrences(self, repeatLength, occurrencesList):
        nonoverlappingIndices = []
        for i in range(len(occurrencesList)):
            if len(nonoverlappingIndices) > 0:
                if (nonoverlappingIndices[-1] + repeatLength <= occurrencesList[i]):#Not already covered
                    nonoverlappingIndices += [occurrencesList[i]]
            else:
                nonoverlappingIndices += [occurrencesList[i]]
        return  nonoverlappingIndices
    #Creates the adjacency list
    def createAdjacencyList(self):
        separatorPassed = False
        for i in range(len(self.concatenatedDAG)):
            if i not in self.separatorIntsIndices:
                node = self.concatenatedNTs[i]
                if separatorPassed and node == 0:
                    self.DAG[node].append([])
                    separatorPassed = False
                if node not in self.DAG:
                    if node == 0:#Target node
                        self.DAG[node] = [[self.concatenatedDAG[i]]]
                    else:
                        self.DAG[node] = [self.concatenatedDAG[i]]
                else:
                    if node == 0:#Target node
                        self.DAG[node][-1].append(self.concatenatedDAG[i])
                    else:
                        self.DAG[node].append(self.concatenatedDAG[i])
            else:
                separatorPassed = True
    #Creates the DAG graph object (adjacency list should already be processed)
    def createDAGGraph(self):
        for node in self.DAG:
            self.DAGGraph.add_node(node)
            if node == 0:
                for l in self.DAG[node]:
                    for n in l:
                        self.DAGGraph.add_node(n)
                        self.DAGGraph.add_edge(n, node)
            else:
                for n in self.DAG[node]:
                    self.DAGGraph.add_node(n)
                    self.DAGGraph.add_edge(n, node)
    #Stores the strings corresponding to each DAG node
    def nodeStringsGenerate(self):
        for node in nx.nodes(self.DAGGraph):
            if self.DAGGraph.in_degree(node) == 0:
                # if self.dic == {}:
                self.DAGStrings[node] = str(node)
                # else:
                #     self.DAGStrings[node] = str(self.dic[node])
            else:
                if node == 0:
                    self.DAGStrings[node] = []
                else:
                    self.DAGStrings[node] = ''
        self. nodeStringsHelper(0)
    # Helper recursive function
    def nodeStringsHelper(self, n):
        if self.DAGStrings[n] != [] and self.DAGStrings[n] != '':
            return
        if n == 0:
            for l in self.DAG[n]:
                self.DAGStrings[n].append('')
                for i in range(len(l)):
                    subnode = l[i]
                    self.nodeStringsHelper(subnode)
                    # if self.dic == {}:
                    self.DAGStrings[n][-1] += ' ' + self.DAGStrings[subnode]
                    # else:
                    #     self.DAGStrings[n][-1] += self.DAGStrings[subnode] + ' '
        else:
            for i in range(len(self.DAG[n])):
                subnode = self.DAG[n][i]
                self.nodeStringsHelper(subnode)
                # if self.dic == {}:
                self.DAGStrings[n] += ' ' + self.DAGStrings[subnode]
                # else:
                #     self.DAGStrings[n] += self.DAGStrings[subnode] + ' '
    #Returns node's corresponding string
    def getNodeString(self, n):
        if n == 0:
            result = []
            for l in self.DAGStrings[n]:
                result.append(' '.join(l.split()))
            return result
        return ' '.join(self.DAGStrings[n].split())

    # ...........Path-Centrality Functions........
    #Returns a list of strings, corresponding to the nodes removed from DAG, according to greedy core identification algorithm, based on the threshold of edge removal tau
    def greedyCoreID_ByTau(self, tau):
        cycle = False
        for p in nx.simple_cycles(self.DAGGraph):
            print p
            cycle = True
        if cycle:
            print 'CYCLE!'
            return
        numberOfUpwardPaths = {}
        numberOfDownwardPaths = {}
        sources = []
        targets = []
        for node in nx.nodes(self.DAGGraph):
            if self.DAGGraph.in_degree(node) == 0:
                sources.append(node)
            if self.DAGGraph.out_degree(node) == 0:
                targets.append(node)
            numberOfUpwardPaths[node] = 0
            numberOfDownwardPaths[node] = 0
        self.calculateNumberOfUpwardPaths(sources, targets, numberOfUpwardPaths)
        self.calculateNumberOfDownwardPaths(sources, targets, numberOfDownwardPaths)
        allPaths = 0
        # print targets
        for n in targets:
            allPaths += numberOfDownwardPaths[n]
        # return
        orig_targets = targets[:]
        for t in targets:
            numberOfUpwardPaths[t] = 0
        # for s in sources:
        #     numberOfDownwardPaths[s] = 0
        number_of_initial_paths = numberOfDownwardPaths[0]
        number_of_current_paths = numberOfDownwardPaths[0]
        listOfCentralNodes = []
        listOfCentralNodes_cents = []
        centralities = self.calculateCentralities(numberOfUpwardPaths, numberOfDownwardPaths)
        centsDic = {k:(v,v2) for k,v,v2 in centralities}

        # count = 1
        # for node in sorted(sources, key = lambda x : centsDic[x], reverse= True):
        #     sys.stderr.write(str(count) + '\n')
        #     count += 1
        #     nodeString = str(self.getListNodeStrings([node])[0])
        #     print nodeString + '\t' + str(centsDic[node]) + '\t',
        #     parentNodes = []
        #     for n in nx.nodes(self.DAGGraph):
        #         if n != 0:
        #             nString = str(self.getListNodeStrings([n])[0])
        #             if nString != nodeString and nString.find(nodeString) >= 0:
        #                 parentNodes.append(n)
        #     parentNodes = sorted(parentNodes, key = lambda x : centsDic[x], reverse=True)
        #     if len(parentNodes) > 0:
        #         if centsDic[node] > centsDic[parentNodes[0]]:
        #             print 'Y\t',
        #         else:
        #             print 'N\t',
        #     else:
        #         print 'Y\t',
        #     for n in parentNodes:
        #         nString = str(self.getListNodeStrings([n])[0])
        #         print nString + '\t' + str(centsDic[n]) + '\t',
        #     print
        # return

        # for node in nx.nodes(self.DAGGraph):
        #     if node not in targets:
        #         print str(numberOfDownwardPaths[node]) + '\t' + str(numberOfUpwardPaths[node]) + '\t' + str(centsDic[node])
        # return

        # for node in nx.nodes(self.DAGGraph):
        #     if node not in tagets:
        #         print str(self.DAGGraph.out_degree(node)) + '\t' + str(numberOfDownwardPaths[node]) + '\t' + str(numberOfUpwardPaths[node])+ '\t' + str(centsDic[node])
        # return


        # print len(nx.nodes(self.DAGGraph)) - 1

        # print allPaths
        # return

        orig_cents = {k:(v,v2) for k,v,v2 in centralities}
        topCentralNodeInfo = max(centralities, key=lambda x:x[1])
        # print topCentralNodeInfo[1], topCentralNodeInfo[2][0], topCentralNodeInfo[2][1]
        # return
        top_num = 20
        import math
        top10CentsSorted = sorted(centralities, key=lambda x:x[1], reverse = True)[:top_num]
        # print top10CentsSorted[int(top_num / 2)][1], top10CentsSorted[int(top_num / 2)][2][0], top10CentsSorted[int(top_num / 2)][2][1]
        # return
        # print top10CentsSorted[0][1],
        # top10CentsSorted = sorted(centralities, key=lambda x: x[2][0], reverse=True)[:top_num]
        # print top10CentsSorted[0][2][0],
        # top10CentsSorted = sorted(centralities, key=lambda x: x[2][1] if x[2][0] > 1 else 0, reverse=True)[:top_num]
        # print top10CentsSorted[0][2][1]

        # return

        allMaxes = [k for k in centralities if k[1] == topCentralNodeInfo[1]]
        allMaxes = [allMaxes[0]]
        # print '-------------', topCentralNodeInfo[1], len(allMaxes)
        while topCentralNodeInfo[1] > 0 and float(number_of_current_paths)/float(number_of_initial_paths) > 1-tau:#Node with positive centrality exists
            for nodeToBeRemoved in allMaxes:
                nodeToBeRemoved = nodeToBeRemoved[0]
                self.DAGGraph.remove_node(nodeToBeRemoved)
                if nodeToBeRemoved in sources:
                    sources.remove(nodeToBeRemoved)
                listOfCentralNodes.append(nodeToBeRemoved)
                listOfCentralNodes_cents.append(topCentralNodeInfo[1])
                print topCentralNodeInfo[1]
            numberOfUpwardPaths = {}
            numberOfDownwardPaths = {}
            for node in nx.nodes(self.DAGGraph):
                numberOfUpwardPaths[node] = 0
                numberOfDownwardPaths[node] = 0
            self.calculateNumberOfUpwardPaths(sources, targets, numberOfUpwardPaths)
            self.calculateNumberOfDownwardPaths(sources, targets, numberOfDownwardPaths)
            # for t in targets:
            #     numberOfUpwardPaths[t] = 0
            # for s in sources:
            #     numberOfDownwardPaths[s] = 0
            centralities = self.calculateCentralities(numberOfUpwardPaths, numberOfDownwardPaths)
            topCentralNodeInfo = max(centralities, key=lambda x: x[1])
            allMaxes = [k for k in centralities if k[1] == topCentralNodeInfo[1]]
            allMaxes = [allMaxes[0]]
            number_of_current_paths = numberOfDownwardPaths[0]
        self.DAGGraph = nx.MultiGraph()
        self.createDAGGraph()#Reconstructing the DAG graph
        core = []
        # print str(len(nx.nodes(self.DAGGraph)) - len(targets) - len(sources)) + '\t' + str(allPaths)
        arrayOfStrings = self.getListNodeStrings(listOfCentralNodes)
        for i in range(len(arrayOfStrings)):
            nodeString = arrayOfStrings[i]
            core.append(nodeString.rstrip())
            print nodeString.rstrip() + '\t' + str(listOfCentralNodes_cents[i]) + '\t' + str(orig_cents[listOfCentralNodes[i]])
            # print str(listOfCentralNodes_cents[i])
            # print len(nodeString.rstrip().split())
            # break
        return core, listOfCentralNodes_cents
    def getListNodeStrings(self, listNodes):
        arrayOfStrings = []
        for i in range(len(listNodes)):
            if listNodes[i] == 0:
                arrayOfStrings.append('N0')
                continue
            # print i
            # print 'aaa', listNodes[1]
            # print arrayOfStrings
            nodeStringInt = self.getNodeString(listNodes[i])
            nodeString = ''
            for w in nodeStringInt.split():
                nodeString += self.dic[int(w)] + ' '
            arrayOfStrings.append(nodeString)
            # arrayOfStrings = sorted(arrayOfStrings, key = lambda x : len(x.split()))
        return arrayOfStrings
    def greedyCoreID_ByTau_knee(self, age, tau, node_dic, knee_threshold):
        listOfNodes = []
        for node in nx.nodes(self.DAGGraph):
            if node != 0:
                nodeString = self.getListNodeStrings(list([node]))[0]
                if nodeString not in node_dic:
                    node_dic[nodeString] = {'age_index':age, 'core_index': 0, 'core_count': 0}
        cycle = False
        for p in nx.simple_cycles(self.DAGGraph):
            print p
            cycle = True
        if cycle:
            print 'CYCLE!'
            return
        numberOfUpwardPaths = {}
        numberOfDownwardPaths = {}
        sources = []
        targets = []
        for node in nx.nodes(self.DAGGraph):
            if self.DAGGraph.in_degree(node) == 0:
                sources.append(node)
            if self.DAGGraph.out_degree(node) == 0:
                targets.append(node)
            numberOfUpwardPaths[node] = 0
            numberOfDownwardPaths[node] = 0
        self.calculateNumberOfUpwardPaths(sources, targets, numberOfUpwardPaths)
        self.calculateNumberOfDownwardPaths(sources, targets, numberOfDownwardPaths)
        allPaths = 0
        # print targets
        allNodes = len(nx.nodes(self.DAGGraph))-len(targets)-len(sources)
        for n in targets:
            allPaths += numberOfDownwardPaths[n]
        # return
        for t in targets:
            numberOfUpwardPaths[t] = 0
        # for s in sources:
        #     numberOfDownwardPaths[s] = 0
        number_of_initial_paths = numberOfDownwardPaths[0]
        number_of_current_paths = numberOfDownwardPaths[0]
        listOfCentralNodes = []
        listOfCentralNodes_cents = []
        centralities = self.calculateCentralities(numberOfUpwardPaths, numberOfDownwardPaths)
        centsDic = {k:v for k,v in centralities}
        # for node in nx.nodes(self.DAGGraph):
        #     if node not in targets:
        #         print str(numberOfDownwardPaths[node]) + '\t' + str(numberOfUpwardPaths[node]) + '\t' + str(centsDic[node])
        # return
        orig_cents = {k:v for k,v in centralities}
        topCentralNodeInfo = max(centralities, key=lambda x:x[1])
        allMaxes = [k for k in centralities if k[1] == topCentralNodeInfo[1]]
        # print '-------------', topCentralNodeInfo[1], len(allMaxes)
        number_of_prev_covered_paths = 0
        number_of_current_covered_paths = 0
        while topCentralNodeInfo[1] > 0 and float(number_of_current_paths)/float(number_of_initial_paths) > 1-tau:#Node with positive centrality exists
            for nodeToBeRemoved in allMaxes:
                nodeToBeRemoved = nodeToBeRemoved[0]
                self.DAGGraph.remove_node(nodeToBeRemoved)
                if nodeToBeRemoved in sources:
                    sources.remove(nodeToBeRemoved)
                listOfCentralNodes.append(nodeToBeRemoved)
                listOfCentralNodes_cents.append(topCentralNodeInfo[1])
                number_of_current_covered_paths += topCentralNodeInfo[1]
            # print (float(number_of_current_covered_paths - number_of_prev_covered_paths)/float(allPaths)) / (float(len(allMaxes))/float(allNodes))
            if (float(number_of_current_covered_paths - number_of_prev_covered_paths)/float(allPaths)) / (float(len(allMaxes))/float(allNodes)) < knee_threshold:
                break
            number_of_prev_covered_paths = number_of_current_covered_paths
            numberOfUpwardPaths = {}
            numberOfDownwardPaths = {}
            for node in nx.nodes(self.DAGGraph):
                numberOfUpwardPaths[node] = 0
                numberOfDownwardPaths[node] = 0
            self.calculateNumberOfUpwardPaths(sources, targets, numberOfUpwardPaths)
            self.calculateNumberOfDownwardPaths(sources, targets, numberOfDownwardPaths)
            for t in targets:
                numberOfUpwardPaths[t] = 0
            # for s in sources:
            #     numberOfDownwardPaths[s] = 0
            centralities = self.calculateCentralities(numberOfUpwardPaths, numberOfDownwardPaths)
            topCentralNodeInfo = max(centralities, key=lambda x: x[1])
            allMaxes = [k for k in centralities if k[1] == topCentralNodeInfo[1]]
            number_of_current_paths = numberOfDownwardPaths[0]
        self.DAGGraph = nx.MultiGraph()
        self.createDAGGraph()#Reconstructing the DAG graph
        core = []
        # print str(len(nx.nodes(self.DAGGraph)) - len(targets) - len(sources)) + '\t' + str(allPaths)
        arrayOfStrings = self.getListNodeStrings(listOfCentralNodes)
        for i in range(len(arrayOfStrings)):
            nodeString = arrayOfStrings[i]
            if node_dic[nodeString]['core_index'] == 0:
                node_dic[nodeString]['core_index'] = age
            node_dic[nodeString]['core_count'] += 1
            core.append(nodeString.rstrip())
            # print nodeString.rstrip() + '\t' + str(listOfCentralNodes_cents[i]) + '\t' + str(orig_cents[listOfCentralNodes[i]])
        return core, listOfCentralNodes_cents
    # Returns a list of strings, corresponding to the nodes removed from DAG, according to greedy core identification algorithm, based on the cardinality of the extracted set
    def greedyCoreID_ByCardinality(self, k):
        numberOfUpwardPaths = {}
        numberOfDownwardPaths = {}
        sources = []
        targets = []
        for node in nx.nodes(self.DAGGraph):
            if self.DAGGraph.in_degree(node) == 0:
                sources.append(node)
            if self.DAGGraph.out_degree(node) == 0:
                targets.append(node)
            numberOfUpwardPaths[node] = 0
            numberOfDownwardPaths[node] = 0
        self.calculateNumberOfUpwardPaths(sources, targets, numberOfUpwardPaths)
        self.calculateNumberOfDownwardPaths(sources, targets, numberOfDownwardPaths)
        for t in targets:
            numberOfUpwardPaths[t] = 0
        for s in sources:
            numberOfDownwardPaths[s] = 0
        number_of_initial_paths = numberOfDownwardPaths[0]
        number_of_current_paths = numberOfDownwardPaths[0]
        listOfCentralNodes = []
        centralities = self.calculateCentralities(numberOfUpwardPaths, numberOfDownwardPaths)
        topCentralNodeInfo = max(centralities, key=lambda x: x[1])
        allMaxes = [k for k in centralities if k[1] == topCentralNodeInfo[1]]
        while topCentralNodeInfo[1] > 0 and len(listOfCentralNodes) <= k:  # Node with positive centrality exists
            for nodeToBeRemoved in allMaxes:
                nodeToBeRemoved = nodeToBeRemoved[0]
                self.DAGGraph.remove_node(nodeToBeRemoved)
                listOfCentralNodes.append(nodeToBeRemoved)
            numberOfUpwardPaths = {}
            numberOfDownwardPaths = {}
            for node in nx.nodes(self.DAGGraph):
                numberOfUpwardPaths[node] = 0
                numberOfDownwardPaths[node] = 0
            self.calculateNumberOfUpwardPaths(sources, targets, numberOfUpwardPaths)
            self.calculateNumberOfDownwardPaths(sources, targets, numberOfDownwardPaths)
            for t in targets:
                numberOfUpwardPaths[t] = 0
            for s in sources:
                numberOfDownwardPaths[s] = 0
            centralities = self.calculateCentralities(numberOfUpwardPaths, numberOfDownwardPaths)
            topCentralNodeInfo = max(centralities, key=lambda x: x[1])
            allMaxes = [k for k in centralities if k[1] == topCentralNodeInfo[1]]
            number_of_current_paths = numberOfDownwardPaths[0]
        self.DAGGraph = nx.MultiGraph()
        self.createDAGGraph()  # Reconstructing the DAG graph
        core = []
        for i in range(len(listOfCentralNodes)):
            core.append(self.getNodeString(listOfCentralNodes[i]))
        return core
    #Calculates the centralities for all nodes
    def Length(self, node):
        return len(nx.label(self.DAGGraph, node).split())
    def calculateCentralities(self, numberOfUpwardPaths, numberOfDownwardPaths):
        result = []
        for node in nx.nodes(self.DAGGraph):
            result.append((node, numberOfUpwardPaths[node] * numberOfDownwardPaths[node],(numberOfUpwardPaths[node],numberOfDownwardPaths[node])))
            # result.append((node, numberOfUpwardPaths[node] * Length[node]))
        return result
    #Calculates the number of Upward paths for all nodes
    def calculateNumberOfUpwardPaths(self, sources, targets, numberOfUpwardPaths):
        for n in sources:
            self.dfsUpward(n, sources, targets, numberOfUpwardPaths)
    # Helper recursive function
    def dfsUpward(self, n, sources, targets, numberOfUpwardPaths):
        if self.DAGGraph.out_degree(n) == 0:
            # if n in targets:
            numberOfUpwardPaths[n] = 1
            return
            # else:
            #     numberOfUpwardPaths[n] = 0
            #     return
        elif numberOfUpwardPaths[n] > 0:
            return
        else:
            for o in self.DAGGraph.out_edges(n):
                self.dfsUpward(o[1], sources, targets, numberOfUpwardPaths)
                numberOfUpwardPaths[n] += numberOfUpwardPaths[o[1]]
    # Calculates the number of Downward paths for all nodes
    def calculateNumberOfDownwardPaths(self, sources, targets, numberOfDownwardPaths):
        for n in targets:
            self.dfsDownward(n, sources, targets, numberOfDownwardPaths)
    # Helper recursive function
    def dfsDownward(self, n, sources, targets, numberOfDownwardPaths):
        if self.DAGGraph.in_degree(n) == 0:
            # if n in sources:
            numberOfDownwardPaths[n] = 1
            return
            # else:
            #     numberOfDownwardPaths[n] = 0
            #     return
        elif numberOfDownwardPaths[n] > 0:
            return
        else:
            for o in self.DAGGraph.in_edges(n):
                self.dfsDownward(o[0], sources, targets, numberOfDownwardPaths)
                numberOfDownwardPaths[n] += numberOfDownwardPaths[o[0]]

    # Calculates the number of Downward paths for all nodes
    def calculateNumber_and_LengthOfDownwardPaths(self, sources, targets, numberOfDownwardPaths, lengths):
        for n in targets:
            self.dfsDownward_length(n, sources, targets, numberOfDownwardPaths, lengths)

    # Helper recursive function
    def dfsDownward_length(self, n, sources, targets, numberOfDownwardPaths, lengths):
        if self.DAGGraph.in_degree(n) == 0:
            numberOfDownwardPaths[n] = 1
            lengths[n] = [0]
            return
        elif numberOfDownwardPaths[n] > 0:
            return
        else:
            for o in self.DAGGraph.in_edges(n):
                self.dfsDownward_length(o[0], sources, targets, numberOfDownwardPaths, lengths)
                numberOfDownwardPaths[n] += numberOfDownwardPaths[o[0]]
                for l in lengths[o[0]]:
                    lengths[n].append(1+l)
    # ...........Printing Functions........
    # Prints the DAG, optionally in integer form if intDAGPrint==True
    def printDAG(self, intDAGPrint):
        # self.logMessage('DAGCost(Concats): ' + str(self.DAGCost(CostFunction.ConcatenationCost)))
        # self.logMessage('DAGCost(Edges):' + str(self.DAGCost(CostFunction.EdgeCost)))
        print 'DAGCost(Concats): ' + str(self.DAGCost(CostFunction.ConcatenationCost))
        print 'DAGCost(Edges):' + str(self.DAGCost(CostFunction.EdgeCost))
        # return
        DAG = self.concatenatedDAG
        # print 'dag'
        # print DAG
        NTs = self.concatenatedNTs
        # print 'nts'
        # print NTs
        separatorInts = self.separatorInts
        Dic = self.dic
        nodes = {}
        ntDic = {}
        counter = 1
        NTsSorted = set([])
        for i in range(len(NTs)):
            if NTs[i] not in ntDic and NTs[i] not in separatorInts:
                NTsSorted.add(NTs[i])
                # ntDic[NTs[i]] = 'N'+str(counter)
                # nodes['N'+str(counter)] = ''
                ntDic[NTs[i]] = 'N' + str(NTs[i])
                nodes['N' + str(NTs[i])] = ''
                counter += 1
        for i in range(len(DAG)):
            if DAG[i] not in NTsSorted:
                # sys.stderr.write(str(DAG[i]) + ' ')
                if DAG[i] not in separatorInts:
                    if not intDAGPrint:
                        try:
                            nodes[ntDic[NTs[i]]] = str(nodes[ntDic[NTs[i]]]) + ' ' + str(Dic[DAG[i]])
                        except:
                            print DAG[i], NTs[i]
                            raise
                    else:
                        nodes[ntDic[NTs[i]]] = str(nodes[ntDic[NTs[i]]]) + ' ' + str(DAG[i])
                else:
                    nodes[ntDic[NTs[i - 1]]] = str(nodes[ntDic[NTs[i - 1]]]) + ' ||'
            else:
                if not intDAGPrint:
                    try:
                        nodes[ntDic[NTs[i]]] = str(nodes[ntDic[NTs[i]]]) + ' ' + str(ntDic[DAG[i]])
                    except:
                        print DAG[i], NTs[i]
                        raise
                else:
                    nodes[ntDic[NTs[i]]] = str(nodes[ntDic[NTs[i]]]) + ' ' + str(ntDic[DAG[i]])
        NTsSorted = sorted(list(NTsSorted))
        nodeCounter = 0
        for nt in NTsSorted:
            if intDAGPrint:
                subnodes = nodes[ntDic[nt]].rstrip(' ||').split(' ||')
                for s in subnodes:
                    print ntDic[nt] + ' ->' + s
            else:
                subnodes = nodes[ntDic[nt]].rstrip(' ||').split(' ||')
                for s in subnodes:
                    print ntDic[nt] + ' -> ' + s
            nodeCounter += 1
    def printDAG_toFile(self, outFile, intDAGPrint):
        # self.logMessage('DAGCost(Concats): ' + str(self.DAGCost(CostFunction.ConcatenationCost)))
        # self.logMessage('DAGCost(Edges):' + str(self.DAGCost(CostFunction.EdgeCost)))
        outFile.write('DAGCost(Concats): ' + str(self.DAGCost(CostFunction.ConcatenationCost)) + '\n')
        outFile.write('DAGCost(Edges):' + str(self.DAGCost(CostFunction.EdgeCost)) + '\n')
        DAG = self.concatenatedDAG
        # print 'dag'
        # print DAG
        NTs = self.concatenatedNTs
        # print 'nts'
        # print NTs
        separatorInts = self.separatorInts
        Dic = self.dic
        nodes = {}
        ntDic = {}
        counter = 1
        NTsSorted = set([])
        for i in range(len(NTs)):
            if NTs[i] not in ntDic and NTs[i] not in separatorInts:
                NTsSorted.add(NTs[i])
                # ntDic[NTs[i]] = 'N'+str(counter)
                # nodes['N'+str(counter)] = ''
                ntDic[NTs[i]] = 'N' + str(NTs[i])
                nodes['N' + str(NTs[i])] = ''
                counter += 1
        # print DAG
        # print separatorInts
        # print NTs
        # print NTsSorted
        for i in range(len(DAG)):
            if DAG[i] not in NTsSorted:
                # sys.stderr.write(str(DAG[i]) + ' ')
                if DAG[i] not in separatorInts:
                    if not intDAGPrint:
                        try:
                            nodes[ntDic[NTs[i]]] = str(nodes[ntDic[NTs[i]]]) + ' ' + str(Dic[DAG[i]])
                        except:
                            print DAG[i], NTs[i]
                            raise
                    else:
                        nodes[ntDic[NTs[i]]] = str(nodes[ntDic[NTs[i]]]) + ' ' + str(DAG[i])
                else:
                    # print i - 1
                    # print NTs[i - 1]
                    # print ntDic[NTs[i - 1]]
                    # print nodes[ntDic[NTs[i - 1]]]
                    nodes[ntDic[NTs[i - 1]]] = str(nodes[ntDic[NTs[i - 1]]]) + ' ||'
            else:
                if not intDAGPrint:
                    try:
                        nodes[ntDic[NTs[i]]] = str(nodes[ntDic[NTs[i]]]) + ' ' + str(ntDic[DAG[i]])
                    except:
                        print DAG[i], NTs[i]
                        raise
                else:
                    nodes[ntDic[NTs[i]]] = str(nodes[ntDic[NTs[i]]]) + ' ' + str(ntDic[DAG[i]])
        NTsSorted = sorted(list(NTsSorted))
        nodeCounter = 0
        for nt in NTsSorted:
            if intDAGPrint:
                subnodes = nodes[ntDic[nt]].rstrip(' ||').split(' ||')
                for s in subnodes:
                    outFile.write(ntDic[nt] + ' ->' + s + '\n')
            else:
                subnodes = nodes[ntDic[nt]].rstrip(' ||').split(' ||')
                for s in subnodes:
                    outFile.write(ntDic[nt] + ' -> ' + s + '\n')
            nodeCounter += 1
        outFile.close()
    # Log via flags
    def logViaFlag(self, flag):
        if not self.quietLog:
            if flag == LogFlag.ConcatenationCostLog:
                sys.stderr.write('DAGCost(Concats): ' + str(self.DAGCost(CostFunction.ConcatenationCost)) + '\n')
                print(str('DAGCost(Concats): ' + str(self.DAGCost(CostFunction.ConcatenationCost))))
            if flag == LogFlag.EdgeCostLog:
                sys.stderr.write('DAGCost(Edges): ' + str(self.DAGCost(CostFunction.EdgeCost)) + '\n')
                print(str('DAGCost(Edges): ' + str(self.DAGCost(CostFunction.EdgeCost))))
    # Log custom message
    def logMessage(self, message):
        if not self.quietLog:
            sys.stderr.write(message + '\n')
            print(str(message))

    # ...........Utility Functions........
    # Converts the input data into an integer sequence, returns the integer sequence and the dictionary for recovering orginal letters
    def preprocessInput(self, inputFile, charSeq=SequenceType.Character, noNewLineFlag=True):
        if charSeq == SequenceType.Character:  # Building an integer-spaced sequence from the input string
            letterDict = {}
            counterDict = {}
            i = 0
            counter = 1
            newContents = ''
            if noNewLineFlag:
                line = inputFile.read()
                for i in range(len(line)):
                    if line[i] not in counterDict:
                        letterDict[counter] = line[i]
                        counterDict[line[i]] = counter
                        counter += 1
                    newContents += str(counterDict[line[i]]) + ' '
            else:
                for line in inputFile:
                    line = line.rstrip('\n')
                    for i in range(len(line)):
                        if line[i] not in counterDict:
                            letterDict[counter] = line[i]
                            counterDict[line[i]] = counter
                            counter += 1
                        newContents += str(counterDict[line[i]]) + ' '
                    newContents += '\n'
            return (newContents.rstrip('\n'), letterDict)
        if charSeq == SequenceType.Integer:  # input is space seperated integers
            newContents = ''
            dict = {}
            for l in inputFile.read().splitlines():
                line = l.split()
                for i in range(len(line)):
                    if not isinstance(int(line[i]), int) or line[i] == ' ':
                        raise ValueError('Input file is not in space-separated integer form.')
                    else:
                        dict[int(line[i])] = line[i]
                newContents += l + '\n'
            return (newContents.rstrip('\n'), dict)
        if charSeq == SequenceType.SpaceSeparated:  # input is space-seperated words
            wordDict = {}
            counterDict = {}
            i = 0
            counter = 1
            newContents = ''
            for line in inputFile:
                line = line.rstrip('\n')
                for w in line.split():
                    if w not in counterDict:
                        wordDict[counter] = w
                        counterDict[w] = counter
                        counter += 1
                    newContents += str(counterDict[w]) + ' '
                newContents += '\n'
            return (newContents.rstrip('\n'), wordDict)
    def calcPaths(self):
        # for p in nx.simple_cycles(self.DAGGraph):
        #     print p
        #     return
        numberOfDownwardPaths = {}
        lengths = {}
        sources = []
        targets = []
        for node in nx.nodes(self.DAGGraph):
            if self.DAGGraph.in_degree(node) == 0:
                sources.append(node)
            if self.DAGGraph.out_degree(node) == 0:
                targets.append(node)
            numberOfDownwardPaths[node] = 0
            lengths[node] = []
        print '\t' + '\t' + '\t' + '\t' + '\t' + '\t' + str(len(sources))
        return
        self.calculateNumber_and_LengthOfDownwardPaths(sources, targets, numberOfDownwardPaths, lengths)
        centralNodes, cents = self.greedyCoreID_ByTau(0.9)
        # print centralNodes
        # print cents
        max = 0
        sum = 0
        num = 0
        for n in targets:
            for l in lengths[n]:
                if max < l:
                    max = l
                sum += l
                num += 1
        print '\t' + str(len(nx.nodes(self.DAGGraph))-len(targets)-len(sources)) + '\t' + str(max) + '\t' + str(float(sum)/float(num)) + '\t' + str(len(centralNodes)) + '\t' + str(cents[0]) + '\t' + str(1-float(len(centralNodes))/float(len(sources)))
    def stats(self):
        # sources = []
        # targets = []
        # for node in nx.nodes(self.DAGGraph):
        #     if self.DAGGraph.in_degree(node) == 0:
        #         sources.append(node)
        #     if self.DAGGraph.out_degree(node) == 0:
        #         targets.append(node)
        # print '\t' + str(len(nx.nodes(self.DAGGraph))-len(targets)-len(sources))

        g.calcPaths()


def structureParenthesization(grammarFile):
    counter = 1
    grammar = {}
    for line in open(grammarFile,'r').readlines():
        if counter <= 2:
            counter += 1
            continue
        nt = line.split(' ->  ')[0]
        rule = line.split(' ->  ')[1].split()
        if nt not in grammar:
            grammar[nt] = []
        grammar[nt].append(rule)
    parentheses = []
    for rule in grammar['N0']:
        ruleParenthesesList = []
        parenthesisIndex = 0
        stack = copy.deepcopy(rule)
        ntStack = ['N0']
        ntText = []
        while len(stack) > 0:
            c = stack.pop(0)
            if c == -2:  # Repeat NT recursion
                ntStack.pop()
                ntText.append(-2)
                continue
            if c in grammar:
                ntStack.append(c)
                stack = grammar[c][0] + [-2] + stack
                ntText.append(-1)
            else:
                ntText.append(c)
        # print ntText
        trueIndex = 0
        parentheses.append(set([]))
        parenthStack = []
        for i in range(0,len(ntText)):
            if ntText[i] == -1:
                parenthStack.append(trueIndex)
            elif ntText[i] == -2:
                parentheses[-1].add((parenthStack.pop(0),trueIndex))
            else:
                trueIndex += 1
    return parentheses
def structSimTest(file1, file2):
    csParenth = structureParenthesization(file1)
    testParenth = structureParenthesization(file2)
    meanDistance = 0.0
    for i in range(0,len(csParenth)):
        p1 = csParenth[i]
        p2 = testParenth[i]
        # print 'p1', p1
        # print 'p2', p2
        # break
        if len(p1) == 0 and len(p2) == 0:
            meanDistance += 1
        else:
            meanDistance += 2*len(p1.intersection(p2))/(len(p1)+len(p2))
    meanDistance /= len(csParenth)
    return meanDistance
#Sets the value of parameters
def processParams(argv):
    chFlag = SequenceType.Character #if false, accepts integer sequence
    printIntsDAG = False #if true, prints the DAG in integer sequence format
    quietLog = False #if true, disables logging
    rFlag = 'mr' #repeat type (for normal repeat replacements)
    functionFlag = 'e' #cost function to be optimized
    noNewLineFlag = True #consider each line as a separate string
    loadDAGFlag = False

    usage = """Usage: ./python Lexis.py [-t (c | i | s) | -p (i) | -q | -r (r | mr | lmr | smr) | -f (c | e) | -m | -l] <filename>
    [-t]: choosing between character sequence, integer sequence or space-separated sequence
        c - character sequence
        i - integer sequence
        s - space-separated sequence
    [-p]: specifies DAG printing option (for debugging purposes)
        i - prints the DAG in integer sequence format
    [-q]: disables logging
    [-r]: repeat type (for normal repeat replacements)
        r - repeat
        mr - maximal repeat (default)
        lmr - largest-maximal repeat
        smr - super-maximal repeat
    [-f]: cost function to be optimized
        c - concatenation cost
        e - edge cost (default)
    [-m]: consider each line of the input file as a separate target string
    [-l]: load a DAG file (will override -r -t -m options)
                    """
    if len(argv) == 1 or (len(argv) == 2 and argv[1] == '-h'):
        sys.stderr.write('Invalid input\n')
        sys.stderr.write(usage + '\n')
        sys.exit()
    optlist,args = getopt.getopt(argv[1:], 't:p:qr:f:ml')
    for opt,arg in optlist:
        if opt == '-t':
            for ch in arg:
                if ch == 'c' or ch == 'i' or ch == 's':
                    chFlag = ch
                else:
                    sys.stderr.write('Invalid input in ' + '-i' + ' flag\n')
                    sys.stderr.write(usage + '\n')
                    sys.exit()
        if opt == '-p':
            for ch in arg:
                if ch == 'i':
                    printIntsDAG = True
                else:
                    sys.stderr.write('Invalid input in ' + '-p' + ' flag\n')
                    sys.stderr.write(usage + '\n')
                    sys.exit()
        if opt == '-q':
            quietLog = True
        if opt == '-r':
            if arg == 'r' or arg == 'mr' or arg == 'lmr' or arg == 'smr':
                rFlag = arg
            else:
                sys.stderr.write('Invalid input in ' + '-r' + ' flag\n')
                sys.stderr.write(usage + '\n')
                sys.exit()
        if opt == '-f':
            if arg == 'c' or arg == 'e':
                functionFlag = arg
            else:
                sys.stderr.write('Invalid input in ' + '-f' + ' flag\n')
                sys.stderr.write(usage + '\n')
                sys.exit()
        if opt == '-m':
            noNewLineFlag = False
        if opt == '-l':
            loadDAGFlag = True
    return (chFlag, printIntsDAG, quietLog, rFlag, functionFlag, noNewLineFlag, loadDAGFlag)

def rand_input_q_analysis(rand_inputs_path, nodes_dic_path, num_rands):
    import pickle
    import os
    nodes_dic = pickle.load(open(nodes_dic_path, "rb"))
    nodes_rands = []; edges_rand=[]; sources_rand = []; intermediate_nodes_rand = [];
    rand_inputs = [f for f in os.listdir(rand_inputs_path) if os.path.isfile(join(rand_inputs_path, f)) and not f.startswith('.')]
    #get rand inoput stats
    counter = 1
    tmp_dag = DAG(open(rand_inputs_path + rand_inputs[0], 'r'), True, SequenceType.SpaceSeparated, noNewLineFlag)
    sources = [];targets = []
    for node in nx.nodes(tmp_dag.DAGGraph):
        if tmp_dag.DAGGraph.in_degree(node) == 0: sources.append(node)
        if tmp_dag.DAGGraph.out_degree(node) == 0: targets.append(node)
    for f in rand_inputs:
        sys.stderr.write(str(counter) + '\n')
        counter += 1
        tmp_dag = DAG(open(rand_inputs_path + f, 'r'), True, SequenceType.SpaceSeparated, noNewLineFlag)
        nodes_rands.append(len(nx.nodes(tmp_dag.DAGGraph))); edges_rand.append(len(nx.edges(tmp_dag.DAGGraph)));
        sources_rand.append((len(sources)));intermediate_nodes_rand.append((len(nx.nodes(tmp_dag.DAGGraph)) - len(sources)))
    print str(np.mean(nodes_rands)) + '±' + str(np.std(nodes_rands)) + '\t',
    print str(np.mean(edges_rand)) + '±' + str(np.std(edges_rand)) + '\t',
    print str(np.mean(sources_rand)) + '±' + str(np.std(sources_rand)) + '\t',
    print str(np.mean(intermediate_nodes_rand)) + '±' + str(np.std(intermediate_nodes_rand))
    print
    print
    for q in [0.001, 0.01] + list(np.arange(0.1, 1, 0.1)) + [0.95, 0.99, 0.999]:
        sys.stderr.write(str(q) + '\n')
        q_nodes_rands = []; q_edges_rand = []; q_sources_rand = []; q_intermediate_nodes_rand = [];
        q_num_of_pruned_nodes_rand = []; q_frac_of_pruned_nodes_rand = []; q_num_nonsource_pruned_rand = [];
        for f in rand_inputs:
            tmp_dag = DAG(open(rand_inputs_path + f, 'r'), True, SequenceType.SpaceSeparated, noNewLineFlag)
            new_tmp_dag = pruneDAG_withNodeDic(nodes_dic, num_rands, tmp_dag, q)
            new_sources = [];
            new_targets = []
            for node in nx.nodes(new_tmp_dag.DAGGraph):
                if new_tmp_dag.DAGGraph.in_degree(node) == 0:
                    new_sources.append(node)
                if new_tmp_dag.DAGGraph.out_degree(node) == 0:
                    new_targets.append(node)
            q_nodes_rands.append(len(nx.nodes(new_tmp_dag.DAGGraph)));
            q_edges_rand.append(len(nx.edges(new_tmp_dag.DAGGraph)));
            q_sources_rand.append((len(new_sources)));
            q_intermediate_nodes_rand.append((len(nx.nodes(new_tmp_dag.DAGGraph)) - len(new_sources)))

            q_num_of_pruned_nodes_rand.append(len(nx.nodes(tmp_dag.DAGGraph))-len(nx.nodes(new_tmp_dag.DAGGraph)))
            q_frac_of_pruned_nodes_rand.append(float(len(nx.nodes(tmp_dag.DAGGraph))-len(nx.nodes(new_tmp_dag.DAGGraph)))/float(len(nx.nodes(tmp_dag.DAGGraph))))
            q_num_nonsource_pruned_rand.append(len(nx.nodes(tmp_dag.DAGGraph))-len(nx.nodes(new_tmp_dag.DAGGraph))-len(sources))
        print str(np.mean(q_nodes_rands)) + '±' + str(np.std(q_nodes_rands)) + '\t',
        print str(np.mean(q_edges_rand)) + '±' + str(np.std(q_edges_rand)) + '\t',
        print str(np.mean(q_sources_rand)) + '±' + str(np.std(q_sources_rand)) + '\t',
        print str(np.mean(q_intermediate_nodes_rand)) + '±' + str(np.std(q_intermediate_nodes_rand)) + '\t',

        print str(np.mean(q_num_of_pruned_nodes_rand)) + '±' + str(np.std(q_num_of_pruned_nodes_rand)) + '\t',
        print str(np.mean(q_frac_of_pruned_nodes_rand)) + '±' + str(np.std(q_frac_of_pruned_nodes_rand)) + '\t',
        print str(np.mean(q_num_nonsource_pruned_rand)) + '±' + str(np.std(q_num_nonsource_pruned_rand))
    return

def calc_max_prob_diff(file1, file2):
    ranks1 = [l.split('\t')[1] for l in open(file1, 'r').readlines()]
    ranks2 = [l.split('\t')[1] for l in open(file2, 'r').readlines()]
    max_diff = 0
    for i in range(len(ranks1)):
        if max_diff < abs(float(ranks1[i])-float(ranks2[i])):
            max_diff = abs(float(ranks1[i])-float(ranks2[i]))
    print max_diff

def calc_rank_corr(file1, file2):
    import scipy.stats
    ranks1 = [l.split('\t')[0] for l in open(file1,'r').readlines()]
    ranks2 = [l.split('\t')[0] for l in open(file2,'r').readlines()]
    print scipy.stats.spearmanr(ranks1, ranks2)
    print scipy.stats.kendalltau(ranks1, ranks2)

def listProbs(dag, num_rands):
    import pickle
    nodes_dic = pickle.load(open("nodes-dic/nodes-dic"+str(num_rands)+".p", "rb"))
    nodeStrings = dag.getListNodeStrings(nx.nodes(dag.DAGGraph))
    node_list = list(nx.nodes(dag.DAGGraph))
    probs = {}
    for i in range(len(nodeStrings)):
        node = node_list[i]
        node_str = nodeStrings[i]
        probs[node_str] = float(nodes_dic[node_str]) / float(num_rands)
    probs = {k:probs[k] for k in probs if len(k.split()) > 1}
    probs_list = sorted(probs.iteritems(), key = lambda x : (x[1],x[0]), reverse = True)
    for i in range(len(probs_list)):
        print str(probs_list[i][0]) + '\t' + str(probs_list[i][1])

def create_nodes_prob_dic(origFile, name, folderName, num_rand):
    NUMBER_OF_RANDOMIZATIONS = num_rand
    import pickle
    offset = 1000
    # nodes_dic = pickle.load(open("nodes-dic/nodes-dic"+str(NUMBER_OF_RANDOMIZATIONS-offset)+".p", "rb"))
    # start_index = NUMBER_OF_RANDOMIZATIONS - offset
    start_index = 0
    nodes_dic = defaultdict(int)
    totalFileString = ''
    lengths = []
    # origFileObj = open(folderName+'/'+origFile+'.txt','r')
    for l in origFile.readlines():
        totalFileString += l
        lengths.append(len(l.split()))
    orig_totalFileString_list = totalFileString.split()
    for r in range(start_index, NUMBER_OF_RANDOMIZATIONS):
        sys.stderr.write('rand' + str(r) + '\n')
        if True:
            totalFileString_list = orig_totalFileString_list
            random.shuffle(totalFileString_list)
            new_strings = []
            for l in lengths:
                new_strings.append(' '.join(totalFileString_list[:l]))
                totalFileString_list = totalFileString_list[l:]
            tmp_file = open(folderName +'/' + name+ '-rand' +'/' + name+ '-rand' + str(r) + '.txt', 'w')
            tmp_file.write('\n'.join(new_strings))
            tmp_file.close()
            tmp_dag = DAG(open(folderName +'/' + name+ '-rand' +'/' + name+ '-rand' + str(r) + '.txt', 'r'), False, SequenceType.SpaceSeparated,
                          noNewLineFlag)
            tmp_dag.GLexis(True, RepeatClass.MaximalRepeat, CostFunction.EdgeCost)
            tmp_dag.printDAG_toFile(open(folderName +'/' + name+ '-rand' +'/' + name+ '-gram-rand' + str(r) + '.txt', 'w'), False)
        else:
            tmp_dag = DAG(open(folderName + '/gram-rand' + ("%05d" % (r,)) + '.txt', 'r'), True,
                          SequenceType.SpaceSeparated, noNewLineFlag)
        tmp_nodeStrings = tmp_dag.getListNodeStrings(nx.nodes(tmp_dag.DAGGraph))
        for i in range(len(tmp_nodeStrings)):
            node = nx.nodes(tmp_dag.DAGGraph)[i]
            node_str = tmp_nodeStrings[i]
            if node != 0:
                nodes_dic[node_str] += 1
    import pickle
    pickle.dump(nodes_dic, open(folderName +'/' + name+ '-rand' +'/' + name+ '-nodes-dic' + str(NUMBER_OF_RANDOMIZATIONS) + ".p", "wb"))
    # nodes_dic = pickle.load(open("nodes-dic"+str(NUMBER_OF_RANDOMIZATIONS)+".p", "rb"))
    return nodes_dic

def pruneDAG(origFile, name, folderName, dag, q, num_rand):
    NUMBER_OF_RANDOMIZATIONS = num_rand
    # nodes_dic = create_nodes_prob_dic(origFile, folderName, dag, num_rand)
    nodes_dic = create_nodes_prob_dic(origFile, name, folderName, num_rand)
    removed_nodes = set([])
    nodeStrings = dag.getListNodeStrings(nx.nodes(dag.DAGGraph))
    for i in range(len(nodeStrings)):
        node = list(nx.nodes(dag.DAGGraph))[i]
        node_str = nodeStrings[i]
        if float(nodes_dic[node_str])/float(NUMBER_OF_RANDOMIZATIONS) > q:
            removed_nodes.add(node)
    for nodeToBeRemoved in removed_nodes:
        dag.DAGGraph.remove_node(nodeToBeRemoved)
    return removed_nodes, dag

def pruneDAG_withNodeDic(nodes_dic, num_rand, input_dag, q):
    removed_nodes = set([])
    import copy
    dag = copy.deepcopy(input_dag)
    nodeStrings = dag.getListNodeStrings(nx.nodes(dag.DAGGraph))
    for i in range(len(nodeStrings)):
        node = list(nx.nodes(dag.DAGGraph))[i]
        node_str = nodeStrings[i]
        if float(nodes_dic[node_str])/float(num_rand) > q:
            removed_nodes.add(node)
    for nodeToBeRemoved in removed_nodes:
        dag.DAGGraph.remove_node(nodeToBeRemoved)
    return dag

def convertGMLtoDAG(gmlFile):
    pass

def printNodeStats2(graph, gr_nodes):
    sources = []
    targets = []
    for node in nx.nodes(graph):
        if graph.in_degree(node) == 0:
            sources.append(node)
        if graph.out_degree(node) == 0:
            targets.append(node)
    centsDic, numberOfDownwardPaths, numberOfUpwardPaths = getAllNodesCentralities(graph)
    for node in nx.nodes(graph):
        if node not in targets:
            print str(len(node.split())) + '\t' + str(graph.out_degree(node)) + '\t' + str(numberOfDownwardPaths[node]) + '\t' + str(numberOfUpwardPaths[node])+ '\t' + str(centsDic[node]) + '\t',
            if node in gr_nodes:
                print 1
            else:
                print 0

def printNodeStats(graph, filePath):
    sources = []
    targets = []
    for node in nx.nodes(graph):
        if graph.in_degree(node) == 0:
            sources.append(node)
        if graph.out_degree(node) == 0:
            targets.append(node)
    centsDic, numberOfDownwardPaths, numberOfUpwardPaths = getAllNodesCentralities(graph)
    # print str(len(nx.nodes(graph))) + '\t' + str(len(nx.edges(graph))) + '\t' + str(len(sources)) + '\t' + str(len(nx.nodes(graph))-len(sources))
    # return

    outFile = open(filePath,'w')
    for node in nx.nodes(graph):
        if node not in targets:
            # print str(len(node.split())) + '\t' + str(graph.out_degree(node)) + '\t' + str(numberOfDownwardPaths[node]) + '\t' + str(numberOfUpwardPaths[node])+ '\t' + str(centsDic[node])
            # outFile.write(str(node) + '\t' + str(len(node.split())) + '\t' + str(graph.out_degree(node)) + '\t' + str(numberOfDownwardPaths[node]) + '\t' + str(numberOfUpwardPaths[node]) + '\t' + str(centsDic[node]) + '\n')
            outFile.write(str(len(node.split())) + '\t' + str(graph.out_degree(node)) + '\t' + str(
                numberOfDownwardPaths[node]) + '\t' + str(numberOfUpwardPaths[node]) + '\t' + str(
                centsDic[node]) + '\n')
            # print str(node) + '\t' + str(graph.out_degree(node)) + '\t' + str(numberOfDownwardPaths[node]) + '\t' + str(numberOfUpwardPaths[node]) + '\t' + str(centsDic[node])
    outFile.close()

def getAllNodesCentralities(graph):
    numberOfUpwardPaths = {}
    numberOfDownwardPaths = {}
    sources = []
    targets = []
    for node in nx.nodes(graph):
        if graph.in_degree(node) == 0:
            sources.append(node)
        if graph.out_degree(node) == 0:
            targets.append(node)
        numberOfUpwardPaths[node] = 0
        numberOfDownwardPaths[node] = 0
    calculateNumberOfUpwardPaths(graph, sources, targets, numberOfUpwardPaths)
    calculateNumberOfDownwardPaths(graph, sources, targets, numberOfDownwardPaths)
    centralities = calculateCentralities(graph, numberOfUpwardPaths, numberOfDownwardPaths)
    return {k: v for k, v in centralities}, numberOfDownwardPaths, numberOfUpwardPaths
def calculateCentralities(graph, numberOfUpwardPaths, numberOfDownwardPaths):
    result = []
    for node in nx.nodes(graph):
        result.append((node, numberOfUpwardPaths[node] * numberOfDownwardPaths[node]))
        # result.append((node, numberOfUpwardPaths[node] * len(node.split())))
        # result.append((node, len(node.split()) * numberOfDownwardPaths[node]))
    return result
#Calculates the number of Upward paths for all nodes
def calculateNumberOfUpwardPaths(graph, sources, targets, numberOfUpwardPaths):
    for n in sources:
        dfsUpward(graph, n, sources, targets, numberOfUpwardPaths)
# Helper recursive function
def dfsUpward(graph, n, sources, targets, numberOfUpwardPaths):
    if graph.out_degree(n) == 0:
        numberOfUpwardPaths[n] = 1
        return
    elif numberOfUpwardPaths[n] > 0:
        return
    else:
        for o in graph.out_edges(n):
            dfsUpward(graph, o[1], sources, targets, numberOfUpwardPaths)
            numberOfUpwardPaths[n] += numberOfUpwardPaths[o[1]]
# Calculates the number of Downward paths for all nodes
def calculateNumberOfDownwardPaths(graph, sources, targets, numberOfDownwardPaths):
    for n in targets:
        dfsDownward(graph, n, sources, targets, numberOfDownwardPaths)
# Helper recursive function
def dfsDownward(graph, n, sources, targets, numberOfDownwardPaths):
    if graph.in_degree(n) == 0:
        numberOfDownwardPaths[n] = 1
        return
    elif numberOfDownwardPaths[n] > 0:
        return
    else:
        for o in graph.in_edges(n):
            dfsDownward(graph, o[0], sources, targets, numberOfDownwardPaths)
            numberOfDownwardPaths[n] += numberOfDownwardPaths[o[0]]

def coreID_byTau(graph, tau):
    cycle = False
    for p in nx.simple_cycles(graph):
        print p
        cycle = True
    if cycle:
        print 'CYCLE!'
        return
    numberOfUpwardPaths = {}
    numberOfDownwardPaths = {}
    sources = []
    targets = []
    for node in nx.nodes(graph):
        if graph.in_degree(node) == 0:
            sources.append(node)
        if graph.out_degree(node) == 0:
            targets.append(node)
        numberOfUpwardPaths[node] = 0
        numberOfDownwardPaths[node] = 0
    calculateNumberOfUpwardPaths(graph, sources, targets, numberOfUpwardPaths)
    calculateNumberOfDownwardPaths(graph, sources, targets, numberOfDownwardPaths)
    allPaths = 0
    # print targets
    for n in targets:
        allPaths += numberOfDownwardPaths[n]
    # return
    lenNodes = len(nx.nodes(graph))
    lenAllPaths = allPaths
    lenSources = len([x for x in nx.nodes(graph) if graph.in_degree(x) == 0])
    # print str(len(nx.nodes(graph))) + '\t' + str(allPaths)
    for t in targets:
        numberOfUpwardPaths[t] = 0
    # for s in sources:
    #     numberOfDownwardPaths[s] = 0
    number_of_initial_paths = allPaths
    number_of_current_paths = allPaths
    listOfCentralNodes = []
    listOfCentralNodes_cents = []
    centralities = calculateCentralities(graph, numberOfUpwardPaths, numberOfDownwardPaths)
    centsDic = {k: v for k, v in centralities}

    orig_cents = {k: v for k, v in centralities}
    topCentralNodeInfo = max(centralities, key=lambda x: x[1])
    allMaxes = [k for k in centralities if k[1] == topCentralNodeInfo[1]]
    allMaxes = [allMaxes[0]]
    # print '-------------', topCentralNodeInfo[1], len(allMaxes)
    while topCentralNodeInfo[1] > 0 and float(number_of_current_paths) / float(
            number_of_initial_paths) > 1 - tau:  # Node with positive centrality exists
        for nodeToBeRemoved in allMaxes:
            nodeToBeRemoved = nodeToBeRemoved[0]
            graph.remove_node(nodeToBeRemoved)
            if nodeToBeRemoved in sources:
                sources.remove(nodeToBeRemoved)
            listOfCentralNodes.append(nodeToBeRemoved)
            listOfCentralNodes_cents.append((topCentralNodeInfo[1], orig_cents[nodeToBeRemoved]))
        numberOfUpwardPaths = {}
        numberOfDownwardPaths = {}
        for node in nx.nodes(graph):
            numberOfUpwardPaths[node] = 0
            numberOfDownwardPaths[node] = 0
        calculateNumberOfUpwardPaths(graph, sources, targets, numberOfUpwardPaths)
        calculateNumberOfDownwardPaths(graph, sources, targets, numberOfDownwardPaths)
        for t in targets:
            numberOfUpwardPaths[t] = 0
        # for s in sources:
        #     numberOfDownwardPaths[s] = 0
        centralities = calculateCentralities(graph, numberOfUpwardPaths, numberOfDownwardPaths)
        topCentralNodeInfo = max(centralities, key=lambda x: x[1])
        allMaxes = [k for k in centralities if k[1] == topCentralNodeInfo[1]]
        allMaxes = [allMaxes[0]]
        allPaths_tmp = 0
        for n in sources:
            allPaths_tmp += numberOfUpwardPaths[n]
        number_of_current_paths = allPaths_tmp
    core = []
    # print str(len(nx.nodes(self.DAGGraph)) - len(targets) - len(sources)) + '\t' + str(allPaths)
    return listOfCentralNodes, listOfCentralNodes_cents, lenNodes, lenAllPaths, lenSources
    # arrayOfStrings = self.getListNodeStrings(listOfCentralNodes)
    # for i in range(len(arrayOfStrings)):
    #     nodeString = arrayOfStrings[i]
    #     core.append(nodeString.rstrip())
    #     print nodeString.rstrip() + '\t' + str(listOfCentralNodes_cents[i]) + '\t' + str(
    #         orig_cents[listOfCentralNodes[i]])
    # return core, listOfCentralNodes_cents

def matrixGenerator(N, alpha, beta):
    M = np.zeros((N, N))
    B = np.zeros(N)
    # NUM_IT = np.power(N,3)
    NUM_IT = 1
    for it in range(NUM_IT):
        tmp_M = np.zeros((N, N))
        for j in range(N):
            B[j] = np.nextafter(np.power(float(j+1),-beta), float('inf'))
        B = B/np.sum(B)
        for i in range(N):
            # if beta == 0:
            #     P = range(N)
            # else:
            P = np.random.choice(np.arange(N), p=B, size=N, replace=False)
            for j in range(N):
                tmp_M[i,P[j]] = np.nextafter(np.power(float(j+1),-alpha), float('inf'))
            tmp_M[i, :] = tmp_M[i,:] / np.sum(tmp_M[i,:])
        M += tmp_M
        # print B
        # print tmp_M
    M /= NUM_IT
    # print M
    # col_sum = np.sum(M,axis=0)
    # print 'sum0', col_sum/np.sum(col_sum)
    # print 'sum1', np.sum(M, axis=1)
    return M

def stringGeneratorFromMatrix(M, lengthArray):
    targetSet = []
    N = np.shape(M)[0]
    abundance = np.sum(M,axis=0)
    abundance = abundance/np.sum(abundance)
    next_char = np.random.choice(np.arange(N), p=abundance, size=1, replace=False)[0]
    for l in lengthArray:
        tmp_target = ''
        for i in range(l):
            tmp_target += str(next_char) + ' '
            next_char = np.random.choice(np.arange(N), p=M[next_char,:], size=1, replace=False)[0]
        targetSet.append(tmp_target)
    return targetSet

def empiricalMatrixGenerator(T, outPath):
    part_freq = defaultdict(int)
    for t in T:
        for p in t.split():
            part_freq[p] += 1
    N = len(part_freq.keys())
    two_gram_matrix = np.zeros((N, N))
    part_to_index = {x[1]:x[0] for x in enumerate(part_freq.keys())}
    for t in T:
        prev_char = ' '
        for p in t.split():
            if prev_char != ' ':
                two_gram_matrix[part_to_index[prev_char]][part_to_index[p]] += 1.
                # two_gram_matrix[part_to_index[p]][part_to_index[prev_char]] += 1.
            prev_char = p
    # for row in range(N):
    #     if np.sum(two_gram_matrix[row, :]) != 0:
    #         two_gram_matrix[row, :] = two_gram_matrix[row, :] / np.sum(two_gram_matrix[row, :])
    f = open(outPath, 'w')
    for row in range(N):
        for col in range(N):
            # print str(two_gram_matrix[row, col]) + '\t',
            f.write(str(two_gram_matrix[row, col]) + '\t')
        # print
        f.write('\n')
    f.close()

def chopByiGEM(T, outPath):
    igem_data = open('igem.txt','r').readlines()
    igem_data = igem_data + igem_data + igem_data
    # print len(igem_data)
    parts = T.split()
    file = open(outPath, 'w')
    while len(parts) > 0:
        tmp_device = ''
        length = len(igem_data.pop(0).split())
        for p in range(length):
            tmp_device += parts.pop(0) + ' '
            if len(parts) == 0:
                break
        file.write(tmp_device + '\n')
    file.close()

def clusteringiGEM(T):
    part_dic = {}
    new_igem = []
    count = 1000
    for t in T:
        tt = t.split()
        tmp_t = ''
        for p in tt:
            if p not in part_dic:
                part_dic[p] = unichr(count)
                count += 1
            tmp_t += part_dic[p]
        new_igem.append(tmp_t)
        if count > 1200:
            break
    from jellyfish import jaro_distance
    def d(coord):
        i, j = coord
        return 1 - jaro_distance(new_igem[i], new_igem[j])
    import numpy as np
    utg = np.triu_indices(len(new_igem), 1)
    dist_utg = np.apply_along_axis(d, 0, utg)
    import scipy.cluster.hierarchy
    from matplotlib import pyplot as plt
    from matplotlib.backends.backend_pdf import PdfPages
    pp = PdfPages('testyyy1.pdf')
    Z = scipy.cluster.hierarchy.linkage(dist_utg)
    plt.figure(figsize=(25, 10))
    plt.title('Hierarchical Clustering Dendrogram')
    plt.xlabel('sample index')
    plt.ylabel('distance')
    scipy.cluster.hierarchy.dendrogram(Z,count_sort=True)
    pp.savefig()
    pp.close()
    plt.show()


if __name__ == "__main__":
    (chFlag, printIntsDAG, quietLog, rFlag, functionFlag, noNewLineFlag, loadDAGFlag) = processParams(sys.argv)


    #########Get iGEM Age-Reuse scatter out of CS and INC full profiles
    # def igemAgeReuseScatter():
    #     from collections import defaultdict
    #     agePath = sys.argv[-2]
    #     targetAgeDic = {}
    #     targetAges = open(agePath, 'r').readlines()
    #     for i in range(len(targetAges)):
    #         targetAgeDic[i+1] = int(targetAges[i].split('\t')[1])
    #     # iGEM fullprofile path
    #     path = sys.argv[-1]
    #     filesTMP = os.listdir(path)[1:]
    #     # filesTMP.remove('.DS_Store')
    #     # print filesTMP
    #     # print len(filesTMP)
    #     # return
    #     # print filesTMP[0]
    #     # print filesTMP[0].split('gram')[-1].split('.txt.txt')[0]
    #     files = sorted(filesTMP, key=lambda x: int(x.split('gram')[-1].split('.txt.txt')[0]))
    #     reuseDic = defaultdict(int)
    #     ageDic = defaultdict(int)
    #     for i in range(len(files)):
    #         sys.stderr.write(str(i) + '\n')
    #     # for i in [3923,3924]:
    #         age = 59+425-targetAgeDic[int(files[i].split('gram')[-1].split('.txt.txt')[0])]
    #         d = DAG(open(sys.argv[-1]+files[i], 'r'), loadDAGFlag, chFlag, noNewLineFlag)
    #         nodeStrs = d.getListNodeStrings(nx.nodes(d.DAGGraph))
    #         for n in nodeStrs:
    #             if n not in ageDic:
    #                 ageDic[n] = age
    #         # print ageDic
    #         if i == len(files) - 1:
    #             stats = getAllNodesCentralities(d.DAGGraph)
    #             for n in stats[2]:
    #                 if stats[1][n] == 1 or stats[2][n] == 1:
    #                     continue
    #                 nodeStr = ''
    #                 for w in d.getNodeString(n).split():
    #                     nodeStr += d.dic[int(w)] + ' '
    #                 reuseDic[nodeStr] = stats[0][n]
    #     ageReuseScatter = [(ageDic[n],reuseDic[n],n) for n in reuseDic if n in ageDic]
    #     for e in sorted(ageReuseScatter, key = lambda x : (x[0],x[1])):
    #         print str(e[0]) + '\t' + str(e[1]) + '\t' + str(e[2])
    # igemAgeReuseScatter()
    #######Run G-Lexis on stream
    # path = 'genSeqs-Final/' + sys.argv[-1]
    # data = open(path, 'r').readlines()
    # tmp_dataset = []
    # prev_len_tmp_dataset = 0
    # data_increment = 0.05
    # for i in range(len(data)):
    #     t = data[i]
    #     tmp_dataset.append(t)
    #     if len(tmp_dataset)-prev_len_tmp_dataset > data_increment * float(len(data)) or i == len(data) - 1:
    #         #run Lexis on tmp_dataset
    #         sys.stderr.write(str((float(len(tmp_dataset))/float(len(data)))*100) + '%\n')
    #         f = open('genSeqs-Final/streamData/'+'tmp-' +sys.argv[-1].split('.')[0]+'-'+str(int((float(len(tmp_dataset))/float(len(data)))*100))+'.txt', 'w')
    #         for tt in tmp_dataset:
    #             f.write(tt)
    #         f.close()
    #         g = DAG(open('genSeqs-Final/streamData/'+'tmp-' +sys.argv[-1].split('.')[0]+'-'+str(int((float(len(tmp_dataset))/float(len(data)))*100))+'.txt', 'r'), loadDAGFlag, chFlag, noNewLineFlag)
    #         g.GLexis(quietLog, rFlag, functionFlag)
    #         # g.printDAG(printIntsDAG)
    #         g.printDAG_toFile(open('genSeqs-Final/DAGs/'+sys.argv[-1].split('.')[0]+'-'+str(int((float(len(tmp_dataset))/float(len(data)))*100))+'.txt','w'), printIntsDAG)
    #         prev_len_tmp_dataset = len(tmp_dataset)

    # clusteringiGEM(open('igem.txt','r').readlines())

    #######Chopping iGEM to 500 Alphbet - Extract Abundance and (most abundant) Digram Frequencies
    # igem_data = open('igem.txt','r').readlines()
    # part_freq = defaultdict(int)
    # digrams = {}
    # extracted_lines = []
    # chop_alph_size = 100
    # count = 1
    # count_up = 50
    # # while len(part_freq.keys()) < chop_alph_size:
    # while count <= count_up:
    #     for l in igem_data:
    #         parts = l.split()
    #         prev_char = ' '
    #         for p in parts:
    #             part_freq[p] += 1
    #             if prev_char != ' ':
    #                 if prev_char not in digrams:
    #                     digrams[prev_char] = defaultdict(int)
    #                 digrams[prev_char][p] += 1
    #             prev_char = p
    #             # if len(part_freq.keys()) == chop_alph_size:
    #             #     break
    #         extracted_lines.append(l)
    #         if len(part_freq.keys()) >= chop_alph_size:
    #             # f = open('igem_' + str(chop_alph_size) + '-' + str(count) + '.txt', 'w')
    #             # for l in extracted_lines:
    #             #     f.write(l)
    #             # f.close()
    #             # for p in part_freq:
    #             #     print str(part_freq[p]) + '\t',
    #             # print
    #             most_abundant = min(part_freq.items(), key=lambda x: x[1])[0]
    #             if most_abundant in digrams:
    #                 for p in digrams[most_abundant]:
    #                     print str(digrams[most_abundant][p]) + '\t',
    #                 print
    #             part_freq = defaultdict(int)
    #             extracted_lines = []
    #             count += 1
    #             if count == count_up:
    #                 break
    # sys.exit()

    #######Plain run of Lexis
    # g = DAG(open(sys.argv[-1], 'r'), loadDAGFlag, chFlag, noNewLineFlag)
    # g.GLexis(quietLog, rFlag, functionFlag)
    # g.printDAG(printIntsDAG)
    # # print nx.dag_longest_path(g.DAGGraph)
    # # print nx.dag_longest_path_length(g.DAGGraph)
    # # print len(nx.nodes(g.DAGGraph))
    # sys.exit()

    # #######Generator matrix
    # iterations = 1
    # mean_cost = 0
    # costs = []
    # for i in range(iterations):
    #     sys.stderr.write(str(i) + '\n')
    #     M = matrixGenerator(int(sys.argv[-3]), float(sys.argv[-2]), float(sys.argv[-1]))
    #     print np.sum(M,0)
    #     T = stringGeneratorFromMatrix(M, [50000])
    #         # freqs = defaultdict(float)
    #         # for ch in T[0]:
    #         #     if ch != ' ':
    #         #         freqs[ch] += 1
    #         # sumFreqs = 0
    #         # for ch in freqs:
    #         #     sumFreqs += freqs[ch]
    #         # for ch in freqs:
    #         #     freqs[ch] /= sumFreqs
    #         # for ch in sorted(list(freqs.items()),key=lambda x: x[1]):
    #         #     print ch[1],
    #         # print
    #     # T = []
    #     # t = ''
    #     # for i in range(23943):
    #     #     next_char = np.random.choice(np.arange(int(sys.argv[-3])), p=[float(1)/int(sys.argv[-3]) for i in range(int(sys.argv[-3]))], size=1, replace=False)[0]
    #     #     t += str(next_char) + ' '
    #     # T.append(t)
    #     f = open('genSeqs3/tmp'+sys.argv[-2]+sys.argv[-1]+'-'+str(i)+'.txt','w')
    #     for t in T:
    #         f.writelines(t)
    #     f.close()
    # #     g = DAG(open('tmp'+sys.argv[-2]+sys.argv[-1]+'.txt', 'r'), loadDAGFlag, chFlag, noNewLineFlag)
    # #     g.GLexis(quietLog, rFlag, functionFlag)
    # #     costs.append(g.DAGCost(CostFunction.EdgeCost))
    # # print np.mean(costs), np.std(costs)
    # # sys.stderr.write(sys.argv[-1].split('gram')[1].split('.txt')[0]+'\n')
    # # print sys.argv[-1].split('gram')[1].split('.txt')[0]
    # # sys.exit()

    #######Generating empirical generator matrix
    # # names = ['tmp'+sys.argv[-2]+sys.argv[-1]+'-0']
    # names = ['tmp00-0']
    # # names = ['igem_100-50']
    # # names = ['igem_50']
    # for name in names:
    #     print name
    #     # chopByiGEM(open('genSeqs3/' + name + '.txt','r').readlines()[0],'genSeqs3/' + name + '-chopped.txt')
    #     empiricalMatrixGenerator(open('/Users/payamsiyari/Desktop/topo_genSeqs/20k/data/' + name + '-chopped.txt', 'r').readlines(), '/Users/payamsiyari/Desktop/topo_genSeqs/20k/data/' + name + '-matrix.txt')
    #     # empiricalMatrixGenerator(open('igem_100/' + name + '.txt', 'r').readlines(),'igem_100/' + name + '-matrix.txt')
    # sys.exit()

    #######Dynamic age in the core
    # node_dic = {}
    # files = [f for f in listdir(sys.argv[-1]) if isfile(join(sys.argv[-1], f)) and not f.startswith('.')]
    # files = sorted(files, key=lambda x : int(x.split('gram')[1].split('.txt')[0]))
    # for f in files:
    #     age = int(join(sys.argv[-1], f).split('gram')[1].split('.txt')[0])
    #     sys.stderr.write(str(age) + '\n')
    #     g = DAG(open(join(sys.argv[-1], f),'r'), loadDAGFlag, chFlag, noNewLineFlag)
    #     centralNodes = g.greedyCoreID_ByTau_knee(age, 1, node_dic, 0.75)
    #     # centralNodes = g.greedyCoreID_ByTau(1)
    #     # print len(centralNodes[0])
    # for node, k in sorted(node_dic.iteritems(), key=lambda x: x[1]['age_index']):
    #     print str(node) + '\t' + str(k['age_index']) + '\t' + str(k['core_index']) + '\t' + str(k['core_count'])

    #######Plain central nodes extraction
    # g = DAG(open(sys.argv[-1], 'r'), loadDAGFlag, chFlag, noNewLineFlag)
    # centralNodes = g.greedyCoreID_ByTau(0.99)
    # print centralNodes[1]
    # # print len(centralNodes[0])

    #######DAG Pruning
    # import pickle
    # import os
    # # num_rand = int(sys.argv[-2])
    # NUMBER_OF_RANDOMIZATIONS = 10
    # fileName = sys.argv[-1].split('/')[-1].split('.')[0]
    # randFolder = '/'.join(sys.argv[-1].split('/')[:-2]) + '/' + fileName + '-rand/'
    # nodes_dic = pickle.load(open(randFolder + fileName + '-nodes-dic' + str(NUMBER_OF_RANDOMIZATIONS) + ".p", "rb"))
    # g = DAG(open(sys.argv[-1], 'r'), loadDAGFlag, chFlag, noNewLineFlag)
    # # for q in [0.001]:
    # prunStats = []
    # prunStats.append(['Orig',len(nx.nodes(g.DAGGraph)),len(nx.edges(g.DAGGraph)),len([x for x in nx.nodes(g.DAGGraph) if g.DAGGraph.in_degree(x) == 0]),len(nx.nodes(g.DAGGraph))-len([x for x in nx.nodes(g.DAGGraph) if g.DAGGraph.in_degree(x) == 0])])
    # for q in [0.001, 0.01] + list(np.arange(0.1, 1, 0.1)) + [0.95,0.99,0.999]:
    #     # g.GLexis(quietLog, rFlag, functionFlag)
    #     # g.printDAG(printIntsDAG)
    #     d = pruneDAG_withNodeDic(nodes_dic, NUMBER_OF_RANDOMIZATIONS, g, q)
    #     # _, d = pruneDAG(open(sys.argv[-3],'r'),sys.argv[-1], sys.argv[-2], g, 0.001, 10)
    #     nodes = nx.nodes(d.DAGGraph)
    #     nodesStrings = d.getListNodeStrings(nodes)
    #     labels = {nodes[i]:nodesStrings[i] for i in range(len(nodes))}
    #     nx.relabel_nodes(d.DAGGraph, labels, copy=False)
    #     nx.write_gml(d.DAGGraph, randFolder + fileName + '-prun' + str(q) + '.gml')
    #     printNodeStats(d.DAGGraph, randFolder + fileName + '-prun' + str(q) + '-stats.txt')
    #     prunStats.append([q,
    #                   len(nx.nodes(d.DAGGraph)), len(nx.edges(d.DAGGraph)),
    #                   len([x for x in nx.nodes(d.DAGGraph) if d.DAGGraph.in_degree(x) == 0]),
    #                   len(nx.nodes(d.DAGGraph)) - len([x for x in nx.nodes(d.DAGGraph) if d.DAGGraph.in_degree(x) == 0]),
    #                   len(nx.nodes(g.DAGGraph))-len(nx.nodes(d.DAGGraph)),
    #                   float(len(nx.nodes(g.DAGGraph)) - len(nx.nodes(d.DAGGraph)))/len(nx.nodes(g.DAGGraph)),
    #                   len(nx.nodes(g.DAGGraph)) - len(nx.nodes(d.DAGGraph))-len([x for x in nx.nodes(g.DAGGraph) if g.DAGGraph.in_degree(x) == 0])
    #                   ])
    #     pStats = open(randFolder + fileName + '-prun-stats.txt', 'w')
    #     for l in prunStats:
    #         for e in l:
    #             pStats.write(str(e) + '\t')
    #         pStats.write('\n')
    #     pStats.close()

    #######Plain centrality and contribution
    # gr = nx.read_gml(sys.argv[-1])
    # fileName = sys.argv[-1].split('/')[-1].split('.')[0]
    # folder = '/'.join(sys.argv[-1].split('/')[:-1]) + '/'
    # centralNodes, cents, lenNodes, lenAllPaths, lenSources = coreID_byTau(gr.copy(), 1)
    # lenAllPaths2 = 0
    # for i in range(len(centralNodes)):
    #     lenAllPaths2 += cents[i][0]
    # f = open(folder + fileName + '-coreID.txt', 'w')
    # f.write('\t'.join(map(str,
    #                       [lenNodes, lenAllPaths, lenAllPaths2, lenSources])
    #                   )+ '\n')
    # sumPaths = 0
    # for i in range(len(centralNodes)):
    #     # print str(centralNodes[i]) + '\t' + str(cents[i][0]) + '\t' + str(cents[i][1])
    #     sumPaths += cents[i][0]
    #     # f.write(str(centralNodes[i]) + '\t' + str(cents[i][0]) + '\t' + str(cents[i][1]) + '\t' + str(float(sumPaths)/lenAllPaths) + '\t' + str(float(sumPaths)/lenAllPaths2) + '\t' + str(1-float((i+1))/lenSources) +'\n')
    #     f.write('\t'.join(map(str,
    #                           [centralNodes[i],
    #                            cents[i][0],
    #                            cents[i][1],
    #                            float(sumPaths) / lenAllPaths,
    #                            float(sumPaths) / lenAllPaths2,
    #                            1 - (float((i + 1)) / float(lenSources))])
    #                       ) + '\n')
    # f.close()


    #######Static stats of nodes
    # g = DAG(open(sys.argv[-2], 'r'), loadDAGFlag, chFlag, noNewLineFlag)
    # nodes = nx.nodes(g.DAGGraph)
    # nodesStrings = g.getListNodeStrings(nodes)
    # labels = {nodes[i]: nodesStrings[i] for i in range(len(nodes))}
    # nx.relabel_nodes(g.DAGGraph, labels, copy=False)
    # # gr = nx.read_gml(sys.argv[-1])
    # # gr_nodes = set(nx.nodes(gr))
    # graph = g.DAGGraph
    #
    # # printNodeStats2(g.DAGGraph, gr_nodes)
    # printNodeStats(graph, sys.argv[-1])

    # create_nodes_prob_dic(open(sys.argv[-3], 'r'), sys.argv[-2], int(sys.argv[-1]))

    # g = DAG(open(sys.argv[-1], 'r'), loadDAGFlag, chFlag, noNewLineFlag)
    # listProbs(g, int(sys.argv[-2]))

    # calc_rank_corr(sys.argv[-2], sys.argv[-1])

    # calc_max_prob_diff(sys.argv[-2], sys.argv[-1])

    # rand_input_q_analysis(sys.argv[-3], sys.argv[-2], int(sys.argv[-1]))

    # g = nx.read_gml(sys.argv[-1])
    # gr = nx.read_gml(sys.argv[-2])
    # g_nodes = set(nx.nodes(g))
    # gr_nodes = set(nx.nodes(gr))
    # print len(g_nodes)
    # print len(gr_nodes)
    # for node in g_nodes.difference(gr_nodes):
    #     if len(node.split()) > 1:
    #         print node

    # printNodeStats(gr)
    # nx.relabel_nodes(d.DAGGraph, labels, copy=False)
    # for n in centralNodes:
    #     print labels[n]

    #If desired to see the central nodes, please uncomment the lines below
    # centralNodes = g.greedyCoreID_ByTau(1)
    # print
    # print 'Central Nodes:'
    # for i in range(len(centralNodes)):
    #     print centralNodes[i]

    # g.calcPaths()

    # numData = sys.argv[-1].split('gram')[1].split('.txt.txt')[0]
    # print numData
    # print structSimTest('/Users/payamsiyari/Desktop/inc/cs-fullProfile/clean-slate full profile/gram' + str(numData) + '.txt', sys.argv[-1])

    # from collections import Counter
    # dic = Counter()
    # f=open(sys.argv[-1],'r').readlines()
    # for l in f:
    #     for c in l.split():
    #         dic[c] += 1
    # for c in sorted([(c,dic[c]) for c in dic],key=lambda x:x[1], reverse = True):
    #     # print str(c[0]) + '\t' + str(c[1])
    #     print str(c[1])

    g = DAG(open(sys.argv[-1], 'r'), loadDAGFlag, chFlag, noNewLineFlag)
    # print g.dic
    # sys.exit()
    for n in sorted(g.DAGStrings.keys()):
        if n == 0:
            continue
        s = ''.join(g.DAGStrings[n])
        dic_s = ''
        # print '-------]]]]]'
        # print n, g.DAGStrings[n]
        # print '-------[[[[['
        # print s
        for c in s.split():
            dic_s += g.dic[int(c)] + ' '
        if n != 0 and len(s.split()) > 1:
            pass
            # print n, '=======', dic_s
            print dic_s
    sys.exit()
    nodes = nx.nodes(g.DAGGraph)
    # print list(nodes), 'xxx'
    arrayOfStrings = g.getListNodeStrings(list(nodes))[1:]
    s0 =  sorted(arrayOfStrings,key=lambda x:(len(x.split()),x))
    total_length = 0
    lengths = []
    for x in s0:
        if len(x.split()) > 1:
            # total_length += 1
            lengths.append(len(x.split()))
        # print x
    print '{}\t{}\t{}\t{}'.format(min(lengths), np.median(lengths), np.mean(lengths), max(lengths))

    # g = DAG(open(sys.argv[-1], 'r'), loadDAGFlag, chFlag, noNewLineFlag)
    # nodes = nx.nodes(g.DAGGraph)
    # # print list(nodes), 'xxx'
    # arrayOfStrings = g.getListNodeStrings(list(nodes))[1:]
    # s1 = set(sorted(arrayOfStrings, key=lambda x: (len(x.split()), x)))
    #
    # print float(len(s1.intersection(s0)))/float(len(s1.union(s0)))


    # sources = []
    # targets = []
    # for node in nx.nodes(g.DAGGraph):
    #     if g.DAGGraph.in_degree(node) == 0:
    #         sources.append(node)
    #     if g.DAGGraph.out_degree(node) == 0:
    #         targets.append(node)
    # # tendril_paths = 0
    # # for s in sources:
    # #     for t in targets:
    # #         ps = nx.all_simple_paths(g.DAGGraph, source=s, target=t)
    # #         plens = map(len,ps)
    # #         if len(plens) > 0:
    # #             tendril_paths += sum([i==min(plens) for i in plens])
    # # print 'tau', float(200000-tendril_paths)/200000
    # centralNodes = g.greedyCoreID_ByTau(float(200000-tendril_paths)/200000)
    # # print centralNodes[1]
    # # print len(centralNodes[0])
    # psum = 0
    # pnum = 0
    # num_all_paths = 0
    # listOfSources = []
    # for s in sources:
    #     for t in targets:
    #         ps = nx.all_simple_paths(g.DAGGraph, source=s, target=t)
    #         for p in ps:
    #             psum += len(p)-1
    #             pnum += 1
    #         listOfSources.append((s, pnum))
    #         num_all_paths += pnum
    #         # pnum = 0
    # # print pnum
    # # print psum
    # print str(len(nx.nodes(g.DAGGraph))) + '\t' + str(float(psum)/pnum)
    # sys.exit()
    # listOfSources = sorted(listOfSources, key=lambda x : x[1], reverse=True)
    # perc = 0
    # coreSize = 0
    # coreFlat75 = 0
    # coreFlat85 = 0
    # coreFlat95 = 0
    # # LEN = int(sys.argv[-2])
    # LEN = num_all_paths
    # for s,ps in listOfSources:
    #     perc += float(ps)/LEN
    #     # print str(s) + '\t' + str(ps)
    #     coreSize += 1
    #     if perc > .9 and coreFlat95 == 0:
    #         coreFlat95 = coreSize
    #     elif perc > .8 and coreFlat85 == 0:
    #         coreFlat85 = coreSize
    #     elif perc > .7 and coreFlat75 == 0:
    #         coreFlat75 = coreSize
    # # print
    # print str(coreFlat75) + '\t' +str(coreFlat85) + '\t' +str(coreFlat95)