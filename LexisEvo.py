# -*- coding: utf-8 -*-
"""
Created on Mon Sep  7 11:50:57 2015

@author: payamsiyari
"""
#NOTE: The code for integration of icremental design is written in the method "idea3_Fixed_TGM4".
#The rest of the code is here for historical reasons. I will make this file cleaner in future.

from __future__ import division
import os
import random
from bisect import bisect_left
import fileinput
import sys
import getopt
import operator
import math
import time
import subprocess
import copy
import networkx as nx
import itertools

prev_concats = 0
prev_edges = 0
prev_cost = 0

# prev_concats = 447
# prev_edges = 773
# prev_cost = 1099

class SequenceType:
    Character, Integer, SpaceSeparated = ('c', 'i', 's')
class CostFunction:
    ConcatenationCost, RuleCost, EdgeCost = ('c', 'r', 'e')
class RepeatClass:
    Repeat, MaximalRepeat, LargestMaximalRepeat, SuperMaximalRepeat = ('r', 'mr', 'lmr', 'smr')
class PairSearchMethod:
    ConstantLengthSearch, ExhausivePairSearch, GreedyPairSearch = ('c', 'e', 'g')
class LogFlag:
    ConcatenationCostLog, RuleCostLog = range(2)

class Grammar(object):
    # TMP_OUTPUT_FILE = 'tmpOutput.txt'
    # TMP_INPUT_FILE = 'tmpInput.txt'

    def __init__(self, inputFile, loadGrammarFlag, gap, chFlag = SequenceType.Character, noNewLineFlag = True):
        self.__preprocessedInput = []  # Original input as a sequence of integers
        self.dic = []  # Dictionary for correspondence of integers to original chars (only when charSeq = 'c','s')

        self.__inputName = ''
        self.__concatenatedGrammar = []  # Concatenated grammar rules with seperatorInts
        self.__concatenatedNTs = []  # For each grammar rule, alongside the concatenated grammar
        self.__separatorInts = set([])  # Used for seperating grammar rules in the concatenatedGrammar
        self.__separatorIntsIndices = set([])  # Indices of separatorInts in the concatenated grammar
        self.nextNewInt = 0  # Used for storing ints of repeat non-terminals and separators in odd numbers
        self.__nextNewContextInt = 0  # Used for storing ints for context non-terminals in even numbers
        self.__ctxNtSet = set([])  # Set of context non-terminals (i.e. inside rules), used for better printing

        self.__MAX_LENGTH = 100  # Used for setting upper bound on fixed gap size

        self.__fixedGap = False  # Indicates wether contexts have a fixed gap or not
        self.__fixedGapSavedCost = 0  # Used to correct the grammar cost when __fixedGap==True

        self.__quietLog = False  # if true, disables logging
        self.__numberOfTimesRepeatPicked = 0
        self.__numberOfTimesPairPicked = 0
        self.__iterations = 0
        # sys.stderr.write(str(self.__concatenatedGrammar) + 'gram00\n')
        self.__MAX_LENGTH = gap
        if loadGrammarFlag == 'grammar':
            self.__initFromGrammar(inputFile)
        elif loadGrammarFlag == 'file':
            self.__initFromStringsFile(inputFile, chFlag, noNewLineFlag)
        elif loadGrammarFlag == 'string':
            self.__initFromStrings(inputFile, chFlag, noNewLineFlag)
    #Initializes (an unoptimized) grammar from inputFile. charSeq tells if inputFile is a char sequence, int sequence or space-separated sequence
    def __initFromStringsFile(self, inputFile, chFlag = SequenceType.Character, noNewLineFlag = True):
        self.__inputName = inputFile.name.split('.')[0]
        self.__preprocessedInput = []  # Original input as a sequence of integers
        self.dic = []  # Dictionary for correspondence of integers to original chars (only when charSeq = 'c','s')

        self.__concatenatedGrammar = []  # Concatenated grammar rules with seperatorInts
        self.__concatenatedNTs = []  # For each grammar rule, alongside the concatenated grammar
        self.__separatorInts = set([])  # Used for seperating grammar rules in the concatenatedGrammar
        self.__separatorIntsIndices = set([])  # Indices of separatorInts in the concatenated grammar
        self.nextNewInt = 0  # Used for storing ints of repeat non-terminals and separators in odd numbers

        # self.TMP_OUTPUT_FILE = self.__inputName + '-' + self.TMP_OUTPUT_FILE
        # self.TMP_INPUT_FILE = self.__inputName + '-' + self.TMP_INPUT_FILE
        (self.__preprocessedInput, self.dic) = self.__preprocessInput(inputFile, charSeq = chFlag, noNewLineFlag = noNewLineFlag)
        allLetters = set(map(int,self.__preprocessedInput.split()))
        #Setting odd and even values for nextNewInt and __nextNewContextInt
        self.nextNewInt = max(allLetters)+1
        if self.nextNewInt % 2 == 0:
            self.__nextNewContextInt = self.nextNewInt
            self.nextNewInt += 1
        else:
            self.__nextNewContextInt = self.nextNewInt + 1
        #Initializing the concatenated grammar
        for line in self.__preprocessedInput.split('\n'):
            line = line.rstrip('\n')
            self.__concatenatedGrammar.extend(map(int,line.split()))
            self.__concatenatedGrammar.append(self.nextNewInt)
            self.__concatenatedNTs.extend(0 for j in range(len(map(int,line.split()))))
            self.__concatenatedNTs.append(self.nextNewInt)
            self.__separatorInts.add(self.nextNewInt)
            self.__separatorIntsIndices.add(len(self.__concatenatedGrammar)-1)
            self.nextNewInt += 2
            # if len(line.split()) > self.__MAX_LENGTH:
            #     self.__MAX_LENGTH = len(line.split())
        self.nextNewInt += 2

    def __initFromStrings(self, inputFile, chFlag=SequenceType.Character, noNewLineFlag=True):
        # self.__inputName = inputFile.name.split('.')[0]
        # self.TMP_OUTPUT_FILE = self.__inputName + '-' + self.TMP_OUTPUT_FILE
        # self.TMP_INPUT_FILE = self.__inputName + '-' + self.TMP_INPUT_FILE
        (self.__preprocessedInput, self.dic) = self.__preprocessInputStrings(inputFile, charSeq=chFlag,
                                                                      noNewLineFlag=noNewLineFlag)
        # sys.stderr.write(str(self.__preprocessedInput) + 'prep\n')
        # sys.stderr.write(str(self.__preprocessedInput.split('\n')) + 'prep2\n')
        allLetters = set(map(int, self.__preprocessedInput.split()))
        # Setting odd and even values for nextNewInt and __nextNewContextInt
        self.nextNewInt = max(allLetters) + 1
        if self.nextNewInt % 2 == 0:
            self.__nextNewContextInt = self.nextNewInt
            self.nextNewInt += 1
        else:
            self.__nextNewContextInt = self.nextNewInt + 1
        # Initializing the concatenated grammar
        for line in self.__preprocessedInput.split('\n'):
            sys.stderr.write(str(line) + 'line\n')
            line = line.rstrip('\n')
            # sys.stderr.write(str(self.__concatenatedGrammar) + 'gram0\n')
            # sys.stderr.write(str(self.__concatenatedNTs) + 'nts0\n')
            self.__concatenatedGrammar.extend(map(int, line.split()))
            self.__concatenatedGrammar.append(self.nextNewInt)
            # sys.stderr.write(str(self.__concatenatedGrammar) + 'gram1\n')
            # sys.stderr.write(str(self.__concatenatedNTs) + 'nts1\n')
            self.__concatenatedNTs.extend(0 for j in range(len(map(int, line.split()))))
            self.__concatenatedNTs.append(self.nextNewInt)
            self.__separatorInts.add(self.nextNewInt)
            self.__separatorIntsIndices.add(len(self.__concatenatedGrammar) - 1)
            self.nextNewInt += 2
            # sys.stderr.write(str(self.__concatenatedGrammar) + 'gram\n')
            # sys.stderr.write(str(self.__concatenatedNTs) + 'nts\n')
            # if len(line.split()) > self.__MAX_LENGTH:
            #     self.__MAX_LENGTH = len(line.split())
        # sys.stderr.write(str(self.__concatenatedGrammar) + 'gram\n')
        # sys.stderr.write(str(self.__concatenatedNTs) + 'nts\n')
    #Loads the grammar from an external file
    def __initFromGrammar(self, inputFile):
        firstLine  = True
        secondLine = True
        grammar = {}
        wordDict = {}
        counterDict = {}
        counter = 0
        textFile = inputFile.read().splitlines()
        # textFile = textFile.replace('   ',' SPACECHAR ')
        # textFile = textFile.replace('  \n',' SPACECHAR\n')
        # print textFile
        tmpRule = []
        for line in textFile:
            # if line == '':
            #     continue
            if firstLine:
                firstLine = False
                continue
            if secondLine:
                secondLine = False
                continue

            if len(line.split(' ->  ')) < 2:
                # tmpRule = ['\n'] + line.split(' ')
                tmpRule = line.split(' ')
                newRule = []
                for w in tmpRule:
                    if w == '':
                        continue
                    if w not in counterDict:
                        wordDict[counter] = w
                        counterDict[w] = counter
                        counter += 1
                    newRule.append(counterDict[w])
                grammar[newNt] += newRule
                continue
            else:
                nt = line.split(' ->  ')[0]
            if counter % 2 == 0:
                if counter != 0:
                    counter += 1
            if nt not in counterDict:
                wordDict[counter] = nt
                counterDict[nt] = counter
                counter += 1
            newNt = counterDict[nt]
            rule = line.split(' ->  ')[1].split(' ')
            newRule = []
            for w in rule:
                if w == '':
                        continue
                if w not in counterDict:
                    wordDict[counter] = w
                    counterDict[w] = counter
                    counter += 1
                newRule.append(counterDict[w])
            if newNt == 0:
                if 0 in grammar:
                    grammar[newNt].append(newRule)
                else:
                    grammar[newNt] = [newRule]
            else:
                grammar[newNt] = newRule
        # print grammar
        self.dic = wordDict
        self.nextNewInt = counter
        if self.nextNewInt % 2 == 0:
            self.__nextNewContextInt = self.nextNewInt
            self.nextNewInt += 1
        else:
            self.__nextNewContextInt = self.nextNewInt + 1
        for nt in sorted(grammar.keys()):
            if nt == 0:
                for rule in grammar[nt]:
                    self.__concatenatedGrammar.extend(rule)
                    self.__concatenatedGrammar.append(self.nextNewInt)
                    self.__concatenatedNTs.extend(nt for j in range(len(rule)))
                    self.__concatenatedNTs.append(self.nextNewInt)
                    self.__separatorInts.add(self.nextNewInt)
                    self.__separatorIntsIndices.add(len(self.__concatenatedGrammar) - 1)
                    self.nextNewInt += 2
            else:
                self.__concatenatedGrammar.extend(grammar[nt])
                self.__concatenatedGrammar.append(self.nextNewInt)
                self.__concatenatedNTs.extend(nt for j in range(len(grammar[nt])))
                self.__concatenatedNTs.append(self.nextNewInt)
                self.__separatorInts.add(self.nextNewInt)
                self.__separatorIntsIndices.add(len(self.__concatenatedGrammar)-1)
                self.nextNewInt += 2
        # print self.__concatenatedGrammar
        # print len(self.__concatenatedGrammar)
        # print self.grammarCost(CostFunction.EdgeCost)
        # sys.exit()
    # Loads the grammar from a grammar dictionary
    def initFromGrammarDic(self, grammar, dic):
        # print 'payam'
        # print grammar
        self.dic = dic
        counter = 0
        for nt in grammar:
            if counter <= nt:
                counter = nt + 1
            for rhs in grammar[nt]:
                for c in rhs:
                    if counter <= c:
                        counter = c + 1
        self.nextNewInt = counter
        if self.nextNewInt % 2 == 0:
            self.__nextNewContextInt = self.nextNewInt
            self.nextNewInt += 1
        else:
            self.__nextNewContextInt = self.nextNewInt + 1
        self.__concatenatedGrammar = []
        self.__concatenatedNTs = []
        self.__separatorInts = set([])
        self.__separatorIntsIndices = set([])
        for nt in grammar:
            for rhs in grammar[nt]:
                self.__concatenatedGrammar.extend(rhs)
                self.__concatenatedGrammar.append(self.nextNewInt)
                self.__concatenatedNTs.extend(nt for j in range(len(rhs)))
                self.__concatenatedNTs.append(self.nextNewInt)
                self.__separatorInts.add(self.nextNewInt)
                self.__separatorIntsIndices.add(len(self.__concatenatedGrammar) - 1)
                self.nextNewInt += 2
        # print 'aaaaaaaa'
        # print grammar
        # print 'bbbbb'
        # print self.__concatenatedGrammar
        # print self.__concatenatedNTs
    #...........Main Algorithm........
    def gSGP(self, pairingEnabled, fixedGap, quiet, normalRepeatType, ctxRepeatType, costFunction, pairSearchMethod):
        self.__fixedGap = fixedGap
        self.__quietLog = quiet
        odd = False
        pairingEnabled = False
        firstRoundFinished = False
        while True: #Main IRR loop
            #Logging Grammar Cost
            self.__logViaFlag(LogFlag.ConcatenationCostLog)
            self.__logViaFlag(LogFlag.RuleCostLog)

            (maximumRepeatGainValue, selectedRepeatOccs) = self.__retreiveMaximumGainRepeat(normalRepeatType, CostFunction.EdgeCost)
            if maximumRepeatGainValue >= 0:
                self.__logMessage('maxR ' + str(maximumRepeatGainValue) + ' : ' + str(self.__concatenatedGrammar[
                                                                                      selectedRepeatOccs[1][0]:
                                                                                      selectedRepeatOccs[1][0] +
                                                                                      selectedRepeatOccs[0]]) + '\n')
                self.__replaceRepeat(selectedRepeatOccs)  # Replacing the chosen repeat
                self.__numberOfTimesRepeatPicked += 1
                self.__iterations += 1
            if maximumRepeatGainValue == -1:
                break

        self.__logMessage('---------------')
        self.__logMessage('Number of Times Iterations: ' + str(self.__iterations))
        self.__logMessage('Number of Times Picked Repeats: ' + str(self.__numberOfTimesRepeatPicked))
        self.__logMessage('Number of Times Picked Pairs: ' + str(self.__numberOfTimesPairPicked))

    #Returns the cost of the grammar according to the selected costFunction
    def grammarCost(self, costFunction):
        if costFunction == CostFunction.ConcatenationCost:
            if not self.__fixedGap:
                return len(self.__concatenatedGrammar)-2*len(self.__separatorInts)
            else:
                return len(self.__concatenatedGrammar)-2*len(self.__separatorInts)+self.__numberOfTimesPairPicked
        if costFunction == CostFunction.RuleCost:
            if not self.__fixedGap:
                return len(self.__concatenatedGrammar)
            else:
                return len(self.__concatenatedGrammar)-self.__fixedGapSavedCost
        if costFunction == CostFunction.EdgeCost:
            if not self.__fixedGap:
                return len(self.__concatenatedGrammar) - len(self.__separatorInts)
            else:
                return len(self.__concatenatedGrammar) - len(self.__separatorInts) + self.__numberOfTimesPairPicked

    def customPrint(self, string):
        nt = string.split('--')[0]
        string = string.split('--')[1]
        array = map(int,string.split(', '))
        print  nt, '-> ',
        for i in range(len(array)):
            print  self.dic[array[i]],
    #...........Printing Functions........
    #Prints the grammar, optionally in integer form if intGrammarPrint==True
    def printGrammarWithOffsetToNTs(self, intGrammarPrint, offset, inputDic = None):
        # print self.__concatenatedGrammar
        # print len(self.__concatenatedGrammar)
        # print self.__separatorInts
        # print len(self.__separatorInts)

        # print 'GrammarCost(Concats):' , str(prev_concats + self.grammarCost(CostFunction.ConcatenationCost))
        # f = open('output.txt','a')
        # f.write('GrammarCost(Edges): ' + str(prev_edges + self.grammarCost(CostFunction.EdgeCost)) + '\n')
        # f.close()
        # print 'GrammarCost(Edges):', str(prev_edges + self.grammarCost(CostFunction.EdgeCost))
        # print 'GrammarCost:' , str(prev_cost + self.grammarCost(CostFunction.RuleCost))
        # print
        # return
        output = open('tmpGram.txt','a')
        Grammar = self.__concatenatedGrammar
        NTs = self.__concatenatedNTs
        separatorInts = self.__separatorInts
        # if inputDic == None:
        Dic = self.dic
        # else:
        #     Dic = inputDic
        rules = {}
        ntDic = {}
        counter = 1
        NTsSorted = set([])
        # print '------------for debugging begin'
        # print Dic
        # print Grammar
        # print NTs
        # print '------------for debugging end'
        for i in range(len(NTs)):
            if NTs[i] not in ntDic and NTs[i] not in separatorInts:
                NTsSorted.add(NTs[i])
                # ntDic[NTs[i]] = 'N'+str(counter)
                # rules['N'+str(counter)] = ''
                if NTs[i] == 0:
                    ntDic[NTs[i]] = 'N' + str(NTs[i])
                    rules['N' + str(NTs[i])] = ''
                else:
                    ntDic[NTs[i]] = 'N'+str(NTs[i]+offset)
                    rules['N'+str(NTs[i]+offset)] = ''
                counter += 1
        for i in range(len(Grammar)):
            if Grammar[i] not in NTsSorted:
                if Grammar[i] not in separatorInts:
                    if not intGrammarPrint:
                        try:
                            if inputDic == None:
                                rules[ntDic[NTs[i]]] = rules[ntDic[NTs[i]]] + ' ' + Dic[Grammar[i]]
                            else:
                                if Grammar[i] not in inputDic:
                                    rules[ntDic[NTs[i]]] = rules[ntDic[NTs[i]]] + ' ' + Dic[Grammar[i]]
                                else:
                                    rules[ntDic[NTs[i]]] = rules[ntDic[NTs[i]]] + ' ' + inputDic[Grammar[i]]
                        except:
                            print Grammar[i], NTs[i]
                            raise
                    else:
                        rules[ntDic[NTs[i]]] = rules[ntDic[NTs[i]]] + ' ' + str(Grammar[i])
                else:
                    rules[ntDic[NTs[i-1]]] = rules[ntDic[NTs[i-1]]] + ' ||'
            else:
                if not intGrammarPrint:
                    try:
                        rules[ntDic[NTs[i]]] = rules[ntDic[NTs[i]]] + ' ' + ntDic[Grammar[i]]
                    except:
                            print Grammar[i], NTs[i]
                            raise
                else:
                    rules[ntDic[NTs[i]]] = rules[ntDic[NTs[i]]] + ' ' + ntDic[Grammar[i]]
        NTsSorted = sorted(list(NTsSorted))
        ruleCounter = 0
        for nt in NTsSorted:
            if nt not in self.__ctxNtSet:
                if intGrammarPrint:
                    subrules = rules[ntDic[nt]].rstrip(' ||').split(' ||')
                    for s in subrules:
                        # print ntDic[nt] + ' ->' + s
                        output.write(str(ntDic[nt]) + ' -> ' + str(s) + '\n')
                else:
                    subrules = rules[ntDic[nt]].rstrip(' ||').split(' ||')
                    for s in subrules:
                        # print ntDic[nt] + ' -> ' + s
                        output.write(str(ntDic[nt]) + ' -> ' + str(s) + '\n')
            ruleCounter += 1
            if ruleCounter == 1:
                    for nt in sorted(list(self.__ctxNtSet)):
                        if intGrammarPrint:
                            subrules = rules[ntDic[nt]].rstrip(' ||').split(' ||')
                            for s in subrules:
                                # print ntDic[nt] + ' ->' + s
                                output.write(str(ntDic[nt]) + ' -> ' + str(s) + '\n')
                        else:
                            subrules = rules[ntDic[nt]].rstrip(' ||').split(' ||')
                            for s in subrules:
                                # print ntDic[nt] + ' -> ' + s
                                output.write(str(ntDic[nt]) + ' -> ' + str(s) + '\n')
        #printFromDic(listOfIndices, Dic):
        #''.join([Dic[ch] for ch in listOfIndices])
        output.close()

    def printGrammar(self, intGrammarPrint):
        # print self.__concatenatedGrammar
        # print len(self.__concatenatedGrammar)
        # print self.__separatorInts
        # print len(self.__separatorInts)

        print 'GrammarCost(Concats):', str(
            prev_concats + self.grammarCost(CostFunction.ConcatenationCost))
        # f = open('output.txt','a')
        # f.write('GrammarCost(Edges): ' + str(prev_edges + self.grammarCost(CostFunction.EdgeCost)) + '\n')
        # f.close()
        print 'GrammarCost(Edges):', str(prev_edges + self.grammarCost(CostFunction.EdgeCost))
        # print 'GrammarCost:' , str(prev_cost + self.grammarCost(CostFunction.RuleCost))
        # print
        # return
        Grammar = self.__concatenatedGrammar
        NTs = self.__concatenatedNTs
        separatorInts = self.__separatorInts
        Dic = self.dic
        rules = {}
        ntDic = {}
        counter = 1
        NTsSorted = set([])
        # print '------------for debugging begin'
        # print Dic
        # print Grammar
        # print NTs
        # print '------------for debugging end'
        for i in range(len(NTs)):
            if NTs[i] not in ntDic and NTs[i] not in separatorInts:
                NTsSorted.add(NTs[i])
                # ntDic[NTs[i]] = 'N'+str(counter)
                # rules['N'+str(counter)] = ''
                ntDic[NTs[i]] = 'N' + str(NTs[i])
                rules['N' + str(NTs[i])] = ''
                counter += 1
        for i in range(len(Grammar)):
            if Grammar[i] not in NTsSorted:
                if Grammar[i] not in separatorInts:
                    if not intGrammarPrint:
                        try:
                            rules[ntDic[NTs[i]]] = rules[ntDic[NTs[i]]] + ' ' + Dic[Grammar[i]]
                        except KeyError:
                            print Grammar[i], NTs[i]
                            print Dic
                            print Grammar
                            print NTs
                            raise
                    else:
                        rules[ntDic[NTs[i]]] = rules[ntDic[NTs[i]]] + ' ' + str(Grammar[i])
                else:
                    rules[ntDic[NTs[i - 1]]] = rules[ntDic[NTs[i - 1]]] + ' ||'
            else:
                if not intGrammarPrint:
                    try:
                        rules[ntDic[NTs[i]]] = rules[ntDic[NTs[i]]] + ' ' + ntDic[Grammar[i]]
                    except:
                        print Grammar[i], NTs[i]
                        raise
                else:
                    rules[ntDic[NTs[i]]] = rules[ntDic[NTs[i]]] + ' ' + ntDic[Grammar[i]]
        NTsSorted = sorted(list(NTsSorted))
        ruleCounter = 0
        for nt in NTsSorted:
            if nt not in self.__ctxNtSet:
                if intGrammarPrint:
                    subrules = rules[ntDic[nt]].rstrip(' ||').split(' ||')
                    for s in subrules:
                        print ntDic[nt] + ' ->' + s
                else:
                    subrules = rules[ntDic[nt]].rstrip(' ||').split(' ||')
                    for s in subrules:
                        print ntDic[nt] + ' -> ' + s
            ruleCounter += 1
            if ruleCounter == 1:
                for nt in sorted(list(self.__ctxNtSet)):
                    if intGrammarPrint:
                        subrules = rules[ntDic[nt]].rstrip(' ||').split(' ||')
                        for s in subrules:
                            print ntDic[nt] + ' ->' + s
                    else:
                        subrules = rules[ntDic[nt]].rstrip(' ||').split(' ||')
                        for s in subrules:
                            print ntDic[nt] + ' -> ' + s
                            # printFromDic(listOfIndices, Dic):
                            # ''.join([Dic[ch] for ch in listOfIndices])

    def printGrammarToFile(self, filename, intGrammarPrint):
        # print self.__concatenatedGrammar
        # print len(self.__concatenatedGrammar)
        # print self.__separatorInts
        # print len(self.__separatorInts)
        # outputFile = open('/Users/payamsiyari/Desktop/1/'+filename+'.txt', 'w')
        outputFile = open(filename, 'w')
        outputFile.write('GrammarCost(Concats): ' + str(prev_concats + self.grammarCost(CostFunction.ConcatenationCost))+'\n')
        # f = open('output.txt','a')
        # f.write('GrammarCost(Edges): ' + str(prev_edges + self.grammarCost(CostFunction.EdgeCost)) + '\n')
        # f.close()
        outputFile.write('GrammarCost(Edges): ' + str(prev_edges + self.grammarCost(CostFunction.EdgeCost))+'\n')
        # print 'GrammarCost:' , str(prev_cost + self.grammarCost(CostFunction.RuleCost))
        # print
        # return
        Grammar = self.__concatenatedGrammar
        NTs = self.__concatenatedNTs
        separatorInts = self.__separatorInts
        Dic = self.dic
        rules = {}
        ntDic = {}
        counter = 1
        NTsSorted = set([])
        # print '------------for debugging begin'
        # print Dic
        # print Grammar
        # print NTs
        # print '------------for debugging end'
        for i in range(len(NTs)):
            if NTs[i] not in ntDic and NTs[i] not in separatorInts:
                NTsSorted.add(NTs[i])
                # ntDic[NTs[i]] = 'N'+str(counter)
                # rules['N'+str(counter)] = ''
                ntDic[NTs[i]] = 'N' + str(NTs[i])
                rules['N' + str(NTs[i])] = ''
                counter += 1
        for i in range(len(Grammar)):
            if Grammar[i] not in NTsSorted:
                if Grammar[i] not in separatorInts:
                    if not intGrammarPrint:
                        try:
                            rules[ntDic[NTs[i]]] = rules[ntDic[NTs[i]]] + ' ' + Dic[Grammar[i]]
                        except KeyError:
                            print Grammar[i], NTs[i]
                            print Dic
                            print Grammar
                            print NTs
                            raise
                    else:
                        rules[ntDic[NTs[i]]] = rules[ntDic[NTs[i]]] + ' ' + str(Grammar[i])
                else:
                    rules[ntDic[NTs[i - 1]]] = rules[ntDic[NTs[i - 1]]] + ' ||'
            else:
                if not intGrammarPrint:
                    try:
                        rules[ntDic[NTs[i]]] = rules[ntDic[NTs[i]]] + ' ' + ntDic[Grammar[i]]
                        if ntDic[NTs[i]] == ntDic[Grammar[i]]:
                            raise('Recursion')
                    except:
                        print Grammar[i], NTs[i]
                        raise
                else:
                    rules[ntDic[NTs[i]]] = rules[ntDic[NTs[i]]] + ' ' + ntDic[Grammar[i]]
        NTsSorted = sorted(list(NTsSorted))
        ruleCounter = 0
        for nt in NTsSorted:
            if nt not in self.__ctxNtSet:
                if intGrammarPrint:
                    subrules = rules[ntDic[nt]].rstrip(' ||').split(' ||')
                    for s in subrules:
                        outputFile.write(ntDic[nt] + ' ->' + s + '\n')
                else:
                    subrules = rules[ntDic[nt]].rstrip(' ||').split(' ||')
                    for s in subrules:
                        outputFile.write(ntDic[nt] + ' -> ' + s + '\n')
            ruleCounter += 1
            if ruleCounter == 1:
                for nt in sorted(list(self.__ctxNtSet)):
                    if intGrammarPrint:
                        subrules = rules[ntDic[nt]].rstrip(' ||').split(' ||')
                        for s in subrules:
                            outputFile.write(ntDic[nt] + ' ->' + s + '\n')
                    else:
                        subrules = rules[ntDic[nt]].rstrip(' ||').split(' ||')
                        for s in subrules:
                            outputFile.write(ntDic[nt] + ' -> ' + s + '\n')
                            # printFromDic(listOfIndices, Dic):
                            # ''.join([Dic[ch] for ch in listOfIndices])
        outputFile.close()
    #Prints all rules corresponding to the nonterminal n (int)
    def __printRules(self, n):
        return ''
    #Prints all yields corresponding to the nonterminal n (int)
    def __yieldOfNT(self, n):
        print 'Yield'
    #Prints the yield corresponding to the rule r
    def __yieldOfRule(self, r):
        print 'Yield'
    #Log via flags
    def __logViaFlag(self, flag):
        if not self.__quietLog:
            if flag == LogFlag.ConcatenationCostLog:
                sys.stderr.write('GrammarCost(Concats): ' + str(self.grammarCost(CostFunction.ConcatenationCost)) + '\n')
                # print(str('GrammarCost(Concats): ' + str(self.grammarCost(CostFunction.ConcatenationCost))))
            if flag == LogFlag.RuleCostLog:
                sys.stderr.write('GrammarCost: ' + str(self.grammarCost(CostFunction.RuleCost)) + '\n')
                # print(str('GrammarCost: ' + str(self.grammarCost(CostFunction.RuleCost))))
    #Log custom message
    def __logMessage(self, message):
        if not self.__quietLog:
            sys.stderr.write(str(message) + '\n')
            # print(str(message))

    #...........Utility Functions........
    #Converts the input data into an integer sequence, returns the integer sequence and the dictionary for recovering orginal letters
    def __preprocessInput(self, inputFile, charSeq = SequenceType.Character, noNewLineFlag = True):
        # print 'sssssssssssssssssssssssss', charSeq
        if charSeq == SequenceType.Character:#Building an integer-spaced sequence from the input string
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
            # print ';;;;;;;;;;;;;;;;;', letterDict
            return (newContents.rstrip('\n'), letterDict)
        if charSeq == SequenceType.Integer:#input is space seperated integers
            newContents = []
            letterDict = {}
            for line in inputFile:
                try:
                    for sym in line.split():
                        letterDict[int(sym)] = sym
                except ValueError:
                    raise ValueError('Input file is not in space-separated integer form: %s'%sym)
                newContents.append(line.strip())
                newContents = " ".join(newContents)
                #for i in range(len(line)):
                #    if line[i] not in [str(_x) for _x in range(10)] and line[i] not in {' ','\n'}:
                        
            return (newContents , letterDict )
        if charSeq == SequenceType.SpaceSeparated:#input is space-seperated words
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
            # print newContents
            return (newContents.rstrip('\n'), wordDict)

    def __preprocessInputStrings(self, inputFile, charSeq=SequenceType.Character, noNewLineFlag=True):
        # print 'sssssssssssssssssssssssss', charSeq
        if charSeq == SequenceType.Character:  # Building an integer-spaced sequence from the input string
            letterDict = {}
            counterDict = {}
            i = 0
            counter = 1
            newContents = ''
            if noNewLineFlag:
                line = inputFile
                for i in range(len(line)):
                    if line[i] not in counterDict:
                        letterDict[counter] = line[i]
                        counterDict[line[i]] = counter
                        counter += 1
                    newContents += str(counterDict[line[i]]) + ' '
            else:
                for line in inputFile.split('\n'):
                    line = line.rstrip('\n')
                    for i in range(len(line)):
                        if line[i] not in counterDict:
                            letterDict[counter] = line[i]
                            counterDict[line[i]] = counter
                            counter += 1
                        newContents += str(counterDict[line[i]]) + ' '
                    newContents += '\n'
            # print ';;;;;;;;;;;;;;;;;', letterDict
            return (newContents.rstrip('\n'), letterDict)
        if charSeq == SequenceType.Integer:  # input is space seperated integers
            newContents = []
            letterDict = {}
            for line in inputFile:
                try:
                    for sym in line.split():
                        letterDict[int(sym)] = sym
                except ValueError:
                    raise ValueError('Input file is not in space-separated integer form: %s' % sym)
                newContents.append(line.strip())
                newContents = " ".join(newContents)
                # for i in range(len(line)):
                #    if line[i] not in [str(_x) for _x in range(10)] and line[i] not in {' ','\n'}:

            return (newContents, letterDict)
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
            # print newContents
            return (newContents.rstrip('\n'), wordDict)
    #Replaces a repeat's occurrences with a new nonterminal and creates a new rule in the grammar
    def __replaceRepeat(self,(repeatLength, (repeatOccs))):
        repeat = self.__concatenatedGrammar[repeatOccs[0]:repeatOccs[0]+repeatLength]
        newTmpConcatenatedGrammar = []
        newTmpConcatenatedNTs = []
        prevIndex = 0
        self.nextNewInt += 2
        for i in repeatOccs:
            newTmpConcatenatedGrammar += self.__concatenatedGrammar[prevIndex:i] + [self.nextNewInt]
            newTmpConcatenatedNTs += self.__concatenatedNTs[prevIndex:i] + [self.__concatenatedNTs[i]]
            prevIndex = i+repeatLength
        self.__concatenatedGrammar = newTmpConcatenatedGrammar + self.__concatenatedGrammar[prevIndex:]
        self.__concatenatedNTs = newTmpConcatenatedNTs + self.__concatenatedNTs[prevIndex:]
        self.__concatenatedGrammar = self.__concatenatedGrammar + repeat
        self.__concatenatedNTs = self.__concatenatedNTs + [self.nextNewInt for j in range(repeatLength)]
        if self.nextNewInt == 8383:
            print 'yyyyyy'
            print self.nextNewInt
            print repeat
            sys.exit()
        self.__logMessage('Added Nonterminal: ' + str(self.nextNewInt))
        self.nextNewInt += 2
        self.__concatenatedGrammar = self.__concatenatedGrammar + [self.nextNewInt]
        self.__concatenatedNTs = self.__concatenatedNTs + [self.nextNewInt]
        self.__separatorInts.add(self.nextNewInt)
        self.__separatorIntsIndices = set([])
        for i in range(len(self.__concatenatedGrammar)):
            if self.__concatenatedGrammar[i] in self.__separatorInts:
                self.__separatorIntsIndices.add(i)
        self.nextNewInt += 2

    def replaceRepeat(self, repeatLength, repeatOccs):
        repeat = self.__concatenatedGrammar[repeatOccs[0]:repeatOccs[0] + repeatLength]
        newTmpConcatenatedGrammar = []
        newTmpConcatenatedNTs = []
        prevIndex = 0
        for i in repeatOccs:
            newTmpConcatenatedGrammar += self.__concatenatedGrammar[prevIndex:i] + [self.nextNewInt]
            newTmpConcatenatedNTs += self.__concatenatedNTs[prevIndex:i] + [self.__concatenatedNTs[i]]
            prevIndex = i + repeatLength
        self.__concatenatedGrammar = newTmpConcatenatedGrammar + self.__concatenatedGrammar[prevIndex:]
        self.__concatenatedNTs = newTmpConcatenatedNTs + self.__concatenatedNTs[prevIndex:]
        self.__concatenatedGrammar = self.__concatenatedGrammar + repeat
        self.__concatenatedNTs = self.__concatenatedNTs + [self.nextNewInt for j in range(repeatLength)]
        self.__logMessage('Added Nonterminal: ' + str(self.nextNewInt))
        self.nextNewInt += 2
        self.__concatenatedGrammar = self.__concatenatedGrammar + [self.nextNewInt]
        self.__concatenatedNTs = self.__concatenatedNTs + [self.nextNewInt]
        self.__separatorInts.add(self.nextNewInt)
        self.__separatorIntsIndices = set([])
        for i in range(len(self.__concatenatedGrammar)):
            if self.__concatenatedGrammar[i] in self.__separatorInts:
                self.__separatorIntsIndices.add(i)
        self.nextNewInt += 2

    def replaceRepeatEvo(self, nt, repeatLength, repeatOccs):
        repeat = self.__concatenatedGrammar[repeatOccs[0]:repeatOccs[0] + repeatLength]
        newTmpConcatenatedGrammar = []
        newTmpConcatenatedNTs = []
        prevIndex = 0
        for i in repeatOccs:
            newTmpConcatenatedGrammar += self.__concatenatedGrammar[prevIndex:i] + [nt]
            newTmpConcatenatedNTs += self.__concatenatedNTs[prevIndex:i] + [self.__concatenatedNTs[i]]
            prevIndex = i + repeatLength
        self.__concatenatedGrammar = newTmpConcatenatedGrammar + self.__concatenatedGrammar[prevIndex:]
        self.__concatenatedNTs = newTmpConcatenatedNTs + self.__concatenatedNTs[prevIndex:]
        # self.__concatenatedGrammar = self.__concatenatedGrammar + repeat
        # self.__concatenatedNTs = self.__concatenatedNTs + [nt for j in range(repeatLength)]
        # self.__logMessage('Replaced Nonterminal: ' + str(nt))
        # self.__concatenatedGrammar = self.__concatenatedGrammar + [self.nextNewInt]
        # self.__concatenatedNTs = self.__concatenatedNTs + [self.nextNewInt]
        # self.__separatorInts.add(self.nextNewInt)
        # self.__separatorIntsIndices = set([])
        # for i in range(len(self.__concatenatedGrammar)):
        #     if self.__concatenatedGrammar[i] in self.__separatorInts:
        #         self.__separatorIntsIndices.add(i)
        # self.nextNewInt += 2
    #Retrieves the maximum-gain repeat (randomizes within ties).
    #Output is a tuple: "(RepeatGain, (RepeatLength, (RepeatOccurrences)))"
    #1st entry of output is the maximum repeat gain value
    #2nd entry of output is a tuple of form: "(selectedRepeatLength, selectedRepeatOccsList)"
    def __retreiveMaximumGainRepeat(self, repeatClass, costFunction):
        repeats = self.__extractRepeats(repeatClass)
        maxRepeatGain = -1
        candidateRepeats = []
        for r in repeats: #Extracting maximum repeat
            repeatStats = r.split()
            repeatOccs = self.__extractNonoverlappingRepeatOccurrences(int(repeatStats[0]),map(int,repeatStats[2][1:-1].split(',')))
            if maxRepeatGain < self.__repeatGain(int(repeatStats[0]), len(repeatOccs), costFunction):
                maxRepeatGain = self.__repeatGain(int(repeatStats[0]), len(repeatOccs), costFunction)
                candidateRepeats = [(int(repeatStats[0]),len(repeatOccs),repeatOccs)]
            else:
                if maxRepeatGain >= 0 and maxRepeatGain == self.__repeatGain(int(repeatStats[0]), len(repeatOccs), costFunction):
                    candidateRepeats.append((int(repeatStats[0]),len(repeatOccs),repeatOccs))
        if(len(candidateRepeats) == 0):
            return (-1, (0, []))
        #Randomizing between candidates with maximum gain
        #selectedRepeatStats = candidateRepeats[random.randrange(len(candidateRepeats))]
        selectedRepeatStats = candidateRepeats[0]
        selectedRepeatLength = selectedRepeatStats[0]
        selectedRepeatOccs = sorted(selectedRepeatStats[2])
        return (maxRepeatGain, (selectedRepeatLength, selectedRepeatOccs))

    def retreiveMaximumGainRepeat(self, repeatClass, costFunction):
        repeats = self.__extractRepeats(repeatClass)
        maxRepeatGain = 0
        candidateRepeats = []
        for r in repeats:  # Extracting maximum repeat
            repeatStats = r.split()
            repeatOccs = self.__extractNonoverlappingRepeatOccurrences(int(repeatStats[0]),
                                                                       map(int, repeatStats[2][1:-1].split(',')))
            if maxRepeatGain < self.__repeatGain(int(repeatStats[0]), len(repeatOccs), costFunction):
                maxRepeatGain = self.__repeatGain(int(repeatStats[0]), len(repeatOccs), costFunction)
                candidateRepeats = [(int(repeatStats[0]), len(repeatOccs), repeatOccs)]
            else:
                if maxRepeatGain > 0 and maxRepeatGain == self.__repeatGain(int(repeatStats[0]), len(repeatOccs),
                                                                            costFunction):
                    candidateRepeats.append((int(repeatStats[0]), len(repeatOccs), repeatOccs))
        if (len(candidateRepeats) == 0):
            return {'score': -1, 'length': 0, 'occs': []}
        # Randomizing between candidates with maximum gain
        # selectedRepeatStats = candidateRepeats[random.randrange(len(candidateRepeats))]
        selectedRepeatStats = candidateRepeats[0]
        selectedRepeatLength = selectedRepeatStats[0]
        selectedRepeatOccs = sorted(selectedRepeatStats[2])
        return {'score': maxRepeatGain, 'length': selectedRepeatLength, 'occs': selectedRepeatOccs}
    #Returns the repeat gain, according to the chosen cost function
    def __repeatGain(self, repeatLength, repeatOccsLength, costFunction):
        if costFunction == CostFunction.ConcatenationCost:
            return (repeatLength-1)*(repeatOccsLength-1)
        if costFunction == CostFunction.EdgeCost:
            return (repeatLength - 1) * (repeatOccsLength - 1)-1
        if costFunction == CostFunction.RuleCost:
            return (repeatLength-1)*(repeatOccsLength-1)-2
    #Extracts the designated class of repeats (Assumes ./repeats binary being in the same directory)
    #Output is a string, each line containing: "RepeatLength    NumberOfOccurrence  (CommaSeparatedOccurrenceIndices)"
    def __extractRepeats(self, repeatClass):
        #with open(self.TMP_OUTPUT_FILE, "w") as text_file:
            #text_file.write(' '.join(map(str,self.__concatenatedGrammar)))
            #text_file.close()
            #os.system("./repeats -i -r "+repeatClass+" -n 2 -p sol " + self.TMP_OUTPUT_FILE + " > " + self.TMP_INPUT_FILE)
        # print 'y1'
        # process = subprocess.Popen(["./repeats11", "-i", "-r"+repeatClass, "-n2", "-psol"],stdout=subprocess.PIPE, stdin=subprocess.PIPE, stderr=subprocess.STDOUT)
        process = subprocess.Popen(["./repeats1/repeats11", "-i", "-r"+repeatClass, "-n1", "-psol"],stdout=subprocess.PIPE, stdin=subprocess.PIPE, stderr=subprocess.STDOUT)
        process.stdin.write(' '.join(map(str,self.__concatenatedGrammar)))
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

        # process = subprocess.Popen(["./repeats11", "-i", "-r"+repeatClass, "-n1", "-psolw"],stdout=subprocess.PIPE, stdin=subprocess.PIPE, stderr=subprocess.STDOUT)
        # process.stdin.write(' '.join(map(str,self.__concatenatedGrammar)))
        # text_file = ''
        # while process.poll() is None:
        #     output = process.communicate()[0].rstrip()
        #     text_file += output
        # process.wait()
        # repeats1=[]
        # firstLine = False
        # for line in text_file.splitlines():
        #     if firstLine == False:
        #         firstLine = True
        #         continue
        #     repeats1.append(line.rstrip('\n'))
        # print 'rrrrrrrrrrrrrr', repeats1
        return repeats
    #Extracts the non-overlapping occurrences of a repeat from a list of occurrences (scans from left to right)
    def __extractNonoverlappingRepeatOccurrences(self, repeatLength, occurrencesList):
        nonoverlappingIndices = []
        for i in range(len(occurrencesList)):
            if len(nonoverlappingIndices) > 0:
                if (nonoverlappingIndices[-1] + repeatLength <= occurrencesList[i]):#Not already covered
                    nonoverlappingIndices += [occurrencesList[i]]
            else:
                nonoverlappingIndices += [occurrencesList[i]]
        # print '1 ' , repeatLength, ':', occurrencesList
        # print '2 ' , repeatLength, ':', nonoverlappingIndices
        return  nonoverlappingIndices

    #Replaces a pair's occurrences with a new nonterminal, creates a new rule for the pairs and create corresponding rules for gaps in the grammar
    #Returns the occurrences of the (now repeated) context indices in the new concatenated grammar for use in next iteration
    def __replacePair(self, pairOccurrences):
        insideStringsSet = {}
        for o in pairOccurrences:
            insideString = ' '.join(map(str,self.__concatenatedGrammar[o[0][0]:o[0][1]]))
            if insideString in insideStringsSet:
                insideStringsSet[insideString].add(o)
            else:
                insideStringsSet[insideString] = set([o])
        print 'Inside Strings:',insideStringsSet.items()
        if len(insideStringsSet.items()) == 1:
            print insideStringsSet
            print 'single inside rule selected!'
            exit()
        usedRanges = self.__extractNonoverlappingPairOccurrences(pairOccurrences)
        print 'Inside Strings Ranges:',usedRanges
        newRepeatsList = [] #Used for next iteration, the case might happen that created repeats from contexts have equal gains as other repeats in the next iteration
        newRepeatsLength = usedRanges[0][2]+usedRanges[0][1]+1
        newTmpConcatenatedGrammar = []
        newTmpConcatenatedNTs = []
        prevIndex = 0
        if self.__nextNewContextInt < self.nextNewInt - 1:
                self.__nextNewContextInt = self.nextNewInt - 1
        for i in range(len(usedRanges)):
            tmpRange = usedRanges[i]
            newTmpConcatenatedGrammar += self.__concatenatedGrammar[prevIndex:tmpRange[0][0]] + [self.__nextNewContextInt]
            newRepeatsList.append(len(newTmpConcatenatedGrammar)-1-tmpRange[1])
            newTmpConcatenatedNTs += self.__concatenatedNTs[prevIndex:tmpRange[0][0]] + [self.__concatenatedNTs[tmpRange[0][0]-1]]
            prevIndex = tmpRange[0][1]
        newTmpConcatenatedGrammar += self.__concatenatedGrammar[prevIndex:]
        newTmpConcatenatedNTs += self.__concatenatedNTs[prevIndex:]
        currentNT = self.__nextNewContextInt
        self.__ctxNtSet.add(currentNT)
        print 'Added Nonterminal:', str(self.__nextNewContextInt)
        print 'Number of original occurrences:', len(pairOccurrences)
        print 'Number of non-overlapping occurrences:', len(usedRanges)
        self.__nextNewContextInt += 2
        #irredundantMiddles = set()
        for i in range(len(usedRanges)):
            tmpRange = usedRanges[i]
            #Avoiding to add extra middle strings when one is already added
            #if(tuple(self.__concatenatedGrammar[tmpRange[0][0]:tmpRange[0][1]]) in irredundantMiddles):
            #    continue
            #else:
            #    irredundantMiddles.add(tuple(self.__concatenatedGrammar[tmpRange[0][0]:tmpRange[0][1]]))
            newTmpConcatenatedGrammar += self.__concatenatedGrammar[tmpRange[0][0]:tmpRange[0][1]] + [self.nextNewInt]
            newTmpConcatenatedNTs += [currentNT for j in range(tmpRange[0][1]-tmpRange[0][0])] + [self.nextNewInt]
            self.__separatorInts.add(self.nextNewInt)
            self.nextNewInt += 2
        self.__separatorIntsIndices = set([])
        for i in range(len(newTmpConcatenatedGrammar)):
            if newTmpConcatenatedGrammar[i] in self.__separatorInts:
                self.__separatorIntsIndices.add(i)
        self.__concatenatedGrammar = newTmpConcatenatedGrammar
        self.__concatenatedNTs = newTmpConcatenatedNTs
        if self.__fixedGap: #Correcting the extra cost in case of using fixed-gap contexts
            # self.__fixedGapSavedCost += len(usedRanges)-1
            self.__fixedGapSavedCost += len(usedRanges) #The Extra improvement added after XRCE
        return (newRepeatsLength, newRepeatsList)
    #Retrieves the maximum-gain pair (first that is found).
    #Output is a tuple: "(RepeatGain, (RepeatLength, (RepeatOccurrences)))"
    #1st entry of output is the maximum pair gain value
    #2nd entry of output is a list of tuples of the form: "(GapOccurrenceRange,R1Length,R2Length)"
    def __retreiveMaximumGainPair(self, repeatClass, costFunction, pairSearchMethod):
        pairDic = self.__extractPairs(repeatClass, pairSearchMethod, costFunction)
        # print 'ddddddddddd', pairDic
        return self.__retreiveMaximumGainPairFromPairDic(pairDic, costFunction)
    #Retrieves the maximum-gain pair from a dictionary of {pair:occurrences} (first that is found)
    #1st entry of output is the maximum pair gain value
    #2nd entry of output is a list of tuples of the form: "(GapOccurrenceRange,R1Length,R2Length)"
    def __retreiveMaximumGainPairFromPairDic(self, pairDic, costFunction):
        maxPairGain = 0
        reducedRanges = []
        pairGainDic = {}
        for key in pairDic:
            r1Length = len(key[0])
            #r1Length = pairDic[key][0][1]
            r2Length = len(key[1])
            #r2Length = pairDic[key][0][2]
            pairDic[key] = self.__extractNonoverlappingPairOccurrences(pairDic[key])
            pairGainDic[key] = self.__pairGain(r1Length, r2Length, pairDic[key], costFunction)
        # print 'nonnnnnnnnnnnnn', pairDic
        # print 'gainnnnnnnnnnnnn', pairGainDic
        # print 'gramarrrrrrrrrrrr', self.__concatenatedGrammar
        if len(pairDic) != 0 and len(pairGainDic) != 0:
            sortedPairGains = sorted(pairGainDic.items(), key=operator.itemgetter(1),reverse=True)
            if (sortedPairGains[0])[1] > maxPairGain and (sortedPairGains[0])[1] != 0:
                maxPairGain = (sortedPairGains[0])[1]
                reducedRanges = pairDic[(sortedPairGains[0])[0]]
        if len(reducedRanges) == 0:
            return (-1,[])
        #Fix pair occurrences if chosen greedy pair search method
        #---------
        return (maxPairGain, reducedRanges)
    #Returns the pair gain, according to the chosen cost function
    def __pairGain(self, r1Length, r2Length, pairOccs, costFunction):
        pairOccsLength = len(pairOccs)
        if costFunction == CostFunction.ConcatenationCost:
            if not self.__fixedGap:
                return (r1Length + r2Length - 4)*(pairOccsLength-1)-2
            else:
                return (r1Length + r2Length - 2)*(pairOccsLength-1)-4
        if costFunction == CostFunction.RuleCost:
            additionalGain = 0
            insideStringsSet = {}
            for o in pairOccs:
                insideString = ' '.join(map(str,self.__concatenatedGrammar[o[0][0]:o[0][1]]))
                if insideString in insideStringsSet:
                    insideStringsSet[insideString].add(o)
                else:
                    insideStringsSet[insideString] = set([o])
            if len(insideStringsSet.items()) == 1:
                return 0
            # for key in insideStringsSet:
            #     if len(key.split()) > 1 and len(insideStringsSet[key]) > 1:
            #         additionalGain += (len(insideStringsSet[key]) - 1)*(len(key.split())-1)-2
            if not self.__fixedGap:
                return (r1Length + r2Length - 2)*(pairOccsLength-1)-4
            else:
                # totalGain = (r1Length + r2Length-1)*(pairOccsLength-1)-5 + additionalGain
                totalGain = (r1Length + r2Length - 1) * (pairOccsLength - 1) - 4 + additionalGain # Extra Gain Added after XRCE
                return totalGain
    #Extracts the designated class of repeated-contexts (Assumes ./repeats binary being in the same directory)
    #Output is a dictionary of the form: "((R1),(R2)):(GapOccurrenceRange,R1Length,R2Length)"
    def __extractPairs(self, repeatClass, pairSearchMethod, costFunction):
        ctxRepeats = self.__extractRepeats(repeatClass)
        # print 'cccccccccccc', ctxRepeats
        pairDic = {}
        allRepeatOccs = []
        #Storing repeats as tuples of "(RepeatLength, OccurrenceIndex)"
        for r in ctxRepeats:
            allRepeatOccs.extend([(int((r.split())[0]),j) for j in list((map(int, ((r.split())[2])[1:-1].split(','))))])
        allRepeatOccs.extend([(-1,j) for j in self.__separatorIntsIndices]) #Merging with separatorIntsIndices for easier detection of input strings' ends
        allRepeatOccs = sorted(allRepeatOccs,key=lambda x: (x[1],x[0]))
        #print self.__concatenatedGrammar
        #print
        if self.__fixedGap:
            pairDic = self.__fixedGapPairSearch(allRepeatOccs, costFunction)
        else:
            if pairSearchMethod == PairSearchMethod.ConstantLengthSearch:
                pairDic = self.__variableGapPairSearchWithConstantMaxGap(allRepeatOccs)
            if pairSearchMethod == PairSearchMethod.ExhausivePairSearch:
                pairDic = self.__exhausivePairSearch(allRepeatOccs)
            if pairSearchMethod == PairSearchMethod.GreedyPairSearch:
                pairDic = self.__greedyPairSearch(allRepeatOccs)
            #Filtering only non-overlapping pair occurrences
            # for key in pairDic:
            #     pairDic[key] = self.__extractNonoverlappingPairOccurrences(pairDic[key])
        return pairDic
    #Fixed-Gap pair search.
    #Input is the gap and the sorted list of all repeat occurrences: [(repeatLength, repeatOccurrenceIndex)]
    #Output is a dictionary of the form: "((R1),(R2)):(GapOccurrenceRange,R1Length,R2Length)"
    def __fixedGapPairSearch(self, repeatOccurrences, costFunction):
        pairDic = {}
        reverseRepeatOccs = {}
        reverseRepeatEnds = {}
        for repOcc in repeatOccurrences:
            if repOcc[1] not in self.__separatorIntsIndices:
                #print repOcc[1]
                if repOcc[1] in reverseRepeatOccs:
                    reverseRepeatOccs[repOcc[1]].append(repOcc[0])
                else:
                    reverseRepeatOccs[repOcc[1]] = [repOcc[0]]
                if repOcc[1]+repOcc[0]-1 in reverseRepeatEnds:
                    reverseRepeatEnds[repOcc[1]+repOcc[0]-1].append(repOcc[0])
                else:
                    reverseRepeatEnds[repOcc[1]+repOcc[0]-1] = [repOcc[0]]
        maxGapGain = -1
        #minK = self.__MAX_LENGTH
        #for k in xrange(minK,self.__MAX_LENGTH):
        for k in xrange(1,self.__MAX_LENGTH+1):
        # for k in xrange(3,4):
            sys.stderr.write(str(k) + '\n')
            tmpPairDic = {}
            currentStringRepsOccs = {}
            currentStringRepsEnds = {}
            currentStringStart = 0
            currentStringEnd = 0
            for index in range(len(self.__concatenatedGrammar)):
                if index in self.__separatorIntsIndices:
                    # print 'starts', currentStringRepsOccs
                    # print 'ends', currentStringRepsEnds
                    currentStringEnd = index
                    # print 's', currentStringStart
                    # print 'e', currentStringEnd
                    for currentIndex in range(currentStringStart,currentStringEnd):
                        if (currentStringRepsOccs.has_key(currentIndex+k+1)) and (currentStringRepsEnds.has_key(currentIndex)):
                            for repL1 in currentStringRepsEnds[currentIndex]:
                                for repL2 in currentStringRepsOccs[currentIndex+k+1]:
                                    if tmpPairDic.has_key((tuple(self.__concatenatedGrammar[currentIndex-repL1+1:currentIndex+1]),tuple(self.__concatenatedGrammar[currentIndex+k+1:currentIndex+k+1+repL2]))):
                                        tmpPairDic[(tuple(self.__concatenatedGrammar[currentIndex-repL1+1:currentIndex+1]),tuple(self.__concatenatedGrammar[currentIndex+k+1:currentIndex+k+1+repL2]))].append(((currentIndex+1,currentIndex+k+1),repL1,repL2))
                                    else:
                                        tmpPairDic[(tuple(self.__concatenatedGrammar[currentIndex-repL1+1:currentIndex+1]),tuple(self.__concatenatedGrammar[currentIndex+k+1:currentIndex+k+1+repL2]))] = [((currentIndex+1,currentIndex+k+1),repL1,repL2)]
                    currentStringStart = index + 1
                    currentStringRepsOccs = {}
                    currentStringRepsEnds = {}
                    # print 'tmpPairDic', tmpPairDic
                else:
                    if index in reverseRepeatOccs:
                        currentStringRepsOccs[index] = reverseRepeatOccs[index]
                    if index in reverseRepeatEnds:
                        currentStringRepsEnds[index] = reverseRepeatEnds[index]
            # for key in tmpPairDic:
            #     tmpPairDic[key] = self.__extractNonoverlappingPairOccurrences(tmpPairDic[key])
            (maxPairGain, reducedRanges) = self.__retreiveMaximumGainPairFromPairDic(tmpPairDic, costFunction)
            if maxPairGain > maxGapGain:
                pairDic = tmpPairDic
                maxGapGain = maxPairGain
        return pairDic
    #Variable-Gap pair search.
    #Input is the gap and the sorted list of all repeat occurrences: [(repeatLength, repeatOccurrenceIndex)]
    #Output is a dictionary of the form: "((R1),(R2)):(GapOccurrenceRange,R1Length,R2Length)"
    def __variableGapPairSearchWithConstantMaxGap(self, repeatOccurrences):
        #pairDic = {}
        reverseRepeatOccs = {}
        reverseRepeatEnds = {}
        for repOcc in repeatOccurrences:
            if repOcc[1] not in self.__separatorIntsIndices:
                #print repOcc[1]
                if repOcc[1] in reverseRepeatOccs:
                    reverseRepeatOccs[repOcc[1]].append(repOcc[0])
                else:
                    reverseRepeatOccs[repOcc[1]] = [repOcc[0]]
                if repOcc[1]+repOcc[0]-1 in reverseRepeatEnds:
                    reverseRepeatEnds[repOcc[1]+repOcc[0]-1].append(repOcc[0])
                else:
                    reverseRepeatEnds[repOcc[1]+repOcc[0]-1] = [repOcc[0]]
        maxGapGain = -1
        #minK = self.__MAX_LENGTH
        #for k in xrange(minK,self.__MAX_LENGTH):
        for k in xrange(1,self.__MAX_LENGTH):
            sys.stderr.write(str(k) + '\n')
            tmpPairDic = {}
            currentStringRepsOccs = {}
            currentStringRepsEnds = {}
            currentStringStart = 0
            currentStringEnd = 0
            for index in range(len(self.__concatenatedGrammar)):
                if index in self.__separatorIntsIndices:
                    currentStringEnd = index
                    for currentIndex in range(currentStringStart,currentStringEnd):
                        if (currentStringRepsOccs.has_key(currentIndex+k+1)) and (currentStringRepsEnds.has_key(currentIndex)):
                            for repL1 in currentStringRepsEnds[currentIndex]:
                                for repL2 in currentStringRepsOccs[currentIndex+k+1]:
                                    if tmpPairDic.has_key((tuple(self.__concatenatedGrammar[currentIndex-repL1+1:currentIndex+1]),tuple(self.__concatenatedGrammar[currentIndex+k+1:currentIndex+k+1+repL2]))):
                                        tmpPairDic[(tuple(self.__concatenatedGrammar[currentIndex-repL1+1:currentIndex+1]),tuple(self.__concatenatedGrammar[currentIndex+k+1:currentIndex+k+1+repL2]))].append(((currentIndex+1,currentIndex+k+1),repL1,repL2))
                                    else:
                                        tmpPairDic[(tuple(self.__concatenatedGrammar[currentIndex-repL1+1:currentIndex+1]),tuple(self.__concatenatedGrammar[currentIndex+k+1:currentIndex+k+1+repL2]))] = [((currentIndex+1,currentIndex+k+1),repL1,repL2)]
                    currentStringStart = index + 1
                    currentStringRepsOccs = {}
                    currentStringRepsEnds = {}
                else:
                    if index in reverseRepeatOccs:
                        currentStringRepsOccs[index] = reverseRepeatOccs[index]
                    if index in reverseRepeatEnds:
                        currentStringRepsEnds[index] = reverseRepeatEnds[index]
            # for key in tmpPairDic:
            #     tmpPairDic[key] = self.__extractNonoverlappingPairOccurrences(tmpPairDic[key])
            #(maxPairGain, reducedRanges) = self.__retreiveMaximumGainPairFromPairDic(tmpPairDic, costFunction)
            #if maxPairGain > maxGapGain:
            #    pairDic = tmpPairDic
            #    maxGapGain = maxPairGain
        return tmpPairDic
    #Exhausive variable-length gap pair search.
    #Input is the sorted list of all repeat occurrences: [(repeatLength, repeatOccurrenceIndex)]
    #Output is a dictionary of the form: "((R1),(R2)):(GapOccurrenceRange,R1Length,R2Length)"
    def __exhausivePairSearch(self, repeatOccurrences):
        pairDic = {}
        currentStringPairOccs = []
        for r in repeatOccurrences:#Scanning pair occurrences
            if r[1] in self.__separatorIntsIndices:#Reached the end of an input string
                for k in range(len(currentStringPairOccs)):#Greedy Pairing
                #for r1 in currentStringPairOccs:
                    r1 = currentStringPairOccs[k]
                    for j in range(len(currentStringPairOccs)-k-1):
                    #for r2 in currentStringPairOccs:
                        r2 = currentStringPairOccs[k+1+j]
                        r1Length = r1[0]
                        r2Length = r2[0]
                        oc1 = r1[1]
                        oc2 = r2[1]
                        if (oc2 < oc1 or oc1 + r1Length >= oc2):
                            continue
                        #Large gap filter
                            #gap = 2
                            #if not (oc2-(oc1+r1Length) >= gap):
                                #continue
                        #hash((tuple(self.__concatenatedGrammar[oc1:oc1+r1Length]),tuple(self.__concatenatedGrammar[oc2:oc2+r2Length])))
                        newPair = (tuple(self.__concatenatedGrammar[oc1:oc1+r1Length]),tuple(self.__concatenatedGrammar[oc2:oc2+r2Length]))
                        if newPair in pairDic:
                            pairDic[newPair].append(((oc1+r1Length,oc2),r1Length,r2Length))
                            #pairDic[(repeatIndexHashes[(r1Length,oc1)],repeatIndexHashes[(r2Length,oc2)])].append(((oc1+r1Length,oc2),r1Length,r2Length))
                        else:
                            pairDic[newPair] = [((oc1+r1Length,oc2),r1Length,r2Length)]
                            #pairDic[(repeatIndexHashes[(r1Length,oc1)],repeatIndexHashes[(r2Length,oc2)])] = [((oc1+r1Length,oc2),r1Length,r2Length)]
                currentStringPairOccs = []
            else:
                currentStringPairOccs.append(r)
        return pairDic
    #Greedy variable-length gap pair search.
    #Input is the sorted list of all repeat occurrences: [(repeatLength, repeatOccurrenceIndex)]
    #Output is a dictionary of the form: "((R1),(R2)):(GapOccurrenceRange,R1Length,R2Length)"
    def __greedyPairSearch(self, repeatOccurrences):
        pairDic = {}
        pairStart = -1 #Indicates the start of a pair
        pairEnd = -1 #Indicates the ending of a pair
        i = 0
        newString = True
        identifiedPairs = []
        while i < len(repeatOccurrences):#Scanning pair occurrences
            if repeatOccurrences[i][1] in self.__separatorIntsIndices:#Reached the end of an input string
                newString = True
                i += 1
            else:
                if newString:
                    pairStart = repeatOccurrences[i]
                    j = i + 1
                    validStartings = [pairStart]
                    while j < len(repeatOccurrences) and repeatOccurrences[j][1] == pairStart[1]: #Scanning all repeats starting at the same index as pairStart
                        validStartings.append(repeatOccurrences[j])
                        #Selecting the shortest repeat as pairStart
                        if pairStart[0] > repeatOccurrences[j][0]:
                            pairStart = repeatOccurrences[j]
                        j += 1
                    pairStart = random.choice(validStartings)
                    i = j
                    while i < len(repeatOccurrences) and repeatOccurrences[i][1] <= pairStart[1] + pairStart[0]: #Skipping overlapping repeats and fixing the problem of having a gap with zero length
                        i += 1
                    newString = False
                else:
                    pairEnd = repeatOccurrences[i]
                    j = i + 1
                    validEndings = [pairEnd]
                    while j < len(repeatOccurrences) and repeatOccurrences[j][1] == pairEnd[1]: #Scanning all repeats starting at the same index as pairEnd
                        validEndings.append(repeatOccurrences[j])
                        #Selecting the shortest repeat as pairEnd
                        if pairEnd[0] > repeatOccurrences[j][0]:
                            pairEnd = repeatOccurrences[j]
                        j += 1
                    pairEnd = random.choice(validEndings)
                    i = j
                    while i < len(repeatOccurrences) and repeatOccurrences[i][1] <= pairEnd[1] + pairEnd[0]: #Setting the start position for next pair
                        i += 1
                    #identifiedPairs.append((tuple(self.__concatenatedGrammar[pairStart[1]:pairStart[1]+pairStart[0]]),tuple(self.__concatenatedGrammar[pairEnd[1]:pairEnd[1]+pairEnd[0]])))
                    #identifiedPairs.append((pairStart[1],pairEnd[1]))
                    if (tuple(self.__concatenatedGrammar[pairStart[1]:pairStart[1]+pairStart[0]]),tuple(self.__concatenatedGrammar[pairEnd[1]:pairEnd[1]+pairEnd[0]])) in pairDic:
                        pairDic[(tuple(self.__concatenatedGrammar[pairStart[1]:pairStart[1]+pairStart[0]]),tuple(self.__concatenatedGrammar[pairEnd[1]:pairEnd[1]+pairEnd[0]]))].append(((pairStart[1]+pairStart[0],pairEnd[1]),pairStart[0],pairEnd[0]))
                    else:
                        pairDic[(tuple(self.__concatenatedGrammar[pairStart[1]:pairStart[1]+pairStart[0]]),tuple(self.__concatenatedGrammar[pairEnd[1]:pairEnd[1]+pairEnd[0]]))] = [((pairStart[1]+pairStart[0],pairEnd[1]),pairStart[0],pairEnd[0])]
                    newString = True
        #for p in identifiedPairs:
            #print p,
        #print
        return pairDic
    #Extracts non-overlapping occurrences of a pair from a all lists of its occurrences in exhausive pair search method
    #Input is of the form of the values from pairDic, scans from left to right)
    def __extractNonoverlappingPairOccurrences(self, occurrencesList):
        gain = 0
        #reducedRanges = sorted(pairDic[key], key=lambda x: (x[0][0],x[0][1]))
        reducedRanges = sorted(occurrencesList, key=lambda x: (x[0][0],x[0][1]))
        usedRanges = []
        if not self.__fixedGap:
            for i in range(len(reducedRanges)):
                invalidPair = False
                tmpRange = reducedRanges[i]
                #for candidateRange in usedRanges:#excluding overlapping occurrences
                if(len(usedRanges) > 0):
                    candidateRange = usedRanges[-1]
                        #if invalidPair:
                            #break
                    if (candidateRange[0][0] >= tmpRange[0][0] and candidateRange[0][0] <= tmpRange[0][1]) or (candidateRange[0][1] >= tmpRange[0][0] and candidateRange[0][1] <= tmpRange[0][1]) or (candidateRange[0][0]-candidateRange[1] >= tmpRange[0][0] and candidateRange[0][0]-candidateRange[1] <= tmpRange[0][1]) or (candidateRange[0][1]+candidateRange[2] >= tmpRange[0][0] and candidateRange[0][1]+candidateRange[2] <= tmpRange[0][1]):
                        invalidPair = True
                if not invalidPair:
                    usedRanges += [tmpRange]
        else:#reducing fixed-gaps, only store the gap with highest number of occurrences
            gapDic = {}
            for r in reducedRanges:
                gapDic[r[0][1]-r[0][0]] = []
            for r in reducedRanges:
                gapDic[r[0][1]-r[0][0]].append(r)
            tmpUsedRanges = []
            for gap in gapDic:
            #for i in range(len(reducedRanges)):
                for i in range(len(gapDic[gap])):
                    invalidPair = False
                    tmpRange = gapDic[gap][i]
                    #for candidateRange in tmpUsedRanges:#excluding overlapping occurrences
                    if(len(tmpUsedRanges) > 0):
                        candidateRange = tmpUsedRanges[-1]
                        #if invalidPair:
                            #break
                        if (candidateRange[0][0] >= tmpRange[0][0] and candidateRange[0][0] <= tmpRange[0][1]) or (candidateRange[0][1] >= tmpRange[0][0] and candidateRange[0][1] <= tmpRange[0][1]) or (candidateRange[0][0]-candidateRange[1] >= tmpRange[0][0] and candidateRange[0][0]-candidateRange[1] <= tmpRange[0][1]) or (candidateRange[0][1]+candidateRange[2] >= tmpRange[0][0] and candidateRange[0][1]+candidateRange[2] <= tmpRange[0][1]):
                            invalidPair = True
                    if not invalidPair:
                        tmpUsedRanges += [tmpRange]
                if len(usedRanges) < len(tmpUsedRanges):
                    usedRanges = tmpUsedRanges
                tmpUsedRanges = []
        return usedRanges

    def grammarDic(self):
        # print '**', self.__concatenatedGrammar
        # print '**', self.__concatenatedNTs
        grammar = {}
        prevIndex = 0
        sepsInd = sorted(list(self.__separatorIntsIndices))
        for i in range(len(sepsInd)):
            rhs = self.__concatenatedGrammar[prevIndex:sepsInd[i]]
            nt = self.__concatenatedNTs[prevIndex]
            prevIndex = sepsInd[i]+1
            if nt in grammar:
                grammar[nt].append(rhs)
            else:
                grammar[nt] = [rhs]
        return grammar

    def ntYield(self, grammar, inputNT):
        # print 'NO'
        iterateCheck = 0
        for rhs in grammar[inputNT]:
            stack = copy.deepcopy(rhs)
            ntStack = [inputNT]
            grammarText = []
            while len(stack) > 0:
                iterateCheck += 1
                if iterateCheck > 1000:
                    break
                # print 'len', len(stack)
                c = stack.pop(0)
                # print 'c', c
                if c == -2:  # Repeat NT recursion
                    ntStack.pop()
                    continue
                if c in grammar:
                    ntStack.append(c)
                    stack = grammar[c][0] + [-2] + stack
                    # print 'gram', grammar[c][0]
                else:
                    grammarText.append(c)
        # print grammarText
        # print 'YES'
        return grammarText
    def getMaxEvoR(self, ntYields):
        rsoList = []
        for nt in ntYields:
            rsoList.append({'nt': nt, 'sub': ntYields[nt][0], 'length': len(ntYields[nt][0]),'occs': [],
                            'score': 0})  # (substring, [[TargetIndex, occurrences]], overallScore)
            occ = 0
            tmpOccs = KnuthMorrisPratt(self.__concatenatedGrammar, ntYields[nt][0])
            removeOccs = []
            for i in tmpOccs:
                if (self.__concatenatedNTs[i] == nt):
                    removeOccs.append(i)
            tmpOccs = [item for item in tmpOccs if item not in removeOccs]
            occ += len(tmpOccs)
            if len(tmpOccs) > 0:
                rsoList[-1]['occs'].extend(tmpOccs)
            if (occ - 1) * len(ntYields[nt][0]) > 0:
                # rsoList[-1]['score'] = (occ - 1) * len(ntYields[nt][0])
                rsoList[-1]['score'] = (occ) * (len(ntYields[nt][0])-1)
        maxrsoScore = 0
        maxrso = {'nt': [], 'sub': [], 'length': 0,'occs': [],
                            'score': -1}
        for rso in rsoList:
            if maxrsoScore < rso['score']:
                maxrsoScore = rso['score']
                maxrso = rso
        return maxrso

class Grammar2(object):
    # TMP_OUTPUT_FILE = 'tmpOutput.txt'
    # TMP_INPUT_FILE = 'tmpInput.txt'
    __preprocessedInput = []  # Original input as a sequence of integers
    dic = []  # Dictionary for correspondence of integers to original chars (only when charSeq = 'c','s')

    __inputName = ''
    __concatenatedGrammar = []  # Concatenated grammar rules with seperatorInts
    __concatenatedNTs = []  # For each grammar rule, alongside the concatenated grammar
    __separatorInts = set([])  # Used for seperating grammar rules in the concatenatedGrammar
    __separatorIntsIndices = set([])  # Indices of separatorInts in the concatenated grammar
    nextNewInt = 0  # Used for storing ints of repeat non-terminals and separators in odd numbers
    __nextNewContextInt = 0  # Used for storing ints for context non-terminals in even numbers
    __ctxNtSet = set([])  # Set of context non-terminals (i.e. inside rules), used for better printing

    __MAX_LENGTH = 100  # Used for setting upper bound on fixed gap size

    __fixedGap = False  # Indicates wether contexts have a fixed gap or not
    __fixedGapSavedCost = 0  # Used to correct the grammar cost when __fixedGap==True

    __quietLog = False  # if true, disables logging
    __numberOfTimesRepeatPicked = 0
    __numberOfTimesPairPicked = 0
    __iterations = 0

    def __init__(self, inputFile, loadGrammarFlag, gap, chFlag=SequenceType.Character, noNewLineFlag=True):
        sys.stderr.write(str(self.__concatenatedGrammar) + 'gram00\n')
        self.__MAX_LENGTH = gap
        if loadGrammarFlag == 'grammar':
            self.__initFromGrammar(inputFile)
        elif loadGrammarFlag == 'file':
            self.__initFromStringsFile(inputFile, chFlag, noNewLineFlag)
        elif loadGrammarFlag == 'string':
            self.__initFromStrings(inputFile, chFlag, noNewLineFlag)

    # Initializes (an unoptimized) grammar from inputFile. charSeq tells if inputFile is a char sequence, int sequence or space-separated sequence
    def __initFromStringsFile(self, inputFile, chFlag=SequenceType.Character, noNewLineFlag=True):
        self.__inputName = inputFile.name.split('.')[0]
        # self.TMP_OUTPUT_FILE = self.__inputName + '-' + self.TMP_OUTPUT_FILE
        # self.TMP_INPUT_FILE = self.__inputName + '-' + self.TMP_INPUT_FILE
        (self.__preprocessedInput, self.dic) = self.__preprocessInput(inputFile, charSeq=chFlag,
                                                                      noNewLineFlag=noNewLineFlag)
        allLetters = set(map(int, self.__preprocessedInput.split()))
        # Setting odd and even values for nextNewInt and __nextNewContextInt
        self.nextNewInt = max(allLetters) + 1
        if self.nextNewInt % 2 == 0:
            self.__nextNewContextInt = self.nextNewInt
            self.nextNewInt += 1
        else:
            self.__nextNewContextInt = self.nextNewInt + 1
        # Initializing the concatenated grammar
        for line in self.__preprocessedInput.split('\n'):
            line = line.rstrip('\n')
            self.__concatenatedGrammar.extend(map(int, line.split()))
            self.__concatenatedGrammar.append(self.nextNewInt)
            self.__concatenatedNTs.extend(0 for j in range(len(map(int, line.split()))))
            self.__concatenatedNTs.append(self.nextNewInt)
            self.__separatorInts.add(self.nextNewInt)
            self.__separatorIntsIndices.add(len(self.__concatenatedGrammar) - 1)
            self.nextNewInt += 2
            # if len(line.split()) > self.__MAX_LENGTH:
            #     self.__MAX_LENGTH = len(line.split())

    def __initFromStrings(self, inputFile, chFlag=SequenceType.Character, noNewLineFlag=True):
        # self.__inputName = inputFile.name.split('.')[0]
        # self.TMP_OUTPUT_FILE = self.__inputName + '-' + self.TMP_OUTPUT_FILE
        # self.TMP_INPUT_FILE = self.__inputName + '-' + self.TMP_INPUT_FILE
        (self.__preprocessedInput, self.dic) = self.__preprocessInputStrings(inputFile, charSeq=chFlag,
                                                                             noNewLineFlag=noNewLineFlag)
        sys.stderr.write(str(self.__preprocessedInput) + 'prep\n')
        sys.stderr.write(str(self.__preprocessedInput.split('\n')) + 'prep2\n')
        allLetters = set(map(int, self.__preprocessedInput.split()))
        # Setting odd and even values for nextNewInt and __nextNewContextInt
        self.nextNewInt = max(allLetters) + 1
        if self.nextNewInt % 2 == 0:
            self.__nextNewContextInt = self.nextNewInt
            self.nextNewInt += 1
        else:
            self.__nextNewContextInt = self.nextNewInt + 1
        # Initializing the concatenated grammar
        for line in self.__preprocessedInput.split('\n'):
            sys.stderr.write(str(line) + 'line\n')
            line = line.rstrip('\n')
            sys.stderr.write(str(self.__concatenatedGrammar) + 'gram0\n')
            sys.stderr.write(str(self.__concatenatedNTs) + 'nts0\n')
            self.__concatenatedGrammar.extend(map(int, line.split()))
            self.__concatenatedGrammar.append(self.nextNewInt)
            sys.stderr.write(str(self.__concatenatedGrammar) + 'gram1\n')
            sys.stderr.write(str(self.__concatenatedNTs) + 'nts1\n')
            self.__concatenatedNTs.extend(0 for j in range(len(map(int, line.split()))))
            self.__concatenatedNTs.append(self.nextNewInt)
            self.__separatorInts.add(self.nextNewInt)
            self.__separatorIntsIndices.add(len(self.__concatenatedGrammar) - 1)
            self.nextNewInt += 2
            sys.stderr.write(str(self.__concatenatedGrammar) + 'gram\n')
            sys.stderr.write(str(self.__concatenatedNTs) + 'nts\n')
            # if len(line.split()) > self.__MAX_LENGTH:
            #     self.__MAX_LENGTH = len(line.split())
        sys.stderr.write(str(self.__concatenatedGrammar) + 'gram\n')
        sys.stderr.write(str(self.__concatenatedNTs) + 'nts\n')

    # Loads the grammar from an external file
    def __initFromGrammar(self, inputFile):
        firstLine = True
        grammar = {}
        wordDict = {}
        counterDict = {}
        counter = 0
        textFile = inputFile.read().splitlines()
        # textFile = textFile.replace('   ', ' SPACECHAR ')
        # textFile = textFile.replace('  \n', ' SPACECHAR\n')
        # print textFile
        tmpRule = []
        for line in textFile:
            # if line == '':
            #     continue
            if firstLine:
                firstLine = False
                continue
            if len(line.split(' ->  ')) < 2:
                # tmpRule = ['\n'] + line.split(' ')
                tmpRule = line.split(' ')
                newRule = []
                for w in tmpRule:
                    if w == '':
                        continue
                    if w not in counterDict:
                        wordDict[counter] = w
                        counterDict[w] = counter
                        counter += 1
                    newRule.append(counterDict[w])
                grammar[newNt] += newRule
                continue
            else:
                nt = line.split(' ->  ')[0]
            if counter % 2 == 0:
                if counter != 0:
                    counter += 1
            if nt not in counterDict:
                wordDict[counter] = nt
                counterDict[nt] = counter
                counter += 1
            newNt = counterDict[nt]
            rule = line.split(' ->  ')[1].split(' ')
            newRule = []
            for w in rule:
                if w == '':
                    continue
                if w not in counterDict:
                    wordDict[counter] = w
                    counterDict[w] = counter
                    counter += 1
                newRule.append(counterDict[w])
            grammar[newNt] = newRule
        # print grammar
        self.dic = wordDict
        self.nextNewInt = counter
        if self.nextNewInt % 2 == 0:
            self.__nextNewContextInt = self.nextNewInt
            self.nextNewInt += 1
        else:
            self.__nextNewContextInt = self.nextNewInt + 1
        for nt in grammar:
            self.__concatenatedGrammar.extend(grammar[nt])
            self.__concatenatedGrammar.append(self.nextNewInt)
            self.__concatenatedNTs.extend(nt for j in range(len(grammar[nt])))
            self.__concatenatedNTs.append(self.nextNewInt)
            self.__separatorInts.add(self.nextNewInt)
            self.__separatorIntsIndices.add(len(self.__concatenatedGrammar) - 1)
            self.nextNewInt += 2
            # print self.__concatenatedGrammar
            # print len(self.__concatenatedGrammar)


    # Loads the grammar from a grammar dictionary
    def initFromGrammarDic(self, grammar, dic):
        # print 'payam'
        # print grammar
        self.dic = dic
        counter = 0
        for nt in grammar:
            if counter <= nt:
                counter = nt + 1
            for rhs in grammar[nt]:
                for c in rhs:
                    if counter <= c:
                        counter = c + 1
        self.nextNewInt = counter
        if self.nextNewInt % 2 == 0:
            self.__nextNewContextInt = self.nextNewInt
            self.nextNewInt += 1
        else:
            self.__nextNewContextInt = self.nextNewInt + 1
        self.__concatenatedGrammar = []
        self.__concatenatedNTs = []
        self.__separatorInts = set([])
        self.__separatorIntsIndices = set([])
        for nt in grammar:
            for rhs in grammar[nt]:
                self.__concatenatedGrammar.extend(rhs)
                self.__concatenatedGrammar.append(self.nextNewInt)
                self.__concatenatedNTs.extend(nt for j in range(len(rhs)))
                self.__concatenatedNTs.append(self.nextNewInt)
                self.__separatorInts.add(self.nextNewInt)
                self.__separatorIntsIndices.add(len(self.__concatenatedGrammar) - 1)
                self.nextNewInt += 2
                # print 'aaaaaaaa'
                # print grammar
                # print 'bbbbb'
                # print self.__concatenatedGrammar
                # print self.__concatenatedNTs

    # ...........Main Algorithm........
    def gSGP(self, pairingEnabled, fixedGap, quiet, normalRepeatType, ctxRepeatType, costFunction,
             pairSearchMethod):
        self.__fixedGap = fixedGap
        self.__quietLog = quiet
        odd = False
        pairingEnabled = False
        firstRoundFinished = False
        while True:  # Main IRR loop
            # Logging Grammar Cost
            self.__logViaFlag(LogFlag.ConcatenationCostLog)
            self.__logViaFlag(LogFlag.RuleCostLog)

            (maximumRepeatGainValue, selectedRepeatOccs) = self.__retreiveMaximumGainRepeat(normalRepeatType,
                                                                                            CostFunction.EdgeCost)
            if maximumRepeatGainValue > 0:
                self.__logMessage('maxR ' + str(maximumRepeatGainValue) + ' : ' + str(self.__concatenatedGrammar[
                                                                                      selectedRepeatOccs[1][0]:
                                                                                      selectedRepeatOccs[1][0] +
                                                                                      selectedRepeatOccs[
                                                                                          0]]) + '\n')
                self.__replaceRepeat(selectedRepeatOccs)  # Replacing the chosen repeat
                self.__numberOfTimesRepeatPicked += 1
                self.__iterations += 1
            if maximumRepeatGainValue == -1:
                break

        self.__logMessage('---------------')
        self.__logMessage('Number of Times Iterations: ' + str(self.__iterations))
        self.__logMessage('Number of Times Picked Repeats: ' + str(self.__numberOfTimesRepeatPicked))
        self.__logMessage('Number of Times Picked Pairs: ' + str(self.__numberOfTimesPairPicked))

    # Returns the cost of the grammar according to the selected costFunction
    def grammarCost(self, costFunction):
        if costFunction == CostFunction.ConcatenationCost:
            if not self.__fixedGap:
                return len(self.__concatenatedGrammar) - 2 * len(self.__separatorInts)
            else:
                return len(self.__concatenatedGrammar) - 2 * len(
                    self.__separatorInts) + self.__numberOfTimesPairPicked
        if costFunction == CostFunction.RuleCost:
            if not self.__fixedGap:
                return len(self.__concatenatedGrammar)
            else:
                return len(self.__concatenatedGrammar) - self.__fixedGapSavedCost
        if costFunction == CostFunction.EdgeCost:
            if not self.__fixedGap:
                return len(self.__concatenatedGrammar) - len(self.__separatorInts)
            else:
                return len(self.__concatenatedGrammar) - len(self.__separatorInts) + self.__numberOfTimesPairPicked

    def customPrint(self, string):
        nt = string.split('--')[0]
        string = string.split('--')[1]
        array = map(int, string.split(', '))
        print  nt, '-> ',
        for i in range(len(array)):
            print  self.dic[array[i]],

    # ...........Printing Functions........
    # Prints the grammar, optionally in integer form if intGrammarPrint==True
    def printGrammar(self, intGrammarPrint):
        # print self.__concatenatedGrammar
        # print len(self.__concatenatedGrammar)
        # print self.__separatorInts
        # print len(self.__separatorInts)
        print 'GrammarCost(Concats):', str(self.grammarCost(CostFunction.ConcatenationCost))
        print 'GrammarCost(Edges):', str(self.grammarCost(CostFunction.EdgeCost))
        print 'GrammarCost:', str(self.grammarCost(CostFunction.RuleCost))
        print
        Grammar = self.__concatenatedGrammar
        NTs = self.__concatenatedNTs
        separatorInts = self.__separatorInts
        Dic = self.dic
        rules = {}
        ntDic = {}
        counter = 1
        NTsSorted = set([])
        # print '------------for debugging begin'
        # print Dic
        # print Grammar
        # print NTs
        # print '------------for debugging end'
        for i in range(len(NTs)):
            if NTs[i] not in ntDic and NTs[i] not in separatorInts:
                NTsSorted.add(NTs[i])
                # ntDic[NTs[i]] = 'N'+str(counter)
                # rules['N'+str(counter)] = ''
                ntDic[NTs[i]] = 'N' + str(NTs[i])
                rules['N' + str(NTs[i])] = ''
                counter += 1
        for i in range(len(Grammar)):
            if Grammar[i] not in NTsSorted:
                if Grammar[i] not in separatorInts:
                    if not intGrammarPrint:
                        try:
                            rules[ntDic[NTs[i]]] = rules[ntDic[NTs[i]]] + ' ' + Dic[Grammar[i]]
                        except:
                            print Grammar[i], NTs[i]
                            raise
                    else:
                        rules[ntDic[NTs[i]]] = rules[ntDic[NTs[i]]] + ' ' + str(Grammar[i])
                else:
                    rules[ntDic[NTs[i - 1]]] = rules[ntDic[NTs[i - 1]]] + ' ||'
            else:
                if not intGrammarPrint:
                    try:
                        rules[ntDic[NTs[i]]] = rules[ntDic[NTs[i]]] + ' ' + ntDic[Grammar[i]]
                    except:
                        print Grammar[i], NTs[i]
                        raise
                else:
                    rules[ntDic[NTs[i]]] = rules[ntDic[NTs[i]]] + ' ' + ntDic[Grammar[i]]
        NTsSorted = sorted(list(NTsSorted))
        ruleCounter = 0
        for nt in NTsSorted:
            if nt not in self.__ctxNtSet:
                if intGrammarPrint:
                    subrules = rules[ntDic[nt]].rstrip(' ||').split(' ||')
                    for s in subrules:
                        print ntDic[nt] + ' ->' + s
                else:
                    subrules = rules[ntDic[nt]].rstrip(' ||').split(' ||')
                    for s in subrules:
                        print ntDic[nt] + ' -> ' + s
            ruleCounter += 1
            if ruleCounter == 1:
                for nt in sorted(list(self.__ctxNtSet)):
                    if intGrammarPrint:
                        subrules = rules[ntDic[nt]].rstrip(' ||').split(' ||')
                        for s in subrules:
                            print ntDic[nt] + ' ->' + s
                    else:
                        subrules = rules[ntDic[nt]].rstrip(' ||').split(' ||')
                        for s in subrules:
                            print ntDic[nt] + ' -> ' + s
                            # printFromDic(listOfIndices, Dic):
                            # ''.join([Dic[ch] for ch in listOfIndices])

    # Prints all rules corresponding to the nonterminal n (int)
    def __printRules(self, n):
        return ''

    # Prints all yields corresponding to the nonterminal n (int)
    def __yieldOfNT(self, n):
        print 'Yield'

    # Prints the yield corresponding to the rule r
    def __yieldOfRule(self, r):
        print 'Yield'

    # Log via flags
    def __logViaFlag(self, flag):
        if not self.__quietLog:
            if flag == LogFlag.ConcatenationCostLog:
                sys.stderr.write(
                    'GrammarCost(Concats): ' + str(self.grammarCost(CostFunction.ConcatenationCost)) + '\n')
                # print(str('GrammarCost(Concats): ' + str(self.grammarCost(CostFunction.ConcatenationCost))))
            if flag == LogFlag.RuleCostLog:
                sys.stderr.write('GrammarCost: ' + str(self.grammarCost(CostFunction.RuleCost)) + '\n')
                # print(str('GrammarCost: ' + str(self.grammarCost(CostFunction.RuleCost))))

    # Log custom message
    def __logMessage(self, message):
        if not self.__quietLog:
            sys.stderr.write(str(message) + '\n')
            # print(str(message))

    # ...........Utility Functions........
    # Converts the input data into an integer sequence, returns the integer sequence and the dictionary for recovering orginal letters
    def __preprocessInput(self, inputFile, charSeq=SequenceType.Character, noNewLineFlag=True):
        # print 'sssssssssssssssssssssssss', charSeq
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
            # print ';;;;;;;;;;;;;;;;;', letterDict
            return (newContents.rstrip('\n'), letterDict)
        if charSeq == SequenceType.Integer:  # input is space seperated integers
            newContents = []
            letterDict = {}
            for line in inputFile:
                try:
                    for sym in line.split():
                        letterDict[int(sym)] = sym
                except ValueError:
                    raise ValueError('Input file is not in space-separated integer form: %s' % sym)
                newContents.append(line.strip())
                newContents = " ".join(newContents)
                # for i in range(len(line)):
                #    if line[i] not in [str(_x) for _x in range(10)] and line[i] not in {' ','\n'}:

            return (newContents, letterDict)
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
            # print newContents
            return (newContents.rstrip('\n'), wordDict)

    def __preprocessInputStrings(self, inputFile, charSeq=SequenceType.Character, noNewLineFlag=True):
        # print 'sssssssssssssssssssssssss', charSeq
        if charSeq == SequenceType.Character:  # Building an integer-spaced sequence from the input string
            letterDict = {}
            counterDict = {}
            i = 0
            counter = 1
            newContents = ''
            if noNewLineFlag:
                line = inputFile
                for i in range(len(line)):
                    if line[i] not in counterDict:
                        letterDict[counter] = line[i]
                        counterDict[line[i]] = counter
                        counter += 1
                    newContents += str(counterDict[line[i]]) + ' '
            else:
                for line in inputFile.split('\n'):
                    line = line.rstrip('\n')
                    for i in range(len(line)):
                        if line[i] not in counterDict:
                            letterDict[counter] = line[i]
                            counterDict[line[i]] = counter
                            counter += 1
                        newContents += str(counterDict[line[i]]) + ' '
                    newContents += '\n'
            # print ';;;;;;;;;;;;;;;;;', letterDict
            return (newContents.rstrip('\n'), letterDict)
        if charSeq == SequenceType.Integer:  # input is space seperated integers
            newContents = []
            letterDict = {}
            for line in inputFile:
                try:
                    for sym in line.split():
                        letterDict[int(sym)] = sym
                except ValueError:
                    raise ValueError('Input file is not in space-separated integer form: %s' % sym)
                newContents.append(line.strip())
                newContents = " ".join(newContents)
                # for i in range(len(line)):
                #    if line[i] not in [str(_x) for _x in range(10)] and line[i] not in {' ','\n'}:

            return (newContents, letterDict)
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
            # print newContents
            return (newContents.rstrip('\n'), wordDict)

    # Replaces a repeat's occurrences with a new nonterminal and creates a new rule in the grammar
    def __replaceRepeat(self, (repeatLength, (repeatOccs))):
        repeat = self.__concatenatedGrammar[repeatOccs[0]:repeatOccs[0] + repeatLength]
        newTmpConcatenatedGrammar = []
        newTmpConcatenatedNTs = []
        prevIndex = 0
        for i in repeatOccs:
            newTmpConcatenatedGrammar += self.__concatenatedGrammar[prevIndex:i] + [self.nextNewInt]
            newTmpConcatenatedNTs += self.__concatenatedNTs[prevIndex:i] + [self.__concatenatedNTs[i]]
            prevIndex = i + repeatLength
        self.__concatenatedGrammar = newTmpConcatenatedGrammar + self.__concatenatedGrammar[prevIndex:]
        self.__concatenatedNTs = newTmpConcatenatedNTs + self.__concatenatedNTs[prevIndex:]
        self.__concatenatedGrammar = self.__concatenatedGrammar + repeat
        self.__concatenatedNTs = self.__concatenatedNTs + [self.nextNewInt for j in range(repeatLength)]
        self.__logMessage('Added Nonterminal: ' + str(self.nextNewInt))
        self.nextNewInt += 2
        self.__concatenatedGrammar = self.__concatenatedGrammar + [self.nextNewInt]
        self.__concatenatedNTs = self.__concatenatedNTs + [self.nextNewInt]
        self.__separatorInts.add(self.nextNewInt)
        self.__separatorIntsIndices = set([])
        for i in range(len(self.__concatenatedGrammar)):
            if self.__concatenatedGrammar[i] in self.__separatorInts:
                self.__separatorIntsIndices.add(i)
        self.nextNewInt += 2

    def replaceRepeat(self, repeatLength, repeatOccs):
        repeat = self.__concatenatedGrammar[repeatOccs[0]:repeatOccs[0] + repeatLength]
        newTmpConcatenatedGrammar = []
        newTmpConcatenatedNTs = []
        prevIndex = 0
        for i in repeatOccs:
            newTmpConcatenatedGrammar += self.__concatenatedGrammar[prevIndex:i] + [self.nextNewInt]
            newTmpConcatenatedNTs += self.__concatenatedNTs[prevIndex:i] + [self.__concatenatedNTs[i]]
            prevIndex = i + repeatLength
        self.__concatenatedGrammar = newTmpConcatenatedGrammar + self.__concatenatedGrammar[prevIndex:]
        self.__concatenatedNTs = newTmpConcatenatedNTs + self.__concatenatedNTs[prevIndex:]
        self.__concatenatedGrammar = self.__concatenatedGrammar + repeat
        self.__concatenatedNTs = self.__concatenatedNTs + [self.nextNewInt for j in range(repeatLength)]
        self.__logMessage('Added Nonterminal: ' + str(self.nextNewInt))
        self.nextNewInt += 2
        self.__concatenatedGrammar = self.__concatenatedGrammar + [self.nextNewInt]
        self.__concatenatedNTs = self.__concatenatedNTs + [self.nextNewInt]
        self.__separatorInts.add(self.nextNewInt)
        self.__separatorIntsIndices = set([])
        for i in range(len(self.__concatenatedGrammar)):
            if self.__concatenatedGrammar[i] in self.__separatorInts:
                self.__separatorIntsIndices.add(i)
        self.nextNewInt += 2

    def replaceRepeatEvo(self, nt, repeatLength, repeatOccs):
        repeat = self.__concatenatedGrammar[repeatOccs[0]:repeatOccs[0] + repeatLength]
        newTmpConcatenatedGrammar = []
        newTmpConcatenatedNTs = []
        prevIndex = 0
        for i in repeatOccs:
            newTmpConcatenatedGrammar += self.__concatenatedGrammar[prevIndex:i] + [nt]
            newTmpConcatenatedNTs += self.__concatenatedNTs[prevIndex:i] + [self.__concatenatedNTs[i]]
            prevIndex = i + repeatLength
        self.__concatenatedGrammar = newTmpConcatenatedGrammar + self.__concatenatedGrammar[prevIndex:]
        self.__concatenatedNTs = newTmpConcatenatedNTs + self.__concatenatedNTs[prevIndex:]
        # self.__concatenatedGrammar = self.__concatenatedGrammar + repeat
        # self.__concatenatedNTs = self.__concatenatedNTs + [nt for j in range(repeatLength)]
        # self.__logMessage('Replaced Nonterminal: ' + str(nt))
        # self.__concatenatedGrammar = self.__concatenatedGrammar + [self.nextNewInt]
        # self.__concatenatedNTs = self.__concatenatedNTs + [self.nextNewInt]
        # self.__separatorInts.add(self.nextNewInt)
        # self.__separatorIntsIndices = set([])
        # for i in range(len(self.__concatenatedGrammar)):
        #     if self.__concatenatedGrammar[i] in self.__separatorInts:
        #         self.__separatorIntsIndices.add(i)
        # self.nextNewInt += 2

    # Retrieves the maximum-gain repeat (randomizes within ties).
    # Output is a tuple: "(RepeatGain, (RepeatLength, (RepeatOccurrences)))"
    # 1st entry of output is the maximum repeat gain value
    # 2nd entry of output is a tuple of form: "(selectedRepeatLength, selectedRepeatOccsList)"
    def __retreiveMaximumGainRepeat(self, repeatClass, costFunction):
        repeats = self.__extractRepeats(repeatClass)
        maxRepeatGain = 0
        candidateRepeats = []
        for r in repeats:  # Extracting maximum repeat
            repeatStats = r.split()
            repeatOccs = self.__extractNonoverlappingRepeatOccurrences(int(repeatStats[0]),
                                                                       map(int, repeatStats[2][1:-1].split(',')))
            if maxRepeatGain < self.__repeatGain(int(repeatStats[0]), len(repeatOccs), costFunction):
                maxRepeatGain = self.__repeatGain(int(repeatStats[0]), len(repeatOccs), costFunction)
                candidateRepeats = [(int(repeatStats[0]), len(repeatOccs), repeatOccs)]
            else:
                if maxRepeatGain > 0 and maxRepeatGain == self.__repeatGain(int(repeatStats[0]), len(repeatOccs),
                                                                            costFunction):
                    candidateRepeats.append((int(repeatStats[0]), len(repeatOccs), repeatOccs))
        if (len(candidateRepeats) == 0):
            return (-1, (0, []))
        # Randomizing between candidates with maximum gain
        # selectedRepeatStats = candidateRepeats[random.randrange(len(candidateRepeats))]
        selectedRepeatStats = candidateRepeats[0]
        selectedRepeatLength = selectedRepeatStats[0]
        selectedRepeatOccs = sorted(selectedRepeatStats[2])
        return (maxRepeatGain, (selectedRepeatLength, selectedRepeatOccs))

    def retreiveMaximumGainRepeat(self, repeatClass, costFunction):
        repeats = self.__extractRepeats(repeatClass)
        maxRepeatGain = 0
        candidateRepeats = []
        for r in repeats:  # Extracting maximum repeat
            repeatStats = r.split()
            repeatOccs = self.__extractNonoverlappingRepeatOccurrences(int(repeatStats[0]),
                                                                       map(int, repeatStats[2][1:-1].split(',')))
            if maxRepeatGain < self.__repeatGain(int(repeatStats[0]), len(repeatOccs), costFunction):
                maxRepeatGain = self.__repeatGain(int(repeatStats[0]), len(repeatOccs), costFunction)
                candidateRepeats = [(int(repeatStats[0]), len(repeatOccs), repeatOccs)]
            else:
                if maxRepeatGain > 0 and maxRepeatGain == self.__repeatGain(int(repeatStats[0]), len(repeatOccs),
                                                                            costFunction):
                    candidateRepeats.append((int(repeatStats[0]), len(repeatOccs), repeatOccs))
        if (len(candidateRepeats) == 0):
            return {'score': -1, 'length': 0, 'occs': []}
        # Randomizing between candidates with maximum gain
        # selectedRepeatStats = candidateRepeats[random.randrange(len(candidateRepeats))]
        selectedRepeatStats = candidateRepeats[0]
        selectedRepeatLength = selectedRepeatStats[0]
        selectedRepeatOccs = sorted(selectedRepeatStats[2])
        return {'score': maxRepeatGain, 'length': selectedRepeatLength, 'occs': selectedRepeatOccs}

    # Returns the repeat gain, according to the chosen cost function
    def __repeatGain(self, repeatLength, repeatOccsLength, costFunction):
        if costFunction == CostFunction.ConcatenationCost:
            return (repeatLength - 1) * (repeatOccsLength - 1)
        if costFunction == CostFunction.EdgeCost:
            return (repeatLength - 1) * (repeatOccsLength - 1) - 1
        if costFunction == CostFunction.RuleCost:
            return (repeatLength - 1) * (repeatOccsLength - 1) - 2

    # Extracts the designated class of repeats (Assumes ./repeats binary being in the same directory)
    # Output is a string, each line containing: "RepeatLength    NumberOfOccurrence  (CommaSeparatedOccurrenceIndices)"
    def __extractRepeats(self, repeatClass):
        # with open(self.TMP_OUTPUT_FILE, "w") as text_file:
        # text_file.write(' '.join(map(str,self.__concatenatedGrammar)))
        # text_file.close()
        # os.system("./repeats -i -r "+repeatClass+" -n 2 -p sol " + self.TMP_OUTPUT_FILE + " > " + self.TMP_INPUT_FILE)
        # print 'y1'
        # process = subprocess.Popen(["./repeats11", "-i", "-r"+repeatClass, "-n2", "-psol"],stdout=subprocess.PIPE, stdin=subprocess.PIPE, stderr=subprocess.STDOUT)
        process = subprocess.Popen(["./repeats11", "-i", "-r" + repeatClass, "-n1", "-psol"],
                                   stdout=subprocess.PIPE, stdin=subprocess.PIPE, stderr=subprocess.STDOUT)
        process.stdin.write(' '.join(map(str, self.__concatenatedGrammar)))
        text_file = ''
        while process.poll() is None:
            output = process.communicate()[0].rstrip()
            text_file += output
        process.wait()
        repeats = []
        firstLine = False
        for line in text_file.splitlines():
            if firstLine == False:
                firstLine = True
                continue
            repeats.append(line.rstrip('\n'))

        # process = subprocess.Popen(["./repeats11", "-i", "-r"+repeatClass, "-n1", "-psolw"],stdout=subprocess.PIPE, stdin=subprocess.PIPE, stderr=subprocess.STDOUT)
        # process.stdin.write(' '.join(map(str,self.__concatenatedGrammar)))
        # text_file = ''
        # while process.poll() is None:
        #     output = process.communicate()[0].rstrip()
        #     text_file += output
        # process.wait()
        # repeats1=[]
        # firstLine = False
        # for line in text_file.splitlines():
        #     if firstLine == False:
        #         firstLine = True
        #         continue
        #     repeats1.append(line.rstrip('\n'))
        # print 'rrrrrrrrrrrrrr', repeats1
        return repeats

    # Extracts the non-overlapping occurrences of a repeat from a list of occurrences (scans from left to right)
    def __extractNonoverlappingRepeatOccurrences(self, repeatLength, occurrencesList):
        nonoverlappingIndices = []
        for i in range(len(occurrencesList)):
            if len(nonoverlappingIndices) > 0:
                if (nonoverlappingIndices[-1] + repeatLength <= occurrencesList[i]):  # Not already covered
                    nonoverlappingIndices += [occurrencesList[i]]
            else:
                nonoverlappingIndices += [occurrencesList[i]]
        # print '1 ' , repeatLength, ':', occurrencesList
        # print '2 ' , repeatLength, ':', nonoverlappingIndices
        return nonoverlappingIndices

    # Replaces a pair's occurrences with a new nonterminal, creates a new rule for the pairs and create corresponding rules for gaps in the grammar
    # Returns the occurrences of the (now repeated) context indices in the new concatenated grammar for use in next iteration
    def __replacePair(self, pairOccurrences):
        insideStringsSet = {}
        for o in pairOccurrences:
            insideString = ' '.join(map(str, self.__concatenatedGrammar[o[0][0]:o[0][1]]))
            if insideString in insideStringsSet:
                insideStringsSet[insideString].add(o)
            else:
                insideStringsSet[insideString] = set([o])
        print 'Inside Strings:', insideStringsSet.items()
        if len(insideStringsSet.items()) == 1:
            print insideStringsSet
            print 'single inside rule selected!'
            exit()
        usedRanges = self.__extractNonoverlappingPairOccurrences(pairOccurrences)
        print 'Inside Strings Ranges:', usedRanges
        newRepeatsList = []  # Used for next iteration, the case might happen that created repeats from contexts have equal gains as other repeats in the next iteration
        newRepeatsLength = usedRanges[0][2] + usedRanges[0][1] + 1
        newTmpConcatenatedGrammar = []
        newTmpConcatenatedNTs = []
        prevIndex = 0
        if self.__nextNewContextInt < self.nextNewInt - 1:
            self.__nextNewContextInt = self.nextNewInt - 1
        for i in range(len(usedRanges)):
            tmpRange = usedRanges[i]
            newTmpConcatenatedGrammar += self.__concatenatedGrammar[prevIndex:tmpRange[0][0]] + [
                self.__nextNewContextInt]
            newRepeatsList.append(len(newTmpConcatenatedGrammar) - 1 - tmpRange[1])
            newTmpConcatenatedNTs += self.__concatenatedNTs[prevIndex:tmpRange[0][0]] + [
                self.__concatenatedNTs[tmpRange[0][0] - 1]]
            prevIndex = tmpRange[0][1]
        newTmpConcatenatedGrammar += self.__concatenatedGrammar[prevIndex:]
        newTmpConcatenatedNTs += self.__concatenatedNTs[prevIndex:]
        currentNT = self.__nextNewContextInt
        self.__ctxNtSet.add(currentNT)
        print 'Added Nonterminal:', str(self.__nextNewContextInt)
        print 'Number of original occurrences:', len(pairOccurrences)
        print 'Number of non-overlapping occurrences:', len(usedRanges)
        self.__nextNewContextInt += 2
        # irredundantMiddles = set()
        for i in range(len(usedRanges)):
            tmpRange = usedRanges[i]
            # Avoiding to add extra middle strings when one is already added
            # if(tuple(self.__concatenatedGrammar[tmpRange[0][0]:tmpRange[0][1]]) in irredundantMiddles):
            #    continue
            # else:
            #    irredundantMiddles.add(tuple(self.__concatenatedGrammar[tmpRange[0][0]:tmpRange[0][1]]))
            newTmpConcatenatedGrammar += self.__concatenatedGrammar[tmpRange[0][0]:tmpRange[0][1]] + [
                self.nextNewInt]
            newTmpConcatenatedNTs += [currentNT for j in range(tmpRange[0][1] - tmpRange[0][0])] + [
                self.nextNewInt]
            self.__separatorInts.add(self.nextNewInt)
            self.nextNewInt += 2
        self.__separatorIntsIndices = set([])
        for i in range(len(newTmpConcatenatedGrammar)):
            if newTmpConcatenatedGrammar[i] in self.__separatorInts:
                self.__separatorIntsIndices.add(i)
        self.__concatenatedGrammar = newTmpConcatenatedGrammar
        self.__concatenatedNTs = newTmpConcatenatedNTs
        if self.__fixedGap:  # Correcting the extra cost in case of using fixed-gap contexts
            # self.__fixedGapSavedCost += len(usedRanges)-1
            self.__fixedGapSavedCost += len(usedRanges)  # The Extra improvement added after XRCE
        return (newRepeatsLength, newRepeatsList)

    # Retrieves the maximum-gain pair (first that is found).
    # Output is a tuple: "(RepeatGain, (RepeatLength, (RepeatOccurrences)))"
    # 1st entry of output is the maximum pair gain value
    # 2nd entry of output is a list of tuples of the form: "(GapOccurrenceRange,R1Length,R2Length)"
    def __retreiveMaximumGainPair(self, repeatClass, costFunction, pairSearchMethod):
        pairDic = self.__extractPairs(repeatClass, pairSearchMethod, costFunction)
        # print 'ddddddddddd', pairDic
        return self.__retreiveMaximumGainPairFromPairDic(pairDic, costFunction)

    # Retrieves the maximum-gain pair from a dictionary of {pair:occurrences} (first that is found)
    # 1st entry of output is the maximum pair gain value
    # 2nd entry of output is a list of tuples of the form: "(GapOccurrenceRange,R1Length,R2Length)"
    def __retreiveMaximumGainPairFromPairDic(self, pairDic, costFunction):
        maxPairGain = 0
        reducedRanges = []
        pairGainDic = {}
        for key in pairDic:
            r1Length = len(key[0])
            # r1Length = pairDic[key][0][1]
            r2Length = len(key[1])
            # r2Length = pairDic[key][0][2]
            pairDic[key] = self.__extractNonoverlappingPairOccurrences(pairDic[key])
            pairGainDic[key] = self.__pairGain(r1Length, r2Length, pairDic[key], costFunction)
        # print 'nonnnnnnnnnnnnn', pairDic
        # print 'gainnnnnnnnnnnnn', pairGainDic
        # print 'gramarrrrrrrrrrrr', self.__concatenatedGrammar
        if len(pairDic) != 0 and len(pairGainDic) != 0:
            sortedPairGains = sorted(pairGainDic.items(), key=operator.itemgetter(1), reverse=True)
            if (sortedPairGains[0])[1] > maxPairGain and (sortedPairGains[0])[1] != 0:
                maxPairGain = (sortedPairGains[0])[1]
                reducedRanges = pairDic[(sortedPairGains[0])[0]]
        if len(reducedRanges) == 0:
            return (-1, [])
        # Fix pair occurrences if chosen greedy pair search method
        # ---------
        return (maxPairGain, reducedRanges)

    # Returns the pair gain, according to the chosen cost function
    def __pairGain(self, r1Length, r2Length, pairOccs, costFunction):
        pairOccsLength = len(pairOccs)
        if costFunction == CostFunction.ConcatenationCost:
            if not self.__fixedGap:
                return (r1Length + r2Length - 4) * (pairOccsLength - 1) - 2
            else:
                return (r1Length + r2Length - 2) * (pairOccsLength - 1) - 4
        if costFunction == CostFunction.RuleCost:
            additionalGain = 0
            insideStringsSet = {}
            for o in pairOccs:
                insideString = ' '.join(map(str, self.__concatenatedGrammar[o[0][0]:o[0][1]]))
                if insideString in insideStringsSet:
                    insideStringsSet[insideString].add(o)
                else:
                    insideStringsSet[insideString] = set([o])
            if len(insideStringsSet.items()) == 1:
                return 0
            # for key in insideStringsSet:
            #     if len(key.split()) > 1 and len(insideStringsSet[key]) > 1:
            #         additionalGain += (len(insideStringsSet[key]) - 1)*(len(key.split())-1)-2
            if not self.__fixedGap:
                return (r1Length + r2Length - 2) * (pairOccsLength - 1) - 4
            else:
                # totalGain = (r1Length + r2Length-1)*(pairOccsLength-1)-5 + additionalGain
                totalGain = (r1Length + r2Length - 1) * (
                pairOccsLength - 1) - 4 + additionalGain  # Extra Gain Added after XRCE
                return totalGain

    # Extracts the designated class of repeated-contexts (Assumes ./repeats binary being in the same directory)
    # Output is a dictionary of the form: "((R1),(R2)):(GapOccurrenceRange,R1Length,R2Length)"
    def __extractPairs(self, repeatClass, pairSearchMethod, costFunction):
        ctxRepeats = self.__extractRepeats(repeatClass)
        # print 'cccccccccccc', ctxRepeats
        pairDic = {}
        allRepeatOccs = []
        # Storing repeats as tuples of "(RepeatLength, OccurrenceIndex)"
        for r in ctxRepeats:
            allRepeatOccs.extend(
                [(int((r.split())[0]), j) for j in list((map(int, ((r.split())[2])[1:-1].split(','))))])
        allRepeatOccs.extend([(-1, j) for j in
                              self.__separatorIntsIndices])  # Merging with separatorIntsIndices for easier detection of input strings' ends
        allRepeatOccs = sorted(allRepeatOccs, key=lambda x: (x[1], x[0]))
        # print self.__concatenatedGrammar
        # print
        if self.__fixedGap:
            pairDic = self.__fixedGapPairSearch(allRepeatOccs, costFunction)
        else:
            if pairSearchMethod == PairSearchMethod.ConstantLengthSearch:
                pairDic = self.__variableGapPairSearchWithConstantMaxGap(allRepeatOccs)
            if pairSearchMethod == PairSearchMethod.ExhausivePairSearch:
                pairDic = self.__exhausivePairSearch(allRepeatOccs)
            if pairSearchMethod == PairSearchMethod.GreedyPairSearch:
                pairDic = self.__greedyPairSearch(allRepeatOccs)
                # Filtering only non-overlapping pair occurrences
                # for key in pairDic:
                #     pairDic[key] = self.__extractNonoverlappingPairOccurrences(pairDic[key])
        return pairDic

    # Fixed-Gap pair search.
    # Input is the gap and the sorted list of all repeat occurrences: [(repeatLength, repeatOccurrenceIndex)]
    # Output is a dictionary of the form: "((R1),(R2)):(GapOccurrenceRange,R1Length,R2Length)"
    def __fixedGapPairSearch(self, repeatOccurrences, costFunction):
        pairDic = {}
        reverseRepeatOccs = {}
        reverseRepeatEnds = {}
        for repOcc in repeatOccurrences:
            if repOcc[1] not in self.__separatorIntsIndices:
                # print repOcc[1]
                if repOcc[1] in reverseRepeatOccs:
                    reverseRepeatOccs[repOcc[1]].append(repOcc[0])
                else:
                    reverseRepeatOccs[repOcc[1]] = [repOcc[0]]
                if repOcc[1] + repOcc[0] - 1 in reverseRepeatEnds:
                    reverseRepeatEnds[repOcc[1] + repOcc[0] - 1].append(repOcc[0])
                else:
                    reverseRepeatEnds[repOcc[1] + repOcc[0] - 1] = [repOcc[0]]
        maxGapGain = -1
        # minK = self.__MAX_LENGTH
        # for k in xrange(minK,self.__MAX_LENGTH):
        for k in xrange(1, self.__MAX_LENGTH + 1):
            # for k in xrange(3,4):
            sys.stderr.write(str(k) + '\n')
            tmpPairDic = {}
            currentStringRepsOccs = {}
            currentStringRepsEnds = {}
            currentStringStart = 0
            currentStringEnd = 0
            for index in range(len(self.__concatenatedGrammar)):
                if index in self.__separatorIntsIndices:
                    # print 'starts', currentStringRepsOccs
                    # print 'ends', currentStringRepsEnds
                    currentStringEnd = index
                    # print 's', currentStringStart
                    # print 'e', currentStringEnd
                    for currentIndex in range(currentStringStart, currentStringEnd):
                        if (currentStringRepsOccs.has_key(currentIndex + k + 1)) and (
                        currentStringRepsEnds.has_key(currentIndex)):
                            for repL1 in currentStringRepsEnds[currentIndex]:
                                for repL2 in currentStringRepsOccs[currentIndex + k + 1]:
                                    if tmpPairDic.has_key((tuple(
                                            self.__concatenatedGrammar[currentIndex - repL1 + 1:currentIndex + 1]),
                                                           tuple(self.__concatenatedGrammar[
                                                                 currentIndex + k + 1:currentIndex + k + 1 + repL2]))):
                                        tmpPairDic[(tuple(
                                            self.__concatenatedGrammar[currentIndex - repL1 + 1:currentIndex + 1]),
                                                    tuple(self.__concatenatedGrammar[
                                                          currentIndex + k + 1:currentIndex + k + 1 + repL2]))].append(
                                            ((currentIndex + 1, currentIndex + k + 1), repL1, repL2))
                                    else:
                                        tmpPairDic[(tuple(
                                            self.__concatenatedGrammar[currentIndex - repL1 + 1:currentIndex + 1]),
                                                    tuple(self.__concatenatedGrammar[
                                                          currentIndex + k + 1:currentIndex + k + 1 + repL2]))] = [
                                            ((currentIndex + 1, currentIndex + k + 1), repL1, repL2)]
                    currentStringStart = index + 1
                    currentStringRepsOccs = {}
                    currentStringRepsEnds = {}
                    # print 'tmpPairDic', tmpPairDic
                else:
                    if index in reverseRepeatOccs:
                        currentStringRepsOccs[index] = reverseRepeatOccs[index]
                    if index in reverseRepeatEnds:
                        currentStringRepsEnds[index] = reverseRepeatEnds[index]
            # for key in tmpPairDic:
            #     tmpPairDic[key] = self.__extractNonoverlappingPairOccurrences(tmpPairDic[key])
            (maxPairGain, reducedRanges) = self.__retreiveMaximumGainPairFromPairDic(tmpPairDic, costFunction)
            if maxPairGain > maxGapGain:
                pairDic = tmpPairDic
                maxGapGain = maxPairGain
        return pairDic

    # Variable-Gap pair search.
    # Input is the gap and the sorted list of all repeat occurrences: [(repeatLength, repeatOccurrenceIndex)]
    # Output is a dictionary of the form: "((R1),(R2)):(GapOccurrenceRange,R1Length,R2Length)"
    def __variableGapPairSearchWithConstantMaxGap(self, repeatOccurrences):
        # pairDic = {}
        reverseRepeatOccs = {}
        reverseRepeatEnds = {}
        for repOcc in repeatOccurrences:
            if repOcc[1] not in self.__separatorIntsIndices:
                # print repOcc[1]
                if repOcc[1] in reverseRepeatOccs:
                    reverseRepeatOccs[repOcc[1]].append(repOcc[0])
                else:
                    reverseRepeatOccs[repOcc[1]] = [repOcc[0]]
                if repOcc[1] + repOcc[0] - 1 in reverseRepeatEnds:
                    reverseRepeatEnds[repOcc[1] + repOcc[0] - 1].append(repOcc[0])
                else:
                    reverseRepeatEnds[repOcc[1] + repOcc[0] - 1] = [repOcc[0]]
        maxGapGain = -1
        # minK = self.__MAX_LENGTH
        # for k in xrange(minK,self.__MAX_LENGTH):
        for k in xrange(1, self.__MAX_LENGTH):
            sys.stderr.write(str(k) + '\n')
            tmpPairDic = {}
            currentStringRepsOccs = {}
            currentStringRepsEnds = {}
            currentStringStart = 0
            currentStringEnd = 0
            for index in range(len(self.__concatenatedGrammar)):
                if index in self.__separatorIntsIndices:
                    currentStringEnd = index
                    for currentIndex in range(currentStringStart, currentStringEnd):
                        if (currentStringRepsOccs.has_key(currentIndex + k + 1)) and (
                        currentStringRepsEnds.has_key(currentIndex)):
                            for repL1 in currentStringRepsEnds[currentIndex]:
                                for repL2 in currentStringRepsOccs[currentIndex + k + 1]:
                                    if tmpPairDic.has_key((tuple(
                                            self.__concatenatedGrammar[currentIndex - repL1 + 1:currentIndex + 1]),
                                                           tuple(self.__concatenatedGrammar[
                                                                 currentIndex + k + 1:currentIndex + k + 1 + repL2]))):
                                        tmpPairDic[(tuple(
                                            self.__concatenatedGrammar[currentIndex - repL1 + 1:currentIndex + 1]),
                                                    tuple(self.__concatenatedGrammar[
                                                          currentIndex + k + 1:currentIndex + k + 1 + repL2]))].append(
                                            ((currentIndex + 1, currentIndex + k + 1), repL1, repL2))
                                    else:
                                        tmpPairDic[(tuple(
                                            self.__concatenatedGrammar[currentIndex - repL1 + 1:currentIndex + 1]),
                                                    tuple(self.__concatenatedGrammar[
                                                          currentIndex + k + 1:currentIndex + k + 1 + repL2]))] = [
                                            ((currentIndex + 1, currentIndex + k + 1), repL1, repL2)]
                    currentStringStart = index + 1
                    currentStringRepsOccs = {}
                    currentStringRepsEnds = {}
                else:
                    if index in reverseRepeatOccs:
                        currentStringRepsOccs[index] = reverseRepeatOccs[index]
                    if index in reverseRepeatEnds:
                        currentStringRepsEnds[index] = reverseRepeatEnds[index]
                        # for key in tmpPairDic:
                        #     tmpPairDic[key] = self.__extractNonoverlappingPairOccurrences(tmpPairDic[key])
                        # (maxPairGain, reducedRanges) = self.__retreiveMaximumGainPairFromPairDic(tmpPairDic, costFunction)
                        # if maxPairGain > maxGapGain:
                        #    pairDic = tmpPairDic
                        #    maxGapGain = maxPairGain
        return tmpPairDic

    # Exhausive variable-length gap pair search.
    # Input is the sorted list of all repeat occurrences: [(repeatLength, repeatOccurrenceIndex)]
    # Output is a dictionary of the form: "((R1),(R2)):(GapOccurrenceRange,R1Length,R2Length)"
    def __exhausivePairSearch(self, repeatOccurrences):
        pairDic = {}
        currentStringPairOccs = []
        for r in repeatOccurrences:  # Scanning pair occurrences
            if r[1] in self.__separatorIntsIndices:  # Reached the end of an input string
                for k in range(len(currentStringPairOccs)):  # Greedy Pairing
                    # for r1 in currentStringPairOccs:
                    r1 = currentStringPairOccs[k]
                    for j in range(len(currentStringPairOccs) - k - 1):
                        # for r2 in currentStringPairOccs:
                        r2 = currentStringPairOccs[k + 1 + j]
                        r1Length = r1[0]
                        r2Length = r2[0]
                        oc1 = r1[1]
                        oc2 = r2[1]
                        if (oc2 < oc1 or oc1 + r1Length >= oc2):
                            continue
                            # Large gap filter
                            # gap = 2
                            # if not (oc2-(oc1+r1Length) >= gap):
                            # continue
                        # hash((tuple(self.__concatenatedGrammar[oc1:oc1+r1Length]),tuple(self.__concatenatedGrammar[oc2:oc2+r2Length])))
                        newPair = (tuple(self.__concatenatedGrammar[oc1:oc1 + r1Length]),
                                   tuple(self.__concatenatedGrammar[oc2:oc2 + r2Length]))
                        if newPair in pairDic:
                            pairDic[newPair].append(((oc1 + r1Length, oc2), r1Length, r2Length))
                            # pairDic[(repeatIndexHashes[(r1Length,oc1)],repeatIndexHashes[(r2Length,oc2)])].append(((oc1+r1Length,oc2),r1Length,r2Length))
                        else:
                            pairDic[newPair] = [((oc1 + r1Length, oc2), r1Length, r2Length)]
                            # pairDic[(repeatIndexHashes[(r1Length,oc1)],repeatIndexHashes[(r2Length,oc2)])] = [((oc1+r1Length,oc2),r1Length,r2Length)]
                currentStringPairOccs = []
            else:
                currentStringPairOccs.append(r)
        return pairDic

    # Greedy variable-length gap pair search.
    # Input is the sorted list of all repeat occurrences: [(repeatLength, repeatOccurrenceIndex)]
    # Output is a dictionary of the form: "((R1),(R2)):(GapOccurrenceRange,R1Length,R2Length)"
    def __greedyPairSearch(self, repeatOccurrences):
        pairDic = {}
        pairStart = -1  # Indicates the start of a pair
        pairEnd = -1  # Indicates the ending of a pair
        i = 0
        newString = True
        identifiedPairs = []
        while i < len(repeatOccurrences):  # Scanning pair occurrences
            if repeatOccurrences[i][1] in self.__separatorIntsIndices:  # Reached the end of an input string
                newString = True
                i += 1
            else:
                if newString:
                    pairStart = repeatOccurrences[i]
                    j = i + 1
                    validStartings = [pairStart]
                    while j < len(repeatOccurrences) and repeatOccurrences[j][1] == pairStart[
                        1]:  # Scanning all repeats starting at the same index as pairStart
                        validStartings.append(repeatOccurrences[j])
                        # Selecting the shortest repeat as pairStart
                        if pairStart[0] > repeatOccurrences[j][0]:
                            pairStart = repeatOccurrences[j]
                        j += 1
                    pairStart = random.choice(validStartings)
                    i = j
                    while i < len(repeatOccurrences) and repeatOccurrences[i][1] <= pairStart[1] + pairStart[
                        0]:  # Skipping overlapping repeats and fixing the problem of having a gap with zero length
                        i += 1
                    newString = False
                else:
                    pairEnd = repeatOccurrences[i]
                    j = i + 1
                    validEndings = [pairEnd]
                    while j < len(repeatOccurrences) and repeatOccurrences[j][1] == pairEnd[
                        1]:  # Scanning all repeats starting at the same index as pairEnd
                        validEndings.append(repeatOccurrences[j])
                        # Selecting the shortest repeat as pairEnd
                        if pairEnd[0] > repeatOccurrences[j][0]:
                            pairEnd = repeatOccurrences[j]
                        j += 1
                    pairEnd = random.choice(validEndings)
                    i = j
                    while i < len(repeatOccurrences) and repeatOccurrences[i][1] <= pairEnd[1] + pairEnd[
                        0]:  # Setting the start position for next pair
                        i += 1
                    # identifiedPairs.append((tuple(self.__concatenatedGrammar[pairStart[1]:pairStart[1]+pairStart[0]]),tuple(self.__concatenatedGrammar[pairEnd[1]:pairEnd[1]+pairEnd[0]])))
                    # identifiedPairs.append((pairStart[1],pairEnd[1]))
                    if (tuple(self.__concatenatedGrammar[pairStart[1]:pairStart[1] + pairStart[0]]),
                        tuple(self.__concatenatedGrammar[pairEnd[1]:pairEnd[1] + pairEnd[0]])) in pairDic:
                        pairDic[(tuple(self.__concatenatedGrammar[pairStart[1]:pairStart[1] + pairStart[0]]),
                                 tuple(self.__concatenatedGrammar[pairEnd[1]:pairEnd[1] + pairEnd[0]]))].append(
                            ((pairStart[1] + pairStart[0], pairEnd[1]), pairStart[0], pairEnd[0]))
                    else:
                        pairDic[(tuple(self.__concatenatedGrammar[pairStart[1]:pairStart[1] + pairStart[0]]),
                                 tuple(self.__concatenatedGrammar[pairEnd[1]:pairEnd[1] + pairEnd[0]]))] = [
                            ((pairStart[1] + pairStart[0], pairEnd[1]), pairStart[0], pairEnd[0])]
                    newString = True
                    # for p in identifiedPairs:
                    # print p,
        # print
        return pairDic

    # Extracts non-overlapping occurrences of a pair from a all lists of its occurrences in exhausive pair search method
    # Input is of the form of the values from pairDic, scans from left to right)
    def __extractNonoverlappingPairOccurrences(self, occurrencesList):
        gain = 0
        # reducedRanges = sorted(pairDic[key], key=lambda x: (x[0][0],x[0][1]))
        reducedRanges = sorted(occurrencesList, key=lambda x: (x[0][0], x[0][1]))
        usedRanges = []
        if not self.__fixedGap:
            for i in range(len(reducedRanges)):
                invalidPair = False
                tmpRange = reducedRanges[i]
                # for candidateRange in usedRanges:#excluding overlapping occurrences
                if (len(usedRanges) > 0):
                    candidateRange = usedRanges[-1]
                    # if invalidPair:
                    # break
                    if (candidateRange[0][0] >= tmpRange[0][0] and candidateRange[0][0] <= tmpRange[0][1]) or (
                            candidateRange[0][1] >= tmpRange[0][0] and candidateRange[0][1] <= tmpRange[0][1]) or (
                                candidateRange[0][0] - candidateRange[1] >= tmpRange[0][0] and candidateRange[0][
                        0] - candidateRange[1] <= tmpRange[0][1]) or (
                                candidateRange[0][1] + candidateRange[2] >= tmpRange[0][0] and candidateRange[0][
                        1] + candidateRange[2] <= tmpRange[0][1]):
                        invalidPair = True
                if not invalidPair:
                    usedRanges += [tmpRange]
        else:  # reducing fixed-gaps, only store the gap with highest number of occurrences
            gapDic = {}
            for r in reducedRanges:
                gapDic[r[0][1] - r[0][0]] = []
            for r in reducedRanges:
                gapDic[r[0][1] - r[0][0]].append(r)
            tmpUsedRanges = []
            for gap in gapDic:
                # for i in range(len(reducedRanges)):
                for i in range(len(gapDic[gap])):
                    invalidPair = False
                    tmpRange = gapDic[gap][i]
                    # for candidateRange in tmpUsedRanges:#excluding overlapping occurrences
                    if (len(tmpUsedRanges) > 0):
                        candidateRange = tmpUsedRanges[-1]
                        # if invalidPair:
                        # break
                        if (candidateRange[0][0] >= tmpRange[0][0] and candidateRange[0][0] <= tmpRange[0][1]) or (
                                candidateRange[0][1] >= tmpRange[0][0] and candidateRange[0][1] <= tmpRange[0][
                            1]) or (candidateRange[0][0] - candidateRange[1] >= tmpRange[0][0] and
                                                candidateRange[0][0] - candidateRange[1] <= tmpRange[0][1]) or (
                                    candidateRange[0][1] + candidateRange[2] >= tmpRange[0][0] and
                                    candidateRange[0][1] + candidateRange[2] <= tmpRange[0][1]):
                            invalidPair = True
                    if not invalidPair:
                        tmpUsedRanges += [tmpRange]
                if len(usedRanges) < len(tmpUsedRanges):
                    usedRanges = tmpUsedRanges
                tmpUsedRanges = []
        return usedRanges

    def grammarDic(self):
        grammar = {}
        prevIndex = 0
        sepsInd = sorted(list(self.__separatorIntsIndices))
        for i in range(len(sepsInd)):
            rhs = self.__concatenatedGrammar[prevIndex:sepsInd[i]]
            nt = self.__concatenatedNTs[prevIndex]
            prevIndex = sepsInd[i] + 1
            if nt in grammar:
                grammar[nt].append(rhs)
            else:
                grammar[nt] = [rhs]
        return grammar

    def ntYield(self, grammar, inputNT):
        for rhs in grammar[inputNT]:
            stack = copy.deepcopy(rhs)
            ntStack = [inputNT]
            grammarText = []
            while len(stack) > 0:
                c = stack.pop(0)
                if c == -2:  # Repeat NT recursion
                    ntStack.pop()
                    continue
                if c in grammar:
                    ntStack.append(c)
                    stack = grammar[c][0] + [-2] + stack
                else:
                    grammarText.append(c)
        return grammarText

    def getMaxEvoR(self, ntYields):
        rsoList = []
        for nt in ntYields:
            rsoList.append({'nt': nt, 'sub': ntYields[nt][0], 'length': len(ntYields[nt][0]), 'occs': [],
                            'score': 0})  # (substring, [[TargetIndex, occurrences]], overallScore)
            occ = 0
            tmpOccs = KnuthMorrisPratt(self.__concatenatedGrammar, ntYields[nt][0])
            removeOccs = []
            for i in tmpOccs:
                if (self.__concatenatedNTs[i] == nt):
                    removeOccs.append(i)
            tmpOccs = [item for item in tmpOccs if item not in removeOccs]
            occ += len(tmpOccs)
            if len(tmpOccs) > 0:
                rsoList[-1]['occs'].extend(tmpOccs)
            if (occ - 1) * len(ntYields[nt][0]) > 0:
                # rsoList[-1]['score'] = (occ - 1) * len(ntYields[nt][0])
                rsoList[-1]['score'] = (occ) * (len(ntYields[nt][0]) - 1)
        maxrsoScore = 0
        maxrso = {'nt': [], 'sub': [], 'length': 0, 'occs': [],
                  'score': -1}
        for rso in rsoList:
            if maxrsoScore < rso['score']:
                maxrsoScore = rso['score']
                maxrso = rso
        return maxrso
#Sets the value of parameters
def processParams(argv):
    aFlag = False #if false, the algorithm becomes equivalent to IRR-MC
    fFlag = False #if true along with p flag, only reduces the fixed-gap contexts
    chFlag = SequenceType.Character #if false, accepts integer sequence
    printIntsGrammar = False #if true, prints the grammar in integer sequence format
    quietLog = False #if true, disables logging
    rFlag = 'mr' #repeat type (for normal repeat replacements)
    cFlag = 'mr' #repeat type (for context replacements)
    pairFlag = 'c' #context pair search method, either exhausive or greedy
    functionFlag = 'r' #cost function to be optimized
    noNewLineFlag = False #if false, considers each line as a separate string
    loadGrammarFlag = False
    gap = 50

    usage = """Usage:
    [-a]: specifies the algorithm flags
        p - if set, the algorithm enforces a repeat reduction after identifying each context-reduction
        f - if set along with p flag, only reduces the fixed-gap contexts
    [-t]: choosing between character sequence, integer sequence or space-separated sequence
        c - character sequence
        i - integer sequence
        s - space-separated sequence
    [-p]: specifies grammar printing option
        i - prints the grammar in integer sequence format
    [-q]: disables logging
    [-r]: repeat type (for normal repeat replacements)
        r - repeat
        mr - maximal repeat (default)
        lmr - largest-maximal repeat
        smr - super-maximal repeat
    [-c]: repeat type (for context replacements)
        r - repeat
        mr - maximal repeat (default)
        lmr - largest-maximal repeat
        smr - super-maximal repeat
    [-s]: variable-length context pairs search method
        c - constant maximum length (is set hardcoded)
        e - exhausive (default), searches over all pairs
        g - greedy , selects pairs greedily so that maximum number of consistent pairs are selected
    [-f]: cost function to be optimized
        c - concatenation cost
        r - rule cost (default)
    [-m]: consider each line as a separate string
    [-l]: load a grammar file (will override -r -c -t -m options)
            (as of now, only straight-line grammars are supported)
    [-g]: amount of gap in fixed-gap context-detection mode
                    """
    if len(argv) == 1 or (len(argv) == 2 and argv[1] == '-h'):
        sys.stderr.write('Invalid input\n')
        sys.stderr.write(usage + '\n')
        sys.exit()
    optlist,args = getopt.getopt(argv[1:], 'a:t:p:qr:c:s:f:mlg:')
    for opt,arg in optlist:
        if opt == '-a':
            for ch in arg:
                if ch == 'p':
                    aFlag = True
                else:
                    if ch == 'f':
                        fFlag = True
                    else:
                        sys.stderr.write('Invalid input in ' + '-a' + ' flag\n')
                        sys.stderr.write(usage + '\n')
                        sys.exit()
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
                    printIntsGrammar = True
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
        if opt == '-c':
            if arg == 'r' or arg == 'mr' or arg == 'lmr' or arg == 'smr':
                cFlag = arg
            else:
                sys.stderr.write('Invalid input in ' + '-c' + ' flag\n')
                sys.stderr.write(usage + '\n')
                sys.exit()
        if opt == '-s':
            if arg == 'c' or arg == 'e' or arg == 'g':
                pairFlag = arg
            else:
                sys.stderr.write('Invalid input in ' + '-s' + ' flag\n')
                sys.stderr.write(usage + '\n')
                sys.exit()
        if opt == '-f':
            if arg == 'c' or arg == 'r':
                functionFlag = arg
            else:
                sys.stderr.write('Invalid input in ' + '-f' + ' flag\n')
                sys.stderr.write(usage + '\n')
                sys.exit()
        if opt == '-m':
            noNewLineFlag = False
        if opt == '-l':
            loadGrammarFlag = True
        if opt == '-g':
            gap = int(arg)

    return (aFlag, fFlag, chFlag, printIntsGrammar, quietLog, rFlag, cFlag, pairFlag, functionFlag, noNewLineFlag, loadGrammarFlag, gap)

def buildShiftTable(pattern):
    shifts = [1] * (len(pattern) + 1)
    shift = 1
    for pos in range(len(pattern)):
        while shift <= pos and pattern[pos] != pattern[pos - shift]:
            shift += shifts[pos - shift]
        shifts[pos + 1] = shift
    return shifts
def findMatch(text, pattern, shifts):
    startPos = 0
    matchLen = 0
    for c in text:
        while matchLen == len(pattern) or \
                                matchLen >= 0 and pattern[matchLen] != c:
            startPos += shifts[matchLen]
            matchLen -= shifts[matchLen]
        matchLen += 1
        if matchLen == len(pattern):
            return startPos
    return -1
def KnuthMorrisPratt(text, pattern):
    # pattern = list(pattern)
    # build table of shift amounts
    shifts = buildShiftTable(pattern)
    # do the actual search
    starts = []
    textStart = 0
    while True:
        tmpStart = findMatch(text[textStart:], pattern, shifts)
        if tmpStart == -1:
            break
        starts.append(textStart + tmpStart)
        if (textStart + tmpStart + len(pattern) <= len(text)-1):
            textStart = textStart + tmpStart + len(pattern)
        else:
            break
        # print 'textStart', textStart
        # print 'tmpStart', tmpStart
        # print 'starts', starts
    return starts

def idea1(sys_args, batchSize):
    g = Grammar(open(sys_args[-2], 'r'), 'file', gap, chFlag, noNewLineFlag)
    reverseDic = {}
    for c in g.dic:
        reverseDic[g.dic[c]] = c
    g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
    allNewTargets = open(sys_args[-1], 'r').read().splitlines()
    for x in range(0, len(allNewTargets), batchSize):
        sys.stderr.write('*************\n')
        sys.stderr.write(str('\n'.join(open(sys_args[-1], 'r').read().split('\n')[x:x + batchSize])) + ' x\n')
        g2 = Grammar2('\n'.join(open(sys_args[-1], 'r').read().split('\n')[x:x + batchSize]), 'string', gap, chFlag,
                     noNewLineFlag)
        # reverseDic2 = {}
        # for c in g2.dic:
        #     reverseDic2[g2.dic[c]] = c
        g2.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
        # g2.printGrammar(printIntsGrammar)
        newTargets = []
        for j in range(x, x + batchSize):
            # if noNewLineFlag:
            #     newTargets.append(allNewTargets[j])  # Assuming space sep chars
            # else:
            newTargets.append(allNewTargets[j].split())  # Assuming space sep chars
        newTargetsInt = []
        for t in newTargets:
            tmpT = []
            for i in range(len(t)):
                tmpT.append(reverseDic[t[i]])
            newTargetsInt.append(tmpT)
        # print newTargetsInt
        # On D_t
        grammarDic = g.grammarDic()
        ntYields = {}
        for nt in grammarDic:
            if nt == 0:
                continue
            if nt in ntYields:
                ntYields[nt].append(g.ntYield(grammarDic, nt))
            else:
                ntYields[nt] = [g.ntYield(grammarDic, nt)]
        # On D_\delta
        grammarDic2 = g2.grammarDic()
        ntYields2 = {}
        for nt in grammarDic2:
            if nt == 0:
                continue
            if nt in ntYields2:
                ntYields2[nt].append(g2.ntYield(grammarDic2, nt))
            else:
                ntYields2[nt] = [g2.ntYield(grammarDic2, nt)]
        toBeParsedStrings = newTargetsInt
        toBeParsedNts = [0 for i in range(len(toBeParsedStrings))]
        while len(toBeParsedStrings) > 0:
            # run optimal parsing on newTargetsInt
            optimallyParsedTargetInts = []
            for t in toBeParsedStrings:
                # create a graph
                G = nx.DiGraph()
                edgeLabels = {}  # used for saving non-terminals
                G.add_nodes_from([0, len(t) + 1])
                for i in range(len(t)):
                    G.add_edge(i, i + 1)
                    edgeLabels[(i, i + 1)] = -1
                #Adding edges from D_t
                for nt in ntYields:
                    newEdgesStarts = KnuthMorrisPratt(t, ntYields[nt][0])
                    # print 't', t
                    # print 'ntYields[nt]', nt, ntYields[nt][0]
                    # print 'newEdgesStarts', newEdgesStarts
                    for s in newEdgesStarts:
                        G.add_edge(s, s + len(ntYields[nt][0]))
                        edgeLabels[(s, s + len(ntYields[nt][0]))] = nt
                #Adding edges from the D_\delta
                for nt in ntYields2:
                    if ntYields2[nt][0] == t:
                        continue
                    newEdgesStarts2 = KnuthMorrisPratt(t, ntYields2[nt][0])
                    # print 't', t
                    # print 'ntYields[nt]', nt, ntYields[nt][0]
                    # print 'newEdgesStarts', newEdgesStarts
                    for s in newEdgesStarts2:
                        G.add_edge(s, s + len(ntYields2[nt][0]))
                        edgeLabels[(s, s + len(ntYields2[nt][0]))] = nt
                paths = nx.shortest_path(G, source=0, target=len(t), weight=None)
                # all shortest paths
                # print 'edgeLabels', edgeLabels
                # print 'edges', G.edges()
                # print 'paths', paths
                # for i in range(len(paths[0])):
                sys.stderr.write(str(newTargetsInt) + ' newTargetsInt\n')
                sys.stderr.write(str(toBeParsedStrings) + ' toBeParsedStrings\n')
                sys.stderr.write(str(t) + ' t\n')
                sys.stderr.write(str(paths) + ' paths\n')
                optimalParsing = []
                for i in range(len(paths) - 1):
                    if edgeLabels[(paths[i], paths[i + 1])] == -1:
                        # print t[paths[i]],
                        sys.stderr.write(str(optimalParsing) + ' parsing\n')
                        optimalParsing.append(t[paths[i]])
                    else:
                        sys.stderr.write(str(optimalParsing) + ' parsing\n')
                        # print edgeLabels[(paths[i],paths[i+1])],
                        optimalParsing.append(edgeLabels[(paths[i], paths[i + 1])])
                # print
                # sys.exit()
                sys.stderr.write(str(optimalParsing) + ' parsing2\n')
                optimallyParsedTargetInts.append(optimalParsing)
            # add newly parsed targets to grammar and convert grammardic to new grammar
            newToBeParsedStrings = []
            newToBeParsedNts = []
            sys.stderr.write(str(optimallyParsedTargetInts) + ' optimally\n')
            for i in range(len(optimallyParsedTargetInts)):
                t = optimallyParsedTargetInts[i]
                if toBeParsedNts[i] in grammarDic:
                    grammarDic[toBeParsedNts[i]].append(t)
                else:
                    grammarDic[toBeParsedNts[i]] = [t]
                    sys.stderr.write(str(t) + ' dsadsa\n')
                for c in t:
                    #Substring picked from D_\delta
                    if c in ntYields2 and c not in ntYields:
                        newToBeParsedStrings.append(ntYields2[c][0])
                        newToBeParsedNts.append(c)
            # toBeParsedStrings = newToBeParsedStrings
            # newToBeParsedNts = newToBeParsedNts
            toBeParsedStrings = copy.deepcopy(newToBeParsedStrings)
            toBeParsedNts = copy.deepcopy(newToBeParsedNts)
            sys.stderr.write(str(ntYields) + ' ntYields\n')
            sys.stderr.write(str(ntYields2) + ' ntYields2\n')
            sys.stderr.write(str(toBeParsedStrings) + ' toBeParsedStrings\n')
            # sys.exit()

        g.initFromGrammarDic(grammarDic, g.dic)
        # while True:
        #     maxR = g.retreiveMaximumGainRepeat(rFlag, CostFunction.EdgeCost)
        #     if maxR['score'] == -1:
        #         break
        #     else:
        #         # print '\tmaxR'
        #         sys.stderr.write(str(maxR) + '\n')
        #         g.replaceRepeat(maxR['length'], maxR['occs'])
    g.printGrammar(printIntsGrammar)

def idea2(sys_args, batchSize):
    g = Grammar(open(sys_args[-2], 'r'), 'file', gap, chFlag, noNewLineFlag)
    reverseDic = {}
    for c in g.dic:
        reverseDic[g.dic[c]] = c
    g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
    # g.printGrammar(printIntsGrammar)
    # return
    allNewTargets = open(sys_args[-1], 'r').read().splitlines()
    for x in range(0, len(allNewTargets), batchSize):
        newTargets = []
        for j in range(x, x + batchSize):
            # if not noNewLineFlag:
            newTargets.append(allNewTargets[j])  # Assuming space sep chars
            # else:
            # newTargets.append(allNewTargets[j].split())  # Assuming space sep chars
        newTargetsInt = []
        for t in newTargets:
            tmpT = []
            for i in range(len(t)):
                tmpT.append(reverseDic[t[i]])
            newTargetsInt.append(tmpT)
        # print 'int', newTargetsInt
        # #D_t
        grammarDic = g.grammarDic()
        ntYields = {}
        for nt in grammarDic:
            if nt == 0:
                continue
            if nt in ntYields:
                ntYields[nt].append(g.ntYield(grammarDic, nt))
            else:
                ntYields[nt] = [g.ntYield(grammarDic, nt)]
        # convert grammardic to new grammar
        for t in newTargetsInt:
            grammarDic[0].append(t)
        # print 'Before'
        # g.printGrammar(printIntsGrammar)
        g.initFromGrammarDic(grammarDic, g.dic)
        # print 'Mid'
        # g.printGrammar(printIntsGrammar)
        while True:
            maxR = g.retreiveMaximumGainRepeat(rFlag, CostFunction.EdgeCost)
            maxEvoR = g.getMaxEvoR(ntYields)#search within previously found repeats
            # print 'maxR', maxR
            # print 'maxEvoR', maxEvoR
            if maxR['score'] == -1 and maxEvoR['score'] == -1:
                break
            if maxR['score'] > maxEvoR['score']:
                # print '\tmaxR'
                sys.stderr.write(str(maxR) + '\n')
                g.replaceRepeat(maxR['length'], maxR['occs'])
            else:
                # print '\tmaxEvoR'
                sys.stderr.write(str(maxEvoR) + '\n')
                g.replaceRepeatEvo(maxEvoR['nt'], maxEvoR['length'], maxEvoR['occs'])
    # print 'After'
    g.printGrammar(printIntsGrammar)

def idea3(sys_args, batchSize):
    g = Grammar(open(sys_args[-2], 'r'), 'file', gap, chFlag, noNewLineFlag)
    reverseDic = {}
    maxInt = -1
    for c in g.dic:
        if maxInt < c:
            maxInt = c + 2
        reverseDic[g.dic[c]] = c
    g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
    # g.printGrammar(printIntsGrammar)
    # return
    allNewTargets = open(sys_args[-1], 'r').read().splitlines()
    for x in range(0, len(allNewTargets), batchSize):
        newTargets = []
        for j in range(x, x + batchSize):
            # if not noNewLineFlag:
            if j >= len(allNewTargets):
                break
            newTargets.append(allNewTargets[j])  # Assuming space sep chars
            # else:
            # newTargets.append(allNewTargets[j].split())  # Assuming space sep chars
        newTargetsInt = []
        # print newTargets
        for t in newTargets:
            tmpT = []
            tt = t.split()
            for i in range(len(tt)):  # For space-sep chars
                if tt[i] in reverseDic:
                    tmpT.append(reverseDic[tt[i]])
                else:
                    reverseDic[tt[i]] = maxInt
                    g.dic[maxInt] = tt[i]
                    maxInt += 2
                    tmpT.append(reverseDic[tt[i]])
            # for i in range(len(t)):#For seq chars
            #     if t[i] in reverseDic:
            #         tmpT.append(reverseDic[t[i]])
            #     else:
            #         reverseDic[t[i]] = maxInt
            #         g.dic[maxInt] = t[i]
            #         maxInt += 2
            #         tmpT.append(reverseDic[t[i]])
            newTargetsInt.append(tmpT)
        # print newTargetsInt
        # print g.dic
        # print reverseDic

        # print 'int', newTargetsInt
        # #D_t
        grammarDic = g.grammarDic()
        ntYields = {}
        for nt in grammarDic:
            if nt == 0:
                continue
            if nt in ntYields:
                ntYields[nt].append(g.ntYield(grammarDic, nt))
            else:
                ntYields[nt] = [g.ntYield(grammarDic, nt)]
        #run optimal parsing on newTargetsInt
        optimallyParsedTargetInts =[]
        for t in newTargetsInt:
            #create a graph
            G = nx.DiGraph()
            edgeLabels = {} #used for saving non-terminals
            G.add_nodes_from([0, len(t)+1])
            for i in range(len(t)):
                G.add_edge(i, i+1)
                edgeLabels[(i,i+1)] = -1
            # print 'ntYields.keys()', ntYields.keys()
            # print 't', t
            for nt in ntYields:
                newEdgesStarts = KnuthMorrisPratt(t, ntYields[nt][0])
                # print 't', t
                # print 'ntYields[nt]', nt, ntYields[nt][0]
                # print 'newEdgesStarts', newEdgesStarts
                for s in newEdgesStarts:
                    G.add_edge(s, s+len(ntYields[nt][0]))
                    edgeLabels[(s, s+len(ntYields[nt][0]))] = nt
            paths = nx.shortest_path(G, source=0, target=len(t), weight=None)
            ## sys.stderr.write(str(paths) + 'paths\n')
            ## paths = random.choice(list(nx.all_simple_paths(G, source=0, target=len(t))))
            ## ctr = 1
            # for p in nx.all_simple_paths(G, source=0, target=len(t)):
            #     paths = p
                ## sys.stderr.write(str(ctr) + '\n')
                ## ctr += 1
                # break
            # sys.stderr.write(str(list(nx.all_simple_paths(G, source=0, target=len(t)))) + 'paths\n')
            # sys.exit()
            #all shortest paths
            # print 'edgeLabels', edgeLabels
            # print 'edges', G.edges()
            # print 'paths', paths
            # for i in range(len(paths[0])):
            optimalParsing = []
            for i in range(len(paths)-1):
                if edgeLabels[(paths[i], paths[i + 1])] == -1:
                    # print t[paths[i]],
                    optimalParsing.append(t[paths[i]])
                else:
                    # print edgeLabels[(paths[i],paths[i+1])],
                    optimalParsing.append(edgeLabels[(paths[i],paths[i+1])])
            # print
            # sys.exit()
            optimallyParsedTargetInts.append(optimalParsing)

        # add newly parsed targets to grammar and convert grammardic to new grammar
        for t in optimallyParsedTargetInts:
            grammarDic[0].append(t)
        g.initFromGrammarDic(grammarDic, g.dic)
        while True:
            maxR = g.retreiveMaximumGainRepeat(rFlag, CostFunction.EdgeCost)
            if maxR['score'] == -1:
                break
            else:
                # print '\tmaxR'
                sys.stderr.write(str(maxR) + '\n')
                g.replaceRepeat(maxR['length'], maxR['occs'])
    g.printGrammar(printIntsGrammar)

def idea3_GlobalGLexisWithoutOpt(sys_args, batchSize):
    g = Grammar(open(sys_args[-2], 'r'), 'file', gap, chFlag, noNewLineFlag)
    totalLength = open(sys_args[-2], 'r').read().count(' ')
    reverseDic = {}
    maxInt = -1
    for c in g.dic:
        if maxInt < c:
            maxInt = c + 2
        reverseDic[g.dic[c]] = c
    g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
    # g.printGrammar(printIntsGrammar)
    # return
    allNewTargets = open(sys_args[-1], 'r').read().splitlines()
    for x in range(0, len(allNewTargets), batchSize):
        newTargets = []
        for j in range(x, x + batchSize):
            # if not noNewLineFlag:
            if j >= len(allNewTargets):
                break
            newTargets.append(allNewTargets[j])  # Assuming space sep chars
            # else:
            # newTargets.append(allNewTargets[j].split())  # Assuming space sep chars
        newTargetsInt = []
        # print newTargets
        totalLengthNewTargets = 0
        for t in newTargets:
            tmpT = []
            tt = t.split()
            totalLengthNewTargets += len(tt)
            totalLength += len(tt)
            for i in range(len(tt)):  # For space-sep chars
                if tt[i] in reverseDic:
                    tmpT.append(reverseDic[tt[i]])
                else:
                    reverseDic[tt[i]] = maxInt
                    g.dic[maxInt] = tt[i]
                    maxInt += 2
                    tmpT.append(reverseDic[tt[i]])
            # for i in range(len(t)):#For seq chars
            #     if t[i] in reverseDic:
            #         tmpT.append(reverseDic[t[i]])
            #     else:
            #         reverseDic[t[i]] = maxInt
            #         g.dic[maxInt] = t[i]
            #         maxInt += 2
            #         tmpT.append(reverseDic[t[i]])
            newTargetsInt.append(tmpT)
        # print newTargetsInt
        # print g.dic
        # print reverseDic

        # print 'int', newTargetsInt
        # #D_t
        grammarDic = g.grammarDic()
        ntYields = {}
        for nt in grammarDic:
            if nt == 0:
                continue
            if nt in ntYields:
                ntYields[nt].append(g.ntYield(grammarDic, nt))
            else:
                ntYields[nt] = [g.ntYield(grammarDic, nt)]
        #run optimal parsing on newTargetsInt
        optimallyParsedTargetInts =[]
        for t in newTargetsInt:
            #create a graph
            G = nx.DiGraph()
            edgeLabels = {} #used for saving non-terminals
            G.add_nodes_from([0, len(t)+1])
            for i in range(len(t)):
                G.add_edge(i, i+1)
                edgeLabels[(i,i+1)] = -1
            # print 'ntYields.keys()', ntYields.keys()
            # print 't', t
            for nt in ntYields:
                newEdgesStarts = KnuthMorrisPratt(t, ntYields[nt][0])
                # print 't', t
                # print 'ntYields[nt]', nt, ntYields[nt][0]
                # print 'newEdgesStarts', newEdgesStarts
                for s in newEdgesStarts:
                    G.add_edge(s, s+len(ntYields[nt][0]))
                    edgeLabels[(s, s+len(ntYields[nt][0]))] = nt
            paths = nx.shortest_path(G, source=0, target=len(t), weight=None)
            ## sys.stderr.write(str(paths) + 'paths\n')
            ## paths = random.choice(list(nx.all_simple_paths(G, source=0, target=len(t))))
            ## ctr = 1
            # for p in nx.all_simple_paths(G, source=0, target=len(t)):
            #     paths = p
                ## sys.stderr.write(str(ctr) + '\n')
                ## ctr += 1
                # break
            # sys.stderr.write(str(list(nx.all_simple_paths(G, source=0, target=len(t)))) + 'paths\n')
            # sys.exit()
            #all shortest paths
            # print 'edgeLabels', edgeLabels
            # print 'edges', G.edges()
            # print 'paths', paths
            # for i in range(len(paths[0])):
            optimalParsing = t
            # optimalParsing = []
            # for i in range(len(paths)-1):
            #     if edgeLabels[(paths[i], paths[i + 1])] == -1:
            #         # print t[paths[i]],
            #         optimalParsing.append(t[paths[i]])
            #     else:
            #         # print edgeLabels[(paths[i],paths[i+1])],
            #         optimalParsing.append(edgeLabels[(paths[i],paths[i+1])])
            # print
            # sys.exit()
            optimallyParsedTargetInts.append(optimalParsing)

        # add newly parsed targets to grammar and convert grammardic to new grammar
        for t in optimallyParsedTargetInts:
            grammarDic[0].append(t)
        g.initFromGrammarDic(grammarDic, g.dic)
        previousCost = g.grammarCost(CostFunction.EdgeCost)
        originalCost = previousCost
        for t in newTargetsInt:
            originalCost += len(t)
        intermediateCost = previousCost
        optCost = 0
        for s in optimallyParsedTargetInts:
            intermediateCost += len(s)
            optCost += len(s)
        while True:
            maxR = g.retreiveMaximumGainRepeat(rFlag, CostFunction.EdgeCost)
            if maxR['score'] == -1:
                break
            else:
                # print '\tmaxR'
                sys.stderr.write(str(maxR) + '\n')
                g.replaceRepeat(maxR['length'], maxR['occs'])
        print str(totalLength) + '\t' + str(totalLengthNewTargets) + '\t' + str(
        intermediateCost - previousCost) + '\t' + str(
        totalLengthNewTargets - (intermediateCost - previousCost)) + '\t' + str(
        (intermediateCost - previousCost) - (intermediateCost - g.grammarCost(CostFunction.EdgeCost))) + '\t' + str(
        intermediateCost - g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(g.grammarCost(CostFunction.EdgeCost))
    # g.printGrammar(printIntsGrammar)

def CSAll(sys_args, batchSize=1):
    # g = Grammar(open(sys_args[-1], 'r'), 'file', gap, chFlag, noNewLineFlag)
    totalLength = 0
    allNewTargets = open(sys_args[-1]+'g.txt', 'r').read().splitlines()
    # newTargets = []
    for x in range(67, len(allNewTargets), batchSize):
        # g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
        sys.stderr.write(str(x) + '\n')
        # for j in range(x, x + batchSize):
        newTargets = []
        for j in range(0,x):
            # if not noNewLineFlag:
            if j > len(allNewTargets):
                break
            newTargets.append(allNewTargets[j])  # Assuming space sep chars
            # else:
            # newTargets.append(allNewTargets[j].split())  # Assuming space sep chars
            # print optimallyParsedTargetInts
        g = None
        tmpOut = open('tmpOut.txt', 'w')
        for t in newTargets:
            # for c in t:
            tmpOut.write(str(t))
            tmpOut.write('\n')
        tmpOut.close()
        g = Grammar(open('tmpOut.txt', 'r'), 'file', gap, chFlag, noNewLineFlag)
            # os.remove('tmpOut.txt')
        g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
        # print g.grammarCost(CostFunction.EdgeCost)
        # print str(originalCost) + '\t' + str(intermediateCost) + '\t' + str(g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(g.grammarCost(CostFunction.EdgeCost)-previousCost) + '\t' + str(totalLengthNewTargets) + '\t' + str(totalLength)
        # g.printGrammarToFile(sys_args[-1]+str(x/batchSize+1), printIntsGrammar)
        g.printGrammarToFile(sys_args[-1] + str(x) + '.txt', printIntsGrammar)
    #     print str(g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(totalLengthNewTargets) + '\t' + str(totalLength)
    #     print str(g.grammarCost(CostFunction.EdgeCost)-previousCost) + '\t' + str(totalLengthNewTargets) + '\t' + str(totalLength)



def idea3_Fixed_TGM4(input_file_path, givenGrammar=None, batchSize=10, init=.05, gap=50, chFlag=SequenceType.SpaceSeparated, noNewLineFlag=True, working_path = ''):
    folder = '/'.join(input_file_path.split('/')[:-1]) + '/INC-DAGs/inc-b'+str(batchSize)+'/'
    # folder = 'TBTG/NewData3/Data/INC-DAGs'
    # if not os.path.exists(folder):
    #     os.makedirs(folder)
    fileName = input_file_path.split('/')[-1].split('.')[0]
    firstChoice = True
    mainFile = open(input_file_path, 'r').read().splitlines()
    LEN_MAIN = len(mainFile)
    # data_increment = 0.1
    data_increment = float(batchSize) / LEN_MAIN
    counter = 0
    initData = []
    for l in mainFile:
        if counter < init*LEN_MAIN:
            initData.append(mainFile.pop(0))
        else:
            break
        counter += 1
    tmpOut = open(working_path + '/tmpOut-'+str(batchSize) + fileName + '--.txt', 'w')
    for l in initData:
        tmpOut.write(l + '\n')
    tmpOut.close()

    aFlag = False;fFlag = False;chFlag = SequenceType.SpaceSeparated;printIntsGrammar = False;quietLog = True;
    rFlag = 'mr';cFlag = 'mr';pairFlag = 'c';functionFlag = 'r';noNewLineFlag = False;loadGrammarFlag = False;
    gap = 50
    if givenGrammar == None:
        g = Grammar(open(working_path + '/tmpOut-'+str(batchSize) + fileName + '--.txt', 'r'), 'file', gap, chFlag, noNewLineFlag)
        # totalLength = open('tmpOut-'+str(batchSize) + fileName + '--.txt', 'r').read().count(' ')
        # numData = open('tmpOut-'+str(batchSize) + fileName + '--.txt', 'r').read().count('\n')
        # totalLength = 1496
        reverseDic = {}
        maxInt = -1
        for c in g.dic:
            if maxInt < c:
                maxInt = c + 2
            reverseDic[g.dic[c]] = c
        g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
        ###g.printGrammarToFile(folder + fileName + '-0.txt',printIntsGrammar)
        seedCost = g.grammarCost(CostFunction.EdgeCost)
        # output = open('tmpGram.txt', 'w')
        # output.write('\n')
        # output.close()
        # g.printGrammarWithOffsetToNTs(printIntsGrammar, 0)
        # g.printGrammar(printIntsGrammar)
        # return

        # allNewTargets = open(sys_args[-2], 'r').read().splitlines()
        allNewTargets = mainFile
    else:
        g = Grammar(open(givenGrammar, 'r'), 'grammar', gap, chFlag, noNewLineFlag)
        reverseDic = {}
        maxInt = -1
        for c in g.dic:
            if maxInt < c:
                maxInt = c + 2
            reverseDic[g.dic[c]] = c
        allNewTargets = open(input_file_path, 'r').read().splitlines()
    LEN = len(allNewTargets)
    ratios = []
    newParsedTargets = []
    ntYields = {}
    countingNumberOfOptimalParsings_Recombination = 0
    countingNumberOfGlexises_Innovation = 0
    tmp_dataset = []
    prev_len_tmp_dataset = 0
    remaining_batch_targets = []
    for x in range(0, len(allNewTargets), batchSize):
        # sys.stderr.write(str(x) + '\n')
        newTargets = []
        newTargets = remaining_batch_targets
        # numData += len(remaining_batch_targets)
        remaining_batch_targets = []
        for j in range(x, x + batchSize):
            # if not noNewLineFlag:
            if j >= len(allNewTargets):
                break
            if len(tmp_dataset) - prev_len_tmp_dataset > data_increment * float(LEN_MAIN):
                for k in range(j,x+batchSize):
                    remaining_batch_targets.append(allNewTargets[k])
                break
            newTargets.append(allNewTargets[j])  # Assuming space sep chars
            # tmp_dataset.append(allNewTargets[j])  # Assuming space sep chars
            # numData += 1
            # else:
            # newTargets.append(allNewTargets[j].split())  # Assuming space sep chars
        tmp_dataset = tmp_dataset + newTargets
        newTargetsInt = []
        # print newTargets
        totalLengthNewTargets = 0
        for t in newTargets:
            tmpT = []
            tt = t.split()
            totalLengthNewTargets += len(tt)
            # totalLength += len(tt)
            for i in range(len(tt)):  # For space-sep chars
                if tt[i] in reverseDic:
                    tmpT.append(reverseDic[tt[i]])
                else:
                    reverseDic[tt[i]] = maxInt
                    g.dic[maxInt] = tt[i]
                    maxInt += 2
                    tmpT.append(reverseDic[tt[i]])
            # for i in range(len(t)):#For seq chars
            #     if t[i] in reverseDic:
            #         tmpT.append(reverseDic[t[i]])
            #     else:
            #         reverseDic[t[i]] = maxInt
            #         g.dic[maxInt] = t[i]
            #         maxInt += 2
            #         tmpT.append(reverseDic[t[i]])
            newTargetsInt.append(tmpT)
        # print newTargetsInt
        # print g.dic
        # print reverseDic

        # print 'int', newTargetsInt
        # #D_t
        # sys.stderr.write(str(numData) + '\n')
        grammarDic = g.grammarDic()
        # ntYields = {}
        # for nt in grammarDic:
        #     if nt == 0:
        #         continue
        #     if nt in ntYields:
        #         ntYields[nt].append(g.ntYield(grammarDic, nt))
        #     else:
        #         ntYields[nt] = [g.ntYield(grammarDic, nt)]
        for nt in grammarDic:
            if nt == 0 or nt in ntYields:
                continue
            else:
                # print 'initial NT', nt
                ntYields[nt] = [g.ntYield(grammarDic, nt)]
        #run optimal parsing on newTargetsInt
        optimallyParsedTargetInts =[]
        newParsedTargets = []
        for t in newTargetsInt:
            #create a graph
            G = nx.DiGraph()
            edgeLabels = {} #used for saving non-terminals
            G.add_nodes_from([0, len(t)+1])
            for i in range(len(t)):
                G.add_edge(i, i+1)
                edgeLabels[(i,i+1)] = -1
            # print 'ntYields.keys()', ntYields.keys()
            # print 't', t
            for nt in ntYields:
                newEdgesStarts = KnuthMorrisPratt(t, ntYields[nt][0])
                # print 't', t
                # print 'ntYields[nt]', nt, ntYields[nt][0]
                # print 'newEdgesStarts', newEdgesStarts
                for s in newEdgesStarts:
                    G.add_edge(s, s+len(ntYields[nt][0]))
                    edgeLabels[(s, s+len(ntYields[nt][0]))] = nt
            # paths = nx.shortest_path(G, source=0, target=len(t), weight=None)
            shortestPaths = nx.all_shortest_paths(G, source=0, target=len(t), weight=None)
            shortestPaths = [p for p in shortestPaths]
            shortestPaths = [shortestPaths[0]]
            # if len(shortestPaths) >= 2:
            #     print 'YES'
            newParsedTargets.append([])
            for paths in shortestPaths:
                ## sys.stderr.write(str(paths) + 'paths\n')
                ## paths = random.choice(list(nx.all_simple_paths(G, source=0, target=len(t))))
                ## ctr = 1
                # for p in nx.all_simple_paths(G, source=0, target=len(t)):
                #     paths = p
                    ## sys.stderr.write(str(ctr) + '\n')
                    ## ctr += 1
                    # break
                # sys.stderr.write(str(list(nx.all_simple_paths(G, source=0, target=len(t)))) + 'paths\n')
                # sys.exit()
                #all shortest paths
                # print 'edgeLabels', edgeLabels
                # print 'edges', G.edges()
                # print 'paths', paths
                # for i in range(len(paths[0])):
                optimalParsing = []
                for i in range(len(paths)-1):
                    if edgeLabels[(paths[i], paths[i + 1])] == -1:
                        # print t[paths[i]],
                        optimalParsing.append(t[paths[i]])
                    else:
                        # print edgeLabels[(paths[i],paths[i+1])],
                        optimalParsing.append(edgeLabels[(paths[i],paths[i+1])])
                        countingNumberOfOptimalParsings_Recombination += 1
                # print
                # sys.exit()
                # if len(t) > len(optimalParsing):
                #     print 'yaaaaaaaaaaay1'
                optimallyParsedTargetInts.append(optimalParsing)
                # newParsedTargets.append(optimalParsing)
                newParsedTargets[-1].append(optimalParsing)
                # if len(newParsedTargets[-1]) >= 2:
                #     print 'YES'
                ratios.append(float(len(optimalParsing))/len(t))
        optimalParsingCombinations = list(itertools.product(*newParsedTargets))
        # print 'combs'
        # print optimalParsingCombinations
        previousCost = g.grammarCost(CostFunction.EdgeCost)
        originalCost = previousCost
        for t in newTargetsInt:
            originalCost += len(t)
        intermediateCost = previousCost
        optCost = 0
        for s in optimallyParsedTargetInts:
            intermediateCost += len(s)
            optCost += len(s)
        # print str(intermediateCost) + '\t',
        # add newly parsed targets to grammar and convert grammardic to new grammar
        # for t in optimallyParsedTargetInts:
        #     grammarDic[0].append(t)
        # sys.stderr.write(str(x) + ' 2\n')
        previousDic = g.dic

        minCost = totalLengthNewTargets
        minParsing = []
        for optimallyParsedTargetInts in optimalParsingCombinations:
            # print optimallyParsedTargetInts
            g = None
            tmpOut = open(working_path + '/tmpOut-'+str(batchSize) + fileName + '--.txt', 'w')
            for t in optimallyParsedTargetInts:
                for c in t:
                    tmpOut.write(str(c) + ' ')
                tmpOut.write('\n')
            tmpOut.close()
            g = Grammar(open(working_path + '/tmpOut-'+str(batchSize) + fileName + '--.txt', 'r'), 'file', gap, chFlag, noNewLineFlag)
            # os.remove('tmpOut.txt')
            g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
            # if previousCost + g.grammarCost(CostFunction.EdgeCost) < intermediateCost:
            #     print 'yaaaaaaaaaaay2',
            # sys.stderr.write(str(x) + ' 22\n')
            # g.printGrammarWithOffsetToNTs(printIntsGrammar, maxInt, inputDic=previousDic)
            # g = Grammar(open('tmpGram.txt', 'r'), 'grammar', gap, chFlag, noNewLineFlag)
            # if len(optimalParsingCombinations) >= 2:
            #     print 'minCost\t' + str(g.grammarCost(CostFunction.EdgeCost))
            if minCost >= g.grammarCost(CostFunction.EdgeCost):
                # if minCost != totalLengthNewTargets:
                # print 'diff' + '\t' + str(minCost) + '\t' + str(g.grammarCost(CostFunction.EdgeCost))
                minCost = g.grammarCost(CostFunction.EdgeCost)
                minParsing = optimallyParsedTargetInts
            if firstChoice:
                break
        g = None
        total_length_new_target_set_after_parsing = 0
        tmpOut = open(working_path + '/tmpOut-'+str(batchSize) + fileName + '--.txt', 'w')
        for t in minParsing:
            total_length_new_target_set_after_parsing += len(t)
            for c in t:
                tmpOut.write(str(c) + ' ')
            tmpOut.write('\n')
        tmpOut.close()
        # print 'tttttttttt', total_length_new_target_set_after_parsing
        g = Grammar(open(working_path + '/tmpOut-'+str(batchSize) + fileName + '--.txt', 'r'), 'file', gap, chFlag, noNewLineFlag)
        # os.remove('tmpOut.txt')
        g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
        # g.printGrammarToFile(sys_args[-1] + "incGlex_" + str(x)+'.txt', printIntsGrammar)

        newGrammarDic = g.grammarDic()
        # print newGrammarDic
        maxIntChar = -1
        for nt in grammarDic:
            for rule in grammarDic[nt]:
                for c in rule:
                    if maxIntChar < int(c):
                        maxIntChar = int(c)
        maxIntChar += 2
        newNts = {}
        for nt in sorted(newGrammarDic.keys()):
            # if nt in grammarDic:
            if nt != 0:
                newNts[nt] = nt + maxIntChar
                maxIntChar += 2
        tmpNewGrammarDic = {}
        for nt in newGrammarDic:
            tmpRHS = []
            # if nt == 0:
            for rule in newGrammarDic[nt]:
                # print rule
                tmpRRHS = []
                for c in rule:
                    # if c == 1507:
                    #     print 'wowowow', newGrammarDic[1507]
                    if c in g.dic:
                        tmpRRHS.append(int(g.dic[c]))
                    else:
                        if c in newNts:
                            tmpRRHS.append(int(newNts[c]))
                        else:
                            tmpRRHS.append(int(c))
                if nt!=0:
                    if tmpRRHS[0] == newNts[nt]:
                        print 'damn!'
                        print nt
                        print tmpRRHS
                        print rule
                        print newGrammarDic[nt]
                tmpRHS.append(tmpRRHS)
            # else:
            #     for c in newGrammarDic[nt]:
            #         print c
            #         if c in g.dic:
            #             tmpRHS.append(int(g.dic[c]))
            #         else:
            #             tmpRHS.append(int(c))Q
            if nt in newNts:
                tmpNewGrammarDic[newNts[nt]] = tmpRHS
            else:
                newGrammarDic[nt] = tmpRHS
        for nt in newNts:
            newGrammarDic.pop(nt)
        for nt in tmpNewGrammarDic:
            newGrammarDic[nt] = tmpNewGrammarDic[nt]
        # print newGrammarDic

        # print grammarDic
        for nt in newGrammarDic:
            if nt in grammarDic:
                if nt == 0:
                    grammarDic[nt].extend(newGrammarDic[nt])
                else:
                    # print nt, newGrammarDic[nt]
                    # grammarDic[nt + maxIntChar] = newGrammarDic[nt]
                    # print 1, nt + maxIntChar
                    # print 3, grammarDic[1507]
                    # maxIntChar += 2
                    print 'error'
                    sys.exit(0)
            else:
                # print nt, newGrammarDic[nt]
                grammarDic[nt] = newGrammarDic[nt]
                # grammarDic[nt + maxIntChar] = newGrammarDic[nt]
                # print 2, nt + maxIntChar
                # print 4, grammarDic[1507]
                # maxIntChar += 2
        # sys.stderr.write(str(x) + ' 3\n')
        g.initFromGrammarDic(grammarDic, previousDic)
        # break
        # while True:
        #     maxR = g.retreiveMaximumGainRepeat(rFlag, CostFunction.EdgeCost)
        #     if maxR['score'] == -1:
        #         break
        #     else:
        #         # print '\tmaxR'
        #         sys.stderr.write(str(maxR) + '\n')
        #         g.replaceRepeat(maxR['length'], maxR['occs'])
        # g.printGrammar(printIntsGrammar)
        # print countingNumberOfOptimalParsings_Recombination
        if len(tmp_dataset) - prev_len_tmp_dataset > data_increment * float(LEN_MAIN):
            lengthPer = str(int(math.floor((float(len(tmp_dataset)) / float(LEN_MAIN)) * 100)))
            # print len(tmp_dataset), LEN_MAIN, lengthPer
            ###print 'Length %', lengthPer
            ###g.printGrammarToFile(folder + fileName + '-' + lengthPer, printIntsGrammar)
            prev_len_tmp_dataset = len(tmp_dataset)
    ###g.printGrammarToFile(folder + fileName + '-100.txt', printIntsGrammar)
    return g
    #     print
    #     print str(originalCost) + '\t' + str(intermediateCost) + '\t' + str(g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(g.grammarCost(CostFunction.EdgeCost)-previousCost) + '\t' + str(totalLengthNewTargets) + '\t' + str(totalLength)
    #     g.printGrammarToFile(sys_args[-1]+str(x/batchSize+1)+'.txt', printIntsGrammar)
    #     print str(g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(totalLengthNewTargets) + '\t' + str(totalLength)


        # print str(g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(g.grammarCost(CostFunction.EdgeCost)-previousCost) + '\t' + str(totalLengthNewTargets) + '\t' + str(totalLength)



        # g.printGrammarToFile(sys_args[-1]+'gram'+str(numData)+'.txt', printIntsGrammar)




        # g.printGrammarToFile('tmpGram.txt', printIntsGrammar)
        # sys.stderr.write(str(numData) + '\n')
        # try:
        #     print str(totalLength) + '\t' + str(totalLengthNewTargets) + '\t' + str(intermediateCost-previousCost) + '\t' + str(totalLengthNewTargets-(intermediateCost-previousCost)) + '\t' + str((intermediateCost-previousCost)-(intermediateCost-g.grammarCost(CostFunction.EdgeCost))) + '\t' + str(intermediateCost-g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(g.grammarCost(CostFunction.EdgeCost))\
        #     + '\t' + str(structSimTest(open('tmpGram.txt','r').read(),\
        #                   open('/Users/payamsiyari/Desktop/inc/inc-fullProfile/clean-slate full profile/gram' + str(numData) + '.txt','r').read()))
        # except:
        #     pass


    # previousDic = g.dic
    # g = None
    # tmpOut = open('tmpOut.txt','w')
    # for t in newParsedTargets:
    #     for c in t:
    #         tmpOut.write(str(c) + ' ')
    #     tmpOut.write('\n')
    # tmpOut.close()
    # g = Grammar(open('tmpOut.txt', 'r'), 'file', gap, chFlag, noNewLineFlag)
    # g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
    # g.printGrammarWithOffsetToNTs(printIntsGrammar, maxInt, inputDic=previousDic)

    # g.printGrammarToFile(sys_args[-1]+'.txt', printIntsGrammar)

    #Only for target ratio testing
    # sumNewLengths = 0
    # for t in optimallyParsedTargetInts:
    #     sumNewLengths += len(t)
    # return sumNewLengths

    return ratios

def idea3_Fixed_TGM4_Glexis(input_file_path, givenGrammar=None, batchSize=10, init=.05, gap=50, chFlag=SequenceType.SpaceSeparated, noNewLineFlag=True, working_path = ''):
    folder = '/'.join(input_file_path.split('/')[:-1]) + '/INC-DAGs/inc-b'+str(batchSize)+'/'
    # folder = 'TBTG/NewData3/Data/INC-DAGs'
    # if not os.path.exists(folder):
    #     os.makedirs(folder)
    fileName = input_file_path.split('/')[-1].split('.')[0]
    firstChoice = True
    mainFile = open(input_file_path, 'r').read().splitlines()
    LEN_MAIN = len(mainFile)
    # data_increment = 0.1
    data_increment = float(batchSize) / LEN_MAIN
    counter = 0
    initData = []
    for l in mainFile:
        if counter < init*LEN_MAIN:
            initData.append(mainFile.pop(0))
        else:
            break
        counter += 1
    tmpOut = open(working_path + '/tmpOut-'+str(batchSize) + fileName + '--.txt', 'w')
    for l in initData:
        tmpOut.write(l + '\n')
    tmpOut.close()

    aFlag = False;fFlag = False;chFlag = SequenceType.SpaceSeparated;printIntsGrammar = False;quietLog = True;
    rFlag = 'mr';cFlag = 'mr';pairFlag = 'c';functionFlag = 'r';noNewLineFlag = False;loadGrammarFlag = False;
    gap = 50
    if givenGrammar == None:
        g = Grammar(open(working_path + '/tmpOut-'+str(batchSize) + fileName + '--.txt', 'r'), 'file', gap, chFlag, noNewLineFlag)
        # totalLength = open('tmpOut-'+str(batchSize) + fileName + '--.txt', 'r').read().count(' ')
        # numData = open('tmpOut-'+str(batchSize) + fileName + '--.txt', 'r').read().count('\n')
        # totalLength = 1496
        reverseDic = {}
        maxInt = -1
        for c in g.dic:
            if maxInt < c:
                maxInt = c + 2
            reverseDic[g.dic[c]] = c
        g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
        ###g.printGrammarToFile(folder + fileName + '-0.txt',printIntsGrammar)
        seedCost = g.grammarCost(CostFunction.EdgeCost)
        # output = open('tmpGram.txt', 'w')
        # output.write('\n')
        # output.close()
        # g.printGrammarWithOffsetToNTs(printIntsGrammar, 0)
        # g.printGrammar(printIntsGrammar)
        # return

        # allNewTargets = open(sys_args[-2], 'r').read().splitlines()
        allNewTargets = mainFile
    else:
        g = Grammar(open(givenGrammar, 'r'), 'grammar', gap, chFlag, noNewLineFlag)
        reverseDic = {}
        maxInt = -1
        for c in g.dic:
            if maxInt < c:
                maxInt = c + 2
            reverseDic[g.dic[c]] = c
        allNewTargets = open(input_file_path, 'r').read().splitlines()
    LEN = len(allNewTargets)
    ratios = []
    newParsedTargets = []
    ntYields = {}
    countingNumberOfOptimalParsings_Recombination = 0
    countingNumberOfGlexises_Innovation = 0
    tmp_dataset = []
    prev_len_tmp_dataset = 0
    remaining_batch_targets = []
    for x in range(0, len(allNewTargets), batchSize):
        # sys.stderr.write(str(x) + '\n')
        newTargets = []
        newTargets = remaining_batch_targets
        # numData += len(remaining_batch_targets)
        remaining_batch_targets = []
        for j in range(x, x + batchSize):
            # if not noNewLineFlag:
            if j >= len(allNewTargets):
                break
            if len(tmp_dataset) - prev_len_tmp_dataset > data_increment * float(LEN_MAIN):
                for k in range(j,x+batchSize):
                    remaining_batch_targets.append(allNewTargets[k])
                break
            newTargets.append(allNewTargets[j])  # Assuming space sep chars
            # tmp_dataset.append(allNewTargets[j])  # Assuming space sep chars
            # numData += 1
            # else:
            # newTargets.append(allNewTargets[j].split())  # Assuming space sep chars
        tmp_dataset = tmp_dataset + newTargets
        newTargetsInt = []
        # print newTargets
        totalLengthNewTargets = 0
        for t in newTargets:
            tmpT = []
            tt = t.split()
            totalLengthNewTargets += len(tt)
            # totalLength += len(tt)
            for i in range(len(tt)):  # For space-sep chars
                if tt[i] in reverseDic:
                    tmpT.append(reverseDic[tt[i]])
                else:
                    reverseDic[tt[i]] = maxInt
                    g.dic[maxInt] = tt[i]
                    maxInt += 2
                    tmpT.append(reverseDic[tt[i]])
            # for i in range(len(t)):#For seq chars
            #     if t[i] in reverseDic:
            #         tmpT.append(reverseDic[t[i]])
            #     else:
            #         reverseDic[t[i]] = maxInt
            #         g.dic[maxInt] = t[i]
            #         maxInt += 2
            #         tmpT.append(reverseDic[t[i]])
            newTargetsInt.append(tmpT)
        # print newTargetsInt
        # print g.dic
        # print reverseDic

        # print 'int', newTargetsInt
        # #D_t
        # sys.stderr.write(str(numData) + '\n')
        grammarDic = g.grammarDic()
        # ntYields = {}
        # for nt in grammarDic:
        #     if nt == 0:
        #         continue
        #     if nt in ntYields:
        #         ntYields[nt].append(g.ntYield(grammarDic, nt))
        #     else:
        #         ntYields[nt] = [g.ntYield(grammarDic, nt)]
        for nt in grammarDic:
            if nt == 0 or nt in ntYields:
                continue
            else:
                # print 'initial NT', nt
                ntYields[nt] = [g.ntYield(grammarDic, nt)]
        #run optimal parsing on newTargetsInt
        optimallyParsedTargetInts =[]
        newParsedTargets = []
        for t in newTargetsInt:
            #create a graph
            G = nx.DiGraph()
            edgeLabels = {} #used for saving non-terminals
            G.add_nodes_from([0, len(t)+1])
            for i in range(len(t)):
                G.add_edge(i, i+1)
                edgeLabels[(i,i+1)] = -1
            # print 'ntYields.keys()', ntYields.keys()
            # print 't', t


                    # for nt in ntYields:
                    #     newEdgesStarts = KnuthMorrisPratt(t, ntYields[nt][0])
                    #     # print 't', t
                    #     # print 'ntYields[nt]', nt, ntYields[nt][0]
                    #     # print 'newEdgesStarts', newEdgesStarts
                    #     for s in newEdgesStarts:
                    #         G.add_edge(s, s+len(ntYields[nt][0]))
                    #         edgeLabels[(s, s+len(ntYields[nt][0]))] = nt


            # paths = nx.shortest_path(G, source=0, target=len(t), weight=None)
            shortestPaths = nx.all_shortest_paths(G, source=0, target=len(t), weight=None)
            shortestPaths = [p for p in shortestPaths]
            shortestPaths = [shortestPaths[0]]
            # if len(shortestPaths) >= 2:
            #     print 'YES'
            newParsedTargets.append([])
            for paths in shortestPaths:
                ## sys.stderr.write(str(paths) + 'paths\n')
                ## paths = random.choice(list(nx.all_simple_paths(G, source=0, target=len(t))))
                ## ctr = 1
                # for p in nx.all_simple_paths(G, source=0, target=len(t)):
                #     paths = p
                    ## sys.stderr.write(str(ctr) + '\n')
                    ## ctr += 1
                    # break
                # sys.stderr.write(str(list(nx.all_simple_paths(G, source=0, target=len(t)))) + 'paths\n')
                # sys.exit()
                #all shortest paths
                # print 'edgeLabels', edgeLabels
                # print 'edges', G.edges()
                # print 'paths', paths
                # for i in range(len(paths[0])):
                optimalParsing = []
                for i in range(len(paths)-1):
                    if edgeLabels[(paths[i], paths[i + 1])] == -1:
                        # print t[paths[i]],
                        optimalParsing.append(t[paths[i]])
                    else:
                        # print edgeLabels[(paths[i],paths[i+1])],
                        optimalParsing.append(edgeLabels[(paths[i],paths[i+1])])
                        countingNumberOfOptimalParsings_Recombination += 1
                # print
                # sys.exit()
                # if len(t) > len(optimalParsing):
                #     print 'yaaaaaaaaaaay1'
                optimallyParsedTargetInts.append(optimalParsing)
                # newParsedTargets.append(optimalParsing)
                newParsedTargets[-1].append(optimalParsing)
                # if len(newParsedTargets[-1]) >= 2:
                #     print 'YES'
                ratios.append(float(len(optimalParsing))/len(t))
        optimalParsingCombinations = list(itertools.product(*newParsedTargets))
        # print 'combs'
        # print optimalParsingCombinations
        previousCost = g.grammarCost(CostFunction.EdgeCost)
        originalCost = previousCost
        for t in newTargetsInt:
            originalCost += len(t)
        intermediateCost = previousCost
        optCost = 0
        for s in optimallyParsedTargetInts:
            intermediateCost += len(s)
            optCost += len(s)
        # print str(intermediateCost) + '\t',
        # add newly parsed targets to grammar and convert grammardic to new grammar
        # for t in optimallyParsedTargetInts:
        #     grammarDic[0].append(t)
        # sys.stderr.write(str(x) + ' 2\n')
        previousDic = g.dic

        minCost = totalLengthNewTargets
        minParsing = []
        for optimallyParsedTargetInts in optimalParsingCombinations:
            # print optimallyParsedTargetInts
            g = None
            tmpOut = open(working_path + '/tmpOut-'+str(batchSize) + fileName + '--.txt', 'w')
            for t in optimallyParsedTargetInts:
                for c in t:
                    tmpOut.write(str(c) + ' ')
                tmpOut.write('\n')
            tmpOut.close()
            g = Grammar(open(working_path + '/tmpOut-'+str(batchSize) + fileName + '--.txt', 'r'), 'file', gap, chFlag, noNewLineFlag)
            # os.remove('tmpOut.txt')
            g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
            # if previousCost + g.grammarCost(CostFunction.EdgeCost) < intermediateCost:
            #     print 'yaaaaaaaaaaay2',
            # sys.stderr.write(str(x) + ' 22\n')
            # g.printGrammarWithOffsetToNTs(printIntsGrammar, maxInt, inputDic=previousDic)
            # g = Grammar(open('tmpGram.txt', 'r'), 'grammar', gap, chFlag, noNewLineFlag)
            # if len(optimalParsingCombinations) >= 2:
            #     print 'minCost\t' + str(g.grammarCost(CostFunction.EdgeCost))
            if minCost >= g.grammarCost(CostFunction.EdgeCost):
                # if minCost != totalLengthNewTargets:
                # print 'diff' + '\t' + str(minCost) + '\t' + str(g.grammarCost(CostFunction.EdgeCost))
                minCost = g.grammarCost(CostFunction.EdgeCost)
                minParsing = optimallyParsedTargetInts
            if firstChoice:
                break
        g = None
        tmpOut = open(working_path + '/tmpOut-'+str(batchSize) + fileName + '--.txt', 'w')
        for t in minParsing:
            for c in t:
                tmpOut.write(str(c) + ' ')
            tmpOut.write('\n')
        tmpOut.close()
        g = Grammar(open(working_path + '/tmpOut-'+str(batchSize) + fileName + '--.txt', 'r'), 'file', gap, chFlag, noNewLineFlag)
        # os.remove('tmpOut.txt')
        g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
        # g.printGrammarToFile(sys_args[-1] + "incGlex_" + str(x)+'.txt', printIntsGrammar)

        newGrammarDic = g.grammarDic()
        # print newGrammarDic
        maxIntChar = -1
        for nt in grammarDic:
            for rule in grammarDic[nt]:
                for c in rule:
                    if maxIntChar < int(c):
                        maxIntChar = int(c)
        maxIntChar += 2
        newNts = {}
        for nt in sorted(newGrammarDic.keys()):
            # if nt in grammarDic:
            if nt != 0:
                newNts[nt] = nt + maxIntChar
                maxIntChar += 2
        tmpNewGrammarDic = {}
        for nt in newGrammarDic:
            tmpRHS = []
            # if nt == 0:
            for rule in newGrammarDic[nt]:
                # print rule
                tmpRRHS = []
                for c in rule:
                    # if c == 1507:
                    #     print 'wowowow', newGrammarDic[1507]
                    if c in g.dic:
                        tmpRRHS.append(int(g.dic[c]))
                    else:
                        if c in newNts:
                            tmpRRHS.append(int(newNts[c]))
                        else:
                            tmpRRHS.append(int(c))
                if nt!=0:
                    if tmpRRHS[0] == newNts[nt]:
                        print 'damn!'
                        print nt
                        print tmpRRHS
                        print rule
                        print newGrammarDic[nt]
                tmpRHS.append(tmpRRHS)
            # else:
            #     for c in newGrammarDic[nt]:
            #         print c
            #         if c in g.dic:
            #             tmpRHS.append(int(g.dic[c]))
            #         else:
            #             tmpRHS.append(int(c))Q
            if nt in newNts:
                tmpNewGrammarDic[newNts[nt]] = tmpRHS
            else:
                newGrammarDic[nt] = tmpRHS
        for nt in newNts:
            newGrammarDic.pop(nt)
        for nt in tmpNewGrammarDic:
            newGrammarDic[nt] = tmpNewGrammarDic[nt]
        # print newGrammarDic

        # print grammarDic
        for nt in newGrammarDic:
            if nt in grammarDic:
                if nt == 0:
                    grammarDic[nt].extend(newGrammarDic[nt])
                else:
                    # print nt, newGrammarDic[nt]
                    # grammarDic[nt + maxIntChar] = newGrammarDic[nt]
                    # print 1, nt + maxIntChar
                    # print 3, grammarDic[1507]
                    # maxIntChar += 2
                    print 'error'
                    sys.exit(0)
            else:
                # print nt, newGrammarDic[nt]
                grammarDic[nt] = newGrammarDic[nt]
                # grammarDic[nt + maxIntChar] = newGrammarDic[nt]
                # print 2, nt + maxIntChar
                # print 4, grammarDic[1507]
                # maxIntChar += 2
        # sys.stderr.write(str(x) + ' 3\n')
        g.initFromGrammarDic(grammarDic, previousDic)
        # break
        # while True:
        #     maxR = g.retreiveMaximumGainRepeat(rFlag, CostFunction.EdgeCost)
        #     if maxR['score'] == -1:
        #         break
        #     else:
        #         # print '\tmaxR'
        #         sys.stderr.write(str(maxR) + '\n')
        #         g.replaceRepeat(maxR['length'], maxR['occs'])
        # g.printGrammar(printIntsGrammar)
        # print countingNumberOfOptimalParsings_Recombination
        if len(tmp_dataset) - prev_len_tmp_dataset > data_increment * float(LEN_MAIN):
            lengthPer = str(int(math.floor((float(len(tmp_dataset)) / float(LEN_MAIN)) * 100)))
            # print len(tmp_dataset), LEN_MAIN, lengthPer
            ###print 'Length %', lengthPer
            ###g.printGrammarToFile(folder + fileName + '-' + lengthPer, printIntsGrammar)
            prev_len_tmp_dataset = len(tmp_dataset)
    ###g.printGrammarToFile(folder + fileName + '-100.txt', printIntsGrammar)
    return g
    #     print
    #     print str(originalCost) + '\t' + str(intermediateCost) + '\t' + str(g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(g.grammarCost(CostFunction.EdgeCost)-previousCost) + '\t' + str(totalLengthNewTargets) + '\t' + str(totalLength)
    #     g.printGrammarToFile(sys_args[-1]+str(x/batchSize+1)+'.txt', printIntsGrammar)
    #     print str(g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(totalLengthNewTargets) + '\t' + str(totalLength)


        # print str(g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(g.grammarCost(CostFunction.EdgeCost)-previousCost) + '\t' + str(totalLengthNewTargets) + '\t' + str(totalLength)



        # g.printGrammarToFile(sys_args[-1]+'gram'+str(numData)+'.txt', printIntsGrammar)




        # g.printGrammarToFile('tmpGram.txt', printIntsGrammar)
        # sys.stderr.write(str(numData) + '\n')
        # try:
        #     print str(totalLength) + '\t' + str(totalLengthNewTargets) + '\t' + str(intermediateCost-previousCost) + '\t' + str(totalLengthNewTargets-(intermediateCost-previousCost)) + '\t' + str((intermediateCost-previousCost)-(intermediateCost-g.grammarCost(CostFunction.EdgeCost))) + '\t' + str(intermediateCost-g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(g.grammarCost(CostFunction.EdgeCost))\
        #     + '\t' + str(structSimTest(open('tmpGram.txt','r').read(),\
        #                   open('/Users/payamsiyari/Desktop/inc/inc-fullProfile/clean-slate full profile/gram' + str(numData) + '.txt','r').read()))
        # except:
        #     pass


    # previousDic = g.dic
    # g = None
    # tmpOut = open('tmpOut.txt','w')
    # for t in newParsedTargets:
    #     for c in t:
    #         tmpOut.write(str(c) + ' ')
    #     tmpOut.write('\n')
    # tmpOut.close()
    # g = Grammar(open('tmpOut.txt', 'r'), 'file', gap, chFlag, noNewLineFlag)
    # g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
    # g.printGrammarWithOffsetToNTs(printIntsGrammar, maxInt, inputDic=previousDic)

    # g.printGrammarToFile(sys_args[-1]+'.txt', printIntsGrammar)

    #Only for target ratio testing
    # sumNewLengths = 0
    # for t in optimallyParsedTargetInts:
    #     sumNewLengths += len(t)
    # return sumNewLengths

    return ratios

def remove_targets_from_DAG(input_file):
    chFlag = SequenceType.SpaceSeparated;
    noNewLineFlag = False;
    gap = 50
    g = Grammar(open(input_file, 'r'), 'grammar', gap, chFlag, noNewLineFlag)

def idea3_Fixed(sys_args, batchSize=10, init_batch=.05):
    folder = '/'.join(sys_args[-1].split('/')[:-1]) + '/INC-DAGs/inc-b'+str(batchSize)+'/'
    # folder = 'TBTG/NewData3/Data/INC-DAGs'
    if not os.path.exists(folder):
        os.makedirs(folder)
    fileName = sys_args[-1].split('/')[-1].split('.')[0]
    data_increment = 0.1
    firstChoice = True
    mainFile = open(sys_args[-1], 'r').read().splitlines()
    LEN_MAIN = len(mainFile)
    # init = init_batch
    init = float(batchSize)/LEN_MAIN
    counter = 0
    initData = []
    for l in mainFile:
        if counter < init*LEN_MAIN:
            initData.append(mainFile.pop(0))
        else:
            break
        counter += 1
    tmpOut = open('tmpOut-'+str(batchSize) + fileName + '--.txt', 'w')
    for l in initData:
        tmpOut.write(l + '\n')
    tmpOut.close()
    g = Grammar(open('tmpOut-'+str(batchSize) + fileName + '--.txt', 'r'), 'file', gap, chFlag, noNewLineFlag)
    totalLength = open('tmpOut-'+str(batchSize) + fileName + '--.txt', 'r').read().count(' ')
    numData = open('tmpOut-'+str(batchSize) + fileName + '--.txt', 'r').read().count('\n')
    # totalLength = 1496
    reverseDic = {}
    maxInt = -1
    for c in g.dic:
        if maxInt < c:
            maxInt = c + 2
        reverseDic[g.dic[c]] = c
    g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
    g.printGrammarToFile(folder + fileName + '-0.txt',printIntsGrammar)
    seedCost = g.grammarCost(CostFunction.EdgeCost)
    # output = open('tmpGram.txt', 'w')
    # output.write('\n')
    # output.close()
    # g.printGrammarWithOffsetToNTs(printIntsGrammar, 0)
    # g.printGrammar(printIntsGrammar)
    # return

    # allNewTargets = open(sys_args[-2], 'r').read().splitlines()
    allNewTargets = mainFile
    LEN = len(allNewTargets)
    ratios = []
    newParsedTargets = []
    ntYields = {}
    countingNumberOfOptimalParsings_Recombination = 0
    countingNumberOfGlexises_Innovation = 0
    tmp_dataset = []
    prev_len_tmp_dataset = 0
    remaining_batch_targets = []
    for x in range(0, len(allNewTargets), batchSize):
        # sys.stderr.write(str(x) + '\n')
        newTargets = []
        newTargets = remaining_batch_targets
        numData += len(remaining_batch_targets)
        remaining_batch_targets = []
        for j in range(x, x + batchSize):
            # if not noNewLineFlag:
            if j >= len(allNewTargets):
                break
            if len(tmp_dataset) - prev_len_tmp_dataset > data_increment * float(LEN_MAIN):
                for k in range(j,x+batchSize):
                    remaining_batch_targets.append(allNewTargets[k])
                break
            newTargets.append(allNewTargets[j])  # Assuming space sep chars
            # tmp_dataset.append(allNewTargets[j])  # Assuming space sep chars
            numData += 1
            # else:
            # newTargets.append(allNewTargets[j].split())  # Assuming space sep chars
        tmp_dataset = tmp_dataset + newTargets
        newTargetsInt = []
        # print newTargets
        totalLengthNewTargets = 0
        for t in newTargets:
            tmpT = []
            tt = t.split()
            totalLengthNewTargets += len(tt)
            totalLength += len(tt)
            for i in range(len(tt)):  # For space-sep chars
                if tt[i] in reverseDic:
                    tmpT.append(reverseDic[tt[i]])
                else:
                    reverseDic[tt[i]] = maxInt
                    g.dic[maxInt] = tt[i]
                    maxInt += 2
                    tmpT.append(reverseDic[tt[i]])
            # for i in range(len(t)):#For seq chars
            #     if t[i] in reverseDic:
            #         tmpT.append(reverseDic[t[i]])
            #     else:
            #         reverseDic[t[i]] = maxInt
            #         g.dic[maxInt] = t[i]
            #         maxInt += 2
            #         tmpT.append(reverseDic[t[i]])
            newTargetsInt.append(tmpT)
        # print newTargetsInt
        # print g.dic
        # print reverseDic

        # print 'int', newTargetsInt
        # #D_t
        # sys.stderr.write(str(numData) + '\n')
        grammarDic = g.grammarDic()
        # ntYields = {}
        # for nt in grammarDic:
        #     if nt == 0:
        #         continue
        #     if nt in ntYields:
        #         ntYields[nt].append(g.ntYield(grammarDic, nt))
        #     else:
        #         ntYields[nt] = [g.ntYield(grammarDic, nt)]
        for nt in grammarDic:
            if nt == 0 or nt in ntYields:
                continue
            else:
                # print 'initial NT', nt
                ntYields[nt] = [g.ntYield(grammarDic, nt)]
        #run optimal parsing on newTargetsInt
        optimallyParsedTargetInts =[]
        newParsedTargets = []
        # print '-------', newTargetsInt
        # print '-------', grammarDic
        # print '-------', ntYields
        for t in newTargetsInt:
            #create a graph
            G = nx.DiGraph()
            edgeLabels = {} #used for saving non-terminals
            G.add_nodes_from([0, len(t)+1])
            for i in range(len(t)):
                G.add_edge(i, i+1)
                edgeLabels[(i,i+1)] = -1
            # print 'ntYields.keys()', ntYields.keys()
            # print 't', t
            for nt in ntYields:
                newEdgesStarts = KnuthMorrisPratt(t, ntYields[nt][0])
                # print 't', t
                # print 'ntYields[nt]', nt, ntYields[nt][0]
                # print 'newEdgesStarts', newEdgesStarts
                for s in newEdgesStarts:
                    G.add_edge(s, s+len(ntYields[nt][0]))
                    edgeLabels[(s, s+len(ntYields[nt][0]))] = nt
            # paths = nx.shortest_path(G, source=0, target=len(t), weight=None)
            shortestPaths = nx.all_shortest_paths(G, source=0, target=len(t), weight=None)
            shortestPaths = [p for p in shortestPaths]
            shortestPaths = [shortestPaths[0]]
            # if len(shortestPaths) >= 2:
            #     print 'YES'
            newParsedTargets.append([])
            for paths in shortestPaths:
                ## sys.stderr.write(str(paths) + 'paths\n')
                ## paths = random.choice(list(nx.all_simple_paths(G, source=0, target=len(t))))
                ## ctr = 1
                # for p in nx.all_simple_paths(G, source=0, target=len(t)):
                #     paths = p
                    ## sys.stderr.write(str(ctr) + '\n')
                    ## ctr += 1
                    # break
                # sys.stderr.write(str(list(nx.all_simple_paths(G, source=0, target=len(t)))) + 'paths\n')
                # sys.exit()
                #all shortest paths
                # print 'edgeLabels', edgeLabels
                # print 'edges', G.edges()
                # print 'paths', paths
                # for i in range(len(paths[0])):
                optimalParsing = []
                for i in range(len(paths)-1):
                    if edgeLabels[(paths[i], paths[i + 1])] == -1:
                        # print t[paths[i]],
                        optimalParsing.append(t[paths[i]])
                    else:
                        # print edgeLabels[(paths[i],paths[i+1])],
                        optimalParsing.append(edgeLabels[(paths[i],paths[i+1])])
                        countingNumberOfOptimalParsings_Recombination += 1
                # print
                # sys.exit()
                # if len(t) > len(optimalParsing):
                #     print 'yaaaaaaaaaaay1'
                optimallyParsedTargetInts.append(optimalParsing)
                # newParsedTargets.append(optimalParsing)
                newParsedTargets[-1].append(optimalParsing)
                # if len(newParsedTargets[-1]) >= 2:
                #     print 'YES'
                ratios.append(float(len(optimalParsing))/len(t))
        optimalParsingCombinations = list(itertools.product(*newParsedTargets))
        # print '=========', optimalParsingCombinations[0]
        # print 'combs'
        # print optimalParsingCombinations
        previousCost = g.grammarCost(CostFunction.EdgeCost)
        originalCost = previousCost
        for t in newTargetsInt:
            originalCost += len(t)
        intermediateCost = previousCost
        optCost = 0
        for s in optimallyParsedTargetInts:
            intermediateCost += len(s)
            optCost += len(s)
        # print str(intermediateCost) + '\t',
        # add newly parsed targets to grammar and convert grammardic to new grammar
        # for t in optimallyParsedTargetInts:
        #     grammarDic[0].append(t)
        # sys.stderr.write(str(x) + ' 2\n')
        previousDic = g.dic

        minCost = totalLengthNewTargets
        minParsing = []
        for optimallyParsedTargetInts in optimalParsingCombinations:
            # print optimallyParsedTargetInts
            g = None
            tmpOut = open('tmpOut-'+str(batchSize) + fileName + '--.txt', 'w')
            for t in optimallyParsedTargetInts:
                for c in t:
                    tmpOut.write(str(c) + ' ')
                tmpOut.write('\n')
            tmpOut.close()
            g = Grammar(open('tmpOut-'+str(batchSize) + fileName + '--.txt', 'r'), 'file', gap, chFlag, noNewLineFlag)
            # os.remove('tmpOut.txt')
            g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
            # if previousCost + g.grammarCost(CostFunction.EdgeCost) < intermediateCost:
            #     print 'yaaaaaaaaaaay2',
            # sys.stderr.write(str(x) + ' 22\n')
            # g.printGrammarWithOffsetToNTs(printIntsGrammar, maxInt, inputDic=previousDic)
            # g = Grammar(open('tmpGram.txt', 'r'), 'grammar', gap, chFlag, noNewLineFlag)
            # if len(optimalParsingCombinations) >= 2:
            #     print 'minCost\t' + str(g.grammarCost(CostFunction.EdgeCost))
            if minCost >= g.grammarCost(CostFunction.EdgeCost):
                # if minCost != totalLengthNewTargets:
                # print 'diff' + '\t' + str(minCost) + '\t' + str(g.grammarCost(CostFunction.EdgeCost))
                minCost = g.grammarCost(CostFunction.EdgeCost)
                minParsing = optimallyParsedTargetInts
            if firstChoice:
                break
        g = None
        tmpOut = open('tmpOut-'+str(batchSize) + fileName + '--.txt', 'w')
        for t in minParsing:
            for c in t:
                tmpOut.write(str(c) + ' ')
            tmpOut.write('\n')
        tmpOut.close()
        g = Grammar(open('tmpOut-'+str(batchSize) + fileName + '--.txt', 'r'), 'file', gap, chFlag, noNewLineFlag)
        # os.remove('tmpOut.txt')
        g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
        # g.printGrammarToFile(sys_args[-1] + "incGlex_" + str(x)+'.txt', printIntsGrammar)

        newGrammarDic = g.grammarDic()
        # print newGrammarDic
        maxIntChar = -1
        for nt in grammarDic:
            for rule in grammarDic[nt]:
                for c in rule:
                    if maxIntChar < int(c):
                        maxIntChar = int(c)
        maxIntChar += 2
        newNts = {}
        for nt in sorted(newGrammarDic.keys()):
            # if nt in grammarDic:
            if nt != 0:
                newNts[nt] = nt + maxIntChar
                maxIntChar += 2
        tmpNewGrammarDic = {}
        for nt in newGrammarDic:
            tmpRHS = []
            # if nt == 0:
            for rule in newGrammarDic[nt]:
                # print rule
                tmpRRHS = []
                for c in rule:
                    # if c == 1507:
                    #     print 'wowowow', newGrammarDic[1507]
                    if c in g.dic:
                        tmpRRHS.append(int(g.dic[c]))
                    else:
                        if c in newNts:
                            tmpRRHS.append(int(newNts[c]))
                        else:
                            tmpRRHS.append(int(c))
                if nt!=0:
                    if tmpRRHS[0] == newNts[nt]:
                        print 'damn!'
                        print nt
                        print tmpRRHS
                        print rule
                        print newGrammarDic[nt]
                tmpRHS.append(tmpRRHS)
            # else:
            #     for c in newGrammarDic[nt]:
            #         print c
            #         if c in g.dic:
            #             tmpRHS.append(int(g.dic[c]))
            #         else:
            #             tmpRHS.append(int(c))Q
            if nt in newNts:
                tmpNewGrammarDic[newNts[nt]] = tmpRHS
            else:
                newGrammarDic[nt] = tmpRHS
        for nt in newNts:
            newGrammarDic.pop(nt)
        for nt in tmpNewGrammarDic:
            newGrammarDic[nt] = tmpNewGrammarDic[nt]
        # print newGrammarDic

        # print grammarDic
        for nt in newGrammarDic:
            if nt in grammarDic:
                if nt == 0:
                    grammarDic[nt].extend(newGrammarDic[nt])
                else:
                    # print nt, newGrammarDic[nt]
                    # grammarDic[nt + maxIntChar] = newGrammarDic[nt]
                    # print 1, nt + maxIntChar
                    # print 3, grammarDic[1507]
                    # maxIntChar += 2
                    print 'error'
                    sys.exit(0)
            else:
                # print nt, newGrammarDic[nt]
                grammarDic[nt] = newGrammarDic[nt]
                # grammarDic[nt + maxIntChar] = newGrammarDic[nt]
                # print 2, nt + maxIntChar
                # print 4, grammarDic[1507]
                # maxIntChar += 2
        # sys.stderr.write(str(x) + ' 3\n')
        g.initFromGrammarDic(grammarDic, previousDic)
        # break
        # while True:
        #     maxR = g.retreiveMaximumGainRepeat(rFlag, CostFunction.EdgeCost)
        #     if maxR['score'] == -1:
        #         break
        #     else:
        #         # print '\tmaxR'
        #         sys.stderr.write(str(maxR) + '\n')
        #         g.replaceRepeat(maxR['length'], maxR['occs'])
        # g.printGrammar(printIntsGrammar)
        # print countingNumberOfOptimalParsings_Recombination
        if len(tmp_dataset) - prev_len_tmp_dataset > data_increment * float(LEN_MAIN):
            lengthPer = str(int(math.floor((float(len(tmp_dataset)) / float(LEN_MAIN)) * 100)))
            # print len(tmp_dataset), LEN_MAIN, lengthPer
            print 'Length %', lengthPer
            g.printGrammarToFile(folder + fileName + '-' + lengthPer+'.txt', printIntsGrammar)
            prev_len_tmp_dataset = len(tmp_dataset)
    g.printGrammarToFile(folder + fileName + '-100.txt', printIntsGrammar)
    #     print
    #     print str(originalCost) + '\t' + str(intermediateCost) + '\t' + str(g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(g.grammarCost(CostFunction.EdgeCost)-previousCost) + '\t' + str(totalLengthNewTargets) + '\t' + str(totalLength)
    #     g.printGrammarToFile(sys_args[-1]+str(x/batchSize+1)+'.txt', printIntsGrammar)
    #     print str(g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(totalLengthNewTargets) + '\t' + str(totalLength)


        # print str(g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(g.grammarCost(CostFunction.EdgeCost)-previousCost) + '\t' + str(totalLengthNewTargets) + '\t' + str(totalLength)



        # g.printGrammarToFile(sys_args[-1]+'gram'+str(numData)+'.txt', printIntsGrammar)




        # g.printGrammarToFile('tmpGram.txt', printIntsGrammar)
        # sys.stderr.write(str(numData) + '\n')
        # try:
        #     print str(totalLength) + '\t' + str(totalLengthNewTargets) + '\t' + str(intermediateCost-previousCost) + '\t' + str(totalLengthNewTargets-(intermediateCost-previousCost)) + '\t' + str((intermediateCost-previousCost)-(intermediateCost-g.grammarCost(CostFunction.EdgeCost))) + '\t' + str(intermediateCost-g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(g.grammarCost(CostFunction.EdgeCost))\
        #     + '\t' + str(structSimTest(open('tmpGram.txt','r').read(),\
        #                   open('/Users/payamsiyari/Desktop/inc/inc-fullProfile/clean-slate full profile/gram' + str(numData) + '.txt','r').read()))
        # except:
        #     pass


    # previousDic = g.dic
    # g = None
    # tmpOut = open('tmpOut.txt','w')
    # for t in newParsedTargets:
    #     for c in t:
    #         tmpOut.write(str(c) + ' ')
    #     tmpOut.write('\n')
    # tmpOut.close()
    # g = Grammar(open('tmpOut.txt', 'r'), 'file', gap, chFlag, noNewLineFlag)
    # g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
    # g.printGrammarWithOffsetToNTs(printIntsGrammar, maxInt, inputDic=previousDic)

    # g.printGrammarToFile(sys_args[-1]+'.txt', printIntsGrammar)

    #Only for target ratio testing
    # sumNewLengths = 0
    # for t in optimallyParsedTargetInts:
    #     sumNewLengths += len(t)
    # return sumNewLengths

    return ratios

def idea3_Fixed_2(sys_args, start, k, batchSize):
    firstChoice = True
    allLines = open(sys.argv[-2], 'r').readlines()
    allLines = allLines[start:start+k]
    R0 = allLines[:int(0.05*len(allLines))]
    data = allLines[int(0.05*len(allLines)):]

    tmp_R0 = open('tmp.txt', 'w')
    for l in R0:
        tmp_R0.write(l)
    tmp_R0.close()
    g = Grammar(open('tmp.txt', 'r'), 'file', gap, chFlag, noNewLineFlag)
    totalLength = open('tmp.txt', 'r').read().count(' ')
    # totalLength = 1496
    reverseDic = {}
    maxInt = -1
    for c in g.dic:
        if maxInt < c:
            maxInt = c + 2
        reverseDic[g.dic[c]] = c
    g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
    seedCost = g.grammarCost(CostFunction.EdgeCost)
    # output = open('tmpGram.txt', 'w')
    # output.write('\n')
    # output.close()
    # g.printGrammarWithOffsetToNTs(printIntsGrammar, 0)
    # g.printGrammar(printIntsGrammar)
    # return
    tmp_R = open('tmp.txt', 'w')
    for l in data:
        tmp_R.write(l)
    tmp_R.close()
    allNewTargets = open('tmp.txt', 'r').read().splitlines()
    ratios = []
    newParsedTargets = []
    ntYields = {}
    countingNumberOfOptimalParsings_Recombination = 0
    countingNumberOfGlexises_Innovation = 0
    for x in range(0, len(allNewTargets), batchSize):
        # sys.stderr.write(str(x) + '\n')
        newTargets = []
        for j in range(x, x + batchSize):
            # if not noNewLineFlag:
            if j >= len(allNewTargets):
                break
            newTargets.append(allNewTargets[j])  # Assuming space sep chars
            # else:
            # newTargets.append(allNewTargets[j].split())  # Assuming space sep chars
        newTargetsInt = []
        # print newTargets
        totalLengthNewTargets = 0
        for t in newTargets:
            tmpT = []
            tt = t.split()
            totalLengthNewTargets += len(tt)
            totalLength += len(tt)
            for i in range(len(tt)):  # For space-sep chars
                if tt[i] in reverseDic:
                    tmpT.append(reverseDic[tt[i]])
                else:
                    reverseDic[tt[i]] = maxInt
                    g.dic[maxInt] = tt[i]
                    maxInt += 2
                    tmpT.append(reverseDic[tt[i]])
            # for i in range(len(t)):#For seq chars
            #     if t[i] in reverseDic:
            #         tmpT.append(reverseDic[t[i]])
            #     else:
            #         reverseDic[t[i]] = maxInt
            #         g.dic[maxInt] = t[i]
            #         maxInt += 2
            #         tmpT.append(reverseDic[t[i]])
            newTargetsInt.append(tmpT)
        # print newTargetsInt
        # print g.dic
        # print reverseDic

        # print 'int', newTargetsInt
        # #D_t
        grammarDic = g.grammarDic()
        # ntYields = {}
        # for nt in grammarDic:
        #     if nt == 0:
        #         continue
        #     if nt in ntYields:
        #         ntYields[nt].append(g.ntYield(grammarDic, nt))
        #     else:
        #         ntYields[nt] = [g.ntYield(grammarDic, nt)]
        for nt in grammarDic:
            if nt == 0 or nt in ntYields:
                continue
            else:
                # print 'initial NT', nt
                ntYields[nt] = [g.ntYield(grammarDic, nt)]
        #run optimal parsing on newTargetsInt
        optimallyParsedTargetInts =[]
        newParsedTargets = []
        for t in newTargetsInt:
            #create a graph
            G = nx.DiGraph()
            edgeLabels = {} #used for saving non-terminals
            G.add_nodes_from([0, len(t)+1])
            for i in range(len(t)):
                G.add_edge(i, i+1)
                edgeLabels[(i,i+1)] = -1
            # print 'ntYields.keys()', ntYields.keys()
            # print 't', t
            for nt in ntYields:
                newEdgesStarts = KnuthMorrisPratt(t, ntYields[nt][0])
                # print 't', t
                # print 'ntYields[nt]', nt, ntYields[nt][0]
                # print 'newEdgesStarts', newEdgesStarts
                for s in newEdgesStarts:
                    G.add_edge(s, s+len(ntYields[nt][0]))
                    edgeLabels[(s, s+len(ntYields[nt][0]))] = nt
            # paths = nx.shortest_path(G, source=0, target=len(t), weight=None)
            shortestPaths = nx.all_shortest_paths(G, source=0, target=len(t), weight=None)
            shortestPaths = [p for p in shortestPaths]
            shortestPaths = [shortestPaths[0]]
            # if len(shortestPaths) >= 2:
            #     print 'YES'
            newParsedTargets.append([])
            for paths in shortestPaths:
                ## sys.stderr.write(str(paths) + 'paths\n')
                ## paths = random.choice(list(nx.all_simple_paths(G, source=0, target=len(t))))
                ## ctr = 1
                # for p in nx.all_simple_paths(G, source=0, target=len(t)):
                #     paths = p
                    ## sys.stderr.write(str(ctr) + '\n')
                    ## ctr += 1
                    # break
                # sys.stderr.write(str(list(nx.all_simple_paths(G, source=0, target=len(t)))) + 'paths\n')
                # sys.exit()
                #all shortest paths
                # print 'edgeLabels', edgeLabels
                # print 'edges', G.edges()
                # print 'paths', paths
                # for i in range(len(paths[0])):
                optimalParsing = []
                for i in range(len(paths)-1):
                    if edgeLabels[(paths[i], paths[i + 1])] == -1:
                        # print t[paths[i]],
                        optimalParsing.append(t[paths[i]])
                    else:
                        # print edgeLabels[(paths[i],paths[i+1])],
                        optimalParsing.append(edgeLabels[(paths[i],paths[i+1])])
                        countingNumberOfOptimalParsings_Recombination += 1
                # print
                # sys.exit()
                # if len(t) > len(optimalParsing):
                #     print 'yaaaaaaaaaaay1'
                optimallyParsedTargetInts.append(optimalParsing)
                # newParsedTargets.append(optimalParsing)
                newParsedTargets[-1].append(optimalParsing)
                # if len(newParsedTargets[-1]) >= 2:
                #     print 'YES'
                ratios.append(float(len(optimalParsing))/len(t))
        optimalParsingCombinations = list(itertools.product(*newParsedTargets))
        # print 'combs'
        # print optimalParsingCombinations
        previousCost = g.grammarCost(CostFunction.EdgeCost)
        originalCost = previousCost
        for t in newTargetsInt:
            originalCost += len(t)
        intermediateCost = previousCost
        for s in optimallyParsedTargetInts:
            intermediateCost += len(s)
        # print str(intermediateCost) + '\t',
        # add newly parsed targets to grammar and convert grammardic to new grammar
        # for t in optimallyParsedTargetInts:
        #     grammarDic[0].append(t)
        # sys.stderr.write(str(x) + ' 2\n')
        previousDic = g.dic

        minCost = totalLengthNewTargets
        minParsing = []
        for optimallyParsedTargetInts in optimalParsingCombinations:
            # print optimallyParsedTargetInts
            g = None
            tmpOut = open('tmpOut.txt', 'w')
            for t in optimallyParsedTargetInts:
                for c in t:
                    tmpOut.write(str(c) + ' ')
                tmpOut.write('\n')
            tmpOut.close()
            g = Grammar(open('tmpOut.txt', 'r'), 'file', gap, chFlag, noNewLineFlag)
            # os.remove('tmpOut.txt')
            g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
            # if previousCost + g.grammarCost(CostFunction.EdgeCost) < intermediateCost:
            #     print 'yaaaaaaaaaaay2',
            # sys.stderr.write(str(x) + ' 22\n')
            # g.printGrammarWithOffsetToNTs(printIntsGrammar, maxInt, inputDic=previousDic)
            # g = Grammar(open('tmpGram.txt', 'r'), 'grammar', gap, chFlag, noNewLineFlag)
            # if len(optimalParsingCombinations) >= 2:
            #     print 'minCost\t' + str(g.grammarCost(CostFunction.EdgeCost))
            if minCost >= g.grammarCost(CostFunction.EdgeCost):
                # if minCost != totalLengthNewTargets:
                # print 'diff' + '\t' + str(minCost) + '\t' + str(g.grammarCost(CostFunction.EdgeCost))
                minCost = g.grammarCost(CostFunction.EdgeCost)
                minParsing = optimallyParsedTargetInts
            if firstChoice:
                break
        g = None
        tmpOut = open('tmpOut.txt', 'w')
        for t in minParsing:
            for c in t:
                tmpOut.write(str(c) + ' ')
            tmpOut.write('\n')
        tmpOut.close()
        g = Grammar(open('tmpOut.txt', 'r'), 'file', gap, chFlag, noNewLineFlag)
        # os.remove('tmpOut.txt')
        g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
        # g.printGrammarToFile(sys_args[-1] + "incGlex_" + str(x)+'.txt', printIntsGrammar)

        newGrammarDic = g.grammarDic()
        # print newGrammarDic
        maxIntChar = -1
        for nt in grammarDic:
            for rule in grammarDic[nt]:
                for c in rule:
                    if maxIntChar < int(c):
                        maxIntChar = int(c)
        maxIntChar += 2
        newNts = {}
        for nt in newGrammarDic:
            # if nt in grammarDic:
            if nt != 0:
                newNts[nt] = nt + maxIntChar
                maxIntChar += 2
        tmpNewGrammarDic = {}
        for nt in newGrammarDic:
            tmpRHS = []
            # if nt == 0:
            for rule in newGrammarDic[nt]:
                # print rule
                tmpRRHS = []
                for c in rule:
                    # if c == 1507:
                    #     print 'wowowow', newGrammarDic[1507]
                    if c in g.dic:
                        tmpRRHS.append(int(g.dic[c]))
                    else:
                        if c in newNts:
                            tmpRRHS.append(int(newNts[c]))
                        else:
                            tmpRRHS.append(int(c))
                tmpRHS.append(tmpRRHS)
            # else:
            #     for c in newGrammarDic[nt]:
            #         print c
            #         if c in g.dic:
            #             tmpRHS.append(int(g.dic[c]))
            #         else:
            #             tmpRHS.append(int(c))Q
            if nt in newNts:
                tmpNewGrammarDic[newNts[nt]] = tmpRHS
            else:
                newGrammarDic[nt] = tmpRHS
        for nt in newNts:
            newGrammarDic.pop(nt)
        for nt in tmpNewGrammarDic:
            newGrammarDic[nt] = tmpNewGrammarDic[nt]
        # print newGrammarDic

        # print grammarDic
        for nt in newGrammarDic:
            if nt in grammarDic:
                if nt == 0:
                    grammarDic[nt].extend(newGrammarDic[nt])
                else:
                    # print nt, newGrammarDic[nt]
                    # grammarDic[nt + maxIntChar] = newGrammarDic[nt]
                    # print 1, nt + maxIntChar
                    # print 3, grammarDic[1507]
                    # maxIntChar += 2
                    print 'error'
                    sys.exit(0)
            else:
                # print nt, newGrammarDic[nt]
                grammarDic[nt] = newGrammarDic[nt]
                # grammarDic[nt + maxIntChar] = newGrammarDic[nt]
                # print 2, nt + maxIntChar
                # print 4, grammarDic[1507]
                # maxIntChar += 2
        # sys.stderr.write(str(x) + ' 3\n')
        g.initFromGrammarDic(grammarDic, previousDic)
        # break
        # while True:
        #     maxR = g.retreiveMaximumGainRepeat(rFlag, CostFunction.EdgeCost)
        #     if maxR['score'] == -1:
        #         break
        #     else:
        #         # print '\tmaxR'
        #         sys.stderr.write(str(maxR) + '\n')
        #         g.replaceRepeat(maxR['length'], maxR['occs'])
        # g.printGrammar(printIntsGrammar)
        # print countingNumberOfOptimalParsings_Recombination
        # g.printGrammarToFile(sys_args[-1] + str(77+x) + '.txt', printIntsGrammar)
    #     print
    #     print str(originalCost) + '\t' + str(intermediateCost) + '\t' + str(g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(g.grammarCost(CostFunction.EdgeCost)-previousCost) + '\t' + str(totalLengthNewTargets) + '\t' + str(totalLength)
    #     g.printGrammarToFile(sys_args[-1]+str(x/batchSize+1)+'.txt', printIntsGrammar)
    #     print str(g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(totalLengthNewTargets) + '\t' + str(totalLength)
        print str(g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(g.grammarCost(CostFunction.EdgeCost)-previousCost) + '\t' + str(totalLengthNewTargets) + '\t' + str(totalLength)
    # previousDic = g.dic
    # g = None
    # tmpOut = open('tmpOut.txt','w')
    # for t in newParsedTargets:
    #     for c in t:
    #         tmpOut.write(str(c) + ' ')
    #     tmpOut.write('\n')
    # tmpOut.close()
    # g = Grammar(open('tmpOut.txt', 'r'), 'file', gap, chFlag, noNewLineFlag)
    # g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
    # g.printGrammarWithOffsetToNTs(printIntsGrammar, maxInt, inputDic=previousDic)
    g.printGrammarToFile(sys_args[-1]+str(start)+'.txt', printIntsGrammar)
    #Only for target ratio testing
    # sumNewLengths = 0
    # for t in optimallyParsedTargetInts:
    #     sumNewLengths += len(t)
    # return sumNewLengths

    return ratios

def idea3_GLexis(sys_args, batchSize):
    g = Grammar(open(sys_args[-3], 'r'), 'file', gap, chFlag, noNewLineFlag)
    g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
    seedCost = g.grammarCost(CostFunction.EdgeCost)
    reverseDic = {}
    totalLength = open(sys_args[-3], 'r').read().count(' ')
    # totalLength = 355
    # totalLength = 1496
    maxInt = g.nextNewInt + 2
    for c in g.dic:
        if maxInt < c:
            maxInt = c + 2
        reverseDic[g.dic[c]] = c
    # g.printGrammar(printIntsGrammar)
    # return
    allNewTargets = open(sys_args[-2], 'r').read().splitlines()
    for x in range(0, len(allNewTargets), batchSize):
        sys.stderr.write(str(x) + '\n')
        newTargets = []
        for j in range(x, x + batchSize):
            # if not noNewLineFlag:
            if j >= len(allNewTargets):
                break
            newTargets.append(allNewTargets[j])  # Assuming space sep chars
            # else:
            # newTargets.append(allNewTargets[j].split())  # Assuming space sep chars
        newTargetsInt = []
        # print newTargets
        newAlph = set([])#Fooling G-Lexis
        totalLengthNewTargets = 0
        for t in newTargets:
            tmpT = []
            tt = t.split()
            totalLengthNewTargets += len(tt)
            totalLength += len(tt)
            for i in range(len(tt)):  # For space-sep chars
                if tt[i]+'*' in newAlph:
                    tmpT.append(reverseDic[tt[i]+'*'])
                else:
                    newAlph.add(tt[i]+'*')
                    reverseDic[tt[i]+'*'] = maxInt
                    g.dic[maxInt] = tt[i]+'*'
                    maxInt += 2
                    tmpT.append(reverseDic[tt[i]+'*'])
            # for i in range(len(t)):#For seq chars
            #     if t[i] in reverseDic:
            #         tmpT.append(reverseDic[t[i]])
            #     else:
            #         reverseDic[t[i]] = maxInt
            #         g.dic[maxInt] = t[i]
            #         maxInt += 2
            #         tmpT.append(reverseDic[t[i]])
            newTargetsInt.append(tmpT)
        # print newTargetsInt
        # print g.dic
        # print reverseDic

        # print 'int', newTargetsInt
        # #D_t
        grammarDic = g.grammarDic()
        # ntYields = {}
        # for nt in grammarDic:
        #     if nt == 0:
        #         continue
        #     if nt in ntYields:
        #         ntYields[nt].append(g.ntYield(grammarDic, nt))
        #     else:
        #         ntYields[nt] = [g.ntYield(grammarDic, nt)]
        #do not run optimal parsing on newTargetsInt
        optimallyParsedTargetInts =newTargetsInt
        # previousCost = g.grammarCost(CostFunction.EdgeCost)
        previousCost = g.grammarCost(CostFunction.EdgeCost)
        originalCost = previousCost
        for t in newTargetsInt:
            originalCost += len(t)
        intermediateCost = previousCost
        for s in optimallyParsedTargetInts:
            intermediateCost += len(s)
        # add newly parsed targets to grammar and convert grammardic to new grammar
        for t in optimallyParsedTargetInts:
            grammarDic[0].append(t)
        g.initFromGrammarDic(grammarDic, g.dic)
        # g.nextNewInt =  maxInt+ 2
        while True:
            maxR = g.retreiveMaximumGainRepeat(rFlag, CostFunction.EdgeCost)
            if maxR['score'] == -1:
                break
            else:
                # print '\tmaxR'
                # sys.stderr.write(str(maxR) + '\n')
                g.replaceRepeat(maxR['length'], maxR['occs'])
                # print 'yaaaaaaaaaaaaaay2',
        # g.printGrammarToFile(sys_args[-1] + str(x / batchSize + 1), printIntsGrammar)
        # print str(g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(totalLengthNewTargets) + '\t' + str(totalLength)


        # print str(originalCost) + '\t' + str(intermediateCost) + '\t' + str(g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(g.grammarCost(CostFunction.EdgeCost) - previousCost) + '\t' + str(totalLengthNewTargets) + '\t' + str(totalLength)

        print str(totalLength) + '\t' + str(totalLengthNewTargets) + '\t' + str(
            intermediateCost - previousCost) + '\t' + str(
            totalLengthNewTargets - (intermediateCost - previousCost)) + '\t' + str(
            (intermediateCost - previousCost) - (intermediateCost - g.grammarCost(CostFunction.EdgeCost))) + '\t' + str(
            intermediateCost - g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(g.grammarCost(CostFunction.EdgeCost))
    # if 'BBa_K150100' in reverseDic:
    #     print '1', reverseDic['BBa_K150100']
    # if 'BBa_K150100*' in reverseDic:
    #     print '2', reverseDic['BBa_K150100*']
    # if 'N723' in reverseDic:
    #     print '3', reverseDic['N723']
    # if '723' in reverseDic:
    #     print '4', reverseDic['723']
    # if 723 in reverseDic:
    #     print '5', reverseDic[723]
    # g.printGrammar(printIntsGrammar)

def idea3_OptimalParsing(sys_args, batchSize):
    g = Grammar(open(sys_args[-3], 'r'), 'file', gap, chFlag, noNewLineFlag)
    reverseDic = {}
    maxInt = -1
    totalLength = open(sys_args[-3], 'r').read().count(' ')
    # totalLength = 355
    # totalLength = 1496
    for c in g.dic:
        if maxInt < c:
            maxInt = c + 2
        reverseDic[g.dic[c]] = c
    g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
    seedCost = g.grammarCost(CostFunction.EdgeCost)
    # g.printGrammar(printIntsGrammar)
    # return
    allNewTargets = open(sys_args[-2], 'r').read().splitlines()
    ratios = []
    for x in range(0, len(allNewTargets), batchSize):
        sys.stderr.write(str(x) + '\n')
        newTargets = []
        for j in range(x, x + batchSize):
            # if not noNewLineFlag:
            if j >= len(allNewTargets):
                break
            newTargets.append(allNewTargets[j])  # Assuming space sep chars
            # else:
            # newTargets.append(allNewTargets[j].split())  # Assuming space sep chars
        newTargetsInt = []
        # print newTargets
        totalLengthNewTargets = 0
        for t in newTargets:
            tmpT = []
            tt = t.split()
            totalLengthNewTargets += len(tt)
            totalLength += len(tt)
            for i in range(len(tt)):  # For space-sep chars
                if tt[i] in reverseDic:
                    tmpT.append(reverseDic[tt[i]])
                else:
                    reverseDic[tt[i]] = maxInt
                    g.dic[maxInt] = tt[i]
                    maxInt += 2
                    tmpT.append(reverseDic[tt[i]])
            # for i in range(len(t)):#For seq chars
            #     if t[i] in reverseDic:
            #         tmpT.append(reverseDic[t[i]])
            #     else:
            #         reverseDic[t[i]] = maxInt
            #         g.dic[maxInt] = t[i]
            #         maxInt += 2
            #         tmpT.append(reverseDic[t[i]])
            newTargetsInt.append(tmpT)
        # print newTargetsInt
        # print g.dic
        # print reverseDic

        # print 'int', newTargetsInt
        # #D_t
        grammarDic = g.grammarDic()
        ntYields = {}
        for nt in grammarDic:
            if nt == 0:
                continue
            if nt in ntYields:
                ntYields[nt].append(g.ntYield(grammarDic, nt))
            else:
                ntYields[nt] = [g.ntYield(grammarDic, nt)]
        #run optimal parsing on newTargetsInt
        optimallyParsedTargetInts =[]
        for t in newTargetsInt:
            #create a graph
            G = nx.DiGraph()
            edgeLabels = {} #used for saving non-terminals
            G.add_nodes_from([0, len(t)+1])
            for i in range(len(t)):
                G.add_edge(i, i+1)
                edgeLabels[(i,i+1)] = -1
            # print 'ntYields.keys()', ntYields.keys()
            # print 't', t
            for nt in ntYields:
                newEdgesStarts = KnuthMorrisPratt(t, ntYields[nt][0])
                # print 't', t
                # print 'ntYields[nt]', nt, ntYields[nt][0]
                # print 'newEdgesStarts', newEdgesStarts
                for s in newEdgesStarts:
                    G.add_edge(s, s+len(ntYields[nt][0]))
                    edgeLabels[(s, s+len(ntYields[nt][0]))] = nt
            paths = nx.shortest_path(G, source=0, target=len(t), weight=None)
            # print paths
            ## sys.stderr.write(str(paths) + 'paths\n')
            ## paths = random.choice(list(nx.all_simple_paths(G, source=0, target=len(t))))
            ## ctr = 1
            # for p in nx.all_simple_paths(G, source=0, target=len(t)):
            #     paths = p
                ## sys.stderr.write(str(ctr) + '\n')
                ## ctr += 1
                # break
            # sys.stderr.write(str(list(nx.all_simple_paths(G, source=0, target=len(t)))) + 'paths\n')
            # sys.exit()
            #all shortest paths
            # print 'edgeLabels', edgeLabels
            # print 'edges', G.edges()
            # print 'paths', paths
            # for i in range(len(paths[0])):
            optimalParsing = []
            for i in range(len(paths)-1):
                if edgeLabels[(paths[i], paths[i + 1])] == -1:
                    # print t[paths[i]],
                    optimalParsing.append(t[paths[i]])
                else:
                    # print edgeLabels[(paths[i],paths[i+1])],
                    optimalParsing.append(edgeLabels[(paths[i],paths[i+1])])
            # print
            # sys.exit()
            optimallyParsedTargetInts.append(optimalParsing)
            ratios.append(float(len(optimalParsing))/len(t))
        # previousCost = g.grammarCost(CostFunction.EdgeCost)
        previousCost = g.grammarCost(CostFunction.EdgeCost)
        originalCost = previousCost
        for t in newTargetsInt:
            originalCost += len(t)
        intermediateCost = previousCost
        for s in optimallyParsedTargetInts:
            intermediateCost += len(s)
        # add newly parsed targets to grammar and convert grammardic to new grammar
        for t in optimallyParsedTargetInts:
            grammarDic[0].append(t)
        g.initFromGrammarDic(grammarDic, g.dic)
        # while True:
        #     maxR = g.retreiveMaximumGainRepeat(rFlag, CostFunction.EdgeCost)
        #     if maxR['score'] == -1:
        #         break
        #     else:
        #         # print '\tmaxR'
        #         sys.stderr.write(str(maxR) + '\n')
        #         g.replaceRepeat(maxR['length'], maxR['occs'])
        # g.printGrammarToFile(sys_args[-1] + str(x / batchSize + 1), printIntsGrammar)
        # print str(g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(totalLengthNewTargets) + '\t' + str(totalLength)
        # print str(g.grammarCost(CostFunction.EdgeCost) - seedCost) + '\t' + str(totalLengthNewTargets) + '\t' + str(totalLength)
        # print str(g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(totalLengthNewTargets) + '\t' + str(totalLength)


        # print str(originalCost) + '\t' + str(intermediateCost) + '\t' + str(g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(g.grammarCost(CostFunction.EdgeCost) - previousCost) + '\t' + str(totalLengthNewTargets) + '\t' + str(totalLength)

        print str(totalLength) + '\t' + str(totalLengthNewTargets) + '\t' + str(
        intermediateCost - previousCost) + '\t' + str(
        totalLengthNewTargets - (intermediateCost - previousCost)) + '\t' + str(
        (intermediateCost - previousCost) - (intermediateCost - g.grammarCost(CostFunction.EdgeCost))) + '\t' + str(
        intermediateCost - g.grammarCost(CostFunction.EdgeCost)) + '\t' + str(g.grammarCost(CostFunction.EdgeCost))
    # g.printGrammar(printIntsGrammar)

    #Only for target ratio testing
    # sumNewLengths = 0
    # for t in optimallyParsedTargetInts:
    #     sumNewLengths += len(t)
    # return sumNewLengths

    return ratios

def idea3_Nothing(sys_args, batchSize):
    g = Grammar(open(sys_args[-2], 'r'), 'file', gap, chFlag, noNewLineFlag)
    reverseDic = {}
    maxInt = -1
    for c in g.dic:
        if maxInt < c:
            maxInt = c + 2
        reverseDic[g.dic[c]] = c
    g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
    # g.printGrammar(printIntsGrammar)
    # return
    allNewTargets = open(sys_args[-1], 'r').read().splitlines()
    for x in range(0, len(allNewTargets), batchSize):
        newTargets = []
        for j in range(x, x + batchSize):
            # if not noNewLineFlag:
            if j >= len(allNewTargets):
                break
            newTargets.append(allNewTargets[j])  # Assuming space sep chars
            # else:
            # newTargets.append(allNewTargets[j].split())  # Assuming space sep chars
        newTargetsInt = []
        # print newTargets
        for t in newTargets:
            tmpT = []
            tt = t.split()
            for i in range(len(tt)):  # For space-sep chars
                if tt[i] in reverseDic:
                    tmpT.append(reverseDic[tt[i]])
                else:
                    reverseDic[tt[i]] = maxInt
                    g.dic[maxInt] = tt[i]
                    maxInt += 2
                    tmpT.append(reverseDic[tt[i]])
            # for i in range(len(t)):#For seq chars
            #     if t[i] in reverseDic:
            #         tmpT.append(reverseDic[t[i]])
            #     else:
            #         reverseDic[t[i]] = maxInt
            #         g.dic[maxInt] = t[i]
            #         maxInt += 2
            #         tmpT.append(reverseDic[t[i]])
            newTargetsInt.append(tmpT)
        # print newTargetsInt
        # print g.dic
        # print reverseDic

        # print 'int', newTargetsInt
        # #D_t
        grammarDic = g.grammarDic()
        ntYields = {}
        for nt in grammarDic:
            if nt == 0:
                continue
            if nt in ntYields:
                ntYields[nt].append(g.ntYield(grammarDic, nt))
            else:
                ntYields[nt] = [g.ntYield(grammarDic, nt)]
        #run optimal parsing on newTargetsInt
        optimallyParsedTargetInts =newTargetsInt

        # add newly parsed targets to grammar and convert grammardic to new grammar
        for t in optimallyParsedTargetInts:
            grammarDic[0].append(t)
        g.initFromGrammarDic(grammarDic, g.dic)
        # while True:
        #     maxR = g.retreiveMaximumGainRepeat(rFlag, CostFunction.EdgeCost)
        #     if maxR['score'] == -1:
        #         break
        #     else:
        #         # print '\tmaxR'
        #         sys.stderr.write(str(maxR) + '\n')
        #         g.replaceRepeat(maxR['length'], maxR['occs'])
    g.printGrammar(printIntsGrammar)

def idea3_daily(sys_args, batchSize):
    g = Grammar(open(sys_args[-2], 'r'), 'file', gap, chFlag, noNewLineFlag)
    reverseDic = {}
    maxInt = -1
    for c in g.dic:
        if maxInt < c:
            maxInt = c + 2
        reverseDic[g.dic[c]] = c
    g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
    # g.printGrammar(printIntsGrammar)
    # return
    allNewTargets = open(sys_args[-1], 'r').read().splitlines()
    # for x in range(0, len(allNewTargets), batchSize):
    index_counter = 0
    # print allNewTargets
    while True:
        if index_counter >= len(allNewTargets):
            break
        newTargets = []
        newTargets.append(allNewTargets[index_counter].split('\t')[0])
        index_counter += 1
        while True:
            if index_counter >= len(allNewTargets):
                break
            if str(allNewTargets[index_counter].split('\t')[1]) == '-1':
                break
            else:
                newTargets.append(allNewTargets[index_counter].split('\t')[0])  # Assuming space sep chars
                index_counter += 1
            # else:
            # newTargets.append(allNewTargets[j].split())  # Assuming space sep chars
        # print newTargets
        newTargetsInt = []
        # print newTargets
        for t in newTargets:
            tmpT = []
            tt = t.split()
            for i in range(len(tt)):  # For space-sep chars
                if tt[i] in reverseDic:
                    tmpT.append(reverseDic[tt[i]])
                else:
                    reverseDic[tt[i]] = maxInt
                    g.dic[maxInt] = tt[i]
                    maxInt += 2
                    tmpT.append(reverseDic[tt[i]])
            # for i in range(len(t)):#For seq chars
            #     if t[i] in reverseDic:
            #         tmpT.append(reverseDic[t[i]])
            #     else:
            #         reverseDic[t[i]] = maxInt
            #         g.dic[maxInt] = t[i]
            #         maxInt += 2
            #         tmpT.append(reverseDic[t[i]])
            newTargetsInt.append(tmpT)
        # print newTargetsInt
        # print g.dic
        # print reverseDic

        # print 'int', newTargetsInt
        # #D_t
        grammarDic = g.grammarDic()
        ntYields = {}
        for nt in grammarDic:
            if nt == 0:
                continue
            if nt in ntYields:
                ntYields[nt].append(g.ntYield(grammarDic, nt))
            else:
                ntYields[nt] = [g.ntYield(grammarDic, nt)]
        #run optimal parsing on newTargetsInt
        optimallyParsedTargetInts =[]
        for t in newTargetsInt:
            #create a graph
            G = nx.DiGraph()
            edgeLabels = {} #used for saving non-terminals
            G.add_nodes_from([0, len(t)+1])
            for i in range(len(t)):
                G.add_edge(i, i+1)
                edgeLabels[(i,i+1)] = -1
            # print 'ntYields.keys()', ntYields.keys()
            # print 't', t
            for nt in ntYields:
                newEdgesStarts = KnuthMorrisPratt(t, ntYields[nt][0])
                # print 't', t
                # print 'ntYields[nt]', nt, ntYields[nt][0]
                # print 'newEdgesStarts', newEdgesStarts
                for s in newEdgesStarts:
                    G.add_edge(s, s+len(ntYields[nt][0]))
                    edgeLabels[(s, s+len(ntYields[nt][0]))] = nt
            paths = nx.shortest_path(G, source=0, target=len(t), weight=None)
            ## sys.stderr.write(str(paths) + 'paths\n')
            ## paths = random.choice(list(nx.all_simple_paths(G, source=0, target=len(t))))
            ## ctr = 1
            # for p in nx.all_simple_paths(G, source=0, target=len(t)):
            #     paths = p
                ## sys.stderr.write(str(ctr) + '\n')
                ## ctr += 1
                # break
            # sys.stderr.write(str(list(nx.all_simple_paths(G, source=0, target=len(t)))) + 'paths\n')
            # sys.exit()
            #all shortest paths
            # print 'edgeLabels', edgeLabels
            # print 'edges', G.edges()
            # print 'paths', paths
            # for i in range(len(paths[0])):
            optimalParsing = []
            for i in range(len(paths)-1):
                if edgeLabels[(paths[i], paths[i + 1])] == -1:
                    # print t[paths[i]],
                    optimalParsing.append(t[paths[i]])
                else:
                    # print edgeLabels[(paths[i],paths[i+1])],
                    optimalParsing.append(edgeLabels[(paths[i],paths[i+1])])
            # print
            # sys.exit()
            optimallyParsedTargetInts.append(optimalParsing)

        # add newly parsed targets to grammar and convert grammardic to new grammar
        for t in optimallyParsedTargetInts:
            grammarDic[0].append(t)
        g.initFromGrammarDic(grammarDic, g.dic)
        while True:
            maxR = g.retreiveMaximumGainRepeat(rFlag, CostFunction.EdgeCost)
            if maxR['score'] == -1:
                break
            else:
                # print '\tmaxR'
                sys.stderr.write(str(maxR) + '\n')
                g.replaceRepeat(maxR['length'], maxR['occs'])
        g.printGrammar(printIntsGrammar)

def idea3_daily2(sys_args, batchSize):
    allNewTargets = open(sys_args[-1], 'r').read().splitlines()
    # for x in range(0, len(allNewTargets), batchSize):
    index_counter = 0
    # print allNewTargets
    newTargets = []
    while True:
        sys.stderr.write(str(len(newTargets)) + '\n')
        if index_counter >= len(allNewTargets):
            break
        newTargets.append(allNewTargets[index_counter].split('\t')[0])
        index_counter += 1
        while True:
            if index_counter >= len(allNewTargets):
                break
            if str(allNewTargets[index_counter].split('\t')[1]) == '-1':
                break
            else:
                newTargets.append(allNewTargets[index_counter].split('\t')[0])  # Assuming space sep chars
                index_counter += 1
        f = open(sys_args[-1].split('.')[0]+'NEW.txt','w')
        f.write('\n'.join(newTargets))
        f.close()
        g = Grammar(open(sys_args[-1].split('.')[0]+'NEW.txt','r'), 'file', gap, chFlag, noNewLineFlag)
        g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
        g.printGrammar(printIntsGrammar)

def syntheticGen1(sys_args):
    g = Grammar(open(sys_args[-1], 'r'), 'file', gap, chFlag, noNewLineFlag)
    g.gSGP(aFlag, fFlag, quietLog, rFlag, cFlag, functionFlag, pairFlag)
    reverseDic = {}
    maxInt = -1
    for c in g.dic:
        if maxInt < c:
            maxInt = c + 2
        reverseDic[g.dic[c]] = c
    grammarDic = g.grammarDic()
    ntYields = {}
    setOfAllNtYields = set([])
    for nt in grammarDic:
        if nt in ntYields:
            ntYields[nt].append(g.ntYield(grammarDic, nt))
        else:
            ntYields[nt] = [g.ntYield(grammarDic, nt)]
        setOfAllNtYields.add(tuple(g.ntYield(grammarDic, nt)))
    # for a in setOfAllNtYields:
    #     print a
    # return
    newTargets = []
    numOutput = 500
    counter = numOutput
    newTarget = ''
    while counter > 0:
        randomNode = random.sample(ntYields.keys(), 1)[0]
        randomString = random.sample(random.sample(ntYields[randomNode], 1),1)[0]
        if len(randomString) <= 2:
            continue
        subPos = random.randint(0,len(randomString)-2)
        subLength = random.randint(2, len(randomString)-subPos)
        randomSubstring = randomString[subPos:subPos+subLength]
        if tuple(randomSubstring) not in setOfAllNtYields:
            counter -= 1
            if counter % 2 == 0 and counter < numOutput:
                newTargets.append(newTarget.rstrip())
                newTarget = ''
            for j in range(0,len(randomSubstring)):
                newTarget += g.dic[randomSubstring[j]] + ' '
    for t in newTargets:
        print t

def syntheticGen2(sys_args):
    strings = open(sys_args[-1], 'r').read().splitlines()
    numOutput = 1000
    counter = numOutput
    newTarget = ''
    while counter > 0:
        randomString = strings[random.randint(0, len(strings) - 1)].split()
        subPos = random.randint(0, len(randomString) - 2)
        subLength = random.randint(2, len(randomString) - subPos)
        randomSubstring = randomString[subPos:subPos + subLength]
        for i in range(0,20):
            for j in range(0, len(randomSubstring)):
                newTarget += randomSubstring[j] + ' '
        counter -= 1
    print newTarget

def syntheticGen3(sys_args):
    rules = open(sys_args[-1], 'r').read().splitlines()
    nonCoveredSubStrings = []
    for r in rules:
        nt = r.split(' ->  ')[0]
        if nt == 'N0':
            rhs = r.split(' ->  ')[1].split()
            tmpSub = []
            for c in rhs:
                if c[0] == 'N':
                    if len(tmpSub) > 2:
                        nonCoveredSubStrings.append(tuple(tmpSub))
                    tmpSub = []
                else:
                    tmpSub.append(c)
            if len(tmpSub) > 2:
                nonCoveredSubStrings.append(tuple(tmpSub))
    nonCoveredSubStrings = set(nonCoveredSubStrings)
    newTarget = ''
    for s in nonCoveredSubStrings:
        # newTarget += ' '.join(random.sample(nonCoveredSubStrings,1)[0]) + ' '
        newTarget += ' '.join(s) + ' '
        print newTarget
        newTarget = ''
        # newTarget += ' '.join(s) + ' '

def structureParenthesization(grammarFile):
    counter = 1
    grammar = {}
    for line in grammarFile.splitlines():
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

def optimalParsingRatioTest_AllCS(igemData):
    ratios = [0]
    meanRatios = [0]
    sumRatios = 0.0
    data = igemData
    for i in range(1,len(data)):
        csData = data[0:i]
        csFile = open('tmpCS.txt','w')
        for t in csData:
            csFile.write(str(t) + '\n')
        csFile.close()
        optData = data[i]
        optFile = open('tmpOpt.txt','w')
        optFile.write(str(optData) + '\n')
        optFile.close()
        optDataLength = len(data[i].split())
        optDataParsedLength = idea3_OptimalParsing(['tmpCS.txt', 'tmpOpt.txt'], 1)
        tmpRatio = float(optDataParsedLength)/float(optDataLength)
        ratios.append(tmpRatio)
        sumRatios += tmpRatio
        meanRatios.append(float(sumRatios)/len(ratios))
        output = open('output.txt', 'a')
        output.write(str(i) + '\t' + str(tmpRatio) + '\t' + str(meanRatios[-1]) + '\n')
        output.close()
        sys.stderr.write(str(i) + '\t' + str(tmpRatio) + '\t' + str(meanRatios[-1]) + '\n')

def optimalParsingRatioTest_Partial(sys_args):
    ratios = idea3_OptimalParsing(sys_args, 1)
    sumRatios = 0
    meanRatios = []
    for i in range(0,len(ratios)):
        sumRatios += ratios[i]
        meanRatios.append(float(sumRatios)/(len(meanRatios)+1))
        print str(i+1) + '\t' + str(ratios[i]) + '\t' + str(meanRatios[-1]) + '\n',
        sys.stderr.write(str(i+1) + '\t' + str(ratios[i]) + '\t' + str(meanRatios[-1]) + '\n')

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
    # print meanDistance

if __name__ == "__main__":
    (aFlag, fFlag, chFlag, printIntsGrammar, quietLog, rFlag, cFlag, pairFlag, functionFlag, noNewLineFlag, loadGrammarFlag, gap) = processParams(sys.argv)
    # optimalParsingRatioTest_AllCS(open(sys.argv[-1],'r').read().splitlines())
    # optimalParsingRatioTest_Partial(sys.argv)
    # structSimTest(sys.argv)
    # idea1(sys.argv, batchSize=1)
    # idea2(sys.argv, batchSize=1)
    # idea3(sys.argv, batchSize=1)
    # CSAll(sys.argv, batchSize=10)

    # idea3_Fixed(sys.argv, batchSize=int(sys.argv[-3]))
    # idea3_Fixed(sys.argv, batchSize=int(sys.argv[-2]))

    #For TGM4
    # idea3_Fixed(sys.argv[-1], givenGrammar = sys.argv[-3], batchSize=int(sys.argv[-2]))
    b = sys.argv[-2]
    idea3_Fixed(sys.argv, batchSize=int(b))
    # num = 2172
    # print str(structSimTest(open('/Users/payamsiyari/Desktop/inc/inc-fullProfile/gram'+ str(num) + '.txt.txt', 'r').read(), \
    #                   open('/Users/payamsiyari/Desktop/inc/cs-fullProfile/clean-slate full profile/gram'+str(num) + '.txt', 'r').read()))
    # idea3_GlobalGLexisWithoutOpt(sys.argv, batchSize=int(sys.argv[-3]))
    # K=int(sys.argv[-4])
    # starts = open('/Users/payamsiyari/Desktop/Q1/Q1.5 INC subseqs/seq' + str(K) + 'Starts.txt', 'r').readlines()
    # for l in starts:
    #     start = int(l)
    #     idea3_Fixed_2(sys.argv, start, K, batchSize=int(sys.argv[-3]))
    #
    # idea3_GLexis(sys.argv, batchSize=int(sys.argv[-4]))
    # idea3_OptimalParsing(sys.argv, batchSize=int(sys.argv[-4]))
    # idea3_Nothing(sys.argv, batchSize=100000)
    # idea3_daily(sys.argv, batchSize=1)
    # idea3_daily2(sys.argv, batchSize=1)

    # syntheticGen1(sys.argv)
    # syntheticGen2(sys.argv)
    # syntheticGen3(sys.argv)
    #
    #Considering new targets, calculate (r,s)
        #Calculate all constituents in D_t √
        #Search them in new targets and calculate the scores √
    #Add the new targets to the grammar √
    #Run SGP again
        #calculate repeats and export Max(R,S)
        #calculate Max(r,s)
        #calculate the maximum and return with its type
        #if normal repeat
            #Go as with SGP replacement
        #else
            #Go the other way
