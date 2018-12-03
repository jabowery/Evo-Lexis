#Main code for generating targets under Evo-Lexis model
#NOTE: The code's interface is now minimal and the parameters should be changed within the code. I'll clean the code in the future.

from __future__ import division
import os
import math
import random
import sys
import numpy as np
from Lexis import *
from LexisEvo import *

class RemovalModel:
    NoModel, AgeBias = ('none', 'age')

class AdditionModel:
    # Random Model
    # Mutation Model
    # Mutations+Selection Model
    # Mutations+Recombination+Selection Model
    RandomModel, RandomSeed, CostBiasWeakSelection, RecombinationCostBiasWeakSelection  = ('random', 'random-seed', 'cost_weak', 'recomb_cost_weak') 

def generateInitials(s, k, n):#Generates s initial random targets of length k from alphabet of size n
    initials = []
    for i in range(s):
        initials.append([random.randrange(n) for j in range(k)])
    return initials

def TRM_AgeBias(batch_size):
    return range(batch_size)

def get_removal_indices(last_dag_path, last_targets_path, removal_model, batch_size, model_extra_parameters = {}, working_path = ''):
        return TRM_AgeBias(batch_size)

def mutate_seed_targets(t_s, n, p):#Generate new target based on previous targets (t_s)
    t_r = []
    # number_of_changed_chars = 0
    for c in t_s:
        if random.random() < p:
            t_r.append(random.randrange(n))
            # number_of_changed_chars += 1
        else:
            t_r.append(c)
    # return t_r, number_of_changed_chars
    return t_r

def recombine_seed_targets(t1, t2, k, n):
    l = random.randint(0,k-2)
    offsprings = []

    offsprings.append((t1[:l] + [random.randrange(n)] + t2[l + 1:], l + 1, k - l - 1, 0, 1))
    offsprings.append((t2[:l] + [random.randrange(n)] + t1[l + 1:], l + 1, k - l - 1, 1, 0))
    offsprings.append((t2[l + 1:] + t1[:l] + [random.randrange(n)], k - l - 1, l + 1, 1, 0))
    offsprings.append((t1[l + 1:] + t2[:l] + [random.randrange(n)], k - l - 1, l + 1, 0, 1))
    random.shuffle(offsprings)
    return offsprings

def TGM_RandomSeed(last_targets_path, targets_set, batch_size, n, p):
    with open(last_targets_path, 'r') as f:
        targets = [map(int, x.split()) for x in f.read().splitlines()]
    new_targets = []
    for i in range(batch_size):
        tmp_target = mutate_seed_targets(random.choice(targets), n, p)
        while ' '.join(map(str, tmp_target)) in targets_set:
            tmp_target[random.randrange(len(tmp_target))] = random.randrange(n)
        new_targets.append(tmp_target)
        targets_set.add(' '.join(map(str, tmp_target)))
    targets_set = set([])
    for t in targets:
        targets_set.add(' '.join(map(str, t)))
    for t in new_targets:
        targets_set.add(' '.join(map(str, t)))
    return new_targets, targets_set

def TGM_CostBias_Endogenous_WeakSelection(last_dag_path, last_targets_path, targets_ts_costs, targets_set, batch_size, n, k, p, working_path = ''):
    with open(last_targets_path, 'r') as f:
        targets = [map(int, x.split()) for x in f.read().splitlines()]
    # print 'Generating batch...'
    sys.stderr.write('Generating batch...\n')
    potential_next_batch = []
    tmp_target_set = set(list(targets_set))
    tmp_prev_batch_ts_costs = targets_ts_costs[:]
    tmp_g = DAG(open(last_dag_path, 'r'), True, SequenceType.SpaceSeparated, False)
    prev_grammar_cost = tmp_g.DAGCost(CostFunction.EdgeCost)
    while len(potential_next_batch) < batch_size:
        random_index = random.randint(0, len(targets_ts_costs) - 1)
        last_target = targets_ts_costs[random_index][0]
        last_cost = targets_ts_costs[random_index][1]
        tmp_target = mutate_seed_targets(last_target, n, p)
        while ' '.join(map(str, tmp_target)) in tmp_target_set:  # duplicate target, change one of the characters randomly
            tmp_target[random.randrange(len(tmp_target))] = random.randrange(n)
        #Get the cost of generated target
        tmp_target_path = working_path + '/tmp_tgm4_new_target.txt'
        with open(tmp_target_path, 'w') as tmp_file:
            tmp_file.write(' '.join(map(str, tmp_target)) + '\n')
        tmp_file.close()
        g_inc = idea3_Fixed_TGM4(tmp_target_path, givenGrammar=last_dag_path, batchSize=2, working_path=working_path)
        target_cost = g_inc.grammarCost(CostFunction.EdgeCost) - prev_grammar_cost
        if target_cost <= last_cost:
            potential_next_batch.append(tmp_target)
            tmp_target_set.add(' '.join(map(str,tmp_target)))
            tmp_prev_batch_ts_costs.append([tmp_target, target_cost, random_index, last_cost])
            # print 'Batch length', len(potential_next_batch), target_cost, last_cost, random_index
            sys.stderr.write('Batch length ' + str(len(potential_next_batch)) + ' ' + str(target_cost) + ' ' + str(last_cost) + ' ' + str(random_index) + '\n')
        else:
            beta = 12
            # D = math.fabs(target_cost - last_cost)
            # acc_prob = math.exp(-beta*D)
            R = target_cost / last_cost
            acc_prob = math.exp(-beta * (R - 1))
            rand = random.random()
            if rand < acc_prob:
                potential_next_batch.append(tmp_target)
                tmp_target_set.add(' '.join(map(str, tmp_target)))
                tmp_prev_batch_ts_costs.append([tmp_target, target_cost, random_index, last_cost])
                # print 'Batch length', len(potential_next_batch), target_cost, last_cost, random_index
                sys.stderr.write('Batch length ' + str(len(potential_next_batch)) + ' ' + str(target_cost) + ' ' + str(last_cost) + ' ' + str(random_index) + '\n')
            else:
                continue
    #potential batch ready
    targets.extend(potential_next_batch)
    for t in potential_next_batch:
        targets_set.add(' '.join(map(str, t)))
    targets_ts_costs = tmp_prev_batch_ts_costs
    return potential_next_batch, targets_set, targets_ts_costs

def TGM_Recombination_CostBias_WeakSelection(last_dag_path, last_targets_path, targets_ts_costs, targets_set, batch_size, n, k, p, working_path = ''):
    with open(last_targets_path, 'r') as f:
        targets = [map(int, x.split()) for x in f.read().splitlines()]
    # print 'Generating batch...'
    sys.stderr.write('Generating batch...\n')
    potential_next_batch = []
    tmp_target_set = set(list(targets_set))
    tmp_prev_batch_ts_costs = targets_ts_costs[:]
    tmp_g = DAG(open(last_dag_path, 'r'), True, SequenceType.SpaceSeparated, False)
    prev_grammar_cost = tmp_g.DAGCost(CostFunction.EdgeCost)
    while len(potential_next_batch) < batch_size:
        random_indices = random.sample(range(len(targets_ts_costs)), 2)
        target_0 = targets_ts_costs[random_indices[0]][0]
        cost_0 = targets_ts_costs[random_indices[0]][1]
        target_1 = targets_ts_costs[random_indices[1]][0]
        cost_1 = targets_ts_costs[random_indices[1]][1]
        tmp_targets = recombine_seed_targets(target_0, target_1, k, n)
        prev_len_potenital_batch = len(potential_next_batch)
        for (tmp_target, l0, l1, i0, i1) in tmp_targets:
            if len(potential_next_batch) > prev_len_potenital_batch: #An offspring was added
                break
            if ' '.join(map(str, tmp_target)) in tmp_target_set: #Skip repeated offsprings
                continue
            #Get the cost of generated target
            tmp_target_path = working_path + '/tmp_tgm4_new_target.txt'
            with open(tmp_target_path, 'w') as tmp_file:
                tmp_file.write(' '.join(map(str, tmp_target)) + '\n')
            tmp_file.close()
            g_inc = idea3_Fixed_TGM4(tmp_target_path, givenGrammar=last_dag_path, batchSize=2, working_path=working_path)
            target_cost = g_inc.grammarCost(CostFunction.EdgeCost) - prev_grammar_cost
            if i0 == 0:
                last_cost = (float(l0) / float(k)) * cost_0 + (float(l1) / float(k)) * cost_1
            elif i0 == 1:
                last_cost = (float(l1) / float(k)) * cost_0 + (float(l0) / float(k)) * cost_1
            if target_cost <= last_cost:
                potential_next_batch.append(tmp_target)
                tmp_target_set.add(' '.join(map(str,tmp_target)))
                tmp_prev_batch_ts_costs.append([tmp_target, target_cost, random_indices[0], random_indices[1], last_cost])
                # print 'Batch length', len(potential_next_batch), target_cost, last_cost, random_indices[0], random_indices[1], i0, i1, l0, l1
                sys.stderr.write('Batch length ' + str(len(potential_next_batch)) + ' ' + str(target_cost) + ' ' + str(last_cost) + ' ' + str(random_indices[0]) + ' ' + str(random_indices[1]) + ' ' + str(i0) + ' ' + str(i1) + ' ' + str(l0) + ' ' + str(l1) + '\n')
            else:
                beta = 12
                R = target_cost/last_cost
                acc_prob = math.exp(-beta * (R-1))
                rand = random.random()
                if rand < acc_prob:
                    potential_next_batch.append(tmp_target)
                    tmp_target_set.add(' '.join(map(str, tmp_target)))
                    tmp_prev_batch_ts_costs.append([tmp_target, target_cost, random_indices[0], random_indices[1], last_cost])
                    # print 'Batch length', len(potential_next_batch), target_cost, last_cost, random_indices[0], random_indices[1], i0, i1, l0, l1
                    sys.stderr.write('Batch length ' + str(len(potential_next_batch)) + ' ' + str(target_cost) + ' ' + str(last_cost) + ' ' + str(random_indices[0]) + ' ' + str(random_indices[1]) + ' ' + str(i0) + ' ' + str(i1) + ' ' + str(l0) + ' ' + str(l1) + '\n')
                else:
                    continue
    #Potential batch ready
    targets.extend(potential_next_batch)
    for t in potential_next_batch:
        targets_set.add(' '.join(map(str, t)))
    targets_ts_costs = tmp_prev_batch_ts_costs
    targets_set = set([])
    for t in targets:
        targets_set.add(' '.join(map(str, t)))
    return potential_next_batch, targets_set, targets_ts_costs

def add_targets(last_dag_path, last_targets_path, n, k, p, addition_model, batch_size, model_extra_parameters = {}, working_path = ''):
    if addition_model == AdditionModel.RandomModel:
        targets_set = model_extra_parameters['targets_set']
        new_targets, targets_set = TGM_RandomSeed(last_targets_path, targets_set, batch_size, n, 1)
        model_extra_parameters['targets_set'] = targets_set
        return new_targets, model_extra_parameters
    elif addition_model == AdditionModel.RandomSeed:
        targets_set = model_extra_parameters['targets_set']
        new_targets, targets_set = TGM_RandomSeed(last_targets_path, targets_set, batch_size, n, p)
        model_extra_parameters['targets_set'] = targets_set
        return new_targets, model_extra_parameters
    elif addition_model == AdditionModel.CostBiasWeakSelection:
        targets_set = model_extra_parameters['targets_set']
        targets_ts_costs = model_extra_parameters['targets_ts_costs']
        new_targets, targets_set, targets_ts_costs =  TGM_CostBias_Endogenous_WeakSelection(last_dag_path, last_targets_path,
                                                                              targets_ts_costs, targets_set, batch_size,
                                                                              n, k, p, working_path = working_path)
        model_extra_parameters['targets_set'] = targets_set
        model_extra_parameters['targets_ts_costs'] = targets_ts_costs
        return new_targets, model_extra_parameters
    elif addition_model == AdditionModel.RecombinationCostBiasWeakSelection:
        targets_set = model_extra_parameters['targets_set']
        targets_ts_costs = model_extra_parameters['targets_ts_costs']
        new_targets, targets_set, targets_ts_costs = TGM_Recombination_CostBias_WeakSelection(last_dag_path, last_targets_path,
                                                                             targets_ts_costs, targets_set, batch_size,
                                                                             n, k, p, working_path=working_path)
        model_extra_parameters['targets_set'] = targets_set
        model_extra_parameters['targets_ts_costs'] = targets_ts_costs
        return new_targets, model_extra_parameters

def clean_tmp_files(working_path):
    dir_name = working_path
    files = os.listdir(dir_name)
    for item in files:
        if item.endswith('.txt') and item.startswith('tmp'):
            os.remove(os.path.join(dir_name, item))

def TBTGR(s, #Number of seed (i.e., initial targets)
          n, #Size of the alphabet
          k, #Length of targets
          p, #Mutation probability
          batch_size, #Size of the batch for each addition/removal
          T_stationary, #Number of stationary targets (i.e., when removal begins)
          no_of_total_targets_generated, #Number of iterations of the target generator
          addition_model, #Model of addition of the targets (Radnom, M, MR or MRS -- see AdditionModel enum)
          removal_model, #Which targets will be removed in each iteration (not customizable for now)
          working_path = '' #The path where all the output target/DAG files are stored (must be an existing directory)
          ):#Tinkering-based Target Generator Algorithm
    # Gen & Save init targets
    targets = generateInitials(s, k, n)
    num_current_targets = s # current number of generated targets
    iteration = 0
    init_targets_path = working_path + '/targets_' + str(num_current_targets) + '-' + str(iteration) + '.txt'
    with open(init_targets_path, 'w') as f:
        for t in targets:
            f.write(' '.join(map(str, t)) + '\n')
    # Gen & Save init DAG
    init_dag = DAG(open(init_targets_path, 'r'), False, SequenceType.SpaceSeparated, False)
    init_dag.GLexis(True, RepeatClass.MaximalRepeat, CostFunction.EdgeCost)
    init_dag_path = working_path + '/dag_' + str(num_current_targets) + '-' + str(iteration) + '.txt'
    with open(init_dag_path, 'w') as f:
        init_dag.printDAG(False, f)
    #Model extra parameters
    targets_set = set([])  # used for checking duplicate targets
    for t in targets:
        targets_set.add(' '.join(map(str, t)))
    targets_ts_costs = [] #used for TGM4
    for i, t in enumerate(targets):
        targets_ts_costs.append([t, 0, -1, -1])
    with open(init_dag_path, 'r') as tmp_file:
        lines = tmp_file.readlines()
        t_counter = 0
        for i, l in enumerate(lines):
            if l.startswith('N0 '):
                targets_ts_costs[t_counter][1] = len(l.split(' ->  ')[1].split())
                t_counter += 1
    model_extra_parameters = {}
    model_extra_parameters['targets_set'] = targets_set
    model_extra_parameters['targets_ts_costs'] = targets_ts_costs

    last_dag_path = init_dag_path
    last_targets_path = init_targets_path
    while num_current_targets < no_of_total_targets_generated:
        # Do the removals
        if num_current_targets >= T_stationary and removal_model != RemovalModel.NoModel:
            removal_indices = get_removal_indices(last_dag_path, last_targets_path, removal_model = removal_model, batch_size = batch_size)
            d = DAG(open(last_dag_path, 'r'), True, SequenceType.SpaceSeparated, False, removal_indices=removal_indices, working_path=working_path)
            after_removal_dag_path = working_path + '/post_removal-' + 'dag_' + str(num_current_targets) + '-' + str(iteration) + '.txt'
            with open(after_removal_dag_path, 'w') as f:
                d.printDAG(False, f)
            remaining_indices = [x for x in range(T_stationary) if x not in removal_indices]
            if addition_model == AdditionModel.CostBiasWeakSelection or addition_model == AdditionModel.RecombinationCostBiasWeakSelection:
                targets_ts_costs = [targets_ts_costs[x] for x in remaining_indices]
                model_extra_parameters['targets_ts_costs'] = targets_ts_costs
            targets = [targets[x] for x in remaining_indices]
        else:
            after_removal_dag_path = last_dag_path
        #Add targets
        new_targets, model_extra_parameters = add_targets(last_dag_path, last_targets_path, n, k, p, addition_model, batch_size, model_extra_parameters=model_extra_parameters, working_path = working_path)
        num_current_targets += batch_size
        iteration += 1
        targets.extend(new_targets)
        targets_path = working_path + '/targets_' + str(num_current_targets) + '-' + str(iteration) + '.txt'
        with open(targets_path, 'w') as f:
            for t in targets:
                f.write(' '.join(map(str, t)) + '\n')
        if addition_model == AdditionModel.CostBiasWeakSelection or addition_model == AdditionModel.RecombinationCostBiasWeakSelection:
            targets_ts_costs = model_extra_parameters['targets_ts_costs']

        #Write new targets in tmp file
        tmp_new_targets_path = working_path + '/tmp_new_targets_' + str(num_current_targets) + '-' + str(iteration) + '.txt'
        with open(tmp_new_targets_path, 'w') as f:
            for t in new_targets:
                f.write(' '.join(map(str, t)) + '\n')
        #Run INC
        tmp_g = idea3_Fixed_TGM4(tmp_new_targets_path, givenGrammar=after_removal_dag_path, batchSize=batch_size, working_path = working_path)
        last_dag_path = working_path + '/dag_' + str(num_current_targets) + '-' + str(iteration) + '.txt'
        last_targets_path = working_path + '/targets_' + str(num_current_targets) + '-' + str(iteration) + '.txt'
        tmp_g.printGrammarToFile(last_dag_path, False)

        sys.stderr.write("number of targets generated so far: " + str(num_current_targets) + '\n')
    clean_tmp_files(working_path = working_path)


working_path = sys.argv[-1]

TBTGR(s=10, #Number of seed (i.e., initial targets)
      n=100, #Size of the alphabet
      k=200, #Length of targets
      p=0.005, #Mutation probability
      batch_size=10, #Size of the batch for each addition/removal
      T_stationary=100, #Number of stationary targets (i.e., when removal begins)
      no_of_total_targets_generated=50000, #Number of iterations of the target generator
      addition_model=AdditionModel.RecombinationCostBiasWeakSelection, #Model of addition of the targets (Radnom, M, MR or MRS -- see AdditionModel enum)
      removal_model=RemovalModel.AgeBias, #Which targets will be removed in each iteration (not customizable for now)
      working_path = working_path #The path where all the output target/DAG files are stored (must be an existing directory)
     )
