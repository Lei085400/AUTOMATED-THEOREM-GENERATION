#!/usr/bin/env python
# -*- coding: utf-8 -*-
# Paper from http://pubs.doc.ic.ac.uk/survey-mcts-methods/survey-mcts-methods.pdf .
import os
import sys
import math
import random
import numpy as np
# from lean_dojo import *
import ssl
ssl._create_default_https_context = ssl._create_unverified_context
import torch
import torch.nn as nn
import torch.nn.functional as F
import torch.optim as optim
# torch.cuda.set_device(2)
import mmverify
from transformers import AutoTokenizer, AutoModelForCausalLM, AutoModelForSeq2SeqLM
import json
import heapq
import transformers
import subprocess
import time
from datetime import datetime
from tqdm import tqdm, trange
from pathlib import Path
# from lean_dojo import *
import traceback
import copy
# TACRIC_NUMBER = 8
MAX_ROUND_NUMBER = 10

def encode_state(state, feature_size):
    state = str([str(sublist) for sublist in state])
    encode_state = [ord(char) for char in state]
    if(len(encode_state)<=feature_size):
        encode_state += [0]*(feature_size-len(encode_state))  #list
    else:
        encode_state = encode_state[:feature_size]
    # print("encode")
    # print(encode_state)
    return encode_state
 
def encode_tactic(tactic,feature_size):
    tactic = str([str(sublist) for sublist in tactic])
    encode_tactic = [ord(char) for char in tactic]
    if(len(encode_tactic)<=feature_size):
        encode_tactic += [0]*(feature_size-len(encode_tactic))
    else:
        encode_tactic = encode_tactic[:feature_size]
    return encode_tactic


def cosine_similarity(vector1, vector2):
    # 计算向量的内积
    dot_product = np.dot(vector1, vector2)
    
    # 计算向量的长度
    norm_vector1 = np.linalg.norm(vector1)
    norm_vector2 = np.linalg.norm(vector2)
    
    # 计算余弦相似度
    if norm_vector1 != 0 and norm_vector2 != 0:
        cosine_sim = dot_product / (norm_vector1 * norm_vector2)
    else:
        cosine_sim = 0  # 避免除零错误
    
    return cosine_sim


def tactic_generator(axiom_file,symbol_file):

  tactic_candidates = []
  with open(symbol_file, 'r') as f:
    for line in f:
        # 解析 JSON 对象并添加到列表中
        json_data = json.loads(line)
        tactic_candidates.append(json_data["theorem"])
  
  count = 0
  with open(axiom_file, 'r') as f:
    for line in f:
      if(count <= 21):
        count += 1
        # 解析 JSON 对象并添加到列表中
        json_data = json.loads(line)
        tactic_candidates.append(json_data["theorem"])  
  # print("___")
  # print(tactic_candidates)

  tac1 = "vx.cv"
  tac2 = "vx.tru"
  if tac1 in tactic_candidates:
    tactic_candidates.remove(tac1)
  if tac2 in tactic_candidates:
    tactic_candidates.remove(tac2)
  return tactic_candidates

##############和mm交互：
Assertion = type[tuple[set[tuple[str, str]], list[tuple[str, str]], list[list[str]], list[str]]]

def read_axioms_json( file_name = 'axioms.json' #文件路径
                     ) -> tuple[list[Assertion],list[str]]:
  """读比赛给的axioms.json文件, 返回转换得到的assersion数组"""

  assertions = [[]]
  assertion = []
  assertion_labels = []
  # 读取JSON文件
  with open(file_name, 'r', encoding='utf-8') as file:
    data = file.readlines()
  # 解析JSON数据并存储为Python对象的列表
  known_axioms = [json.loads(line.strip()) for line in data]
  for axiom in known_axioms:
    # print(axiom['theorem'])
    e_hyps = axiom['e_hypos']
    f_hyps = axiom['f_hypos']
    label = axiom['theorem']
    dvs = axiom['d_vars']
    conclusion = axiom['conclusion']
    proof_steps = axiom['proof_steps']
    assertion = dvs, f_hyps, e_hyps,conclusion
    # print('get assersion:',label,'  ',assertion)
    assertions.append(assertion)
    assertion_labels.append(label)

  # print('assertions:',assertions)
  return assertions,assertion_labels

def read_symbols_json(
        file_name = 'symbols.json'
        ) -> dict:
        """读比赛给的symbols.json文件, 返回符号字典"""

        conclusions = {}
        
        # 读取JSON文件
        with open(file_name, 'r', encoding='utf-8') as file:
            data = file.readlines()

        # 解析JSON数据并存储为Python对象的列表
        known_symbols = [json.loads(line.strip()) for line in data]
     
        for symbol in known_symbols:
            label = symbol['theorem']
            conclusion = symbol['conclusion'].split()
            # print('get conclusion:',label,'  ',conclusion)
            conclusions[label] = conclusion

        # print(conclusions)
        return conclusions

def assertion_trans_to_same_v(
        assertion: Assertion,   # 新断言
        symbol_dict: dict  # 读文件symbols.json之后产生的符号字典
        ) -> Assertion:
        """将生成的新定理做相同的变量替换，并返回替换后的结果
        （该函数只是为了方便判断是否产生了新定理，防止$v类型变量不同带来的干扰） 
        
        """ 
        symbols = ['wph','wps','wch','wth','wta','wet','wze','wsi','wrh','wmu','wla',
                   'wka','vx.wal','vx.cv','cA.wceq','cB.wceq','vx.tru','vy.tru']
        new_assertion = copy.deepcopy(assertion)
        dvs = new_assertion[0]
        f_hyps = new_assertion[1]
        e_hyps = new_assertion[2]
        new_conclusion = new_assertion[3]
        i = 0
        fhs_v = [] # 存需要被替换的$v
        new_f_hyps = []
        new_e_hyps = []

        for fh in f_hyps:
            # print('fh:',fh)
            fhs_v.append(fh[1])  # 需要被替换的v
            new_f_hyps.append(symbol_dict[symbols[i]])
            i += 1
        # print('=-=-= fhs_v:',fhs_v,'new_f_hyps:',new_f_hyps)
        # 替换e_hyps和conclusion
        for eh in e_hyps:
            new_eh = eh
            for i, fh_v in enumerate(fhs_v):
                new_eh = new_eh.replace(fh_v, symbol_dict[symbols[i]][1])
            #当前eh替换完成
            new_e_hyps.append(new_eh)
        for i, ch in enumerate(new_conclusion):
            if ch in fhs_v:
                for j, fh_v in enumerate(fhs_v):
                    if ch == fh_v:
                        new_conclusion[i] = new_f_hyps[j][1]  

        new_assertion = dvs,new_f_hyps,new_e_hyps,new_conclusion
        # print('[ assertion_trans_to_same_v]:',new_assertion)
        return new_assertion  


def assertion_proof_trans_to_same_v(
        mm: mmverify.MM,
        assertion: Assertion,   # 新断言
        proof: list,     # 得到当前断言的证明序列
        symbol_dict: dict  # 读文件symbols.json之后产生的符号字典
        ) -> tuple[Assertion, list]:
        """将生成的新定理做和当前证明步骤 做变量替换，并返回替换后的结果
        
        """ 
        symbols = ['wph','wps','wch','wth','wta','wet','wze','wsi','wrh','wmu','wla',
                   'wka','vx.wal','vx.cv','cA.wceq','cB.wceq','vx.tru','vy.tru']
        new_assertion = copy.deepcopy(assertion)
        dvs = new_assertion[0]
        f_hyps = new_assertion[1]
        e_hyps = new_assertion[2]
        new_conclusion = new_assertion[3]
        new_proof = [] # 替换证明步骤
        i = 0
        fhs_v = [] # 存需要被替换的$v
        labels_p = []  # 需要被替换的标签
        label_dict = {}  # 替换标签字典
        # 思路：应该用一个字典？对应原本assertion的label 对应的是替换后的新label

        new_f_hyps = []
        new_e_hyps = []
        for fh in f_hyps:
            fhs_v.append(fh[1])  # 需要被替换的v
            fh_stmt = str('$f'),list(fh)
            label_p = list(mm.labels.keys())[list(mm.labels.values()).index(fh_stmt)] 
            labels_p.append(label_p)  # 需要被替换的证明步骤
            label_dict[label_p] = symbol_dict[symbols[i]]
            new_f_hyps.append(symbol_dict[symbols[i]])
            i += 1
        # 替换e_hyps和conclusion
        for eh in e_hyps:
            new_eh = eh
            for i, fh_v in enumerate(fhs_v):
                new_eh = new_eh.replace(fh_v, symbol_dict[symbols[i]][1])
            #当前eh替换完成
            new_e_hyps.append(new_eh)
        for i, ch in enumerate(new_conclusion):
            if ch in fhs_v:
                for j, fh_v in enumerate(fhs_v):
                    if ch == fh_v:
                        new_conclusion[i] = new_f_hyps[j][1]  

        for i,step in enumerate(proof):
            if step in labels_p:
                new_step = list(symbol_dict.keys())[list(symbol_dict.values()).index(label_dict[step])] 
                new_proof.append(new_step)
            else:
                new_proof.append(proof[i])

        new_assertion = dvs,new_f_hyps,new_e_hyps,new_conclusion
        # print('[ assertion_trans_to_same_v]:',new_assertion, new_proof)
        #  $a 类型的证明步骤中的标签不用替换，因为mcts 引用的 $a 都是已有的公理集中的标签 
        return new_assertion,new_proof  




def is_new_assertion(
        assertion:Assertion,
        assertions:list[Assertion],  # 当前已有的assertion列表
        symbol_dict:dict    #字符替换用的符号字典（读symbols.json得到）
        )->bool:
        """判断所给assertion是否是新产生的, 若是新产生的, 返回 True。
        参数assertions: 当前已有的assertion列表;
        参数symbol_dict: 字符替换用的符号字典(读symbols.json得到
        """
        #为了判断是否产生新定理，把新定理的假设、结论里的变量做相应替换后再对比
        flag = False
        trans_assertion = assertion_trans_to_same_v(assertion,symbol_dict)  # 对疑似新结论的assertion作符号替换
        if trans_assertion in assertions:# 不属于新定理
            flag = False
        else: #属于新定理,接下来提取证明步骤
            flag = True
        
        return trans_assertion, flag
         

# assersions,assertion_labels = read_axioms_json('axioms.json') # 获取已有公理的assertion list
# symbol_dict = read_symbols_json('symbols.json')  #获取符号字典

def generate_theorem(node,name,assertion_labels):
  # print(node.path)
  # print(node.assersion)
  references = []
  f_hypos = [" ".join(pair) for pair in node.assersion[1]]
  e_hypos = [" ".join(pair) for pair in node.assersion[2]]
  conclusion = " ".join(node.assersion[3])
  # conclusion = conclusion.replace('wff', '|-')
  proof_steps = " ".join(node.path)
  for i in node.path:
    if i in assertion_labels:
      references.append(i)
  new_theorem = {"theorem": name, "type": "$p", "conclusion": conclusion, "d_vars": "", "f_hypos": f_hypos, "e_hypos": e_hypos, "proof_steps": proof_steps, "references": references}
  assertion_labels.append(name)
  return new_theorem
 
#判断是否为新定理
def new_theorem(node, mm, assersions,assertion_labels,symbol_dict):
  # print(assertion_labels)
  # print(self.tac)
  if node.tac in assertion_labels:
    if(node.parent is None or node.flag == False):
      return False
    # elif(len(node.state) == 1 + len(node.parent.state)):
    #   return False   #未生成新定理
    else:
      # return True
      new_conclusion = node.state[-1]
      new_assersion = mm.fs.make_assertion(new_conclusion) # 获取疑似新结论的完整assertion
      node.assersion = new_assersion
      trans_assersion, new_assertion_flag = is_new_assertion(new_assersion,assersions,symbol_dict)
      
      if not new_assertion_flag:# 不属于新定理
          # print('It is not new theorem')
          return False
      else: #属于新定理,接下来提取证明步骤
          # print('New theorem!')
          assersions.append(trans_assersion)  #assertions数组添加新生成的assertion
          # print('new assertion:',new_assersion)  
          return True
  return False 
  
  
class Node(object):
  """
  蒙特卡罗树搜索的树结构的Node，包含了父节点和直接点等信息，还有用于计算UCB的遍历次数和quality值，还有游戏选择这个Node的State。
  """

  def __init__(self,state):
    self.parent = None
    self.children = []
    self.prob = 0
    self.puct = 0
    self.visit_times = 0
    self.quality_value = 0.0
    self.flag = True #记录节点是否可行，不可行则为Flase
    self.new = False #记录该节点是否产生了新定理
    self.tac = None  #记录当前状态是通过哪个策略得到的
    self.state = state
    self.path = None #新定理生成策略路径
    self.tactic_candidates = None    
    self.assersion = None
    self.depth = 0 
    self.similarity = 0

  def set_state(self, state):
    self.state = state

  def get_state(self):  
    return self.state

  def set_parent(self, parent):  
    self.parent = parent

  def get_children(self):  
    return self.children

  def get_visit_times(self):  
    return self.visit_times

  def visit_times_add_one(self):  
    self.visit_times += 1

  def get_quality_value(self): 
    return self.quality_value

  def quality_value_add_n(self, n):  
    self.quality_value += n

  def is_all_expand(self,axiom_file,symbol_file): #### 判断该状态下，是否所有的list中的策略都尝试过了
    return len(self.children) == len(tactic_generator(axiom_file,symbol_file))

  def add_child(self, sub_node):
    sub_node.set_parent(self)
    self.children.append(sub_node)
  
  def select_action(self):
    """
    Select action according to the visit count distribution and the temperature.
    """
    visit_counts = np.array([child.visit_times for child in self.children])
    actions = [action for action in self.children.tac]
    action = actions[np.argmafx(visit_counts)]
    return action

  def is_terminal(self):  ############# 更改为 证明是否完成（证明成功or失败）
    return self.flag == False

  def compute_reward(self):   ############# 证明成功为1，失败为0
    if (self.flag == False):
      return -1
    elif (self.flag == True):
      if(self.new == True):
        with open('output180.json', 'r') as file:
          # 逐行读取 JSON 文件
          for line in file:
              # 解析 JSON 对象
              json_object = json.loads(line)
              conclusion = json_object['conclusion']
              max_length = max(len(self.state), len(conclusion))
              encode_set = encode_state(conclusion,max_length)
              encode_state = encode_state(self.state,max_length)
              vector_set = np.array(encode_set)
              vector_state = np.array(encode_state)
              similarity = cosine_similarity(vector_set, vector_state)
              if(similarity > self.similarity):
                self.similarity = similarity
        return self.similarity
        # return 1
      else:
        return 0
    
  
  def proof(self, tac, mm, f_hyps, e_hyps):
    state = copy.copy(self.state)
    correct_flag, state = mm.verify_and_calculate_proof_step_normal(f_hyps,e_hyps,tac,state, 0)
    # print(state)
    return correct_flag, state

  def get_next_state_with_random_choice(self, index, mm, f_hyps, e_hyps,axiom_file,symbol_file):  ############# 根据当前state输入大模型，获取策略list后，随机选择其中一个策略，返回执行该随机策略后的状态
    # if(self.state==[]):
    #     self.tactic_candidates = tactic_generator()
    # else:
    #     self.tactic_candidates = self.parent.tactic_candidates
    #     self.tactic_candidates.append("新定理")  
    
    # tactic_candidates = self.tactic_candidates
    # random_choice = random.choices([choice for choice in tactic_candidates],k=1)
    
    self.tactic_candidates = tactic_generator(axiom_file,symbol_file)
    random_choice = self.tactic_candidates[index]

    ###############################
    correct_flag, next_state = self.proof( random_choice, mm, f_hyps, e_hyps)
    ###############################
    next_node = Node(next_state)
    next_node.tac = random_choice
    next_node.flag = correct_flag
    return next_node

  
  
  def __repr__(self):
    return "Node: {}, Q/N: {}/{}, state: {}".format(
        hash(self), self.quality_value, self.visit_times, self.state)


class MCTS:

    def __init__(self, node, policy_model, value_model, args, device):
        self.node = node
        self.policy_model = policy_model
        self.value_model = value_model
        self.args = args
        self.device = device

    def tree_policy(self, node, is_exploration, mm, f_hyps, e_hyps,axiom_file,symbol_file, assersions,assertion_labels,symbol_dict ):
      """
      蒙特卡罗树搜索的Selection和Expansion阶段，传入当前需要开始搜索的节点（例如根节点），根据exploration/exploitation算法返回最好的需要expend的节点，注意如果节点是叶子结点直接返回。

      基本策略是先找当前未选择过的子节点，如果有多个则随机选。如果都选择过就找权衡过exploration/exploitation的UCB值最大的，如果UCB值相等则随机选。
      """

      # Check if the current node is the leaf node
      while node.is_terminal() == False:
        
        if node.is_all_expand(axiom_file,symbol_file):
          # print(node.state.state)
          best_node = self.best_child(node, is_exploration)
          node = best_node
          # if(best_node is None):
          #   print("该节点的子节点的所有策略都无效{}".format(node.state))
            
          #   node.flag = 1 
          #   if(node.parent is not None):
          #     node = node.parent
          #   else:
          #     print("目标无解")
          #     sys.exit(0)
          # else:
          #   node = best_node
        else:
          # Return the new sub node
          sub_node = self.expand(node, mm, f_hyps, e_hyps, axiom_file,symbol_file, assersions,assertion_labels,symbol_dict)
          return sub_node

      # Return the leaf node
      return node


    def expand(self,node, mm, f_hyps, e_hyps,axiom_file,symbol_file, assersions,assertion_labels,symbol_dict):
      """
      输入一个节点，在该节点上拓展一个新的节点，使用random方法执行Action，返回新增的节点。注意，需要保证新增的节点与其他节点Action不同。
      """

      # tried_sub_node_states = [     # 统计node已经展开的所有子节点
      #     sub_node.get_state().state.tacticState for sub_node in node.get_children()
      # ]
      
      # tried_sub_node_tacs = [     # 统计node已经展开的所有子节点
      #     sub_node.get_state().tac for sub_node in node.get_children()
      # ]

      new_node = node.get_next_state_with_random_choice(len(node.children), mm, f_hyps, e_hyps,axiom_file,symbol_file)   # 根据当前node状态随机采取action，获得执行后的新状态

      # Check until get the new state which has the different action from others
      # while new_state.state.tacticState in tried_sub_node_states and new_state.tac in tried_sub_node_tacs:  # 判断新状态是否已经被expand，若已经被expand，则重新对node随机采取action，获得新状态
      #   new_state = node.get_next_state_with_random_choice(lean)   # 根据当前node状态随机采取action，获得执行后的新状态
      
      new_node.depth = node.depth + 1
      #########################
      encodestate = encode_state(node.state, self.args['feature_size'])
      #########################
      encodetactic = encode_tactic(new_node.tac, self.args['feature_size'])
      input_policy = encodestate + encodetactic
      input_policy = torch.FloatTensor(np.array(input_policy).astype(np.float64))
      new_node.prob = float(self.policy_model(input_policy))  # 返回的应该不是值，而是数组？
      #########################
      node.add_child(new_node)
      if(new_node.flag == False):
        new_node.new = False
      else:
        if(new_theorem(new_node,mm,assersions,assertion_labels,symbol_dict)):
          new_node.new = True
        else:
          new_node.new = False
      return new_node


    def best_child(self, node, is_exploration):
      """
      使用UCB算法，权衡exploration和exploitation后选择得分最高的子节点，注意如果是预测阶段直接选择当前Q值得分最高的。
      """

      # TODO: Use the min float value
      best_score = -sys.maxsize
      best_sub_node = None

      # Travel all sub nodes to find the best one
      # print("当前节点为{}".format(node.state.state.tacticState))
      for sub_node in node.get_children():
        # if(sub_node.state.error is not None):
        #   # print("该子节点报错")
        #   # sub_node.state.state.print()
        #   # print("该子节点报错")
        #   continue
        # if(sub_node.flag==1):
        #   # print("该子节点的所有策略都无效{}".format(sub_node.state.state.tacticState))
        #   continue
        # Ignore exploration for inference
        if is_exploration:
          C = 1 / math.sqrt(2.0)
          # C = 1
          # C = 2
        else:
          C = 1 / math.sqrt(2.0)

        # UCB = quality / times + C * sqrt(2 * ln(total_times) / times)
        left = sub_node.get_quality_value() / sub_node.get_visit_times()
        right = math.sqrt(node.get_visit_times()) / (sub_node.get_visit_times()+1)
        Puct_score = left + C * sub_node.prob * math.sqrt(right)
        sub_node.puct = Puct_score

        if Puct_score > best_score:
          best_sub_node = sub_node
          best_score = Puct_score
      # print("best:{}".format(best_sub_node.state.state.tacticState))
      return best_sub_node


    def backup(self, node, reward):
      """
      蒙特卡洛树搜索的Backpropagation阶段，输入前面获取需要expend的节点和新执行Action的reward，反馈给expend节点和上游所有节点并更新对应数据。
      """

      # Update util the root node
      while node != None:
        # Update the visit times
        node.visit_times_add_one()

        # Update the quality value
        node.quality_value_add_n(reward)

        # Change the node to the parent node
        node = node.parent


    def run(self, mm, f_hyps, e_hyps, name,axiom_file,symbol_file):
      """
      实现蒙特卡洛树搜索算法，传入一个根节点，在有限的时间内根据之前已经探索过的树结构expand新节点和更新数据，然后返回只要exploitation最高的子节点。

      蒙特卡洛树搜索包含四个步骤，Selection、Expansion、Simulation、Backpropagation。
      前两步使用tree policy找到值得探索的节点。
      第三步使用default policy也就是在选中的节点上随机算法选一个子节点并计算reward。
      最后一步使用backup也就是把reward更新到所有经过的选中节点的节点上。

      进行预测时，只需要根据Q值选择exploitation最大的节点即可，找到下一个最优的节点。
      """
      node =  self.node
      computation_budget = 1000
      assersions,assertion_labels = read_axioms_json(axiom_file) # 获取已有公理的assertion list
      symbol_dict = read_symbols_json(symbol_file)  #获取符号字典
      
      # Run as much as possible under the computation budget
      for i in range(computation_budget):

        # 1. Find the best node to expand
        # print("mcts到第{}次，node为：{}".format(i,node.state))
        expand_node = self.tree_policy(node, True, mm, f_hyps, e_hyps, axiom_file,symbol_file, assersions,assertion_labels,symbol_dict)
        
        ############################################
        if(not expand_node.flag):
          reward = -1
        elif(expand_node.new):
          reward = 1
        else:
          encodestate = encode_state(expand_node.state, self.args['feature_size'])
          input_value = torch.FloatTensor(np.array(encodestate).astype(np.float64))
          reward = float(self.value_model(input_value))

        # 3. Update all passing nodes with reward
        self.backup(expand_node, reward)

      return node,len(tactic_generator(axiom_file,symbol_file))


    def runmcts(self, mm, f_hyps, e_hyps, axiom_file,symbol_file):
     
      node =  self.node
      computation_budget = 5000
      assersions,assertion_labels = read_axioms_json(axiom_file) # 获取已有公理的assertion list
      symbol_dict = read_symbols_json(symbol_file)  #获取符号字典
      outputs = []
      
      # Run as much as possible under the computation budget
      for i in range(computation_budget):

        # 1. Find the best node to expand
        # print("mcts到第{}次，node为：{}".format(i,node.state))
        expand_node = self.tree_policy(node, True, mm, f_hyps, e_hyps, axiom_file,symbol_file, assersions,assertion_labels,symbol_dict)
        
        ############################################
        if(not expand_node.flag):
          reward = -1
        elif(expand_node.new):
          reward = 1
        else:
          encodestate = encode_state(expand_node.state, self.args['feature_size'])
          input_value = torch.FloatTensor(np.array(encodestate).astype(np.float64))
          reward = float(self.value_model(input_value))

        # 3. Update all passing nodes with reward
        self.backup(expand_node, reward)

        if(expand_node.new): #生成了新定理
          name = "new" + str(i)
          path = []  #新定理所用策略
          unused_list = expand_node.state[:-1]
          new_node = copy.copy(expand_node)
          while new_node.parent is not None:
            if(new_node.state == unused_list):
              break
            path.append(new_node.tac)
            new_node = new_node.parent
          path.reverse()
          trans_assertion,trans_proof = assertion_proof_trans_to_same_v(mm,expand_node.assersion,path,symbol_dict)
          
          expand_node.path = trans_proof
          expand_node.assersion = trans_assertion
          
          new_theorem = generate_theorem(expand_node,name+str(i),assertion_labels)
          outputs.append(new_theorem)
          # print(new_theorem)
          with open('out.json', 'a') as file:
            json.dump(new_theorem, file)
            file.write('\n')
          # print(new_theorem)

      return node,outputs



# def main():
#   # Create the initialized state and initialized node
#   init_state = State(state)
#   node = Node()
#   node.set_state(init_state)
#   current_node = node
#   mcts = MCTS(current_node)
#   current_node = mcts.run()
#   print("搜索完成")

# if __name__ == "__main__":
#   main()