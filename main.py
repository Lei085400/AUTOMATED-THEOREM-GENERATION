import os

import torch
import mmverify

from model import policy_model
from model import value_model
from trainer import Trainer
from mcts import Node
from mcts import MCTS
from verify import anatomy


device = torch.device('cpu') 

args = {
    'batch_size': 20,
    'numIters': 10,                                # Total number of training iterations
    'num_simulations': 100,                         # Total number of MCTS simulations to run when deciding on a move to play
    'numEps': 5,                                  # Number of full games (episodes) to run during each iteration
    'numItersForTrainExamplesHistory': 20,
    'epochs': 15,                                    # Number of epochs of training per iteration
    'checkpoint_path': 'latest.pth',                 # location to save latest set of weights
    'TACRIC_NUMBER': 5,
    'feature_size':100
    # 'MAX_ROUND_NUMBER' : 10
}


policyModel = policy_model(args['feature_size']*2, device)
valueModel = value_model(args['feature_size'], device)


axiom_file = "axioms.json"
symbol_file = "symbols.json"
anatomy(axiom_file,symbol_file)
verbosity = 30
# filename='data/anatomy.mm'
filename='Declare.mm'

# 假设这里的mm文件 没有证明序列，没有要证明的断言，只读入声明 (文件最后一个字符是 $=),
mm = mmverify.MM(None,None)
f_hyps,e_hyps = mm.calculate_and_verify_metamath(filename,def_verbosity=verbosity,def_only_calculate=True) #只使用计算功能
step_int = 0
state = []
step = ''
# 先调用一遍，初始化标签
correct_flag,state = mm.verify_and_calculate_proof_step_normal(f_hyps,e_hyps,step,state,step_int)  

# start = timeit.default_timer()
# print("第一次搜索策略")
# mcts = MCTS(current_node, policyModel, valueModel, args, device)
# node = mcts.runmcts(lean)
# end = timeit.default_timer()
# print ("第一次时间：{}".format(str(end-start)))


trainer = Trainer(policyModel, valueModel, args, device)
print("马上开始训练")
trainer.learn(state, mm, f_hyps, e_hyps,axiom_file,symbol_file)

