import numpy as np

import torch
import torch.nn as nn
import torch.nn.functional as F
import torch.optim as optim

class policy_model(nn.Module):

    def __init__(self, feature_size, device):
        super(policy_model, self).__init__()

        self.device = device
        self.feature_size = feature_size

        self.action1 = nn.Linear(in_features=feature_size, out_features=16)
        self.action2 = nn.Linear(in_features=16, out_features=16)

        self.action_head = nn.Linear(in_features=16, out_features=1)

    def forward(self, x):
        # print("hello")
        # print(x)

        x = F.relu(self.action1(x))
        x = F.relu(self.action2(x))

        action_logits = self.action_head(x)

        return torch.sigmoid(action_logits)

    def predict(self, state_policy):
        # state_policy = torch.FloatTensor(state_policy.astype(np.float32)).to(self.device) # 将state_policy从NumPy数组转换为PyTorch张量，并将其数据类型设置为32位浮点数
        # state_policy = state_policy.view(1, self.size) #对state_policy进行形状变换，将其视图更改为1行self.size列的矩阵

        state_policy = torch.FloatTensor(state_policy.astype(np.float32))
        # print("hellohello")
        # print(state_policy)

        state_policy = state_policy.view(1, self.feature_size)
        self.eval()  # 将模型切换到评估模式。在评估模式下，模型不会更新梯度，这在推断阶段是有用的。

        with torch.no_grad():
            pi = self.forward(state_policy)

        return pi.data.cpu().numpy()[0]


class value_model(nn.Module):

    def __init__(self, feature_size, device):
        super(value_model, self).__init__()

        self.device = device
        self.feature_size = feature_size

        self.value1 = nn.Linear(in_features=feature_size, out_features=16)
        self.value2 = nn.Linear(in_features=16, out_features=16)

        self.value_head = nn.Linear(in_features=16, out_features=1)

    def forward(self, x):
        x = F.relu(self.value1(x))
        x = F.relu(self.value2(x))
        value_logit = self.value_head(x)

        return torch.tanh(value_logit)

    def predict(self, state):
        # state = torch.FloatTensor(state.astype(np.float32)).to(self.device)
        # state = state.view(1, self.size)

        state = torch.FloatTensor(state.astype(np.float32))
        state = state.view(1, self.feature_size)
        self.eval()

        with torch.no_grad():
            v = self.forward(state)

        return v.data.cpu().numpy()[0]




# device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
# feature_size = 3 #特征向量的size
# input_policy = np.array([[1,8,4,5,8,6]])
# input_policy = torch.FloatTensor(np.array(input_policy).astype(np.float64))
# policyModel = policy_model(feature_size*2, device)
# result = policyModel(input_policy)
# print(result)

# policy = policy_model(feature_size,device)
# input_policy = np.array([[1,8,4,5,8,6],[8,2,6,4,5,3]])
# policy_result = policy.predict(input_policy)
# target = torch.tensor([0.65])
# print(policy_result)

# def loss_pi(targets, outputs):
#     loss = torch.sum((targets-outputs)**2)/targets.size()[0]
#     return loss

# pi_loss = loss_pi(target,policy_result)
# print(pi_loss)

# optimizer = optim.Adam(policy.parameters(), lr=5e-4)
# optimizer.zero_grad()
# pi_loss.requires_grad_(True)
# pi_loss.backward()
# optimizer.step()

# policy = policy_model(feature_size,device)
# input_polciy = np.array([[1,8,4,5,8,6],[8,2,6,4,5,3]])
# policy_result = policy.predict(input_polciy)
# print(policy_result)
# pi_loss = loss_pi(target,policy_result)
# print(pi_loss)

####################################################

# value = value_model(feature_size,device)
# input_state = np.array([[1,2,3,4,5,6],[1,2,6,4,5,6]])
# value_result = value.predict(input_state)
# target = torch.tensor([0.65])
# print(target)
# print(torch.tensor(value_result))

# def loss_pi(targets, outputs):
#     loss = torch.sum((targets-outputs)**2)/targets.size()[0]
#     return loss

# v_loss = loss_pi(target,value_result)
# print(v_loss)

# optimizer = optim.Adam(value.parameters(), lr=5e-4)
# optimizer.zero_grad()
# v_loss.requires_grad_(True)
# v_loss.backward()
# optimizer.step()

# value = value_model(feature_size,device)
# input_state = np.array([[1,2,3,4,5,6],[1,2,6,4,5,6]])
# value_result = value.predict(input_state)
# target = torch.tensor([0.65])
# v_loss = loss_pi(target,value_result)
# print(v_loss)