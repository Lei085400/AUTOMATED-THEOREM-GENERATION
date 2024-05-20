"""DO NOT rename this file!"""
import os
import json
import textwrap
import time
from string import Template
import numpy as np
import openai

from tqdm import tqdm

outputs = []
with open('output.json', 'r') as f:
    for line in f:
        # 解析 JSON 对象并添加到列表中
        json_data = json.loads(line)
        outputs.append(json.dumps(json_data))  
print(outputs)
        
        
list_str = str(outputs)
# 打开一个文件用于写入 ('w' 模式表示写入)
with open('output.txt', 'w') as file:
    # 将整个列表字符串写入文件
    file.write(list_str)