import json
import re



def extract_string(input_string):
    # 定义正则表达式模式
    pattern = r'(wff|setvar|class)\s+(\w+)'

    # 使用正则表达式进行匹配
    match = re.search(pattern, input_string)

    # 如果匹配成功，返回提取的字符串，否则返回None
    if match:
        return match.group(2).strip()
    else:
        return None
 
def anatomy(axiom_file,symbol_file):   
    axioms_list = []
    symbols_list = []
    metavariables_list = []
    declare = ""
    
    with open(symbol_file, 'r') as f:
        for line in f:
            # 解析 JSON 对象并添加到列表中
            json_data = json.loads(line)
            symbols_list.append(json_data)

    for item in symbols_list:
        
        theorem = item.get('theorem', '')
        type = item.get('type', '')
        conclusion = item.get('conclusion', '')
        
        if(theorem != "vx.cv" and theorem != "vx.tru" ):
            # print(theorem+" "+type+" "+conclusion)
            declare += theorem+" "+type+" "+conclusion+" $."
            declare += '\n'
            metavariables = extract_string(conclusion)
            metavariables_list.append(metavariables)



    # 读取 JSON 文件
    with open(axiom_file, 'r') as f:
        for line in f:
            # 解析 JSON 对象并添加到列表中
            json_data = json.loads(line)
            axioms_list.append(json_data)

    # 提取每个条目中的 "conclusion" 字段并输出
    for item in axioms_list:
        theorem = item.get('theorem', '')
        type = item.get('type', '')
        conclusion = item.get('conclusion', '')
        
        # print(theorem+" "+type+" "+conclusion)
        declare += theorem+" "+type+" "+conclusion+" $."
        declare += '\n'

        
    metavariables_list = set(metavariables_list) #去重
    metavariables = "$v " + " ".join(metavariables_list) + " $."
    # print(metavariables)

    with open('Declare.mm', 'w') as file:
        # 将字符串写入文件
        file.write("$c ( ) -> wff -. |- <-> -/\\ \\/_ /\\ \\/ class setvar if- , A. T. F. = hadd cadd $."+'\n' +metavariables + '\n'+ declare + '\n'+"wnew $p  $=  $.")
