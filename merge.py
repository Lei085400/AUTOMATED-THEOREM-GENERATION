import os
import json

def merge_json_files(folder_path, output_file):
    # 存储所有 JSON 内容的列表
    all_data = []

    # 遍历文件夹中的所有文件
    for root, dirs, files in os.walk(folder_path):
        for file_name in files:
            # 检查文件扩展名是否为 .json
            if file_name.endswith('.json'):
                file_path = os.path.join(root, file_name)
                with open(file_path, 'r') as f:
                    # 读取 JSON 内容并添加到列表中
                    data = json.load(f)
                    all_data.extend(data)

    # 将所有 JSON 内容合并
    merged_data = json.dumps(all_data, indent=4)

    # 将合并后的 JSON 内容写入输出文件
    with open(output_file, 'w') as f:
        f.write(merged_data)

# 示例用法
folder_path = '/home/wanglei/submission/cleaned_theorems'
output_file = 'merged_output.json'
merge_json_files(folder_path, output_file)