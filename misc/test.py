from rela import *
import time
import os
import json
import pandas as pd
import random
from rela.networkmodel.relagraphformat import RelaGraphNC 
from rela.networkmodel.relagraphformat import RelaGraphFEC 
from rela.networkmodel.relagraphformat import RelaDeviceLevelForwardingGraph


output_file = 'combined.json'


data = []
with open(output_file, 'r') as f:
    data = json.load(f)
    
length = len(data)
temp_file = 'temp.json'

seconds = []
for i in range(1, 2001):
    nth = random.randint(0,length-1)
    with open(temp_file, 'w') as f:
        json.dump([data[nth]], f, indent=4)
    
    spec = PStar(pDot) % Preserve()
    compiled_spec = RelaCompiler.compile(spec)
    change_file = os.path.abspath(temp_file)
    start_time = time.perf_counter()
    result = verify_network_change(compiled_spec, change_file)
    end_time = time.perf_counter()
    seconds.append(end_time - start_time)
    
with open('./a.txt', "w") as f:
    for item in seconds:
        f.write(str(item) + "\n")

seconds = []
for i in range(1, 2001):
    nth = random.randint(0,length-1)
    with open(temp_file, 'w') as f:
        json.dump([data[nth]], f, indent=4)
    
    cur_data = (RelaGraphNC.from_json(temp_file).slices)[0]
    before_nodes =  RelaDeviceLevelForwardingGraph.get_nodes(RelaGraphFEC.get_before_state(cur_data))
    after_nodes =RelaDeviceLevelForwardingGraph.get_nodes(RelaGraphFEC.get_after_state(cur_data))
    nodes = list(before_nodes.union(after_nodes))
    delete_node = nodes[random.randint(0,len(nodes)-1)]
    spec = PStar(PNegSymbols (delete_node)) % Preserve()
    compiled_spec = RelaCompiler.compile(spec)
    change_file = os.path.abspath(temp_file)
    start_time = time.perf_counter()
    result = verify_network_change(compiled_spec, change_file)
    end_time = time.perf_counter()
    seconds.append(end_time - start_time)
    
with open('./b.txt', "w") as f:
    for item in seconds:
        f.write(str(item) + "\n")
    

for i in range(1, 2001):
    nth = random.randint(0,length-1)
    with open(temp_file, 'w') as f:
        json.dump([data[nth]], f, indent=4)
    
    cur_data = (RelaGraphNC.from_json(temp_file).slices)[0]
    before_nodes =  RelaDeviceLevelForwardingGraph.get_nodes(RelaGraphFEC.get_before_state(cur_data))
    after_nodes =RelaDeviceLevelForwardingGraph.get_nodes(RelaGraphFEC.get_after_state(cur_data))
    nodes = list(before_nodes.union(after_nodes))
    delete_node = nodes[random.randint(0,len(nodes)-1)]
    change_node = nodes[random.randint(0,len(nodes)-1)]
    spec = ConcatSpec(PStar(PNegSymbols (delete_node)) % Preserve(),ConcatSpec(pDot % Replace (PSymbol(delete_node),PSymbol(change_node)),PStar(PNegSymbols (delete_node)) % Preserve()))
    compiled_spec = RelaCompiler.compile(spec)
    change_file = os.path.abspath(temp_file)
    start_time = time.perf_counter()
    result = verify_network_change(compiled_spec, change_file)
    end_time = time.perf_counter()
    seconds.append(end_time - start_time)
    
with open('./c.txt', "w") as f:
    for item in seconds:
        f.write(str(item) + "\n")





