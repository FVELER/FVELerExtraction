from string import punctuation
import json
import os
import re
import dsp_utils
import shutil
import gc
from tqdm import tqdm
from collections import defaultdict 

import re
from mpmath import mp, mpf, fmod
import hashlib

os.environ['PISA_PATH'] = '/data2/caoqingxing/Portal-to-ISAbelle/src/main/python/'

def hash_string_to_int(arg):
    return int(hashlib.sha256(arg.encode("utf-8")).hexdigest(), 16) % 10**30

def hash_string_to_float(arg):
    x = mpf(hash_string_to_int(arg) / (10 ** 30))
    return fmod(x * mp.pi, mpf(1.))

def get_split(arg):
    float_hash = hash_string_to_float(arg)
    if float_hash < 0.92:
        return "train"
    elif float_hash < 0.96:
        return "val"
    else:
        return "test"

def lemma(name="", session="", dependency=[], theory_name="", context="", statement="", proof=[], proof_state=[], num_steps=0):
    new_lemma = {}
    new_lemma["session"] = session
    new_lemma["dependency"] = dependency
    new_lemma["context"] = context
    new_lemma["proof"] = proof
    new_lemma["proof_state"] = proof_state
    new_lemma["statement"] = statement
    new_lemma["name"] = name
    new_lemma["theory_name"] = theory_name
    new_lemma["num_steps"] = num_steps

    return new_lemma

l4v_folder = "/data2/caoqingxing/verification/l4v/"

lemma_info = []
unnamed_thy_num = 0

def get_lemma_info(thy):
    global unnamed_thy_num
    with open("sel4_extraction/"+thy['path'].replace(".thy", ".json"),"r") as f:
        thy_state = json.load(f)
    pre_state = ""
    return_lemmas = []
    new_lemma = None
    for steps in thy_state:
        state = steps["raw_output"]
        context =steps['step']
        if state != "":
            if pre_state == "":
                name = re.findall("<CTXT> (lemma|corollary|lift_definition|instance|theorem|schematic_goal)(\n| )([\s\S]*):", context)
                if len(name) > 0:
                    name = name[0][2]
                else:
                    unnamed_thy_num += 1
                    name = "unnamed_thy_"+str(unnamed_thy_num)
                statement = context # statement = s[s.find(name)+len(name)+1:]
                new_lemma = lemma(name=name, theory_name=thy['name'], context=context, statement=statement, proof=[statement], proof_state=[state], num_steps=0)
            else:
                new_lemma['context'] += " " + context
                new_lemma['proof'].append(context)
                new_lemma['proof_state'].append(state)
                new_lemma['num_steps'] += 1
        elif pre_state != "":
            if "lemma " in new_lemma["statement"] or "theorem " in new_lemma["statement"]:
                new_lemma['context'] += " " + context
                new_lemma['proof'].append(context)
                new_lemma['num_steps'] += 1
                new_lemma['proof_state'].append("")
                lemma_info.append(new_lemma)
                return_lemmas.append(new_lemma)
                # print(new_lemma)
                # input()    
            new_lemma = None
            
        pre_state = state
    
    return return_lemmas

if __name__ == "__main__":
    with open("sel4_thy_nolemma_info.json","r") as f:
        thy_info = json.load(f)
    with open("sel4_session_info.json","r") as f:
        session_info = json.load(f)
    
    dist_thy = defaultdict(int)
    depth_lemmas =  {"train": defaultdict(int),  "val": defaultdict(int), "test": defaultdict(int), "test_hard":defaultdict(int)}
    step_lemmas = {"train": defaultdict(int),  "val": defaultdict(int), "test": defaultdict(int), "test_hard":defaultdict(int)}
    num_tactics = {"train": defaultdict(int),  "val": defaultdict(int), "test": defaultdict(int), "test_hard":defaultdict(int)}
    num_thy = 0
    num_lemmas = 0
    num_session_lemmas = defaultdict(int)

    split = {"train": [],  "val": [], "test": [], "test_hard":[]}
    selected_testhard_session = ["SysInit", "SysInitExamples", "LibTest"]

    for name, thy in tqdm(thy_info.items()):
        if os.path.isfile("sel4_extraction/"+thy['path'].replace(".thy", ".json")):
            dist_thy[thy["depth"]] += 1
            num_thy += 1
            thy_info[name]['lemmas'] = get_lemma_info(thy)
            for cur_lemma in thy_info[name]['lemmas']:
                if thy["session"].strip('"') in selected_testhard_session:
                    split_name = "test_hard"
                else:
                    split_name = get_split(cur_lemma['context'])
                split[split_name].append(cur_lemma)
                step_lemmas[split_name][cur_lemma['num_steps']] += 1
                depth_lemmas[split_name][thy["depth"]] += 1
                num_lemmas += 1
                
                num_session_lemmas[thy["session"].strip('"')] += 1
                    
                for proof_step in cur_lemma['proof']:
                    # print(proof_step)
                    # display = []
                    tactics = re.findall('".*?"', proof_step)
                    for tactic in tactics:
                        # print(tactic)
                        # display.append(tactic)
                        num_tactics[split_name][tactic] += 1
                        proof_step = proof_step.replace(tactic, "")
                    tactics = re.findall('\(.*?\)', proof_step)
                    for tactic in tactics:
                        num_tactics[split_name][tactic] += 1
                        proof_step = proof_step.replace(tactic, "")
                    tactics = proof_step.split(" ")
                    for tactic in tactics:
                        if len(tactic) > 0:
                            num_tactics[split_name][tactic] += 1
    
    skipped_tactics = ["by", "show", "using", "qed"]
    
    print("Theory: ")
    print(num_thy)
    print("Lemma: ")
    print(num_lemmas)
    print( len(split['train']), len(split['val']), len(split['test']), len(split['test_hard']) )


    #####################################################
    ###  select which sessions are used for test-hard ###
    # layer_lemma = defaultdict(int)
    # layer_lemma_name = defaultdict(list)
    # for name, num in num_session_lemmas.items():
    #     layer_lemma[session_info[name]['depth']] += num
    #     layer_lemma_name[session_info[name]['depth']].append(name)
    #     print(name, num, session_info[name]['depth'])
    # print(layer_lemma)
    # print(layer_lemma_name)
    #####################################################
    
    
    for split_name, depth_dict in depth_lemmas.items():
        depth_sum = 0
        max_depth = 0
        num_lemmas = 0
        for depth, num in depth_dict.items():
            depth_sum += depth*num
            num_lemmas += num
            max_depth = max(max_depth, depth)
        print(split_name, depth_sum*1.0/num_lemmas, max_depth)
    
    for split_name, step_dict in step_lemmas.items():
        step_sum = 0
        max_step = 0
        num_lemmas = 0
        for step, num in step_dict.items():
            step_sum += step*num
            num_lemmas += num
            max_step = max(max_step, step)
        print(split_name, step_sum*1.0/num_lemmas, max_step, step_sum)
    
    session_theory_lemma_num = {}
    for name, info in session_info.items():
        session_theory_lemma_num[name] = {}
        for thy_name in session_info[name]['theories']:
            if thy_name in thy_info and 'lemmas' in thy_info[thy_name]:
                # print(name, thy_name)
                session_theory_lemma_num[name][thy_name] = len(thy_info[thy_name]['lemmas'])
                
    with open("sel4_lemma_info.json","w") as f:
        json.dump(lemma_info, f, indent=4)
    with open("sel4_thy_info.json","w") as f:
        json.dump(thy_info, f, indent=4)
    with open("dataset_lemma_split.json","w") as f:
        json.dump(split, f, indent=4)
    with open("statistic_output.json","w") as f:
        json.dump({"depth_theory":dist_thy, "depth_lemmas":depth_lemmas, "step_lemmas":step_lemmas, "num_tactics": num_tactics, "session_theory_lemma_num": session_theory_lemma_num}, f, indent=4)
