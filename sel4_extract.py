from string import punctuation
import json
import os
import re
import dsp_utils
import shutil
import gc
from tqdm import tqdm

os.environ['PISA_PATH'] = '/data2/caoqingxing/Portal-to-ISAbelle/src/main/python/'
l4v_folder = "/data2/caoqingxing/verification/l4v/"

def save_extraction(extraction_root, input_file_name, o):
    assert "verification/l4v" in input_file_name, input_file_name
    output_file = extraction_root + input_file_name.split("verification/l4v")[1].replace('.thy','.json')
    output_folder = os.path.dirname(output_file)
    if not os.path.isdir(output_folder):
        os.makedirs(output_folder)
    
    with open(output_file,'w') as f:
        json.dump(o, f, indent=4)

def extract_theory(theory_file_name, session_info):
    input_file_name = l4v_folder + theory_file_name
    full_working_dir = []
    for dir in session_info['additional_dir']:
        full_working_dir.append(os.path.join(session_info['ROOT_dir'], session_info['ROOT_relative_dir'], dir))

    extraction_root = 'sel4_extraction'
    assert "verification/l4v" in input_file_name, input_file_name
    output_file = extraction_root + input_file_name.split("verification/l4v")[1].replace('.thy','.json')

    # can not handle AutoCorresTest seems unfinished file that also fail with "isabelle build"
    if "AutoCorresTest" in output_file:
        return False
    if os.path.isfile(output_file):
        return True
    
    with open(input_file_name,"r") as f:
        theorem_and_sledgehammer_proof = f.read()
    
    # skipped keywords defined in imports ... begin, cause failure parent thy parsing in PISA
    context = re.findall('theory[\s\S]+(imports[\s\S]+begin\n)', theorem_and_sledgehammer_proof)[0]
    theory_names = context.split("imports")[1].split("begin")[0].split(" ")
    theory_names = [x.strip().strip('"') for x in theory_names if x.strip().strip('"')]
    skipped = False
    for t in theory_names:
        if "keywords" in t:
            skipped = True
            break

    tmp_files = []
    if skipped:
        result = {'success': False}
    else:
        for folder in full_working_dir:
            files = [f for f in os.listdir(folder) if os.path.isfile(os.path.join(folder, f))]
            for file in files:
                dest = os.path.dirname(input_file_name)
                if not os.path.exists(os.path.join(dest,file)):
                    shutil.copy2(os.path.join(folder,file), dest)
                    tmp_files.append(os.path.join(dest,file))

        checker = dsp_utils.Checker(
            working_dir=session_info['name']+';'+'/data2/caoqingxing/verification/l4v/'+';'+session_info['ROOT_dir'],
            isa_path='/home/caoqingxing/Isabelle2023',
            theory_file=input_file_name,
            port=8001
        )
        # can not handle "private" command: Outer syntax error
        result = checker.check_full_thy(theorem_and_sledgehammer_proof.replace("private",""))

    if result['success']:
        save_extraction(extraction_root, input_file_name, result['step_results'])
    else:
        with open("sel4_extraction/skipped_files.txt",'a+') as f:
            f.write(input_file_name+"\n")
    
    for file in tmp_files:
        os.remove(file)
    
    checker = None
    gc.collect()
    return result['success']

if __name__ == "__main__":

    with open("sel4_thy_info.json","r") as f:
        thy_info = json.load(f)
    with open("sel4_session_info.json","r") as f:
        session_info = json.load(f)

    for id, info in tqdm(thy_info.items()):
        print(id)
        extract_theory(id, session_info[info['session']])

    # transfrom to training format
    # input = "<SOS> <CTXT> {} <PRF_STT> {} <PRF_STP>".format(pre_step, pre_state)
    # output = "{} <EOS>".format(step)
    # pre_step = step
    # pre_state = obs
    # example.append({"input": input, "output": output})