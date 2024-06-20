from string import punctuation
import json
import os
import re

thy_info = {}
session_info = {}
l4v_folder = "/data2/caoqingxing/verification/l4v/"

def session(name="", ROOT_dir="", ROOT_relative_dir="", additional_dir=["."], dependency=[], theories=[]):
    new_session = {}
    new_session["dependency"] = dependency
    new_session["name"] = name
    new_session["theories"] = theories
    new_session["ROOT_dir"] = ROOT_dir
    new_session["ROOT_relative_dir"] = ROOT_relative_dir
    
    new_session["additional_dir"] = additional_dir

    return new_session

def lemma(name="", session="", dependency=[], theory_name="", context="", statement="", proof=""):
    new_lemma = {}
    new_lemma["session"] = session
    new_lemma["dependency"] = dependency
    new_lemma["context"] = context
    new_lemma["proof"] = proof
    new_lemma["statement"] = statement
    new_lemma["name"] = name
    new_lemma["theory_name"] = theory_name

    return new_lemma

def parse_thy_header(filename, full_working_dir):
    dependency = {}
    name = os.path.basename(filename).replace(".thy","")
    with open(filename,"r") as f:
        context = f.read()
        # print(filename)
        context = context[context.find('theory'): ]
        context = context[:context.find('begin')+5]
        # print(context)
        context = re.findall('theory[\s\S]+(imports[\s\S]+begin)', context)
        # print(context)
        context = context[0]
        theory_names_init = []
        theory_names = []
        for x in context.split("imports")[1].split("begin")[0].split(" "):
            for t in x.split("\n"):
                theory_names_init.append(t)
        comment = False
        for x in theory_names_init:
            t = x.strip().strip('"')
            if t:
                if "keywords" in t:
                    break
                elif "(*" == t:
                    comment = True
                elif "*)" == t:
                    comment = False
                elif not comment:
                    theory_names.append(t)
            
        # theory_names = [x.strip().strip('"') for x in theory_names if x.strip().strip('"')]
                      
        for theory_name in theory_names:
            dependency[theory_name] = ""
            for folder in full_working_dir:
                if os.path.isfile(os.path.join(folder,theory_name+".thy")):
                    # id = os.path.abspath(os.path.join(folder,theory_name+".thy")).split("verification/l4v")[1]
                    dependency[theory_name] = os.path.abspath(folder).replace(l4v_folder,"")
                    break
    
    theory_info = {'name': name, "dependency": dependency}
    return theory_info

def parse_thy_c_code(filename):
    code = set([])
    pwd = os.path.dirname(filename)
    with open(filename,"r") as f:
        context = f.read()
        c_command_i = context.find('install_C_file ')
        if c_command_i > 0:
            c = context[c_command_i: ].split(" ")[1]#.strip().strip('"').replace("$L4V_ARCH","ARM")
            c = re.findall('["]*([^"]*)["]*', c)[0].replace("$L4V_ARCH","ARM")
            c_path = os.path.abspath(os.path.join(pwd,c))
            assert os.path.isfile(c_path), filename
            code.add(c_path.replace(l4v_folder,""))

        # a_command_i = context.find('\nautocorres ')
        # if a_command_i > 0:
        #     c = " ".join(context[a_command_i: ].split(" ")[1:])#.strip().strip('"').replace("$L4V_ARCH","ARM")
        #     print(c)
        #     c = re.findall('["]*([^"]*)["]*', c)[0].replace("$L4V_ARCH","ARM")
        #     c_path = os.path.abspath(os.path.join(pwd,c))
        #     assert os.path.isfile(c_path), filename+ "\n" + c + "\n" + c_path
        #     code.add(c_path.replace(l4v_folder,""))
    return list(code)

def get_theory_path_by_name(theory_name, cur_session):
    full_working_dir = []
    for dir in cur_session['additional_dir']:
        full_working_dir.append(l4v_folder+os.path.join(cur_session['ROOT_dir'], cur_session['ROOT_relative_dir'], dir))
    
    theory_info_path = None
    for folder in full_working_dir:
        if os.path.isfile(os.path.join(folder,theory_name+".thy")):
            assert theory_info_path is None, theory_info_path + "\n current: " + os.path.join(folder,theory_name+".thy")
            theory_info_path = os.path.join(folder,theory_name+".thy")#folder
        
    if theory_info_path is None:
        print(theory_name)
        print(cur_session)
        print(full_working_dir)
        input()
    return theory_info_path

def extract_theory_recursive(theory_file_name, cur_session):#(path, entry_file, session_info, package):
    input_file_name = l4v_folder + theory_file_name
    theory_id = os.path.abspath(input_file_name).split("verification/l4v")[1]
    full_working_dir = []
    for dir in cur_session['additional_dir']:
        full_working_dir.append(os.path.join(l4v_folder, cur_session['ROOT_dir'], cur_session['ROOT_relative_dir'], dir))

    theory_info = parse_thy_header(input_file_name, full_working_dir)
    related_c_code = parse_thy_c_code(input_file_name)
    layer = 1

    return_theories = [theory_id]
    for thy_name, thy_path in theory_info['dependency'].items():
        if thy_path:
            thy_path = l4v_folder + thy_path
            dep_thy_id = os.path.abspath(os.path.join(thy_path,thy_name+".thy")).split("verification/l4v")[1]
            if dep_thy_id not in thy_info:
                theories_names = extract_theory_recursive(dep_thy_id, cur_session)
                return_theories += theories_names
            layer = max(layer, thy_info[dep_thy_id]['depth']+1)
            related_c_code += thy_info[dep_thy_id]['related_c_code']
            thy_info[dep_thy_id]['child'] += [theory_id]
        elif "." in thy_name:
            tmp = thy_name.split(".")
            session = tmp[0]
            name = tmp[1]
            if "HOL" not in session and "CParser" not in session and "Simpl-VCG" not in session and "AutoCorres" not in session:
                dep_thy_id = os.path.abspath(get_theory_path_by_name(name, session_info[session])).split("verification/l4v")[1]
                if dep_thy_id not in thy_info:
                    theories_names = extract_theory_recursive(dep_thy_id, session_info[session])
                layer = max(layer, thy_info[dep_thy_id]['depth']+1)
                related_c_code += thy_info[dep_thy_id]['related_c_code']
                thy_info[dep_thy_id]['child'] += [theory_id]
                # return_theories += theories_names
    
    theory_info["depth"] = layer
    theory_info["related_c_code"] = list(set(related_c_code))
    theory_info["child"] = []
    theory_info['path'] = os.path.abspath(input_file_name).split("verification/l4v")[1]
    theory_info['session'] = cur_session['name']
    assert theory_id not in thy_info, theory_id
    thy_info[theory_id] = theory_info

    return return_theories

def get_session_layer(session_name = None):
    if session_name:
        session_name = session_name.strip('"')
        # print(session_name)
        session_info[session_name]['depth'] = 1
        for dep_session in session_info[session_name]['dependency']:
            # if dep_session == '"ExecSpec"': print(session_name)
            if "HOL" not in dep_session and "CParser" not in dep_session and "Simpl-VCG" not in dep_session and "AutoCorres" not in dep_session:
                session_info[session_name]['depth'] = max(session_info[session_name]['depth'], get_session_layer(dep_session)+1)
        return session_info[session_name]['depth']
    else:            
        for name, info in session_info.items():
            if 'depth' in session_info[name]: continue
            session_info[name]['depth'] = 1
            for dep_session in session_info[name]['dependency']:
                # if dep_session == '"ExecSpec"': print(name)
                if "HOL" not in dep_session and "CParser" not in dep_session and "Simpl-VCG" not in dep_session and "AutoCorres" not in dep_session:
                    session_info[name]['depth'] = max(session_info[name]['depth'], get_session_layer(dep_session)+1)

def main(ROOTS_path, parse_thy=True):
    skip = ["tools", "docs", "c-parser", "autocorres"]

    ROOT_path_keywords_other = ["document_files", "options", "description"]

    l4v_path = os.path.dirname(ROOTS_path)
    cur_session = None
    name=""
    with open(ROOTS_path, 'r') as f_rs:
        for ROOTS_line in f_rs.readlines():
            ROOTS_line = ROOTS_line.strip()
            # print(ROOTS_line)
            if ROOTS_line.startswith("#") or ROOTS_line in skip:
                continue
            
            pwd = os.path.join(l4v_path, ROOTS_line)
            ROOT_path = os.path.join(pwd, "ROOT")

            with open(ROOT_path, 'r') as f_r:
                toplevel = ""
                for line in f_r.readlines():
                    line = line.strip()

                    # handling keywords
                    if line.startswith("theories"):
                        toplevel = "theories"
                    elif line.startswith("sessions"):
                        toplevel = "sessions"
                    elif line.startswith("directories"):
                        toplevel = "directories"
                    elif line.startswith("session"):
                        if cur_session is not None: #toplevel != "":
                            # sessions_info.append(cur_session)
                            session_info[cur_session['name']] =cur_session
                        toplevel = ""
                        # session AInvs in "invariant-abstract" = ASpec +
                        dependency = [re.findall('=([\s\S]*)\+', line)[0].strip()]
                        dir = re.findall('in ["]*([\s\S]+)["]* =', line)
                        dir = dir[0].replace("$L4V_ARCH","ARM") if dir else "."
                        if dir.endswith('"'): dir=dir[:-1]
                        theory_dir = os.path.join(pwd, dir)
                        name = line.split(" ")[1]
                        cur_session = session(name=name, ROOT_dir=pwd.replace(l4v_folder,""), ROOT_relative_dir=dir, additional_dir=["."], dependency=dependency)
                    elif line in ROOT_path_keywords_other:
                        toplevel = ""
                    # handling comments
                    elif line.startswith("(*") or line.startswith("*") or line.endswith("*)"):
                        continue
                    elif line == "":
                        continue
                    # no keywords
                    else:
                        if toplevel.startswith("theories"):
                            t = re.findall('["]*([^"]*)["]*', line)
                            t = t[0]

                            thy_file = t.replace("$L4V_ARCH","ARM").replace(".","/")+".thy"
                            for dir in cur_session["additional_dir"]:
                                thy_dir = os.path.join(theory_dir, dir)
                                if os.path.isfile(os.path.join(thy_dir, thy_file)):
                                    break
                                thy_dir = None
                            if thy_dir:
                                thy_id = os.path.abspath(os.path.join(thy_dir, thy_file)).split("verification/l4v")[1]
                                if parse_thy and thy_id not in thy_info:
                                    theory_info = extract_theory_recursive(thy_id, cur_session)
                                    cur_session["theories"]= list(set(cur_session["theories"]).union(set(theory_info)))
                            else:
                                print(ROOT_path, t.replace("$L4V_ARCH","ARM"))
                        elif toplevel.startswith("sessions"):
                            cur_session["dependency"].append(line.strip())
                        elif toplevel.startswith("directories"):
                            dir = re.findall('["]*([^"]*)["]*', line)
                            cur_session["additional_dir"].append(dir[0].replace("$L4V_ARCH","ARM"))

    session_info[cur_session['name']] =cur_session

if __name__ == "__main__":

    main("/data2/caoqingxing/verification/l4v/ROOTS", parse_thy=False)
    main("/data2/caoqingxing/verification/l4v/tools/ROOTS", parse_thy=False)
    print("session parsed")
    main("/data2/caoqingxing/verification/l4v/ROOTS")
    main("/data2/caoqingxing/verification/l4v/tools/ROOTS")
    
    get_session_layer()
    
    with open("sel4_session_info.json","w") as f:
        json.dump(session_info, f, indent=4)
    with open("sel4_thy_nolemma_info.json","w") as f:
        json.dump(thy_info, f, indent=4)