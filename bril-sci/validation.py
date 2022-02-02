

def validate(program: dict) -> bool:
    #Top level should be a dictionary containing "functions" and "structs"
    funcs=program["functions"]
    #check that a main function exists
    if "@main" in funcs:
        pass
    else:
        raise Exception("ERROR: BRIL-SCI program doesn't have a main function")
    for func in funcs:
        #want to check that each instruction in a function is well formed
        #specifically that each operand has the right number of arguments
        #that the types of the arguments match against the specification
        #check that all label values are unique
        lablel_names={}
        func_name=func['name']
        instruction_num=0
        for instr in func['instrs']:
            if 'label' in instr:
                name=instr['label']
                if name in lablel_names:
                    previous_instr=lablel_names[name]
                    error_message_template="""Label name: {0} in function {1} at instruction #{2} is not 
                    unique. It has the same value as instruction number{4}."""
                    message=error_message_template.format(name,func_name,instruction_num,previous_instr)
                    raise Exception(message)
                else:
                    lablel_names[name]=instruction_num
            
                    

