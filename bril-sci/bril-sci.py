import sys, json, typing, queue,math

#interpreter to implement bril language with SCI memory extensions


class HeapPointer:
    """This class implements heap data for the interpreter. It extends the standard key to include information about security groups. Also,
    it enforces default initializiations of all types.
    """

    def __init__(self,base:int, offset:int, element:str=None)->None:
        self.base=base
        self.offset=offset
        self.element=element
    
    def __str__(self):
        result ="(Base: {0}, Offset: {1}, Element: {2} )".format(self.base,self.offset,self.element)
        return result

    def __repr__(self):
        return self.__str__()

    def add(self,offset:int):
        new_offset=self.offset+offset
        result=HeapPointer(self.base,new_offset)
        return(result)
    
    def is_null(self):
        if self.base<0:
            return True
        else:
            return False

class HeapStore:

    def __init__(self,structs)->None:
        self.storage={}
        self.base_types=['int','float','bool']
        self.highest_value=0
        #Heap needs to be passed the structs top level JSON object of the BRIL program for type checking
        self.structs={}
        for struct in structs:
            name=struct['name']
            members=struct['mbrs']
            members_dictionary={}
            for item in members:
                members_dictionary[item['name']]=item['type']
            self.structs[name]=members_dictionary
        self.reclaimed_base_number=queue.SimpleQueue()
    
    def is_empty(self)->bool:
        if len(self.storage.keys())>0:
            return False
        else:
            return True

    def get_base(self)->int:
        if self.reclaimed_base_number.empty():
            result=self.highest_value
            self.highest_value+=1
        else:
            result=self.reclaimed_base_number.get()
        return result

    def alloc(self,bril_type,amt,security_group=0) -> None:
        if amt>0:
            pass
        else:
            raise Exception("Size of memory allocation must be greater than zero")
        new_allocation={}
        new_base=self.get_base()
        self.storage[new_base]=new_allocation

        new_allocation['security_group']=security_group
        new_allocation['bril_type']=bril_type
        default_value=None
        if type(bril_type) is str:
                if bril_type=='int':
                    default_value=0
                elif bril_type=='float':
                    default_value=0.0
                elif bril_type=='bool':
                    default_value=False
                elif bril_type in self.structs:
                    objects=[dict() for x in range(amt)]
                    new_allocation['objects']=objects
                    result=HeapPointer(new_base,0)
                    return result
                else:
                    #something terrible has gone wrong
                    raise Exception("Unexpected type {0} encountered".format(bril_type))
        else: #Here, we have a pointer to a pointer, so the default value will be a null pointer. 
            default_value=HeapPointer(-1,0)  # negative base index is indicative of a null pointer.
        new_allocation['objects']=[default_value]*amt
        result=HeapPointer(new_base,0)
        return result
    
    def free(self,key : HeapPointer, security_group=0):
        #check for null pointer
        if key.is_null():
          raise Exception("Null Pointer Exception: Called free operation on a null pointer")
        #check if the current function has permission to free this memory
        alloc_sec_group=self.storage[key.base]['security_group']
        if alloc_sec_group!=security_group:
            message="ERROR: Memory allocated by security group {0} but free called by security group {1} in location base: {2}"
            message=message.format(alloc_sec_group,security_group,key.base)
            raise Exception(message)
        if key.offset==0:
            if key.base in self.storage:
                del self.storage[key.base]
                self.reclaimed_base_number.put(key.base)
            else:
                message="ERROR: Attempting to double free allocation with base number {0}".format(key.base)
                raise Exception(message)
        else:
            message='ERROR: Tried to free illegal memory location base: {0}, offset: {1}. Offset must be 0.'
            message=message.format(key.base,key.offset)
            raise Exception(message)

    def store(self,key : HeapPointer, value,security_group=0):
        #check for null pointer
        if key.is_null():
          raise Exception("Null Pointer Exception: Called store operation on a null pointer")
        #check if the current function has permission to free this memory
        alloc_sec_group=self.storage[key.base]['security_group']
        if alloc_sec_group!=security_group:
            message="ERROR: Memory allocated by security group {0} but write was attempted by security group {1} in location base: {2}"
            message=message.format(alloc_sec_group,security_group,key.base)
            raise Exception(message)
        data_array=self.storage[key.base]['objects']
        item=data_array[key.offset]
        #print(data)
        if key.element:
            item[key.element]=value
        else:
            item=value
            
    def load(self,key,security_group=0):
        #check for null pointer
        if key.is_null():
          raise Exception("Null Pointer Exception: Called load operation on a null pointer")
        data=self.storage[key.base]
        data=data['objects'][key.offset]
        if key.element:
            result=data[key.element]
        else:
            result=data
        return(result)

    def getmbr(self,key,element,security_group=0):
        #check for null pointer
        if key.is_null():
          raise Exception("Null Pointer Exception: Called get member operation on a null pointer")
        #check that the key points to a struct
        data=self.storage[key.base]
        data_type=data['bril_type']
        if type(data_type) is str:
            if  data_type in self.structs:
                #check if the element is a valid part of the struct
                struct_members=self.structs[data_type]
                if element in struct_members:
                    result=HeapPointer(key.base,key.offset,element)
                    return result
            else:
                message="Error: Get Member can only be called on pointers to structs, but was called on key base {0} with type {1}"
                message=message.format(key.base,data_type)
                raise Exception(message)
        else:
            message="Error: Get Member can only be called on pointers to structs, but was called on key base {0} with type {1}"
            message=message.format(key.base,data_type)
            raise Exception(message)

def eval_instr(state : dict,local_vars : dict ,current_instr) -> dict:
    #gigantic switch statement over instruction op
    label_name=current_instr.get('label')
    if label_name:
        return {'action':'next'}
    op=current_instr['op']
    match op:
        case 'const':
            dest=current_instr['dest']
            value=current_instr['value']
            #convert from string data to python type
            bril_type=current_instr['type']
            if bril_type=='int':
                value=int(value)
            elif bril_type=='float':
                value=float(value)
            elif bril_type=='bool':
                value=bool(value)
            elif 'ptr' in bril_type:
                #only const operation involving pointers is to create a null one
                value=HeapPointer(-1 , 0) # a negative base number indicates a null pointer
            else:
                #we shouldn't reach this block
                raise Exception("Unhandled data type {0} encountered".format(bril_type))
            local_vars[dest]=value
            return {'action':'next'}
        case 'id':
            name=current_instr['args'][0]
            dest=current_instr['dest']
            #should I be making copies of the pointer types?
            local_vars[dest]=local_vars[name]
            return {'action':'next'}
        case 'fadd':
            args=current_instr['args']
            arg1=args[0]
            arg2=args[1]
            value1=local_vars[arg1]
            value2=local_vars[arg2]
            value=value1+value2
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'fmul':
            args=current_instr['args']
            arg1=args[0]
            arg2=args[1]
            value1=local_vars[arg1]
            value2=local_vars[arg2]
            value=value1*value2
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'fsub':
            args=current_instr['args']
            arg1=args[0]
            arg2=args[1]
            value1=local_vars[arg1]
            value2=local_vars[arg2]
            value=value1-value2
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'fdiv':
            args=current_instr['args']
            arg1=args[0]
            arg2=args[1]
            value1=local_vars[arg1]
            value2=local_vars[arg2]
            value=value1/value2
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'fle':
            args=current_instr['args']
            arg1=args[0]
            arg2=args[1]
            value1=local_vars[arg1]
            value2=local_vars[arg2]
            value=arg1<=arg2
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'flt':
            args=current_instr['args']
            arg1=args[0]
            arg2=args[1]
            value1=local_vars[arg1]
            value2=local_vars[arg2]
            value=value1<value2
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'fgt':
            args=current_instr['args']
            arg1=args[0]
            arg2=args[1]
            value1=local_vars[arg1]
            value2=local_vars[arg2]
            value=value1>value2
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'fge':
            args=current_instr['args']
            arg1=args[0]
            arg2=args[1]
            value1=local_vars[arg1]
            value2=local_vars[arg2]
            value=arg1>=arg2
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'and':
            args=current_instr['args']
            arg1=args[0]
            arg2=args[1]
            value1=local_vars[arg1]
            value2=local_vars[arg2]
            value=arg1 and arg2
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'or':
            args=current_instr['args']
            arg1=args[0]
            arg2=args[1]
            value1=local_vars[arg1]
            value2=local_vars[arg2]
            value=arg1 or arg2
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'eq':
            args=current_instr['args']
            arg1=args[0]
            arg2=args[1]
            value1=local_vars[arg1]
            value2=local_vars[arg2]
            value=arg1==arg2
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'feq':
            args=current_instr['args']
            arg1=args[0]
            arg2=args[1]
            value1=local_vars[arg1]
            value2=local_vars[arg2]
            value=arg1==arg2
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'not':
            args=current_instr['args']
            arg1=args[0]
            value1=local_vars[arg1]
            value=not value1
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'add':
            args=current_instr['args']
            arg1=args[0]
            arg2=args[1]
            value1=local_vars[arg1]
            value2=local_vars[arg2]
            value=value1+value2
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'mul':
            args=current_instr['args']
            arg1=args[0]
            arg2=args[1]
            value1=local_vars[arg1]
            value2=local_vars[arg2]
            value=value1*value2
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'sub':
            args=current_instr['args']
            arg1=args[0]
            arg2=args[1]
            value1=local_vars[arg1]
            value2=local_vars[arg2]
            value=value1-value2
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'div':
            args=current_instr['args']
            arg1=args[0]
            arg2=args[1]
            value1=local_vars[arg1]
            value2=local_vars[arg2]
            value=value1/value2
            if value >0:
                value=math.floor(value)
            else:
                value=math.ceil(value)
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'le':
            args=current_instr['args']
            arg1=args[0]
            arg2=args[1]
            value1=local_vars[arg1]
            value2=local_vars[arg2]
            value=arg1<=arg2
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'lt':
            args=current_instr['args']
            arg1=args[0]
            arg2=args[1]
            value1=local_vars[arg1]
            value2=local_vars[arg2]
            value=value1<value2
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'gt':
            args=current_instr['args']
            arg1=args[0]
            arg2=args[1]
            value1=local_vars[arg1]
            value2=local_vars[arg2]
            value=value1>value2
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'ge':
            args=current_instr['args']
            arg1=args[0]
            arg2=args[1]
            value1=local_vars[arg1]
            value2=local_vars[arg2]
            value=arg1>=arg2
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'print':
            args=current_instr['args']
            values=map(lambda x: str(local_vars[x]).lower(),args) 
            #python prints out bools with a capitalized first letter. Using lower function to have
            #results align with brili interpreter                                               
            result=' '.join(values)
            print(result)
            return {'action':'next'}
        case 'jmp':
            target=current_instr['labels'][0]
            return {'action':'jump', 'label':target}
        case 'br':
            name=current_instr['args'][0]
            test=local_vars[name]
            if test:
                target=current_instr['labels'][0]
            else:
                target=current_instr['labels'][1]
            return {'action':'jump','label':target}
        case 'nop':
            return {'action':'next'}
        case 'ret':
            arg=current_instr.get('args')
            if arg:
                value=local_vars[arg[0]]
                return {'action':'end', 'ret':value}
            else:
                return {'action': 'end'}
        case 'call':
            name_of_func=current_instr['funcs'][0]
            #check if there are args
            new_local_vars={}
            called_func=state['funcs'][name_of_func]
            func_args=called_func.get('args')
            if func_args:
                caller_args=current_instr['args']
                for i in range(len(func_args)):
                        value=local_vars[caller_args[i]]
                        name=func_args[i]['name']
                        #should I be creating copies of the point objects?
                        new_local_vars[name]=value
            
            value=eval_call(state,name_of_func,new_local_vars)
            if 'dest' in current_instr:
                dest=current_instr['dest']
                local_vars[dest]=value
            return {'action':'next'}
        case 'alloc':
            arg=current_instr['args'][0]
            size=local_vars[arg]
            typ=current_instr['type']['ptr']
            heap=state['heap'] 
            sec_group=state['security_group'][0]
            ptr=heap.alloc(typ,size,sec_group)
            dest=current_instr['dest']
            local_vars[dest]=ptr
            return {'action':'next'}
        case 'free':
            arg=current_instr['args'][0]
            heap=state['heap']
            ptr=local_vars[arg]
            sec_group=state['security_group'][0]
            heap.free(ptr,sec_group)
            return {'action':'next'}
        case 'store':
            args=current_instr['args']
            ptr_name=args[0]
            ptr=local_vars[ptr_name]
            variable = args[1]
            value = local_vars[variable]
            heap=state['heap']
            sec_group=state['security_group'][0]
            heap.store(ptr,value,sec_group)
            return {'action':'next'}
        case 'load':
            args=current_instr['args']
            ptr_name=args[0]
            ptr=local_vars[ptr_name]
            heap=state['heap']
            sec_group=state['security_group'][0]
            value=heap.load(ptr,sec_group)
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'ptradd':
            args=current_instr['args']
            ptr_name=args[0]
            name=args[1]
            offset=local_vars[name]
            ptr=local_vars[ptr_name]
            new_ptr=ptr.add(offset)
            dest=current_instr['dest']
            local_vars[dest]=new_ptr
            return {'action':'next'}
        case 'getmbr':
            args=current_instr['args']
            ptr_name=args[0]
            ptr=local_vars[ptr_name]
            element_name=args[1]
            heap=state['heap']
            sec_group=state['security_group'][0]
            value=heap.getmbr(ptr,element_name,sec_group)
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'isnull':
            args=current_instr['args']
            ptr_name=args[0]
            ptr=local_vars[ptr_name]
            value = ptr.is_null()
            dest=current_instr['dest']
            local_vars[dest]=value
            return {'action':'next'}
        case 'phi':
            raise Exception("Phi nodes are not yet supported")
        case 'speculate':
            raise Exception("Speculative execution not yet supported")
        case 'guard':
            raise Exception("Speculative execution not yet supported")
        case 'commit':
            raise Exception("Speculative execution not yet supported")
        case _:
          raise Exception("Unhandled instruction type")


        
def eval_call(state : dict , func_name : str, local_vars : dict):
    """It is the responsibility of the calling function to preload the arguments of the function into the local_vars dictionary"""
    #get the named function from the state
    func=state['funcs'][func_name]
    instructions=func['instrs'] # retrieve list of instructions
    labels=func['labels'] #dictionary to look-up instruction # for jump and branch instructions
    instr_num=0
    total_instructions=len(instructions)
    result=None
    security_info=state['security_group']
    #get security info for this function
    sec_group=func.get('security',0)
    security_info.append(sec_group)
    while instr_num<total_instructions:
        current_instr=instructions[instr_num]
        # print("Instruction #: {}".format(state['instr_count']))
        # print("Current function name is: {}".format(func_name))
        # print("Current instruction is: {}".format(current_instr))
        # print(local_vars)
        action=eval_instr(state,local_vars,current_instr)
        state['instr_count']=state['instr_count']+1
        if action['action']=='next':
            instr_num+=1
        elif action['action']=='jump':
            instr_num=labels[action['label']]
        elif action['action']=='end':
            if 'ret' in action:
                result=action['ret']
            break
    #remove this functions security info
    security_info.pop()
    return result

def identify_label_instructions(instrs:list)->dict:
    result={}
    count=0
    for instr in instrs:
        if 'label' in instr:
            name=instr['label']
            result[name]=count
        count+=1
    return result

def parse_main_arguments(expected: list,actual: list) -> dict:
    main_local_vars={}
    if len(expected)!=len(actual):
        message="mismatched main argument arity: expected {0}; got {1}"
        message=message.format(expected,actual)
        raise Exception(message)
    for i in range(len(expected)):
        var=expected[i]
        bril_type=var['type']
        arg_name=var['name']
        value=actual[i]
        if bril_type=='int':
            value=int(value)
        elif bril_type=='float':
            value=float(value)
        elif bril_type=='bool':
            value=bool(value)
        main_local_vars[arg_name]=value
    return main_local_vars

def eval_program(program):
    bril_functions={}
    for func in program['functions']:
        #calculate labels
        label_locations=identify_label_instructions(func['instrs'])
        func['labels']=label_locations
        name=func['name']
        bril_functions[name]=func
    state={}
    structs=program.get('structs',[])
    bril_heap=HeapStore(structs)
    state['heap']=bril_heap
    state['instr_count']=0
    state['funcs']=bril_functions
    state['profiling']=False
    state['security_group']=[]
    args=sys.argv[1:]
    try:
        place=args.index('-p')
        state['profiling']=True
        args=args[place+1:]
    except ValueError:
        #there is no -p option
        pass
    #expected=bril_functions['main']['args']
    main_func=bril_functions['main']
    if 'args' in main_func:
        expected=main_func['args']
        local_vars=parse_main_arguments(expected,args)
    else:
        local_vars={}
    result=eval_call(state,'main',local_vars)
    
    if not bril_heap.is_empty():
        raise Exception('Error: Some memory locations have not been freed by end of execution')
    
    if state['profiling']:
        message='total_dyn_inst: ' + str(state['instr_count'])+'\n'
        sys.stderr.write(message)




if __name__ == '__main__':
  #
  #read program from std-in
  raw_prog=sys.stdin.read()
#   raw_prog="""{
#   "functions": [
#     {
#       "args": [
#         {
#           "name": "head",
#           "type": "int"
#         },
#         {
#           "name": "tail",
#           "type": {
#             "ptr": "int_list"
#           }
#         }
#       ],
#       "instrs": [
#         {
#           "dest": "one",
#           "op": "const",
#           "type": "int",
#           "value": 1
#         },
#         {
#           "args": [
#             "one"
#           ],
#           "dest": "p",
#           "op": "alloc",
#           "type": {
#             "ptr": "int_list"
#           }
#         },
#         {
#           "args": [
#             "p",
#             "elt"
#           ],
#           "dest": "phead",
#           "op": "getmbr",
#           "type": {
#             "ptr": "int"
#           }
#         },
#         {
#           "args": [
#             "p",
#             "next"
#           ],
#           "dest": "ptail",
#           "op": "getmbr",
#           "type": {
#             "ptr": {
#               "ptr": "int_list"
#             }
#           }
#         },
#         {
#           "args": [
#             "phead",
#             "head"
#           ],
#           "op": "store"
#         },
#         {
#           "args": [
#             "ptail",
#             "tail"
#           ],
#           "op": "store"
#         },
#         {
#           "args": [
#             "p"
#           ],
#           "op": "ret"
#         }
#       ],
#       "name": "cons",
#       "type": {
#         "ptr": "int_list"
#       }
#     },
#     {
#       "args": [
#         {
#           "name": "list",
#           "type": {
#             "ptr": "int_list"
#           }
#         }
#       ],
#       "instrs": [
#         {
#           "args": [
#             "list"
#           ],
#           "dest": "empty",
#           "op": "isnull",
#           "type": "bool"
#         },
#         {
#           "args": [
#             "empty"
#           ],
#           "labels": [
#             "end",
#             "print"
#           ],
#           "op": "br"
#         },
#         {
#           "label": "print"
#         },
#         {
#           "args": [
#             "list",
#             "elt"
#           ],
#           "dest": "xp",
#           "op": "getmbr",
#           "type": {
#             "ptr": "int"
#           }
#         },
#         {
#           "args": [
#             "xp"
#           ],
#           "dest": "x",
#           "op": "load",
#           "type": "int"
#         },
#         {
#           "args": [
#             "x"
#           ],
#           "op": "print"
#         },
#         {
#           "args": [
#             "list",
#             "next"
#           ],
#           "dest": "tp",
#           "op": "getmbr",
#           "type": {
#             "ptr": {
#               "ptr": "int_list"
#             }
#           }
#         },
#         {
#           "args": [
#             "tp"
#           ],
#           "dest": "t",
#           "op": "load",
#           "type": {
#             "ptr": "int_list"
#           }
#         },
#         {
#           "args": [
#             "t"
#           ],
#           "funcs": [
#             "print_list"
#           ],
#           "op": "call"
#         },
#         {
#           "label": "end"
#         },
#         {
#           "op": "ret"
#         }
#       ],
#       "name": "print_list"
#     },
#     {
#       "args": [
#         {
#           "name": "list",
#           "type": {
#             "ptr": "int_list"
#           }
#         }
#       ],
#       "instrs": [
#         {
#           "args": [
#             "list"
#           ],
#           "dest": "empty",
#           "op": "isnull",
#           "type": "bool"
#         },
#         {
#           "args": [
#             "empty"
#           ],
#           "labels": [
#             "end",
#             "freetail"
#           ],
#           "op": "br"
#         },
#         {
#           "label": "freetail"
#         },
#         {
#           "args": [
#             "list",
#             "next"
#           ],
#           "dest": "tp",
#           "op": "getmbr",
#           "type": {
#             "ptr": {
#               "ptr": "int_list"
#             }
#           }
#         },
#         {
#           "args": [
#             "tp"
#           ],
#           "dest": "t",
#           "op": "load",
#           "type": {
#             "ptr": "int_list"
#           }
#         },
#         {
#           "args": [
#             "t"
#           ],
#           "funcs": [
#             "free_list"
#           ],
#           "op": "call"
#         },
#         {
#           "args": [
#             "list"
#           ],
#           "op": "free"
#         },
#         {
#           "label": "end"
#         },
#         {
#           "op": "ret"
#         }
#       ],
#       "name": "free_list"
#     },
#     {
#       "instrs": [
#         {
#           "dest": "a",
#           "op": "const",
#           "type": "int",
#           "value": 2
#         },
#         {
#           "dest": "b",
#           "op": "const",
#           "type": "int",
#           "value": 3
#         },
#         {
#           "dest": "c",
#           "op": "const",
#           "type": "int",
#           "value": 5
#         },
#         {
#           "dest": "d",
#           "op": "const",
#           "type": "int",
#           "value": 8
#         },
#         {
#           "dest": "n",
#           "op": "const",
#           "type": {
#             "ptr": "int_list"
#           },
#           "value": 0
#         },
#         {
#           "args": [
#             "a",
#             "n"
#           ],
#           "dest": "s0",
#           "funcs": [
#             "cons"
#           ],
#           "op": "call",
#           "type": {
#             "ptr": "int_list"
#           }
#         },
#         {
#           "args": [
#             "b",
#             "s0"
#           ],
#           "dest": "s1",
#           "funcs": [
#             "cons"
#           ],
#           "op": "call",
#           "type": {
#             "ptr": "int_list"
#           }
#         },
#         {
#           "args": [
#             "c",
#             "s1"
#           ],
#           "dest": "s2",
#           "funcs": [
#             "cons"
#           ],
#           "op": "call",
#           "type": {
#             "ptr": "int_list"
#           }
#         },
#         {
#           "args": [
#             "d",
#             "s2"
#           ],
#           "dest": "s3",
#           "funcs": [
#             "cons"
#           ],
#           "op": "call",
#           "type": {
#             "ptr": "int_list"
#           }
#         },
#         {
#           "args": [
#             "s3"
#           ],
#           "funcs": [
#             "print_list"
#           ],
#           "op": "call"
#         },
#         {
#           "args": [
#             "s3"
#           ],
#           "funcs": [
#             "free_list"
#           ],
#           "op": "call"
#         },
#         {
#           "op": "ret"
#         }
#       ],
#       "name": "main"
#     }
#   ],
#   "structs": [
#     {
#       "mbrs": [
#         {
#           "name": "elt",
#           "type": "int"
#         },
#         {
#           "name": "next",
#           "type": {
#             "ptr": "int_list"
#           }
#         }
#       ],
#       "name": "int_list"
#     }
#   ]
# }"""

  #parse program text into JSON
  prog=json.loads(raw_prog)

  result=eval_program(prog)




    
