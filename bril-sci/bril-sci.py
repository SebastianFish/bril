import sys, json
from validation import validate

#interpreter to implement bril language with SCI memory extensions

#read program from std-in
raw_prog=sys.stdin.read()

#parse program text into JSON
prog=json.loads(raw_prog)

is_valid=validate(prog)

class DataHeap:
    """This class implements heap data for the interpreter. It also, optionally, 
    includes protections against supply chain attacks by limiting which memory addresses groups
    of functions are allowed to modify
    """

    def __init__(self) -> None:
        self.objects=[]
        self.allocations=[]

    def alloc(self,security_group,bril_type,number)->int:
        head=self.head
        new_head=head+number
        for i in range(head,new_head):
            self.types.append(bril_type)
            self.security_group.append(security_group)




    
