import sys
import os

from sys import argv, exit

import logging

logging.basicConfig(
     level = logging.DEBUG,
     filename = "gencode.log",
     filemode = "w",
     format = "%(filename)10s:%(lineno)4d:%(message)s"
)
log = logging.getLogger()

import ply.yacc as yacc

from tppsema import main as tppsema_main

# Get the token map from the lexer.  This is required.
from tpplex import tokens

from mytree import MyNode
from anytree.exporter import DotExporter, UniqueDotExporter
from anytree import RenderTree, AsciiStyle, PreOrderIter

from myerror import MyError

from llvmlite import ir
from llvmlite import binding as llvm

error_handler = MyError('GenCodeErrors')
sem = MyError('SemaErrors')
syn = MyError('ParserErrors')
le = MyError('LexerErrors')

checkKey = False
checkTpp = False

errorArray = []
warningArray = []

root = None

leiaF = None
leiaI = None
escrevaF = None
escrevaI = None
arrError = []
module = None
builder = None
varList = []
iftrue = []
iffalse = []
ifend = []
func = None
funcList = []



# Funcoes Basicas

def browse_node(node, caminho):
    nodeAux = node
    for prox in caminho:
        if prox < 0: 
            nodeAux = nodeAux.parent
        else:
            nodeAux = nodeAux.children[prox]
    return nodeAux
    
def what_type(str):
    inteiro = ["INTEIRO","inteiro","NUM_INTEIRO"]
    flutuante = ["flutuante","NUM_PONTO_FLUTUANTE","FLUTUANTE"]

    if(str in inteiro):
        return "INTEIRO"

    if(str in flutuante):
        return "FLUTUANTE"
    
def create_type_var(str):
    type = what_type(str)

    if(type == "INTEIRO"):
        return ir.IntType(32)
    
    if(type == "FLUTUANTE"):
        return ir.FloatType()
    
    return None

def create_var(node,scope):
    global varList 
    global builder
    global module

    type = create_type_var(browse_node(node, [0,0]).name)
    typel = what_type(browse_node(node, [0,0]).name)
    nodeAux = browse_node(node, [2])
    while len(nodeAux.children) > 2:

        name = browse_node(nodeAux,[2,0,0]).name
        if(scope == None):
            var = ir.GlobalVariable(module, type, name)
        else:
            var = builder.alloca(type, name=name)

        var.initializer = ir.Constant(type, 0)
        var.align = 4
        varList.append({"scope": scope, "name": name,"var" : var, "type": typel})
        nodeAux = browse_node(nodeAux, [0])
    
    name = browse_node(nodeAux,[0,0,0]).name

    if(scope == None):
        var = ir.GlobalVariable(module, type, name)
    else:
        var = builder.alloca(type, name=name)

    var.initializer = ir.Constant(type, 0)
    var.align = 4
    varList.append({"scope": scope, "name": name,"var" : var, "type": typel})

def getVarInList(varName, scope):
    global varList
    global func
 
    for var in varList:
        if( varName == var["name"] and scope == var["scope"]):
            return var["var"]

    for var in func.args:
        if (var.name == varName and scope == func.name):
            return var

    for var in varList:
        if(varName == var["name"] and None == var["scope"]):
            return var["var"]
        
def getFuncInList(funcName):
    global funcList

    for func in funcList:
        if func["name"] == funcName:
            return func["func"]

def atribution(node, scope):
    global builder
    
    NodeAux = None
    
    var = browse_node(node, [0,0,0])
    var_name = var.name
    var_ptr = getVarInList(var_name, scope)
    
    NodeAux = browse_node(node, [2])
    varRes = expressions(NodeAux, scope)

    builder.store(varRes,var_ptr)

def give_args_list(node, scope):
    argsList = []
    nodeAux = None
    ignore_nodes = set()    

    for node in (PreOrderIter(node)):
        
        if any(parent in ignore_nodes for parent in node.ancestors):
            continue

        if node.name in ["chamada_funcao"]:
            ignore_nodes.add(node)
            continue

        if(node.name == 'lista_argumentos'):
            if(len(node.children) > 1):
                nodeAux = browse_node(node, [2])
            else:
                nodeAux = browse_node(node, [0])
       
            argsList.insert(0,expressions(nodeAux, scope))

    return argsList

def expressions_aux(x_temp, y_temp, operation):
    if operation == '>':
        result = builder.icmp_signed('>', x_temp, y_temp, name='maior')
    elif operation == '<':
        result = builder.icmp_signed('<', x_temp, y_temp, name='menor')
    elif operation == '>=':
        result = builder.icmp_signed('>=', x_temp, y_temp, name='maiorIgual')
    elif operation == '<=':
        result = builder.icmp_signed('<=', x_temp, y_temp, name='menorIgual')
    elif operation == '=':
        result = builder.icmp_signed('==', x_temp, y_temp, name='igual')
    elif operation == '<>':
        result = builder.icmp_signed('!=', x_temp, y_temp, name='diferente')
    elif operation == '&&':
        result = builder.and_(x_temp, y_temp, name='and')
    elif operation == '||':
        result = builder.or_(x_temp, y_temp, name='or')
    elif operation == '!':
        result = builder.not_(x_temp, name='>>>> ''not')
    elif operation == '+':
        result = builder.add(x_temp, y_temp, name='soma')
    elif operation == '-':
        result = builder.sub(x_temp, y_temp, name='subtracao')
    elif operation == '*':
        result = builder.mul(x_temp, y_temp, name='multiplicacao')
    elif operation == '/':
        result = builder.sdiv(x_temp, y_temp, name='divisao')
    elif operation == '%':
        result = builder.srem(x_temp, y_temp, name='modulo')
    elif operation == '>>':
        um = ir.Constant(ir.IntType(32), 1)
        result = builder.ashr(x_temp, um, name='shiftDireita')
    elif operation == '<<':
        um = ir.Constant(ir.IntType(32), 1)
        result = builder.shl(x_temp, um, name='shiftEsquerda')
    else:
        raise ValueError("Operação desconhecida")
    
    return result

def expressions(nodeE, scope):
    global builder

    inteiro = ["INTEIRO","inteiro","NUM_INTEIRO"]
    flutuante = ["flutuante","NUM_PONTO_FLUTUANTE", "FLUTUANTE"]
    sinais_aritmeticos = ["+", "-", "*", "/", "%"]
    sinais_logicos = [">", "<", ">=", "<=", "=", "<>", "&&", "||", "!"]

    x_temp = None
    y_temp = None
    nodeAux = None
    varType = None
    expression = None
    var = None
    func = None
    ignore_nodes = set()

    for node in (PreOrderIter(nodeE)):
        if any(parent in ignore_nodes for parent in node.ancestors):
            continue

        if node.name in ["chamada_funcao", "lista_argumentos"]:
            ignore_nodes.add(node)
            continue

        if node.name == "fator":
            if(browse_node(node, [0]).name == 'chamada_funcao'):
                
                nodeAux = browse_node(node, [0,0,0])
                func = getFuncInList(nodeAux.name)
                
                nodeAux = browse_node(node, [0,2])
                if(x_temp == None):
                    x_temp = builder.call(func, give_args_list(nodeAux, scope))
                else:
                    y_temp = builder.call(func, give_args_list(nodeAux, scope))
                    
            elif(browse_node(node, [0,0]).name == "ID"):
                nodeAux = browse_node(node, [0,0,0])
                if(x_temp == None):
                    var = getVarInList(nodeAux.name, scope)
                    if isinstance(var, ir.instructions.AllocaInstr) or isinstance(var, ir.values.GlobalVariable):
                        x_temp = builder.load(var, name='x_temp')
                    else:
                        x_temp = var

                else:
                    var = getVarInList(nodeAux.name, scope)
                    if isinstance(var, ir.instructions.AllocaInstr) or isinstance(var, ir.values.GlobalVariable):
                        y_temp = builder.load(var, name='y_temp')
                    else:
                        y_temp = var

                    x_temp = expressions_aux(x_temp, y_temp, expression)
                    y_temp = None
                    expression = None

            elif(browse_node(node, [0,0]).name in flutuante or browse_node(node, [0,0]).name in inteiro):
                nodeAux = browse_node(node, [0,0])
                varType = create_type_var(nodeAux.name)
                nodeAux = browse_node(nodeAux, [0])
                if(x_temp == None):
                    if (varType == ir.FloatType()):
                        x_temp = ir.Constant(varType,float(nodeAux.name))
                    else:
                        x_temp = ir.Constant(varType,nodeAux.name)
                else:
                    y_temp = ir.Constant(varType,nodeAux.name)
                    x_temp = expressions_aux(x_temp, y_temp, expression)
                    y_temp = None
                    expression = None
            
        if(node.name in sinais_aritmeticos or node.name in sinais_logicos): 
            expression = node.name

    return(x_temp)

def condicao(node, scope, func):
    global builder
    global iftrue
    global iffalse
    global ifend
    
    haveElse = len(node.children) > 5
    
    nodeAux = browse_node(node, [1])
    expressionRes = expressions(nodeAux, scope)
    
    if(haveElse):
        iftrue.append(func.append_basic_block('iftrue_1'))
        iffalse.append(func.append_basic_block('iffalse_1'))
        ifend.append(func.append_basic_block('ifend_1'))

        builder.cbranch(expressionRes,iftrue[-1], iffalse[-1])
    else : 
        iftrue.append(func.append_basic_block('iftrue_1'))
        ifend.append(func.append_basic_block('ifend_1'))

        builder.cbranch(expressionRes,iftrue[-1], ifend[-1])

    builder.position_at_end(iftrue.pop())

def get_type_in_list(varName, scope, list):
    for var in list:
        if(varName == var["name"] and scope == var["scope"]):
            return var["type"]

    for var in list:
        if(varName == var["name"] and None == var["scope"]):
            return var["type"]

def add_another_var_in_list(node, scope, list):
    varType = what_type(browse_node(node, [0,0]).name)
    nodeAux = browse_node(node, [2])
    while len(nodeAux.children) > 2:
        name = browse_node(nodeAux,[2,0,0]).name
        list.append({"name": name, "scope": scope, "type": varType})
        nodeAux = browse_node(nodeAux, [0])
    
    name = browse_node(nodeAux,[0,0,0]).name

    list.append({"name": name, "scope": scope, "type": varType})

def find_first_type_var(expressionNode,list,scope):
    nodeAux = None
    for node in (PreOrderIter(expressionNode)):
        if(node.name == 'fator'):
            nodeAux = browse_node(node, [0,0])

            if(nodeAux.name == 'ID'):
                nodeAux = browse_node(nodeAux, [0])
                return get_type_in_list(nodeAux.name,scope,list)
            else:
                return what_type(nodeAux.name)    

def verify_read_print(tree):
    global module
    global leiaF
    global leiaI
    global escrevaF
    global escrevaI

    inteiro = ["INTEIRO","inteiro","NUM_INTEIRO"]
    flutuante = ["flutuante","NUM_PONTO_FLUTUANTE", "FLUTUANTE"]
    
    haveReadInt = False
    haveReadFloat = False
    havePrintInt = False
    havePrintFloat = False

    nodeAux = None
    nameVar = None
    type = None
    scope = None
    list = []

    for node in (PreOrderIter(tree)):
        
        if(node.name == "declaracao_funcao"):
            scope = browse_node(node, [1,0,0]).name

        if(node.name == "declaracao_variaveis"):
            add_another_var_in_list(node,scope,list)

        if(node.name == "leia" and len(node.children) > 1):
            nameVar = browse_node(node,[2,0,0]).name
            type = get_type_in_list(nameVar, scope, list)

            if(type in flutuante and not haveReadFloat):
                _leiaF = ir.FunctionType(ir.FloatType(), [])
                leiaF = ir.Function(module, _leiaF, "leiaFlutuante")
                haveReadFloat = True
            
            if(type in inteiro and not haveReadInt):
                _leiaI = ir.FunctionType(ir.IntType(32), [])
                leiaI = ir.Function(module, _leiaI, "leiaInteiro")
                haveReadInt = True
            
        if(node.name == "escreva" and len(node.children) > 1):
            
            nodeAux = browse_node(node, [2])
            type = find_first_type_var(nodeAux,list,scope)
            if(type in flutuante and not havePrintFloat):
                _escrevaF = ir.FunctionType(ir.VoidType(), [ir.FloatType()])
                escrevaF = ir.Function(module, _escrevaF, "escrevaFlutuante")
                havePrintFloat = True

            if(type in inteiro and not havePrintInt):
                _escrevaI = ir.FunctionType(ir.VoidType(), [ir.IntType(32)])
                escrevaI = ir.Function(module, _escrevaI, "escrevaInteiro")
                havePrintInt = True

def verify_params(functionDeclarationNode):
    nodeAux = browse_node(functionDeclarationNode, [1,2])

    name = None
    typeList = []
    varNameList = []
    type = None

    for node in (PreOrderIter(nodeAux)):
        if(node.name == "parametro"):
            name = browse_node(node, [2,0]).name
            type = create_type_var(browse_node(node, [0,0]).name)
            typeList.append(type)
            varNameList.append(name)   

    return(varNameList, typeList)
            


# Execucao

def init(file_name):
    global module

    llvm.initialize()
    llvm.initialize_all_targets()
    llvm.initialize_native_target()
    llvm.initialize_native_asmprinter()

    module = ir.Module(file_name + '.bc')
    module.triple = llvm.get_process_triple()
    target = llvm.Target.from_triple(module.triple)
    target_machine = target.create_target_machine()
    module.data_layout = target_machine.target_data

def execute_order_66(tree, file_name):
    global module

    init(file_name)

    aux_vars = {"entryBlock": None,
               "endBasicBlock": None,
               "scope": None,
               "escreva": False,
               "loop": None,
               "loopVal": [],
               "lopeEnd": [],
               "nodeAux": None,
               "type": None,
               "var": None,
               "functInfo": None,
               "name": None}

    verify_read_print(tree)

    for node in (PreOrderIter(tree)):
        aux_vars["nodeAux"] = None
        aux_vars["type"] = None
        aux_vars["var"] = None
        aux_vars["functInfo"] = None
        aux_vars["name"] = None

        if(node.name == "declaracao_funcao"):
            aux_vars = declaracao_funcao(node, aux_vars)

        if(node.name == "fim"):
            aux_vars = fim(node, aux_vars)

        if(node.name == "retorna" and len(node.children) > 1):
            aux_vars = retorna(node, aux_vars)
        
        if(node.name == "declaracao_variaveis"):
            aux_vars = declaracao_variaveis(node, aux_vars)

        if(node.name == "atribuicao"):
            aux_vars = atribuicao(node, aux_vars)

        if(node.name == "se" and len(node.children) > 1):
            aux_vars = se(node, aux_vars)

        if(node.name == "SENAO"):
            aux_vars = senao(aux_vars)

        if(node.name == "escreva" and len(node.children) > 1):
            aux_vars = escreva(node, aux_vars)             

        if(node.name == "leia" and len(node.children) > 1):
            aux_vars = leia(node, aux_vars)
        
        if(node.name == 'repita' and len(node.children) > 1):
            aux_vars = repita(aux_vars)

        if(node.name == 'ATE' and browse_node(node,[-1]).name == 'repita'):
            aux_vars = ate(node, aux_vars)
        
    arquive = open('./tests/'+file_name+'.ll', 'w')
    arquive.write(str(module))
    arquive.close()



# Construtores

def declaracao_funcao(node, aux_vars):
    global module
    global builder
    global varList
    global func
    global funcList

    aux_vars["name"] = browse_node(node, [1,0,0]).name
    if(aux_vars["name"] == 'principal'):
        aux_vars["name"] = 'main'
    elif(aux_vars["name"] == 'main'):
        aux_vars["name"] = 'principal'
    
    aux_vars["scope"] = aux_vars["name"]
    aux_vars["type"] = browse_node(node, [0,0,0]).name
    
    aux_vars["var"] = create_type_var(aux_vars["type"])
    
    varNameList, typeList = verify_params(node)

    aux_vars["functInfo"] = ir.FunctionType(aux_vars["var"], typeList)
    func = ir.Function(module, aux_vars["functInfo"], name=aux_vars["name"])
    funcList.append({"name": aux_vars["name"], "func": func})
    
    for i in range(len(varNameList)):
        func.args[i].name = varNameList[i] + "_param"
    entryBlock = func.append_basic_block('entry')
    
    builder = ir.IRBuilder(entryBlock)
    
    builder.position_at_start(entryBlock)
    for i in range(len(varNameList)):
        typel = what_type(type)
        var2 = builder.alloca(aux_vars["var"], name=varNameList[i])
        var2.initializer = ir.Constant(aux_vars["var"], 0)
        var2.align = 4
        varList.append({"scope": aux_vars["scope"], "name": varNameList[i],"var" : var2, "type": typel})
        
        var_ptr = getVarInList(varNameList[i], aux_vars["scope"])
        varRes = getVarInList(varNameList[i] + "_param", aux_vars["scope"])
        builder.store(varRes,var_ptr)

    return aux_vars

def fim(node, aux_vars):
    global builder
    global ifend
    
    if(browse_node(node, [-1,-1,-1]).name == "declaracao_funcao"):
        aux_vars["scope"] = None

    if(browse_node(node, [-1,-1]).name == "se"):
        builder.branch(ifend[-1])
        builder.position_at_end(ifend.pop())

    return aux_vars

def retorna(node, aux_vars):
    global builder

    aux_vars["nodeAux"] = browse_node(node, [2])
    builder.ret(expressions(aux_vars["nodeAux"], aux_vars["scope"]))

    return aux_vars

def declaracao_variaveis(node, aux_vars):
    create_var(node, aux_vars["scope"])

    return aux_vars

def atribuicao(node, aux_vars):
    atribution(node, aux_vars["scope"])

    return aux_vars

def se(node, aux_vars):
    condicao(node,aux_vars["scope"],func)

    return aux_vars

def senao(aux_vars):
    global builder
    global iffalse
    global ifend

    builder.branch(ifend[-1])
    builder.position_at_end(iffalse.pop())

    return aux_vars

def escreva(node, aux_vars):
    global builder
    global varList
    global escrevaF
    global escrevaI

    aux_vars["nodeAux"] = browse_node(node, [2])
    aux_vars["type"] = find_first_type_var(aux_vars["nodeAux"], varList, aux_vars["scope"])

    if(aux_vars["type"] == 'INTEIRO'):
        builder.call(escrevaI, args=[expressions(aux_vars["nodeAux"], aux_vars["scope"])]) 

    if(aux_vars["type"] == 'FLUTUANTE'):
        builder.call(escrevaF, args=[expressions(aux_vars["nodeAux"], aux_vars["scope"])]) 

    return aux_vars

def leia(node, aux_vars):
    global builder
    global varList
    global leiaF
    global leiaI

    aux_vars["nodeAux"] = browse_node(node, [2,0,0])
    aux_vars["name"] = aux_vars["nodeAux"].name
    aux_vars["type"] = get_type_in_list(aux_vars["name"], aux_vars["scope"], varList)
    aux_vars["var"] = getVarInList(aux_vars["name"], aux_vars["scope"])

    if(aux_vars["type"] == 'INTEIRO'):
        resultado_leia = builder.call(leiaI, args=[])
        builder.store(resultado_leia, aux_vars["var"])

    if(aux_vars["type"] == 'FLUTUANTE'):
        resultado_leia = builder.call(leiaF, args=[])
        builder.store(resultado_leia, aux_vars["var"])

    return aux_vars

def repita(aux_vars):
    global builder

    aux_vars["loop"] = builder.append_basic_block('loop')
    builder.branch(aux_vars["loop"])
    builder.position_at_end(aux_vars["loop"])

    return aux_vars

def ate(node, aux_vars):
    global builder

    aux_vars["loop_val"] = builder.append_basic_block('loop_val')
    aux_vars["loop_end"] = builder.append_basic_block('loop_end')
    builder.branch(aux_vars["loop_val"])
    builder.position_at_end(aux_vars["loop_val"])
    aux_vars["nodeAux"] = browse_node(node, [-1,3])
    var = expressions(aux_vars["nodeAux"], aux_vars["scope"])
    builder.cbranch(var, aux_vars["loop_end"], aux_vars["loop"])

    builder.position_at_end(aux_vars["loop_end"])

    return aux_vars



# Programa Principal

def main():
    global checkKey
    global checkTpp
    global errorArray
    global warningArray

    if(len(sys.argv) < 2):
        errorArray.append(error_handler.newError(checkKey, 'ERR-SEM-USE'))
        raise TypeError(error_handler.newError(checkKey, 'ERR-SEM-USE'))

    posArgv = 0

    for idx,arg in enumerate(sys.argv):
        aux = arg.split('.')
        if aux[-1] == 'tpp':
            checkTpp = True
            posArgv = idx
        
        if arg == "-k":
            checkKey = True
    
    if checkKey and len(sys.argv) < 3:
        errorArray.append(le.newError(checkKey, 'ERR-GC-USE'))
        raise TypeError(errorArray)
    elif not checkTpp:
        errorArray.append(le.newError(checkKey, 'ERR-GC-NOT-TPP'))
        raise IOError(errorArray)
    elif not os.path.exists(argv[posArgv]):
        errorArray.append(le.newError(checkKey, 'ERR-GC-FILE-NOT-EXISTS'))
        raise IOError(errorArray)
    else:
        root, warning_array = tppsema_main(sys.argv)

        execute_order_66(root, argv[posArgv].split('.')[1].split('/')[-1])

        # To visualize the tree:
        #for pre, fill, node in RenderTree(root):
        #    print(f"{pre}{node.name}")

    errorArray += warning_array

    if len(errorArray) > 0:
        raise IOError(errorArray)
    
    else:
        print('\n--------------------------------------------- RES-GEN ---------------------------------------------\n')

if __name__ == "__main__": 
    try:
        main()
    except Exception as e:
        print('\n--------------------------------------------- ERR-GEN ---------------------------------------------\n')
        for x in range(len(e.args[0])):
            print (e.args[0][x])
    except (ValueError, TypeError):
        print('\n-------------------------------------------------------------------------------------------\n')
        for x in range(len(e.args[0])):
            print (e.args[0][x])